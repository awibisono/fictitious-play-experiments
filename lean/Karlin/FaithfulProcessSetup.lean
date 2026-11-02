import Karlin.FaithfulBiasSetup
import Karlin.FaithfulClock
import Karlin.FaithfulGameReindex

/-! The full infinite-process versions of v15 lem:bias and lem:setup.
The initial score vector is arbitrary; no Clock, phase word, or asymptotic
premise is imposed. A supplied action b witnesses the nonempty recurrent set.
Decision time zero of the score process becomes time one after setup. -/
namespace Karlin.FaithfulProcessSetup
open scoped BigOperators
open FaithfulClock FaithfulWindow
variable {m : ℕ}

def score (M : Matrix (Fin m) (Fin m) ℚ) (f : Fin m → ℚ)
    (a : ℕ → Fin m) (t : ℕ) (i : Fin m) : ℚ := f i + cumScore M a t i

@[simp] theorem score_zero (M : Matrix (Fin m) (Fin m) ℚ) (f : Fin m → ℚ)
    (a : ℕ → Fin m) (i : Fin m) : score M f a 0 i = f i := by
  simp [score, cumScore]

theorem score_succ (M : Matrix (Fin m) (Fin m) ℚ) (f : Fin m → ℚ)
    (a : ℕ → Fin m) (t : ℕ) (i : Fin m) :
    score M f a (t+1) i = score M f a t i + M i (a t) := by
  simp [score, cumScore_succ, add_assoc]

def IsWeakProcess (M : Matrix (Fin m) (Fin m) ℚ) (f : Fin m → ℚ)
    (a : ℕ → Fin m) : Prop := ∀ t i, score M f a t i ≤ score M f a t (a t)

def IsStrictProcess (M : Matrix (Fin m) (Fin m) ℚ) (f : Fin m → ℚ)
    (a : ℕ → Fin m) : Prop :=
  ∀ t i, i ≠ a t → score M f a t i < score M f a t (a t)

def IsPriorityProcess (M : Matrix (Fin m) (Fin m) ℚ) (f : Fin m → ℚ)
    (rank : Equiv.Perm (Fin m)) (a : ℕ → Fin m) : Prop :=
  ∀ t i, score M f a t i ≤ score M f a t (a t) ∧
    (i ≠ a t → score M f a t i = score M f a t (a t) →
      (rank (a t)).val < (rank i).val)

theorem strict_is_weak {M : Matrix (Fin m) (Fin m) ℚ} {f : Fin m → ℚ}
    {a : ℕ → Fin m} (ha : IsStrictProcess M f a) : IsWeakProcess M f a := by
  intro t i
  by_cases hi : i = a t
  · simp [hi]
  · exact (ha t i hi).le

theorem priority_action_exists (b : Fin m) (s : Fin m → ℚ)
    (rank : Equiv.Perm (Fin m)) :
    ∃ a : Fin m, ∀ i, s i ≤ s a ∧
      (i ≠ a → s i = s a → (rank a).val < (rank i).val) := by
  classical
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image Finset.univ s ⟨b,Finset.mem_univ b⟩
  let leaders := Finset.univ.filter (fun i => s i = s j)
  have hne : leaders.Nonempty := ⟨j, by simp [leaders]⟩
  obtain ⟨a,ha,hmin⟩ := Finset.exists_min_image leaders (fun i => (rank i).val) hne
  have hs : s a = s j := (Finset.mem_filter.mp ha).2
  refine ⟨a,fun i => ⟨by rw [hs]; exact hmax i (Finset.mem_univ i), ?_⟩⟩
  intro hi he
  have hmem : i ∈ leaders := by simp [leaders,he,hs]
  have hle := hmin i hmem
  have hneval : (rank a).val ≠ (rank i).val := by
    intro h
    exact hi (rank.injective (Fin.ext h)).symm
  omega

def priorityAction (b : Fin m) (s : Fin m → ℚ)
    (rank : Equiv.Perm (Fin m)) : Fin m := Encodable.choose (priority_action_exists b s rank)

theorem priorityAction_spec (b : Fin m) (s : Fin m → ℚ)
    (rank : Equiv.Perm (Fin m)) (i : Fin m) :
    s i ≤ s (priorityAction b s rank) ∧
      (i ≠ priorityAction b s rank → s i = s (priorityAction b s rank) →
        (rank (priorityAction b s rank)).val < (rank i).val) :=
  Encodable.choose_spec (priority_action_exists b s rank) i

def priorityState (b : Fin m) (M : Matrix (Fin m) (Fin m) ℚ)
    (f : Fin m → ℚ) (rank : Equiv.Perm (Fin m)) : ℕ → Fin m → ℚ
  | 0 => f
  | t+1 =>
      let previous := priorityState b M f rank t
      let chosen := priorityAction b previous rank
      fun i => previous i + M i chosen

def priorityPlay (b : Fin m) (M : Matrix (Fin m) (Fin m) ℚ)
    (f : Fin m → ℚ) (rank : Equiv.Perm (Fin m)) (t : ℕ) : Fin m :=
  priorityAction b (priorityState b M f rank t) rank

theorem priorityState_eq_score (b : Fin m) (M : Matrix (Fin m) (Fin m) ℚ)
    (f : Fin m → ℚ) (rank : Equiv.Perm (Fin m)) (t : ℕ) :
    priorityState b M f rank t = score M f (priorityPlay b M f rank) t := by
  induction t with
  | zero => ext i; simp [priorityState]
  | succ t ih =>
      ext i
      simp only [priorityState, score_succ, priorityPlay]
      rw [ih]

theorem priorityPlay_valid (b : Fin m) (M : Matrix (Fin m) (Fin m) ℚ)
    (f : Fin m → ℚ) (rank : Equiv.Perm (Fin m)) :
    IsPriorityProcess M f rank (priorityPlay b M f rank) := by
  intro t i
  have hh := priorityAction_spec b (priorityState b M f rank t) rank i
  simpa only [← priorityState_eq_score] using hh

/-- Exactly the manuscript's rational offsets with its least common grid
denominator; this one vector is fixed before any decision time. -/
def bias (M : Matrix (Fin m) (Fin m) ℚ) (f : Fin m → ℚ)
    (rank : Equiv.Perm (Fin m)) (i : Fin m) : ℚ :=
  tieRemovalBias (m:ℚ) (FaithfulBiasSetup.gridDenominator M f : ℚ) ((rank i).val:ℚ)

theorem biased_score (M : Matrix (Fin m) (Fin m) ℚ) (f beta : Fin m → ℚ)
    (a : ℕ → Fin m) (t : ℕ) (i : Fin m) :
    score M (fun i => f i+beta i) a t i = score M f a t i+beta i := by
  unfold score
  ring

theorem bias_difference_small (b : Fin m) (M : Matrix (Fin m) (Fin m) ℚ)
    (f : Fin m → ℚ) (rank : Equiv.Perm (Fin m)) (i j : Fin m) :
    |bias M f rank i-bias M f rank j| <
      1/(4*(FaithfulBiasSetup.gridDenominator M f : ℚ)) := by
  let D : ℚ := FaithfulBiasSetup.gridDenominator M f
  have hD : 0<D := by
    dsimp [D]
    exact_mod_cast FaithfulBiasSetup.gridDenominator_pos M f
  have hm : (0:ℚ)<m := by exact_mod_cast b.pos
  have hi : ((rank i).val:ℚ)<m := by exact_mod_cast (rank i).isLt
  have hj : ((rank j).val:ℚ)<m := by exact_mod_cast (rank j).isLt
  have hi0 : (0:ℚ)≤(rank i).val := Nat.cast_nonneg _
  have hj0 : (0:ℚ)≤(rank j).val := Nat.cast_nonneg _
  have he : bias M f rank i-bias M f rank j =
      (((rank j).val:ℚ)-((rank i).val:ℚ))/(4*(m:ℚ)*D) := by
    unfold bias tieRemovalBias
    dsimp [D]
    ring
  rw [he,abs_div,abs_of_pos (by positivity : 0<4*(m:ℚ)*D)]
  apply (div_lt_iff₀ (by positivity : 0<4*(m:ℚ)*D)).mpr
  have hr : 1/(4*D)*(4*(m:ℚ)*D) = m := by field_simp
  change |((rank j).val:ℚ)-((rank i).val:ℚ)| < 1/(4*D)*(4*(m:ℚ)*D)
  rw [hr]
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

theorem score_on_grid (M : Matrix (Fin m) (Fin m) ℚ) (f : Fin m → ℚ)
    (a : ℕ → Fin m) (t : ℕ) (i : Fin m) :
    ∃ z : ℤ, (FaithfulBiasSetup.gridDenominator M f : ℚ)*score M f a t i=z := by
  induction t with
  | zero => simpa using FaithfulBiasSetup.grid_vector M f i
  | succ t ih =>
      obtain ⟨z,hz⟩ := ih
      obtain ⟨w,hw⟩ := FaithfulBiasSetup.grid_matrix M f i (a t)
      refine ⟨z+w,?_⟩
      rw [score_succ,mul_add,hz,hw,Int.cast_add]

/-- The perturbation preserves every strict score comparison, for any action
history, not merely comparisons against the scheduled maximizer. -/
theorem strict_comparison_preserved (b : Fin m) (M : Matrix (Fin m) (Fin m) ℚ)
    (f : Fin m → ℚ) (rank : Equiv.Perm (Fin m)) (a : ℕ → Fin m)
    (t : ℕ) (i j : Fin m) (hij : score M f a t i < score M f a t j) :
    score M (fun i => f i+bias M f rank i) a t i <
      score M (fun i => f i+bias M f rank i) a t j := by
  let D : ℚ := FaithfulBiasSetup.gridDenominator M f
  have hD : 0<D := by
    dsimp [D]
    exact_mod_cast FaithfulBiasSetup.gridDenominator_pos M f
  have hgap := integer_grid_strict_gap hD (score_on_grid M f a t j)
    (score_on_grid M f a t i) hij
  have hsmall := (abs_lt.mp (bias_difference_small b M f rank i j)).2
  have hpos : 0<1/(4*D) := by positivity
  have he : 1/D=4*(1/(4*D)) := by field_simp
  change bias M f rank i-bias M f rank j < 1/(4*D) at hsmall
  rw [he] at hgap
  rw [biased_score,biased_score]
  linarith

/-- Every infinite priority process is made strict by the same exact bias.
The proof uses singleton phases, so all integer decision times are included. -/
theorem priority_bias_strict (b : Fin m) (M : Matrix (Fin m) (Fin m) ℚ)
    (f : Fin m → ℚ) (rank : Equiv.Perm (Fin m)) (a : ℕ → Fin m)
    (ha : IsPriorityProcess M f rank a) :
    IsStrictProcess M (fun i => f i+bias M f rank i) a := by
  have ht (t : ℕ) : wordScore M (score M f a t) [a t] = score M f a (t+1) := by
    ext i
    rw [wordScore_singleton, score_succ]
  have hp (t : ℕ) : IsValidPriorityWord M (score M f a t) rank [a t] := by
    intro u hu i
    have hu0 : u=0 := by simpa using hu
    subst u
    simpa [wordScore_nil] using ha t i
  have hh := (priority_phase_family_bias_strict M (score M f a) rank (fun t => [a t])
    b.pos (FaithfulBiasSetup.gridDenominator M f : ℚ)
    (by exact_mod_cast FaithfulBiasSetup.gridDenominator_pos M f)
    (FaithfulBiasSetup.grid_matrix M f)
    (by simpa using FaithfulBiasSetup.grid_vector M f) ht hp).1
  intro t i hi
  have h := hh t 0 (by simp) i (by simpa using hi)
  simpa only [List.take_zero, wordScore_nil, List.getElem_cons_zero, biased_score, bias] using h

/-- Uniqueness holds among all weakly maximizing score processes, not just a
second process already assumed to have strict choices. -/
theorem weak_process_eq_of_strict (M : Matrix (Fin m) (Fin m) ℚ) (f : Fin m → ℚ)
    (a c : ℕ → Fin m) (ha : IsStrictProcess M f a) (hc : IsWeakProcess M f c) : c=a := by
  funext t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      have he (i : Fin m) : score M f c t i = score M f a t i := by
        unfold score cumScore
        congr 1
        apply Finset.sum_congr rfl
        intro u hu
        rw [ih u (Finset.mem_range.mp hu)]
      by_contra hne
      have hw := hc t (a t)
      rw [he,he] at hw
      exact (not_lt_of_ge hw) (ha t (c t) hne)

/-- Lemma bias, without a pre-supplied trajectory-existence hypothesis. The
finite priority maximizer constructs the process from arbitrary rational data. -/
theorem rational_bias_realizes_priority (b : Fin m)
    (M : Matrix (Fin m) (Fin m) ℚ) (f : Fin m → ℚ) (rank : Equiv.Perm (Fin m)) :
    IsPriorityProcess M f rank (priorityPlay b M f rank) ∧
    IsStrictProcess M (fun i => f i+bias M f rank i) (priorityPlay b M f rank) ∧
    ∀ a, IsWeakProcess M (fun i => f i+bias M f rank i) a → a=priorityPlay b M f rank := by
  have hp := priorityPlay_valid b M f rank
  have hs := priority_bias_strict b M f rank _ hp
  exact ⟨hp,hs,fun a ha => weak_process_eq_of_strict M _ _ a hs ha⟩

/-- The literal minimum-based column from v15, not an arbitrary large shift. -/
def setupVector (b : Fin m) (f : Fin m → ℚ) (i : Fin m) : ℚ :=
  f i + FaithfulBiasSetup.shift b f

theorem setupVector_ge_one (b : Fin m) (f : Fin m → ℚ) (i : Fin m) :
    1 ≤ setupVector b f i := FaithfulBiasSetup.one_le_shift b f i

def setupGame (b : Fin m) (M : Matrix (Fin m) (Fin m) ℚ) (f : Fin m → ℚ) :
    Matrix (Option (Fin m)) (Option (Fin m)) ℚ := setupMatrix M (setupVector b f)

def setupPlay (a : ℕ → Fin m) : ℕ → Option (Fin m)
  | 0 => none
  | t+1 => some (a t)

theorem setup_game_skew (b : Fin m) {M : Matrix (Fin m) (Fin m) ℚ}
    (hM : IsSkewSymmetric M) (f : Fin m → ℚ) : IsSkewSymmetric (setupGame b M f) :=
  setupMatrix_skewSymmetric hM _

theorem setup_action_count : Fintype.card (Option (Fin m)) = m+1 := by simp

theorem setup_initial_action (a : ℕ → Fin m) : setupPlay a 0 = none := rfl

theorem setup_not_replayed (a : ℕ → Fin m) {t : ℕ} (ht : 1 ≤ t) :
    setupPlay a t ≠ none := by
  cases t with
  | zero => omega
  | succ t => simp [setupPlay]

theorem setup_zero_scores (b : Fin m) (M : Matrix (Fin m) (Fin m) ℚ)
    (f : Fin m → ℚ) (a : ℕ → Fin m) (i : Option (Fin m)) :
    cumScore (setupGame b M f) (setupPlay a) 0 i = 0 := by simp [cumScore]

theorem setup_zero_empirical_counts (a : ℕ → Fin m) (i : Option (Fin m)) :
    (∑ s ∈ Finset.range 0, if setupPlay a s = i then (1:ℕ) else 0) = 0 := by simp

/-- Exact time convention: after the one setup round, process time t appears
at FP decision time t+1 with the same fixed translation. -/
theorem setup_score_some (b : Fin m) (M : Matrix (Fin m) (Fin m) ℚ)
    (f : Fin m → ℚ) (a : ℕ → Fin m) (t : ℕ) (i : Fin m) :
    cumScore (setupGame b M f) (setupPlay a) (t+1) (some i) =
      score M f a t i + FaithfulBiasSetup.shift b f := by
  induction t with
  | zero => simp [cumScore, setupGame, setupMatrix, setupPlay, setupVector]
  | succ t ih =>
      rw [cumScore_succ, ih, score_succ]
      simp [setupGame, setupMatrix, setupPlay]
      ring

theorem setup_score_none_le (b : Fin m) (M : Matrix (Fin m) (Fin m) ℚ)
    (f : Fin m → ℚ) (a : ℕ → Fin m) (t : ℕ) :
    cumScore (setupGame b M f) (setupPlay a) (t+1) none ≤ -(t:ℚ) := by
  induction t with
  | zero => simp [cumScore,setupGame,setupMatrix,setupPlay]
  | succ t ih =>
      rw [cumScore_succ]
      change cumScore (setupGame b M f) (setupPlay a) (t+1) none +
        -setupVector b f (a t) ≤ -((t+1:ℕ):ℚ)
      push_cast
      linarith [setupVector_ge_one b f (a t)]

theorem process_active_monotone {M : Matrix (Fin m) (Fin m) ℚ}
    (hM : IsSkewSymmetric M) {f : Fin m → ℚ} {a : ℕ → Fin m}
    (ha : IsStrictProcess M f a) : Monotone (fun t => score M f a t (a t)) := by
  apply monotone_nat_of_le_succ
  intro t
  have hh := strict_is_weak ha (t+1) (a t)
  rw [score_succ M f a t (a t), skew_diag_zero hM, add_zero] at hh
  exact hh

theorem setup_active_ge_one (b : Fin m) {M : Matrix (Fin m) (Fin m) ℚ}
    (hM : IsSkewSymmetric M) {f : Fin m → ℚ} {a : ℕ → Fin m}
    (ha : IsStrictProcess M f a) (t : ℕ) :
    1 ≤ cumScore (setupGame b M f) (setupPlay a) (t+1) (some (a t)) := by
  have hm := process_active_monotone hM ha (Nat.zero_le t)
  simp only [score_zero] at hm
  rw [setup_score_some]
  have hh := setupVector_ge_one b f (a 0)
  change 1 ≤ f (a 0) + FaithfulBiasSetup.shift b f at hh
  linarith

/-- Lemma setup for an arbitrary infinite strict score process. Strictness
starts at FP decision time one, while all initial FP counts and scores are zero. -/
theorem setup_strict (b : Fin m) {M : Matrix (Fin m) (Fin m) ℚ}
    (hM : IsSkewSymmetric M) {f : Fin m → ℚ} {a : ℕ → Fin m}
    (ha : IsStrictProcess M f a) : IsStrictFPTrajectory (setupGame b M f) (setupPlay a) := by
  intro t ht j hj
  cases t with
  | zero => omega
  | succ t =>
      cases j with
      | none =>
          have hlo := setup_score_none_le b M f a t
          have hhi := setup_active_ge_one b hM ha t
          change cumScore (setupGame b M f) (setupPlay a) (t+1) none <
            cumScore (setupGame b M f) (setupPlay a) (t+1) (some (a t))
          have hn : (0:ℚ) ≤ t := Nat.cast_nonneg t
          linarith
      | some i =>
          have hi : i ≠ a t := by simpa [setupPlay] using hj
          change cumScore (setupGame b M f) (setupPlay a) (t+1) (some i) <
            cumScore (setupGame b M f) (setupPlay a) (t+1) (some (a t))
          rw [setup_score_some, setup_score_some]
          linarith [ha t i hi]

theorem setup_strict_simultaneous (b : Fin m) {M : Matrix (Fin m) (Fin m) ℚ}
    (hM : IsSkewSymmetric M) {f : Fin m → ℚ} {a : ℕ → Fin m}
    (ha : IsStrictProcess M f a) :
    IsStrictTwoPlayerFPTrajectory (setupGame b M f) (setupPlay a) (setupPlay a) :=
  (isStrictTwoPlayerFPTrajectory_iff_isStrictFPTrajectory (setup_game_skew b hM f) _).mpr
    (setup_strict b hM ha)

theorem setup_unique (b : Fin m) {M : Matrix (Fin m) (Fin m) ℚ}
    (hM : IsSkewSymmetric M) {f : Fin m → ℚ} {a : ℕ → Fin m}
    (ha : IsStrictProcess M f a) (row col : ℕ → Option (Fin m))
    (hw : IsWeakTwoPlayerFPTrajectory (setupGame b M f) row col)
    (hr : row 0=none) (hc : col 0=none) (t : ℕ) :
    row t=setupPlay a t ∧ col t=setupPlay a t :=
  unique_two_player_fp_trajectory (setup_game_skew b hM f) (setup_strict b hM ha) hw hr hc t

theorem actual_setup_process (b : Fin m) {M : Matrix (Fin m) (Fin m) ℚ}
    (hM : IsSkewSymmetric M) {f : Fin m → ℚ} {a : ℕ → Fin m}
    (ha : IsStrictProcess M f a) (row col : ℕ → Option (Fin m))
    (hw : IsWeakTwoPlayerFPTrajectory (setupGame b M f) row col)
    (hr : row 0=none) (hc : col 0=none) (t : ℕ) :
    row (t+1)=some (a t) ∧ col (t+1)=some (a t) :=
  setup_unique b hM ha row col hw hr hc (t+1)

theorem setup_standard_gap (b : Fin m) {M : Matrix (Fin m) (Fin m) ℚ}
    (hM : IsSkewSymmetric M) {f : Fin m → ℚ} {a : ℕ → Fin m}
    (ha : IsStrictProcess M f a) (t : ℕ) :
    standardDualityGap (setupGame b M f) (setupPlay a) (setupPlay a) (t+1) =
      2 * (score M f a t (a t) + FaithfulBiasSetup.shift b f) / ((t+1:ℕ):ℚ) := by
  rw [standardDualityGap_eq_stepDualityGap (setup_game_skew b hM f)
    (setup_strict b hM ha) (by omega)]
  change 2 * cumScore (setupGame b M f) (setupPlay a) (t+1) (some (a t)) / _ = _
  rw [setup_score_some]

/-- Both finishing lemmas combined, with no finite-word or Clock hypothesis. -/
theorem priority_setup_realization (b : Fin m) {M : Matrix (Fin m) (Fin m) ℚ}
    (hM : IsSkewSymmetric M) (f : Fin m → ℚ) (rank : Equiv.Perm (Fin m)) :
    IsStrictTwoPlayerFPTrajectory
      (setupGame b M (fun i => f i+bias M f rank i))
      (setupPlay (priorityPlay b M f rank)) (setupPlay (priorityPlay b M f rank)) :=
  setup_strict_simultaneous b hM (rational_bias_realizes_priority b M f rank).2.1

/-- The setup action is literally the first finite label 0; recurrent label i
is i+1. This is the manuscript's displayed block ordering. -/
def finSetupGame (b : Fin m) (M : Matrix (Fin m) (Fin m) ℚ) (f : Fin m → ℚ) :
    Matrix (Fin (m+1)) (Fin (m+1)) ℚ := FaithfulGameReindex.finGame (setupGame b M f)

def finSetupPlay (a : ℕ → Fin m) : ℕ → Fin (m+1) := FaithfulGameReindex.finPlay (setupPlay a)

theorem finSetup_block (b : Fin m) (M : Matrix (Fin m) (Fin m) ℚ) (f : Fin m → ℚ) :
    finSetupGame b M f 0 0=0 ∧
    (∀ i, finSetupGame b M f i.succ 0=setupVector b f i) ∧
    (∀ i, finSetupGame b M f 0 i.succ= -setupVector b f i) ∧
    (∀ i j, finSetupGame b M f i.succ j.succ=M i j) := by
  simp [finSetupGame,FaithfulGameReindex.finGame,FaithfulReindex.matrix,
    FaithfulGameReindex.optionFinEquiv,setupGame,setupMatrix]

theorem finSetup_initial (a : ℕ → Fin m) : finSetupPlay a 0=0 :=
  FaithfulGameReindex.finPlay_initial _ rfl

theorem finSetup_succ (a : ℕ → Fin m) (t : ℕ) : finSetupPlay a (t+1)=(a t).succ := by
  simp [finSetupPlay,FaithfulGameReindex.finPlay,setupPlay]

theorem finSetup_strict_simultaneous (b : Fin m) {M : Matrix (Fin m) (Fin m) ℚ}
    (hM : IsSkewSymmetric M) {f : Fin m → ℚ} {a : ℕ → Fin m}
    (ha : IsStrictProcess M f a) :
    IsStrictTwoPlayerFPTrajectory (finSetupGame b M f) (finSetupPlay a) (finSetupPlay a) :=
  (FaithfulGameReindex.finGame_strictTwoPlayer_iff _ _ _).mpr (setup_strict_simultaneous b hM ha)

theorem finSetup_score (b : Fin m) (M : Matrix (Fin m) (Fin m) ℚ)
    (f : Fin m → ℚ) (a : ℕ → Fin m) (t : ℕ) (i : Fin m) :
    cumScore (finSetupGame b M f) (finSetupPlay a) (t+1) i.succ =
      score M f a t i + FaithfulBiasSetup.shift b f := by
  unfold finSetupGame finSetupPlay FaithfulGameReindex.finGame FaithfulGameReindex.finPlay
  rw [FaithfulGameReindex.cumScore_reindex]
  simp [FaithfulGameReindex.optionFinEquiv,setup_score_some]

end Karlin.FaithfulProcessSetup
