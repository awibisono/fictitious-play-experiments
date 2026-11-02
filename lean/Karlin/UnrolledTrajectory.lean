import Karlin.FictitiousPlay
import Karlin.RPSClock
import Karlin.CubicSevenAction

/-!
# Unrolled Discrete-Time Fictitious Play Trajectories (`IsStrictFPTrajectory`)

This module bridges the phase-and-run clock verification to the elementary, step-by-step
definition of discrete-time Fictitious Play over `t ∈ ℕ` starting from zero initial counts:

1. **Elementary Step-by-Step Definitions (`cumScore`, `IsStrictFPTrajectory`, `stepDualityGap`)**:
   Defined directly via `∑ s ∈ Finset.range t, M i (a s)` with no auxiliary phase/run state.
2. **Universal Run-Schedule Unrolling Engine (`runStart`, `runIndexOfStep`, `unrollAction`)**:
   - `cumScore_add_offset` & `cumScore_at_runStart`: Connects `∑ s ∈ Finset.range t, M i (a s)`
     to `scoreVec M (entryScore r) (runCount 0 (act r) h)`.
   - `unroll_isStrictFPTrajectory`: Proves `IsStrictFPTrajectory M (unrollAction act len)`
     for all `t ≥ 1` from run-level transitions and strict run margins.
3. **Universal Zero-Count Setup Bridge (`setup_unroll_isStrictFPTrajectory`)**:
   Lifts any recurrent run schedule on `M : Matrix (Fin m) (Fin m) ℚ` with setup vector
   `w = recEntryScore 0 + C • 1 ≥ 0` to a zero-count `IsStrictFPTrajectory (setupMatrix M w)`
   on `Option (Fin m)`.
4. **Hypothesis-Free Unrolled RPS Counterexample (`rps_unrolled_strict_fp_trajectory`)**:
   Proves unconditionally (`IsSkewSymmetric` + `IsStrictFPTrajectory` + exact quadratic time
   `2 * t_k = 9 k² + 45 k + 2` and linear score height `k + 26/3` at every phase boundary)
   for the 4-action game `M4_RPS`.
-/

namespace Karlin

open scoped BigOperators

/-!
## 1. Elementary Step-by-Step Fictitious Play Definitions
-/

/-- Cumulative payoff score of action `i` at integer step `t ∈ ℕ` along the discrete-time
    play sequence `a : ℕ → α`, starting from zero initial counts at `t = 0`. -/
def cumScore {α : Type*} (M : Matrix α α ℚ) (a : ℕ → α) (t : ℕ) (i : α) : ℚ :=
  ∑ s ∈ Finset.range t, M i (a s)

/-- A discrete-time play sequence `a : ℕ → α` is a **strictly tie-free Fictitious Play trajectory**
    of payoff matrix `M` from zero initial counts if at every step `t ≥ 1`, the chosen action `a t`
    is the strictly unique maximizer of `cumScore M a t`. -/
def IsStrictFPTrajectory {α : Type*} (M : Matrix α α ℚ) (a : ℕ → α) : Prop :=
  ∀ t : ℕ, 1 ≤ t → ∀ j : α, j ≠ a t →
    cumScore M a t j < cumScore M a t (a t)

/-- Synchronized zero-sum duality gap `2 * cumScore M a t (a t) / t` at step `t ≥ 1`. -/
def stepDualityGap {α : Type*} (M : Matrix α α ℚ) (a : ℕ → α) (t : ℕ) : ℚ :=
  2 * cumScore M a t (a t) / (t : ℚ)

/-- Cumulative payoff of row action `i` against column play sequence `colPlay` up to step `t`. -/
def rowCumPayoff {α : Type*} (M : Matrix α α ℚ) (colPlay : ℕ → α) (t : ℕ) (i : α) : ℚ :=
  ∑ s ∈ Finset.range t, M i (colPlay s)

/-- Cumulative loss of column action `j` against row play sequence `rowPlay` up to step `t`
    in the zero-sum game with payoff matrix `M` (which the column player minimizes). -/
def colCumLoss {α : Type*} (M : Matrix α α ℚ) (rowPlay : ℕ → α) (t : ℕ) (j : α) : ℚ :=
  ∑ s ∈ Finset.range t, M (rowPlay s) j

/-- Cumulative zero-sum payoff of column action `j` against row play sequence `rowPlay` up to step `t`
    (which the column player maximizes). -/
def colCumPayoff {α : Type*} (M : Matrix α α ℚ) (rowPlay : ℕ → α) (t : ℕ) (j : α) : ℚ :=
  ∑ s ∈ Finset.range t, -M (rowPlay s) j

/-- A pair of discrete-time play sequences `(rowPlay, colPlay)` is a **strictly tie-free
    simultaneous two-player Fictitious Play trajectory** from zero initial counts if at every
    step `t ≥ 1`, `rowPlay t` is the strictly unique maximizer of `rowCumPayoff M colPlay t`
    and `colPlay t` is the strictly unique minimizer of `colCumLoss M rowPlay t`. -/
def IsStrictTwoPlayerFPTrajectory {α : Type*} (M : Matrix α α ℚ) (rowPlay colPlay : ℕ → α) : Prop :=
  ∀ t : ℕ, 1 ≤ t →
    (∀ i : α, i ≠ rowPlay t → rowCumPayoff M colPlay t i < rowCumPayoff M colPlay t (rowPlay t)) ∧
    (∀ j : α, j ≠ colPlay t → colCumLoss M rowPlay t (colPlay t) < colCumLoss M rowPlay t j)

/-- A pair of discrete-time play sequences `(rowPlay, colPlay)` is a **weak simultaneous
    two-player Fictitious Play trajectory** (allowing arbitrary tie-breaking among best responses)
    if at every step `t ≥ 1`, `rowPlay t` maximizes `rowCumPayoff M colPlay t` and `colPlay t`
    minimizes `colCumLoss M rowPlay t`. -/
def IsWeakTwoPlayerFPTrajectory {α : Type*} (M : Matrix α α ℚ) (rowPlay colPlay : ℕ → α) : Prop :=
  ∀ t : ℕ, 1 ≤ t →
    (∀ i : α, rowCumPayoff M colPlay t i ≤ rowCumPayoff M colPlay t (rowPlay t)) ∧
    (∀ j : α, colCumLoss M rowPlay t (colPlay t) ≤ colCumLoss M rowPlay t j)

/-- In a skew-symmetric game `M`, the column player's cumulative loss against `a` is the exact
    negation of `cumScore M a t`. -/
theorem colCumLoss_eq_neg_cumScore {α : Type*} {M : Matrix α α ℚ}
    (hM : IsSkewSymmetric M) (a : ℕ → α) (t : ℕ) (j : α) :
    colCumLoss M a t j = -cumScore M a t j := by
  unfold colCumLoss cumScore
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hM (a s) j]

/-- In a skew-symmetric game `M`, the column player's cumulative zero-sum payoff against `a`
    equals `cumScore M a t`. -/
theorem colCumPayoff_eq_cumScore {α : Type*} {M : Matrix α α ℚ}
    (hM : IsSkewSymmetric M) (a : ℕ → α) (t : ℕ) (j : α) :
    colCumPayoff M a t j = cumScore M a t j := by
  unfold colCumPayoff cumScore
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hM (a s) j, neg_neg]

/-- **Equivalence of Single-Sequence and Synchronized Two-Player Strict FP
    (`isStrictTwoPlayerFPTrajectory_iff_isStrictFPTrajectory`)**:
    For any skew-symmetric matrix `M`, the synchronized pair `(a, a)` is a strictly tie-free
    two-player Fictitious Play trajectory if and only if `a` satisfies `IsStrictFPTrajectory M a`. -/
theorem isStrictTwoPlayerFPTrajectory_iff_isStrictFPTrajectory {α : Type*} {M : Matrix α α ℚ}
    (hM : IsSkewSymmetric M) (a : ℕ → α) :
    IsStrictTwoPlayerFPTrajectory M a a ↔ IsStrictFPTrajectory M a := by
  constructor
  · intro h t ht j hj
    exact (h t ht).1 j hj
  · intro h t ht
    refine ⟨fun i hi => h t ht i hi, fun j hj => ?_⟩
    rw [colCumLoss_eq_neg_cumScore hM, colCumLoss_eq_neg_cumScore hM]
    linarith [h t ht j hj]

/-- **Uniqueness of Two-Player Fictitious Play Under Arbitrary Tie-Breaking
    (`unique_two_player_fp_trajectory`)**:
    If `M` is skew-symmetric and `a` satisfies `IsStrictFPTrajectory M a`, then any weak
    two-player Fictitious Play trajectory `(rowPlay, colPlay)` that agrees with `(a 0, a 0)`
    at the initial tie `t = 0` must equal `(a t, a t)` at every integer step `t ∈ ℕ`. -/
theorem unique_two_player_fp_trajectory {α : Type*} {M : Matrix α α ℚ}
    (hM : IsSkewSymmetric M) {a rowPlay colPlay : ℕ → α}
    (hstrict : IsStrictFPTrajectory M a)
    (hweak : IsWeakTwoPlayerFPTrajectory M rowPlay colPlay)
    (h0_row : rowPlay 0 = a 0) (h0_col : colPlay 0 = a 0) (t : ℕ) :
    rowPlay t = a t ∧ colPlay t = a t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero => exact ⟨h0_row, h0_col⟩
    | succ s =>
      have ht : 1 ≤ s + 1 := Nat.succ_pos s
      have hrow_eq : ∀ i, rowCumPayoff M colPlay (s + 1) i = cumScore M a (s + 1) i := by
        intro i
        unfold rowCumPayoff cumScore
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [(ih u (Finset.mem_range.mp hu)).2]
      have hcol_eq : ∀ j, colCumLoss M rowPlay (s + 1) j = -cumScore M a (s + 1) j := by
        intro j
        rw [← colCumLoss_eq_neg_cumScore hM a (s + 1) j]
        unfold colCumLoss
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [(ih u (Finset.mem_range.mp hu)).1]
      refine ⟨?_, ?_⟩
      · by_contra hne
        have hlt := hstrict (s + 1) ht (rowPlay (s + 1)) hne
        have hle := (hweak (s + 1) ht).1 (a (s + 1))
        rw [hrow_eq, hrow_eq] at hle
        linarith
      · by_contra hne
        have hlt := hstrict (s + 1) ht (colPlay (s + 1)) hne
        have hle := (hweak (s + 1) ht).2 (a (s + 1))
        rw [hcol_eq, hcol_eq] at hle
        linarith

/-- Empirical strategy frequency `(1 / t) * #{0 ≤ s < t : play s = i}` at step `t`. -/
def empiricalStrategy {α : Type*} [DecidableEq α] (play : ℕ → α) (t : ℕ) (i : α) : ℚ :=
  (∑ s ∈ Finset.range t, if play s = i then (1 : ℚ) else 0) / (t : ℚ)

/-- Expected payoff `(M y_bar)_i` of pure row action `i` against the column player's empirical
    strategy `empiricalStrategy colPlay t`. -/
def empiricalRowPayoff {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (colPlay : ℕ → α) (t : ℕ) (i : α) : ℚ :=
  ∑ j : α, M i j * empiricalStrategy colPlay t j

/-- Expected payoff `(x_barᵀ M)_j` of the row player's empirical strategy `empiricalStrategy rowPlay t`
    against pure column action `j`. -/
def empiricalColPayoff {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (rowPlay : ℕ → α) (t : ℕ) (j : α) : ℚ :=
  ∑ i : α, empiricalStrategy rowPlay t i * M i j

/-- **Standard Two-Player Empirical Saddle-Point Duality Gap (`standardDualityGap`, `eq:gap-def`)**:
    `Gap_M(x_bar_t, y_bar_t) = max_i (M y_bar_t)_i - min_j (x_bar_tᵀ M)_j`. -/
def standardDualityGap {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (M : Matrix α α ℚ) (rowPlay colPlay : ℕ → α) (t : ℕ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (empiricalRowPayoff M colPlay t) -
    Finset.univ.inf' Finset.univ_nonempty (empiricalColPayoff M rowPlay t)

theorem empiricalRowPayoff_eq_cumScore_div {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (colPlay : ℕ → α) (t : ℕ) (i : α) :
    empiricalRowPayoff M colPlay t i = cumScore M colPlay t i / (t : ℚ) := by
  unfold empiricalRowPayoff empiricalStrategy cumScore
  simp_rw [mul_div_assoc', ← Finset.sum_div]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [mul_ite]

theorem empiricalColPayoff_eq_colCumLoss_div {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (rowPlay : ℕ → α) (t : ℕ) (j : α) :
    empiricalColPayoff M rowPlay t j = colCumLoss M rowPlay t j / (t : ℚ) := by
  unfold empiricalColPayoff empiricalStrategy colCumLoss
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [ite_mul]

/-- **Standard Empirical Duality Gap Equals `stepDualityGap` (`standardDualityGap_eq_stepDualityGap`)**:
    For any skew-symmetric matrix `M` and strict FP trajectory `a`, at every integer step `t ≥ 1`,
    the standard two-player empirical saddle-point gap `max_i (M y_bar_t)_i - min_j (x_bar_tᵀ M)_j`
    equals `stepDualityGap M a t = 2 * cumScore M a t (a t) / t`. -/
theorem standardDualityGap_eq_stepDualityGap {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {M : Matrix α α ℚ} (hM : IsSkewSymmetric M) {a : ℕ → α}
    (ha : IsStrictFPTrajectory M a) {t : ℕ} (ht : 1 ≤ t) :
    standardDualityGap M a a t = stepDualityGap M a t := by
  unfold standardDualityGap stepDualityGap
  have ht_pos : (0 : ℚ) < (t : ℚ) := by exact_mod_cast ht
  have hmax_le : ∀ i : α, cumScore M a t i ≤ cumScore M a t (a t) := by
    intro i
    by_cases hi : i = a t
    · rw [hi]
    · exact le_of_lt (ha t ht i hi)
  have hsup :
      Finset.univ.sup' Finset.univ_nonempty (empiricalRowPayoff M a t) =
        cumScore M a t (a t) / (t : ℚ) := by
    apply le_antisymm
    · refine Finset.sup'_le Finset.univ_nonempty _ fun i _ => ?_
      rw [empiricalRowPayoff_eq_cumScore_div]
      exact div_le_div_of_nonneg_right (hmax_le i) (le_of_lt ht_pos)
    · have hmem : a t ∈ (Finset.univ : Finset α) := Finset.mem_univ (a t)
      have hle := Finset.le_sup' (empiricalRowPayoff M a t) hmem
      rwa [empiricalRowPayoff_eq_cumScore_div] at hle
  have hinf :
      Finset.univ.inf' Finset.univ_nonempty (empiricalColPayoff M a t) =
        -(cumScore M a t (a t) / (t : ℚ)) := by
    apply le_antisymm
    · have hmem : a t ∈ (Finset.univ : Finset α) := Finset.mem_univ (a t)
      have hle := Finset.inf'_le (empiricalColPayoff M a t) hmem
      rw [empiricalColPayoff_eq_colCumLoss_div, colCumLoss_eq_neg_cumScore hM, neg_div] at hle
      exact hle
    · refine Finset.le_inf' Finset.univ_nonempty _ fun j _ => ?_
      rw [empiricalColPayoff_eq_colCumLoss_div, colCumLoss_eq_neg_cumScore hM, neg_div,
        neg_le_neg_iff]
      exact div_le_div_of_nonneg_right (hmax_le j) (le_of_lt ht_pos)
  rw [hsup, hinf]
  ring

/-- One-step recurrence for `cumScore`. -/
theorem cumScore_succ {α : Type*} (M : Matrix α α ℚ) (a : ℕ → α) (t : ℕ) (i : α) :
    cumScore M a (t + 1) i = cumScore M a t i + M i (a t) := by
  unfold cumScore
  exact Finset.sum_range_succ (fun s => M i (a s)) t

/-- In a skew-symmetric game `M`, playing `a t` at step `t` leaves the cumulative score of `a t`
    unchanged at step `t + 1`. -/
theorem cumScore_succ_self {α : Type*} {M : Matrix α α ℚ}
    (hM : IsSkewSymmetric M) (a : ℕ → α) (t : ℕ) :
    cumScore M a (t + 1) (a t) = cumScore M a t (a t) := by
  rw [cumScore_succ, skew_diag_zero hM (a t), add_zero]

/-- **One-Step Active Score Non-Decrease (`cumScore_active_mono_step`)**:
    In any skew-symmetric game `M`, along any strict FP trajectory `a`, the maximum cumulative
    score `cumScore M a t (a t)` is non-decreasing at every integer step `t ∈ ℕ`. -/
theorem cumScore_active_mono_step {α : Type*} {M : Matrix α α ℚ}
    (hM : IsSkewSymmetric M) {a : ℕ → α} (ha : IsStrictFPTrajectory M a) (t : ℕ) :
    cumScore M a t (a t) ≤ cumScore M a (t + 1) (a (t + 1)) := by
  rw [← cumScore_succ_self hM a t]
  by_cases heq : a t = a (t + 1)
  · rw [heq]
  · exact le_of_lt (ha (t + 1) (Nat.succ_pos t) (a t) heq)

/-- **All-Time Active Score Monotonicity (`cumScore_active_mono`)**:
    In any skew-symmetric game `M`, along any strict FP trajectory `a`, the active cumulative
    score `H(t) = cumScore M a t (a t)` is monotonically non-decreasing for all `t₁ ≤ t₂`. -/
theorem cumScore_active_mono {α : Type*} {M : Matrix α α ℚ}
    (hM : IsSkewSymmetric M) {a : ℕ → α} (ha : IsStrictFPTrajectory M a)
    {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    cumScore M a t₁ (a t₁) ≤ cumScore M a t₂ (a t₂) := by
  induction h with
  | refl => exact le_refl _
  | @step m _ ih => exact le_trans ih (cumScore_active_mono_step hM ha m)

/-- The active cumulative score `cumScore M a t (a t)` is nonnegative at every step `t ∈ ℕ`. -/
theorem cumScore_active_nonneg {α : Type*} {M : Matrix α α ℚ}
    (hM : IsSkewSymmetric M) {a : ℕ → α} (ha : IsStrictFPTrajectory M a) (t : ℕ) :
    0 ≤ cumScore M a t (a t) := by
  have h0 : cumScore M a 0 (a 0) = 0 := by simp [cumScore]
  rw [← h0]
  exact cumScore_active_mono hM ha (Nat.zero_le t)

/-- If `tStart 0 = 1` and `tStart` is strictly increasing, then `p + 1 ≤ tStart p` for all `p`. -/
theorem add_one_le_of_strictMono_tStart {tStart : ℕ → ℕ}
    (ht0 : tStart 0 = 1) (ht_mono : ∀ p, tStart p < tStart (p + 1)) (p : ℕ) :
    p + 1 ≤ tStart p := by
  induction p with
  | zero => omega
  | succ m ih =>
    have hm := ht_mono m
    omega

/-- Structural search for the unique phase index `p ≤ bound` with `tStart p ≤ t`. -/
def findPhaseAux (tStart : ℕ → ℕ) (t : ℕ) : ℕ → ℕ
  | 0 => 0
  | p + 1 => if tStart (p + 1) ≤ t then p + 1 else findPhaseAux tStart t p

theorem findPhaseAux_spec {tStart : ℕ → ℕ} (ht0 : tStart 0 = 1)
    (t bound : ℕ) (ht1 : 1 ≤ t) (ht_bound : t < tStart (bound + 1)) :
    tStart (findPhaseAux tStart t bound) ≤ t ∧
      t < tStart (findPhaseAux tStart t bound + 1) := by
  induction bound with
  | zero =>
    simp [findPhaseAux, ht0, ht1, ht_bound]
  | succ b ih =>
    simp only [findPhaseAux]
    split_ifs with h
    · exact ⟨h, ht_bound⟩
    · exact ih (Nat.lt_of_not_le h)

/-- **Universal All-Integer-Time Power-Law Duality Gap Enclosure
    (`all_integer_time_power_gap_bounds`)**:
    Given a skew-symmetric game `M`, a strict FP trajectory `a`, and strictly increasing phase-start
    times `tStart` with `tStart 0 = 1`, if at every phase `p ∈ ℕ`:
    - `c_low * (tStart (p + 1))^(k - 1) ≤ (2 * H(tStart p))^k`, and
    - `(2 * H(tStart (p + 1)))^k ≤ c_high * (tStart p)^(k - 1)`,
    then at **every** integer step `t ≥ 1`:
    `c_low ≤ standardDualityGap M a a t ^ k * t ≤ c_high`. -/
theorem all_integer_time_power_gap_bounds {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {M : Matrix α α ℚ} (hM : IsSkewSymmetric M)
    {a : ℕ → α} (ha : IsStrictFPTrajectory M a)
    {tStart : ℕ → ℕ} (ht0 : tStart 0 = 1) (ht_mono : ∀ p, tStart p < tStart (p + 1))
    {k : ℕ} (hk : 1 ≤ k) {c_low c_high : ℚ}
    (h_low : ∀ p : ℕ,
      c_low * (tStart (p + 1) : ℚ) ^ (k - 1) ≤
        (2 * cumScore M a (tStart p) (a (tStart p))) ^ k)
    (h_high : ∀ p : ℕ,
      (2 * cumScore M a (tStart (p + 1)) (a (tStart (p + 1)))) ^ k ≤
        c_high * (tStart p : ℚ) ^ (k - 1))
    (t : ℕ) (ht : 1 ≤ t) :
    c_low ≤ standardDualityGap M a a t ^ k * (t : ℚ) ∧
      standardDualityGap M a a t ^ k * (t : ℚ) ≤ c_high := by
  rw [standardDualityGap_eq_stepDualityGap hM ha ht]
  unfold stepDualityGap
  have ht_bound : t < tStart (t + 1) := by
    have hle := add_one_le_of_strictMono_tStart ht0 ht_mono (t + 1)
    omega
  let p := findPhaseAux tStart t t
  have hspec := findPhaseAux_spec ht0 t t ht ht_bound
  have hp_le : tStart p ≤ t := hspec.1
  have ht_lt : t < tStart (p + 1) := hspec.2
  have ht_le : t ≤ tStart (p + 1) := le_of_lt ht_lt
  have htp_pos_nat : 1 ≤ tStart p := by
    have hle := add_one_le_of_strictMono_tStart ht0 ht_mono p
    omega
  have htp_pos : (0 : ℚ) < (tStart p : ℚ) := by exact_mod_cast htp_pos_nat
  have ht_pos : (0 : ℚ) < (t : ℚ) := by exact_mod_cast ht
  have htp1_pos : (0 : ℚ) < (tStart (p + 1) : ℚ) := by
    have : 1 ≤ tStart (p + 1) := by omega
    exact_mod_cast this
  have hH_low : cumScore M a (tStart p) (a (tStart p)) ≤ cumScore M a t (a t) :=
    cumScore_active_mono hM ha hp_le
  have hH_high : cumScore M a t (a t) ≤ cumScore M a (tStart (p + 1)) (a (tStart (p + 1))) :=
    cumScore_active_mono hM ha ht_le
  have hHp_nonneg : 0 ≤ 2 * cumScore M a (tStart p) (a (tStart p)) := by
    have := cumScore_active_nonneg hM ha (tStart p)
    linarith
  have hHt_nonneg : 0 ≤ 2 * cumScore M a t (a t) := by
    have := cumScore_active_nonneg hM ha t
    linarith
  have hnum_low :
      (2 * cumScore M a (tStart p) (a (tStart p))) ^ k ≤ (2 * cumScore M a t (a t)) ^ k :=
    pow_le_pow_left₀ hHp_nonneg (by linarith) k
  have hnum_high :
      (2 * cumScore M a t (a t)) ^ k ≤
        (2 * cumScore M a (tStart (p + 1)) (a (tStart (p + 1)))) ^ k :=
    pow_le_pow_left₀ hHt_nonneg (by linarith) k
  have hden_low : (tStart p : ℚ) ^ (k - 1) ≤ (t : ℚ) ^ (k - 1) :=
    pow_le_pow_left₀ (le_of_lt htp_pos) (by exact_mod_cast hp_le) (k - 1)
  have hden_high : (t : ℚ) ^ (k - 1) ≤ (tStart (p + 1) : ℚ) ^ (k - 1) :=
    pow_le_pow_left₀ (le_of_lt ht_pos) (by exact_mod_cast ht_le) (k - 1)
  have hpow_identity :
      (2 * cumScore M a t (a t) / (t : ℚ)) ^ k * (t : ℚ) =
        (2 * cumScore M a t (a t)) ^ k / (t : ℚ) ^ (k - 1) := by
    have htk : (t : ℚ) ^ k = (t : ℚ) ^ (k - 1) * (t : ℚ) := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    have ht_ne : (t : ℚ) ≠ 0 := ne_of_gt ht_pos
    have htk1_ne : (t : ℚ) ^ (k - 1) ≠ 0 := pow_ne_zero (k - 1) ht_ne
    rw [div_pow, htk]
    field_simp
  rw [hpow_identity]
  have htk1_pos : (0 : ℚ) < (t : ℚ) ^ (k - 1) := pow_pos ht_pos (k - 1)
  constructor
  · rw [le_div_iff₀ htk1_pos]
    by_cases hcl : c_low ≤ 0
    · have h1 : c_low * (t : ℚ) ^ (k - 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hcl (le_of_lt htk1_pos)
      have h2 : 0 ≤ (2 * cumScore M a t (a t)) ^ k := pow_nonneg hHt_nonneg k
      linarith
    · push_neg at hcl
      have hmul : c_low * (t : ℚ) ^ (k - 1) ≤ c_low * (tStart (p + 1) : ℚ) ^ (k - 1) :=
        mul_le_mul_of_nonneg_left hden_high (le_of_lt hcl)
      exact le_trans hmul (le_trans (h_low p) hnum_low)
  · rw [div_le_iff₀ htk1_pos]
    have hch_nonneg : 0 ≤ c_high := by
      have h1 : 0 ≤ (2 * cumScore M a (tStart (p + 1)) (a (tStart (p + 1)))) ^ k := by
        have := cumScore_active_nonneg hM ha (tStart (p + 1))
        exact pow_nonneg (by linarith) k
      have h2 := le_trans h1 (h_high p)
      have h3 : (0 : ℚ) < (tStart p : ℚ) ^ (k - 1) := pow_pos htp_pos (k - 1)
      exact nonneg_of_mul_nonneg_left h2 h3
    have hmul : c_high * (tStart p : ℚ) ^ (k - 1) ≤ c_high * (t : ℚ) ^ (k - 1) :=
      mul_le_mul_of_nonneg_left hden_low hch_nonneg
    exact le_trans hnum_high (le_trans (h_high p) hmul)

/-- Degree-matching polynomial helper for `all_integer_time_power_gap_bounds`. -/
theorem power_gap_phase_bounds_of_deg_bounds
    {H_p H_p1 t_p t_p1 q_p r_p a_low b_high a_high b_low : ℚ} {k : ℕ}
    (ha_low : 0 ≤ a_low) (hb_high : 0 < b_high) (hq : 0 ≤ q_p)
    (ha_high : 0 ≤ a_high) (hb_low : 0 < b_low) (hr : 0 ≤ r_p)
    (ht_p1_nonneg : 0 ≤ t_p1) (hH_p1_nonneg : 0 ≤ 2 * H_p1)
    (h1 : a_low * q_p ^ (k - 1) ≤ 2 * H_p)
    (h2 : t_p1 ≤ b_high * q_p ^ k)
    (h3 : 2 * H_p1 ≤ a_high * r_p ^ (k - 1))
    (h4 : b_low * r_p ^ k ≤ t_p) :
    (a_low ^ k / b_high ^ (k - 1)) * t_p1 ^ (k - 1) ≤ (2 * H_p) ^ k ∧
      (2 * H_p1) ^ k ≤ (a_high ^ k / b_low ^ (k - 1)) * t_p ^ (k - 1) := by
  have h1_pow : (a_low * q_p ^ (k - 1)) ^ k ≤ (2 * H_p) ^ k :=
    pow_le_pow_left₀ (mul_nonneg ha_low (pow_nonneg hq _)) h1 k
  rw [mul_pow a_low, ← pow_mul] at h1_pow
  have h2_pow : t_p1 ^ (k - 1) ≤ (b_high * q_p ^ k) ^ (k - 1) :=
    pow_le_pow_left₀ ht_p1_nonneg h2 (k - 1)
  rw [mul_pow b_high, ← pow_mul, Nat.mul_comm k (k - 1)] at h2_pow
  have hbh_pos : 0 < b_high ^ (k - 1) := pow_pos hb_high (k - 1)
  have h3_pow : (2 * H_p1) ^ k ≤ (a_high * r_p ^ (k - 1)) ^ k :=
    pow_le_pow_left₀ hH_p1_nonneg h3 k
  rw [mul_pow a_high, ← pow_mul] at h3_pow
  have h4_pow : (b_low * r_p ^ k) ^ (k - 1) ≤ t_p ^ (k - 1) :=
    pow_le_pow_left₀ (mul_nonneg (le_of_lt hb_low) (pow_nonneg hr k)) h4 (k - 1)
  rw [mul_pow b_low, ← pow_mul, Nat.mul_comm k (k - 1)] at h4_pow
  have hbl_pos : 0 < b_low ^ (k - 1) := pow_pos hb_low (k - 1)
  constructor
  · have hmul :
        (a_low ^ k / b_high ^ (k - 1)) * t_p1 ^ (k - 1) ≤
          (a_low ^ k / b_high ^ (k - 1)) * (b_high ^ (k - 1) * q_p ^ ((k - 1) * k)) :=
      mul_le_mul_of_nonneg_left h2_pow (div_nonneg (pow_nonneg ha_low k) (le_of_lt hbh_pos))
    have heq :
        (a_low ^ k / b_high ^ (k - 1)) * (b_high ^ (k - 1) * q_p ^ ((k - 1) * k)) =
          a_low ^ k * q_p ^ ((k - 1) * k) := by
      have hne : b_high ^ (k - 1) ≠ 0 := ne_of_gt hbh_pos
      field_simp
    rw [heq] at hmul
    exact le_trans hmul h1_pow
  · have hmul :
        (a_high ^ k / b_low ^ (k - 1)) * (b_low ^ (k - 1) * r_p ^ ((k - 1) * k)) ≤
          (a_high ^ k / b_low ^ (k - 1)) * t_p ^ (k - 1) :=
      mul_le_mul_of_nonneg_left h4_pow (div_nonneg (pow_nonneg ha_high k) (le_of_lt hbl_pos))
    have heq :
        (a_high ^ k / b_low ^ (k - 1)) * (b_low ^ (k - 1) * r_p ^ ((k - 1) * k)) =
          a_high ^ k * r_p ^ ((k - 1) * k) := by
      have hne : b_low ^ (k - 1) ≠ 0 := ne_of_gt hbl_pos
      field_simp
    rw [heq] at hmul
    exact le_trans h3_pow hmul

/-!
## 2. Universal Run-Schedule Unrolling Engine
-/

/-- Cumulative start step `∑ u ∈ Finset.range r, len u` of run `r ∈ ℕ`. -/
def runStart (len : ℕ → ℕ) (r : ℕ) : ℕ :=
  ∑ u ∈ Finset.range r, len u

@[simp]
theorem runStart_zero (len : ℕ → ℕ) : runStart len 0 = 0 := rfl

theorem runStart_succ (len : ℕ → ℕ) (r : ℕ) :
    runStart len (r + 1) = runStart len r + len r :=
  Finset.sum_range_succ len r

theorem runStart_mono (len : ℕ → ℕ) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    runStart len r₁ ≤ runStart len r₂ :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem self_le_runStart {len : ℕ → ℕ} (hlen : ∀ r, 0 < len r) (r : ℕ) :
    r ≤ runStart len r := by
  induction r with
  | zero => simp
  | succ k ih =>
    have hk := hlen k
    rw [runStart_succ]
    omega

/-- Structural search for the largest run index `r ≤ bound` satisfying `runStart len r ≤ t`. -/
def findRunAux (len : ℕ → ℕ) (t : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => if runStart len (r + 1) ≤ t then r + 1 else findRunAux len t r

theorem findRunAux_spec (len : ℕ → ℕ) (t bound : ℕ)
    (ht : t < runStart len (bound + 1)) :
    runStart len (findRunAux len t bound) ≤ t ∧
      t < runStart len (findRunAux len t bound + 1) := by
  induction bound with
  | zero =>
    simp [findRunAux, ht]
  | succ b ih =>
    simp only [findRunAux]
    split_ifs with h
    · exact ⟨h, ht⟩
    · exact ih (Nat.lt_of_not_le h)

theorem findRunAux_eq_of_bounds (len : ℕ → ℕ) (t r bound : ℕ)
    (h1 : runStart len r ≤ t) (h2 : t < runStart len (r + 1)) (hb : r ≤ bound) :
    findRunAux len t bound = r := by
  induction bound with
  | zero =>
    have hr : r = 0 := by omega
    subst hr
    rfl
  | succ b ih =>
    simp only [findRunAux]
    by_cases hrb : r = b + 1
    · subst hrb
      simp [h1]
    · have hle : r + 1 ≤ b + 1 := by omega
      have hlt : t < runStart len (b + 1) := lt_of_lt_of_le h2 (runStart_mono len hle)
      have hnot : ¬ (runStart len (b + 1) ≤ t) := not_le_of_gt hlt
      simp [hnot, ih (by omega)]

/-- The unique run index `r` containing integer step `t`. -/
def runIndexOfStep (len : ℕ → ℕ) (t : ℕ) : ℕ :=
  findRunAux len t t

theorem runIndexOfStep_spec {len : ℕ → ℕ} (hlen : ∀ r, 0 < len r) (t : ℕ) :
    runStart len (runIndexOfStep len t) ≤ t ∧
      t < runStart len (runIndexOfStep len t + 1) := by
  have ht : t < runStart len (t + 1) := by
    have hle := self_le_runStart hlen (t + 1)
    omega
  exact findRunAux_spec len t t ht

theorem runIndexOfStep_at_offset {len : ℕ → ℕ} (hlen : ∀ r, 0 < len r)
    (r h : ℕ) (hh : h < len r) :
    runIndexOfStep len (runStart len r + h) = r := by
  have h1 : runStart len r ≤ runStart len r + h := Nat.le_add_right _ _
  have h2 : runStart len r + h < runStart len (r + 1) := by
    rw [runStart_succ]
    omega
  have hb : r ≤ runStart len r + h := le_trans (self_le_runStart hlen r) h1
  exact findRunAux_eq_of_bounds len (runStart len r + h) r (runStart len r + h) h1 h2 hb

/-- Discrete-time action sequence `a : ℕ → α` unrolled from a run schedule `(act, len)`. -/
def unrollAction {α : Type*} (act : ℕ → α) (len : ℕ → ℕ) (t : ℕ) : α :=
  act (runIndexOfStep len t)

theorem unrollAction_at_offset {α : Type*} (act : ℕ → α) {len : ℕ → ℕ}
    (hlen : ∀ r, 0 < len r) (r h : ℕ) (hh : h < len r) :
    unrollAction act len (runStart len r + h) = act r := by
  unfold unrollAction
  rw [runIndexOfStep_at_offset hlen r h hh]

/-- **Cumulative Score Within a Run (`cumScore_add_offset`)**:
    For any `r ∈ ℕ` and `h ≤ len r`, the cumulative score at step `runStart len r + h`
    equals `scoreVec M (cumScore M a (runStart len r)) (runCount 0 (act r) h)`. -/
theorem cumScore_add_offset {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (act : ℕ → α) {len : ℕ → ℕ}
    (hlen : ∀ r, 0 < len r) (r h : ℕ) (hh : h ≤ len r) :
    cumScore M (unrollAction act len) (runStart len r + h) =
      scoreVec M (cumScore M (unrollAction act len) (runStart len r))
        (runCount (fun _ => 0) (act r) (h : ℚ)) := by
  ext i
  rw [scoreVec_runCount M (cumScore M (unrollAction act len) (runStart len r))
    (fun _ => 0) (act r) i (h : ℚ)]
  have hzero :
      scoreVec M (cumScore M (unrollAction act len) (runStart len r)) (fun _ => 0) i =
        cumScore M (unrollAction act len) (runStart len r) i := by
    simp [scoreVec]
  rw [hzero]
  unfold cumScore
  rw [Finset.sum_range_add]
  congr 1
  have hconst :
      (∑ x ∈ Finset.range h, M i (unrollAction act len (runStart len r + x))) =
        ∑ _x ∈ Finset.range h, M i (act r) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxl : x < len r := lt_of_lt_of_le (Finset.mem_range.mp hx) hh
    rw [unrollAction_at_offset act hlen r x hxl]
  rw [hconst, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Cumulative Score at Run Boundaries (`cumScore_at_runStart`)**:
    If `entryScore 0 = 0` and `entryScore (r + 1) = scoreVec M (entryScore r) (runCount 0 (act r) (len r))`,
    then `cumScore M (unrollAction act len) (runStart len r) = entryScore r` for all `r ∈ ℕ`. -/
theorem cumScore_at_runStart {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (act : ℕ → α) {len : ℕ → ℕ}
    (hlen : ∀ r, 0 < len r) (entryScore : ℕ → α → ℚ)
    (h0 : entryScore 0 = fun _ => 0)
    (hstep : ∀ r, entryScore (r + 1) =
      scoreVec M (entryScore r) (runCount (fun _ => 0) (act r) (len r : ℚ)))
    (r : ℕ) :
    cumScore M (unrollAction act len) (runStart len r) = entryScore r := by
  induction r with
  | zero =>
    ext i
    simp [cumScore, h0]
  | succ u ih =>
    rw [runStart_succ, cumScore_add_offset M act hlen u (len u) (le_refl _), ih, hstep u]

/-- **Universal Run-Schedule Unrolling Theorem (`unroll_isStrictFPTrajectory`)**:
    If run `0` has length `1` (the initial step `t = 0`), `entryScore` tracks the run transitions
    from `entryScore 0 = 0`, and for every run `r ≥ 1` and step offset `h < len r`, `act r` is
    the strictly unique best response under `scoreVec M (entryScore r) (runCount 0 (act r) h)`,
    then `unrollAction act len` is a strictly tie-free Fictitious Play trajectory for all `t ≥ 1`. -/
theorem unroll_isStrictFPTrajectory {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (act : ℕ → α) {len : ℕ → ℕ}
    (hlen : ∀ r, 0 < len r) (hlen0 : len 0 = 1)
    (entryScore : ℕ → α → ℚ)
    (h0 : entryScore 0 = fun _ => 0)
    (hstep : ∀ r, entryScore (r + 1) =
      scoreVec M (entryScore r) (runCount (fun _ => 0) (act r) (len r : ℚ)))
    (hvalid : ∀ r : ℕ, 1 ≤ r → ∀ h : ℕ, h < len r → ∀ j : α, j ≠ act r →
      scoreVec M (entryScore r) (runCount (fun _ => 0) (act r) (h : ℚ)) j <
        scoreVec M (entryScore r) (runCount (fun _ => 0) (act r) (h : ℚ)) (act r)) :
    IsStrictFPTrajectory M (unrollAction act len) := by
  intro t ht j hj
  let r := runIndexOfStep len t
  have hspec := runIndexOfStep_spec hlen t
  have hr_le : runStart len r ≤ t := hspec.1
  have ht_lt : t < runStart len (r + 1) := hspec.2
  rw [runStart_succ] at ht_lt
  let h := t - runStart len r
  have ht_eq : t = runStart len r + h := (Nat.add_sub_of_le hr_le).symm
  have hh_lt : h < len r := by omega
  have hr_pos : 1 ≤ r := by
    by_contra hnot
    have hr0 : r = 0 := by omega
    have ht_lt0 : t < runStart len 0 + len 0 := by simpa [hr0] using ht_lt
    rw [runStart_zero, hlen0] at ht_lt0
    omega
  have hact : unrollAction act len t = act r := by
    rw [ht_eq, unrollAction_at_offset act hlen r h hh_lt]
  have hscore :
      cumScore M (unrollAction act len) t =
        scoreVec M (entryScore r) (runCount (fun _ => 0) (act r) (h : ℚ)) := by
    rw [ht_eq, cumScore_add_offset M act hlen r h (le_of_lt hh_lt),
      cumScore_at_runStart M act hlen entryScore h0 hstep r]
  rw [hact] at hj ⊢
  rw [hscore]
  exact hvalid r hr_pos h hh_lt j hj

/-!
## 3. Universal Zero-Count Setup Bridge (`setupMatrix M w`)
-/

/-- Lift a recurrent run schedule `(recAct, recLen)` on `Fin m` to a full zero-count schedule
    on `Option (Fin m)` by prepending a 1-step run of the setup action `none` at `r = 0`. -/
def setupFullAct {m : ℕ} (recAct : ℕ → Fin m) : ℕ → Option (Fin m)
  | 0 => none
  | u + 1 => some (recAct u)

/-- Full run lengths with `setupFullLen recLen 0 = 1` and `setupFullLen recLen (u + 1) = recLen u`. -/
def setupFullLen (recLen : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | u + 1 => recLen u

/-- Score of a recurrent action `some i` under `setupMatrix M w` after a recurrent run. -/
theorem scoreVec_setupMatrix_some {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℚ) (w : Fin m → ℚ)
    (s₀ : Option (Fin m) → ℚ) (a : Fin m) (h : ℚ) (i : Fin m) :
    scoreVec (setupMatrix M w) s₀ (runCount (fun _ => 0) (some a) h) (some i) =
      scoreVec M (fun k => s₀ (some k)) (runCount (fun _ => 0) a h) i := by
  rw [scoreVec_runCount (setupMatrix M w) s₀ (fun _ => 0) (some a) (some i) h]
  rw [scoreVec_runCount M (fun k => s₀ (some k)) (fun _ => 0) a i h]
  simp [scoreVec, setupMatrix]

/-- Score of the setup action `none` under `setupMatrix M w` after a recurrent run. -/
theorem scoreVec_setupMatrix_none {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℚ) (w : Fin m → ℚ)
    (s₀ : Option (Fin m) → ℚ) (a : Fin m) (h : ℚ) :
    scoreVec (setupMatrix M w) s₀ (runCount (fun _ => 0) (some a) h) none =
      s₀ none - w a * h := by
  rw [scoreVec_runCount (setupMatrix M w) s₀ (fun _ => 0) (some a) none h]
  simp [scoreVec, setupMatrix]
  ring

/-- **Universal Setup-Bridge Unrolling Theorem (`setup_unroll_isStrictFPTrajectory`)**:
    Given a recurrent game `M : Matrix (Fin m) (Fin m) ℚ`, setup vector `w ≥ 0` satisfying
    `w i = recEntryScore 0 i + C`, and a recurrent run schedule `(recAct, recLen)` where:
    1. `recEntryScore (u + 1) = scoreVec M (recEntryScore u) (runCount 0 (recAct u) (recLen u))`,
    2. For every run `u` and step `h < recLen u`, `recAct u` strictly beats every `j ≠ recAct u`
       and has shifted score `0 < score (recAct u) + C`,
    the unrolled zero-count sequence on `setupMatrix M w` satisfies `IsStrictFPTrajectory`. -/
theorem setup_unroll_isStrictFPTrajectory {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℚ) (w : Fin m → ℚ) (C : ℚ)
    (recAct : ℕ → Fin m) (recLen : ℕ → ℕ) (recEntryScore : ℕ → Fin m → ℚ)
    (hw_nonneg : ∀ i : Fin m, 0 ≤ w i)
    (hw_shift : ∀ i : Fin m, w i = recEntryScore 0 i + C)
    (hrecLen : ∀ u : ℕ, 0 < recLen u)
    (hrecStep : ∀ u : ℕ, recEntryScore (u + 1) =
      scoreVec M (recEntryScore u) (runCount (fun _ => 0) (recAct u) (recLen u : ℚ)))
    (hrecValid : ∀ u h : ℕ, h < recLen u → ∀ j : Fin m, j ≠ recAct u →
      scoreVec M (recEntryScore u) (runCount (fun _ => 0) (recAct u) (h : ℚ)) j <
        scoreVec M (recEntryScore u) (runCount (fun _ => 0) (recAct u) (h : ℚ)) (recAct u))
    (hrecPos : ∀ u h : ℕ, h < recLen u →
      0 < scoreVec M (recEntryScore u) (runCount (fun _ => 0) (recAct u) (h : ℚ)) (recAct u) + C) :
    IsStrictFPTrajectory (setupMatrix M w)
      (unrollAction (setupFullAct recAct) (setupFullLen recLen)) := by
  have hlen : ∀ r, 0 < setupFullLen recLen r := by
    intro r
    cases r with
    | zero => simp [setupFullLen]
    | succ u => exact hrecLen u
  let noneScore : ℕ → ℚ := fun u => -∑ v ∈ Finset.range u, w (recAct v) * (recLen v : ℚ)
  let entryScore : ℕ → Option (Fin m) → ℚ
    | 0 => fun _ => 0
    | u + 1 => fun x => match x with
      | none => noneScore u
      | some i => recEntryScore u i + C
  have hstep : ∀ r, entryScore (r + 1) =
      scoreVec (setupMatrix M w) (entryScore r)
        (runCount (fun _ => 0) (setupFullAct recAct r) (setupFullLen recLen r : ℚ)) := by
    intro r
    cases r with
    | zero =>
      ext x
      change entryScore 1 x =
        scoreVec (setupMatrix M w) (entryScore 0) (runCount (fun _ => 0) none 1) x
      rw [scoreVec_runCount (setupMatrix M w) (entryScore 0) (fun _ => 0) none x 1]
      cases x with
      | none =>
        simp [entryScore, noneScore, scoreVec, setupMatrix]
      | some i =>
        simp [entryScore, scoreVec, setupMatrix, hw_shift i]
    | succ u =>
      ext x
      cases x with
      | none =>
        change noneScore (u + 1) =
          scoreVec (setupMatrix M w) (entryScore (u + 1))
            (runCount (fun _ => 0) (some (recAct u)) (recLen u : ℚ)) none
        rw [scoreVec_setupMatrix_none]
        simp only [entryScore, noneScore, Finset.sum_range_succ]
        ring
      | some i =>
        change recEntryScore (u + 1) i + C =
          scoreVec (setupMatrix M w) (entryScore (u + 1))
            (runCount (fun _ => 0) (some (recAct u)) (recLen u : ℚ)) (some i)
        rw [scoreVec_setupMatrix_some, hrecStep u]
        simp only [entryScore, scoreVec]
        ring
  have hnone_nonpos : ∀ u : ℕ, noneScore u ≤ 0 := by
    intro u
    dsimp only [noneScore]
    have hsum : 0 ≤ ∑ v ∈ Finset.range u, w (recAct v) * (recLen v : ℚ) :=
      Finset.sum_nonneg fun v _ => mul_nonneg (hw_nonneg (recAct v)) (Nat.cast_nonneg _)
    linarith
  apply unroll_isStrictFPTrajectory (setupMatrix M w) (setupFullAct recAct) hlen rfl entryScore rfl hstep
  intro r hr h hh j hj
  rcases r with _ | u
  · omega
  · have hh_rec : h < recLen u := hh
    have hactive :
        scoreVec (setupMatrix M w) (entryScore (u + 1))
          (runCount (fun _ => 0) (some (recAct u)) (h : ℚ)) (some (recAct u)) =
        scoreVec M (recEntryScore u) (runCount (fun _ => 0) (recAct u) (h : ℚ)) (recAct u) + C := by
      rw [scoreVec_setupMatrix_some]
      simp only [entryScore, scoreVec]
      ring
    cases j with
    | none =>
      change scoreVec (setupMatrix M w) (entryScore (u + 1))
          (runCount (fun _ => 0) (some (recAct u)) (h : ℚ)) none <
        scoreVec (setupMatrix M w) (entryScore (u + 1))
          (runCount (fun _ => 0) (some (recAct u)) (h : ℚ)) (some (recAct u))
      rw [scoreVec_setupMatrix_none, hactive]
      have hn1 : entryScore (u + 1) none = noneScore u := rfl
      rw [hn1]
      have hn2 : noneScore u ≤ 0 := hnone_nonpos u
      have hw_h : 0 ≤ w (recAct u) * (h : ℚ) :=
        mul_nonneg (hw_nonneg (recAct u)) (Nat.cast_nonneg _)
      have hpos := hrecPos u h hh_rec
      linarith
    | some j_rec =>
      have hj_ne : j_rec ≠ recAct u := by
        intro heq
        apply hj
        simp [setupFullAct, heq]
      change scoreVec (setupMatrix M w) (entryScore (u + 1))
          (runCount (fun _ => 0) (some (recAct u)) (h : ℚ)) (some j_rec) <
        scoreVec (setupMatrix M w) (entryScore (u + 1))
          (runCount (fun _ => 0) (some (recAct u)) (h : ℚ)) (some (recAct u))
      have hj_score :
          scoreVec (setupMatrix M w) (entryScore (u + 1))
            (runCount (fun _ => 0) (some (recAct u)) (h : ℚ)) (some j_rec) =
          scoreVec M (recEntryScore u) (runCount (fun _ => 0) (recAct u) (h : ℚ)) j_rec + C := by
        rw [scoreVec_setupMatrix_some]
        simp only [entryScore, scoreVec]
        ring
      rw [hj_score, hactive]
      have hdom := hrecValid u h hh_rec j_rec hj_ne
      linarith

/-!
## 4. Concrete Unrolled 4-Action RPS Seed Trajectory (`k = 2`)
-/

/-- Setup payoff column `w_RPS = r_2(1) + (20/3) 1_3 = (26/3, 1, 25/3)ᵀ ≥ 1` for the RPS seed clock. -/
def w_RPS (i : Fin 3) : ℚ :=
  r2Vec 1 i + 20 / 3

/-- The 4-action zero-count RPS game `setupMatrix A_RPS w_RPS` starting at phase `q_0 = 1`. -/
def M4_RPS : Matrix (Option (Fin 3)) (Option (Fin 3)) ℚ :=
  setupMatrix A_RPS w_RPS

/-- Recurrent action `u % 3` for run `u` of the RPS clock (`0, 1, 2, 0, 1, 2, …`). -/
def rpsRecAct (u : ℕ) : Fin 3 :=
  match u % 3 with
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- Recurrent run length `u + 8` for run `u` starting at phase `q = u / 3 + 1`:
    in phase `q = k + 1`, the three runs have lengths `3k + 8`, `3k + 9`, `3k + 10`,
    which is simply `u + 8` for `u = 3k, 3k + 1, 3k + 2`. -/
def rpsRecLen (u : ℕ) : ℕ :=
  u + 8

/-- Recurrent entry score vector before run `u` (where phase `q = u / 3 + 1`). -/
def rpsRecEntryScore (u : ℕ) : Fin 3 → ℚ :=
  let q : ℚ := ((u / 3 : ℕ) : ℚ) + 1
  match u % 3 with
  | 0 => r2Vec q
  | 1 => rpsStateAfterRun0 q
  | _ => rpsStateAfterRun1 q

/-- The unrolled discrete-time trajectory `rpsTrajectory : ℕ → Option (Fin 3)` of `M4_RPS`. -/
def rpsTrajectory : ℕ → Option (Fin 3) :=
  unrollAction (setupFullAct rpsRecAct) (setupFullLen rpsRecLen)

set_option linter.unnecessarySeqFocus false

/-- **Hypothesis-Free Unrolled RPS Trajectory Theorem (`rps_unrolled_strict_fp_trajectory`)**:
    The 4-action skew-symmetric game `M4_RPS` and explicit play sequence `rpsTrajectory`
    form a strictly tie-free Fictitious Play trajectory (`IsStrictFPTrajectory`) from zero
    initial counts at `t = 0`. -/
theorem rps_unrolled_strict_fp_trajectory :
    IsSkewSymmetric M4_RPS ∧
    IsStrictFPTrajectory M4_RPS rpsTrajectory := by
  refine ⟨setupMatrix_skewSymmetric A_RPS_skew w_RPS, ?_⟩
  apply setup_unroll_isStrictFPTrajectory A_RPS w_RPS (20 / 3)
    rpsRecAct rpsRecLen rpsRecEntryScore
  · intro i
    fin_cases i <;> simp [w_RPS, r2Vec] <;> norm_num
  · intro i
    simp [w_RPS, rpsRecEntryScore]
  · intro u
    unfold rpsRecLen
    omega
  · intro u
    ext j
    have hmod : u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · have hdiv : (u + 1) / 3 = u / 3 := by omega
      have hm1 : (u + 1) % 3 = 1 := by omega
      have hlen_eq : (rpsRecLen u : ℚ) = 3 * (((u / 3 : ℕ) : ℚ) + 1) + 5 := by
        unfold rpsRecLen
        exact_mod_cast (by omega : u + 8 = 3 * (u / 3 + 1) + 5)
      simp only [rpsRecEntryScore, rpsRecAct, h0, hdiv, hm1, hlen_eq]
      exact (rps_run0_transition (((u / 3 : ℕ) : ℚ) + 1) j).symm
    · have hdiv : (u + 1) / 3 = u / 3 := by omega
      have hm2 : (u + 1) % 3 = 2 := by omega
      have hlen_eq : (rpsRecLen u : ℚ) = 3 * (((u / 3 : ℕ) : ℚ) + 1) + 6 := by
        unfold rpsRecLen
        exact_mod_cast (by omega : u + 8 = 3 * (u / 3 + 1) + 6)
      simp only [rpsRecEntryScore, rpsRecAct, h1, hdiv, hm2, hlen_eq]
      exact (rps_run1_transition (((u / 3 : ℕ) : ℚ) + 1) j).symm
    · have hdiv : (u + 1) / 3 = u / 3 + 1 := by omega
      have hm0 : (u + 1) % 3 = 0 := by omega
      have hlen_eq : (rpsRecLen u : ℚ) = 3 * (((u / 3 : ℕ) : ℚ) + 1) + 7 := by
        unfold rpsRecLen
        exact_mod_cast (by omega : u + 8 = 3 * (u / 3 + 1) + 7)
      simp only [rpsRecEntryScore, rpsRecAct, h2, hdiv, hm0, hlen_eq]
      have hcast : (((u / 3 + 1 : ℕ) : ℚ) + 1) = (((u / 3 : ℕ) : ℚ) + 1) + 1 := by
        push_cast
        ring
      rw [hcast]
      exact (rps_run2_transition (((u / 3 : ℕ) : ℚ) + 1) j).symm
  · intro u h hh j hj
    have hq1 : (1 : ℚ) ≤ ((u / 3 : ℕ) : ℚ) + 1 := by
      have : (0 : ℚ) ≤ ((u / 3 : ℕ) : ℚ) := Nat.cast_nonneg _
      linarith
    have hmod : u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · have hh_le : (h : ℚ) ≤ (3 * (((u / 3 : ℕ) : ℚ) + 1) + 5) - 1 := by
        unfold rpsRecLen at hh
        have hnat : h ≤ 3 * (u / 3 + 1) + 4 := by omega
        have hrat : (h : ℚ) ≤ 3 * (((u / 3 : ℕ) : ℚ) + 1) + 4 := by exact_mod_cast hnat
        linarith
      have hv := rps_run0_valid hq1 (Nat.cast_nonneg h) hh_le
      simp only [rpsRecEntryScore, rpsRecAct, h0] at hj ⊢
      fin_cases j
      · contradiction
      · dsimp; linarith [hv.1]
      · dsimp; linarith [hv.2]
    · have hh_le : (h : ℚ) ≤ (3 * (((u / 3 : ℕ) : ℚ) + 1) + 6) - 1 := by
        unfold rpsRecLen at hh
        have hnat : h ≤ 3 * (u / 3 + 1) + 5 := by omega
        have hrat : (h : ℚ) ≤ 3 * (((u / 3 : ℕ) : ℚ) + 1) + 5 := by exact_mod_cast hnat
        linarith
      have hv := rps_run1_valid hq1 (Nat.cast_nonneg h) hh_le
      simp only [rpsRecEntryScore, rpsRecAct, h1] at hj ⊢
      fin_cases j
      · dsimp; linarith [hv.1]
      · contradiction
      · dsimp; linarith [hv.2]
    · have hh_le : (h : ℚ) ≤ (3 * (((u / 3 : ℕ) : ℚ) + 1) + 7) - 1 := by
        unfold rpsRecLen at hh
        have hnat : h ≤ 3 * (u / 3 + 1) + 6 := by omega
        have hrat : (h : ℚ) ≤ 3 * (((u / 3 : ℕ) : ℚ) + 1) + 6 := by exact_mod_cast hnat
        linarith
      have hv := rps_run2_valid hq1 (Nat.cast_nonneg h) hh_le
      simp only [rpsRecEntryScore, rpsRecAct, h2] at hj ⊢
      fin_cases j
      · dsimp; linarith [hv.1]
      · dsimp; linarith [hv.2]
      · contradiction
  · intro u h _hh
    have hq : (0 : ℚ) ≤ ((u / 3 : ℕ) : ℚ) := Nat.cast_nonneg _
    have hmod : u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · simp only [rpsRecEntryScore, rpsRecAct, h0]
      rw [scoreVec_runCount_self A_RPS_skew]
      simp only [scoreVec, r2Vec, mul_zero, Finset.sum_const_zero, add_zero]
      linarith
    · simp only [rpsRecEntryScore, rpsRecAct, h1]
      rw [scoreVec_runCount_self A_RPS_skew]
      simp only [scoreVec, rpsStateAfterRun0, mul_zero, Finset.sum_const_zero, add_zero]
      linarith
    · simp only [rpsRecEntryScore, rpsRecAct, h2]
      rw [scoreVec_runCount_self A_RPS_skew]
      simp only [scoreVec, rpsStateAfterRun1, mul_zero, Finset.sum_const_zero, add_zero]
      linarith

/-- **Exact Quadratic Elapsed Time at Phase Start (`rps_phase_start_time`)**:
    For every `k ∈ ℕ`, the start time `t_k = runStart (setupFullLen rpsRecLen) (3 * k + 1)`
    of phase `q = k + 1` satisfies `2 * t_k = 9 k^2 + 45 k + 2`. -/
theorem rps_phase_start_time (k : ℕ) :
    2 * (runStart (setupFullLen rpsRecLen) (3 * k + 1) : ℚ) =
      9 * (k : ℚ) ^ 2 + 45 * (k : ℚ) + 2 := by
  induction k with
  | zero =>
    simp [runStart, setupFullLen]
  | succ m ih =>
    have hstep : 3 * (m + 1) + 1 = (3 * m + 1) + 1 + 1 + 1 := by omega
    rw [hstep, runStart_succ, runStart_succ, runStart_succ]
    simp only [setupFullLen, rpsRecLen, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    push_cast
    linarith

/-!
## 5. Two-Level Phase-to-Run Unrolling (`setup_phase_unroll_isStrictFPTrajectory`)
-/

/-- Phase index `p` containing recurrent run `u`. -/
def flatPhase (phaseRunCount : ℕ → ℕ) (u : ℕ) : ℕ :=
  runIndexOfStep phaseRunCount u

/-- Run index `v < phaseRunCount p` within phase `p` for recurrent run `u`. -/
def flatOffset (phaseRunCount : ℕ → ℕ) (u : ℕ) : ℕ :=
  u - runStart phaseRunCount (flatPhase phaseRunCount u)

/-- Flattened recurrent action sequence from a two-level `(phase, runInPhase)` schedule. -/
def flatAct {m : ℕ} (phaseRunCount : ℕ → ℕ) (phaseAct : ℕ → ℕ → Fin m) (u : ℕ) : Fin m :=
  phaseAct (flatPhase phaseRunCount u) (flatOffset phaseRunCount u)

/-- Flattened recurrent run length sequence from a two-level `(phase, runInPhase)` schedule. -/
def flatLen (phaseRunCount : ℕ → ℕ) (phaseLen : ℕ → ℕ → ℕ) (u : ℕ) : ℕ :=
  phaseLen (flatPhase phaseRunCount u) (flatOffset phaseRunCount u)

/-- Flattened recurrent entry score sequence from a two-level `(phase, runInPhase)` schedule. -/
def flatScore {m : ℕ} (phaseRunCount : ℕ → ℕ) (phaseScore : ℕ → ℕ → Fin m → ℚ) (u : ℕ) :
    Fin m → ℚ :=
  phaseScore (flatPhase phaseRunCount u) (flatOffset phaseRunCount u)

/-- **Two-Level Phase-to-Run Setup Unrolling Theorem (`setup_phase_unroll_isStrictFPTrajectory`)**:
    Given a phase-indexed schedule `(phaseRunCount, phaseAct, phaseLen, phaseScore)` where each
    run `v < phaseRunCount p` transitions `phaseScore p v` to `phaseScore p (v + 1)` with strict
    best-response dominance and positive shifted active score, and where the terminal state of
    phase `p` equals the entry state of phase `p + 1` (`phaseScore p (phaseRunCount p) = phaseScore (p + 1) 0`),
    the unrolled discrete-time sequence on `setupMatrix M w` satisfies `IsStrictFPTrajectory`. -/
theorem setup_phase_unroll_isStrictFPTrajectory {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℚ) (w : Fin m → ℚ) (C : ℚ)
    (phaseRunCount : ℕ → ℕ)
    (phaseAct : ℕ → ℕ → Fin m) (phaseLen : ℕ → ℕ → ℕ) (phaseScore : ℕ → ℕ → Fin m → ℚ)
    (hcount : ∀ p : ℕ, 0 < phaseRunCount p)
    (hw_nonneg : ∀ i : Fin m, 0 ≤ w i)
    (hw_shift : ∀ i : Fin m, w i = phaseScore 0 0 i + C)
    (hphaseLen : ∀ p v : ℕ, v < phaseRunCount p → 0 < phaseLen p v)
    (hphaseStep : ∀ p v : ℕ, v < phaseRunCount p →
      phaseScore p (v + 1) =
        scoreVec M (phaseScore p v) (runCount (fun _ => 0) (phaseAct p v) (phaseLen p v : ℚ)))
    (hphaseBoundary : ∀ p : ℕ, phaseScore p (phaseRunCount p) = phaseScore (p + 1) 0)
    (hphaseValid : ∀ p v : ℕ, v < phaseRunCount p → ∀ h : ℕ, h < phaseLen p v →
      ∀ j : Fin m, j ≠ phaseAct p v →
        scoreVec M (phaseScore p v) (runCount (fun _ => 0) (phaseAct p v) (h : ℚ)) j <
          scoreVec M (phaseScore p v) (runCount (fun _ => 0) (phaseAct p v) (h : ℚ)) (phaseAct p v))
    (hphasePos : ∀ p v : ℕ, v < phaseRunCount p → ∀ h : ℕ, h < phaseLen p v →
      0 < scoreVec M (phaseScore p v) (runCount (fun _ => 0) (phaseAct p v) (h : ℚ)) (phaseAct p v) + C) :
    IsStrictFPTrajectory (setupMatrix M w)
      (unrollAction (setupFullAct (flatAct phaseRunCount phaseAct))
        (setupFullLen (flatLen phaseRunCount phaseLen))) := by
  apply setup_unroll_isStrictFPTrajectory M w C
    (flatAct phaseRunCount phaseAct)
    (flatLen phaseRunCount phaseLen)
    (flatScore phaseRunCount phaseScore)
    hw_nonneg
  · intro i
    have h0 : flatPhase phaseRunCount 0 = 0 := by
      unfold flatPhase
      exact runIndexOfStep_at_offset hcount 0 0 (hcount 0)
    have hoff0 : flatOffset phaseRunCount 0 = 0 := by
      unfold flatOffset
      rw [h0, runStart_zero]
    simp [flatScore, h0, hoff0, hw_shift i]
  · intro u
    have hspec := runIndexOfStep_spec hcount u
    have hv : flatOffset phaseRunCount u < phaseRunCount (flatPhase phaseRunCount u) := by
      unfold flatOffset flatPhase
      have h2 := hspec.2
      rw [runStart_succ] at h2
      omega
    exact hphaseLen _ _ hv
  · intro u
    let p := flatPhase phaseRunCount u
    let v := flatOffset phaseRunCount u
    have hspec := runIndexOfStep_spec hcount u
    have hr_le : runStart phaseRunCount p ≤ u := hspec.1
    have hu_lt : u < runStart phaseRunCount (p + 1) := hspec.2
    rw [runStart_succ] at hu_lt
    have hv_def : v = u - runStart phaseRunCount p := rfl
    have hv : v < phaseRunCount p := by
      omega
    have hu_eq : u = runStart phaseRunCount p + v := by
      omega
    have h_rhs :
        scoreVec M (flatScore phaseRunCount phaseScore u)
          (runCount (fun _ => 0) (flatAct phaseRunCount phaseAct u)
            (flatLen phaseRunCount phaseLen u : ℚ)) =
        phaseScore p (v + 1) := by
      exact (hphaseStep p v hv).symm
    rw [h_rhs]
    by_cases hv1 : v + 1 < phaseRunCount p
    · have hu1 : u + 1 = runStart phaseRunCount p + (v + 1) := by omega
      have hp1 : flatPhase phaseRunCount (u + 1) = p := by
        unfold flatPhase
        rw [hu1, runIndexOfStep_at_offset hcount p (v + 1) hv1]
      have hoff1 : flatOffset phaseRunCount (u + 1) = v + 1 := by
        unfold flatOffset
        rw [hp1, hu1]
        omega
      simp [flatScore, hp1, hoff1]
    · have hv_eq : v + 1 = phaseRunCount p := by omega
      have hu1 : u + 1 = runStart phaseRunCount (p + 1) + 0 := by
        rw [runStart_succ]
        omega
      have hp1 : flatPhase phaseRunCount (u + 1) = p + 1 := by
        unfold flatPhase
        rw [hu1, runIndexOfStep_at_offset hcount (p + 1) 0 (hcount (p + 1))]
      have hoff1 : flatOffset phaseRunCount (u + 1) = 0 := by
        unfold flatOffset
        rw [hp1, hu1]
        omega
      simp only [flatScore, hp1, hoff1]
      rw [← hphaseBoundary p, hv_eq]
  · intro u h hh j hj
    have hspec := runIndexOfStep_spec hcount u
    have hv : flatOffset phaseRunCount u < phaseRunCount (flatPhase phaseRunCount u) := by
      unfold flatOffset flatPhase
      have h2 := hspec.2
      rw [runStart_succ] at h2
      omega
    exact hphaseValid _ _ hv h hh j hj
  · intro u h hh
    have hspec := runIndexOfStep_spec hcount u
    have hv : flatOffset phaseRunCount u < phaseRunCount (flatPhase phaseRunCount u) := by
      unfold flatOffset flatPhase
      have h2 := hspec.2
      rw [runStart_succ] at h2
      omega
    exact hphasePos _ _ hv h hh

/-!
## 6. Hypothesis-Free Unrolled 7-Action Counterexample (`M7`, Theorem E.1 `beta7:main`)
-/

/-- Auxiliary cumulative core count vector `q(ℓ) = (3ℓ^2 - 2ℓ, 3ℓ^2, 3ℓ^2 + 2ℓ)ᵀ` in Appendix E. -/
def q_aux (ℓ : ℚ) : Fin 3 → ℚ
  | 0 => 3 * ℓ ^ 2 - 2 * ℓ
  | 1 => 3 * ℓ ^ 2
  | 2 => 3 * ℓ ^ 2 + 2 * ℓ

/-- Full 6-action score state at the start of core sub-cycle `ℓ` in phase `k`. -/
def stateCoreStart (k ℓ : ℚ) (i : Fin 6) : ℚ :=
  V_seven k i + ∑ j : Fin 3, M_seven i ⟨j.val, by omega⟩ * (q_aux ℓ j - q_aux (21 * k + 10) j)

/-- Full 6-action score state after `r_1^{6ℓ+1}` in core sub-cycle `ℓ` of phase `k`. -/
def stateCoreAfterR1 (k ℓ : ℚ) (i : Fin 6) : ℚ :=
  stateCoreStart k ℓ i + (6 * ℓ + 1) * M_seven i 0

/-- Full 6-action score state after `r_2^{6ℓ+3}` in core sub-cycle `ℓ` of phase `k`. -/
def stateCoreAfterR2 (k ℓ : ℚ) (i : Fin 6) : ℚ :=
  stateCoreAfterR1 k ℓ i + (6 * ℓ + 3) * M_seven i 1

theorem stateCoreStart_at_begin (k : ℚ) :
    stateCoreStart k (21 * k + 10) = V_seven k := by
  ext i
  simp [stateCoreStart]

theorem stateCoreStart_at_end (k : ℚ) :
    stateCoreStart k (28 * k + 16) = stateBeforeG1 k := by
  ext i
  fin_cases i <;>
    simp [stateCoreStart, stateBeforeG1, Fin.sum_univ_three, q_aux, Q_seven] <;> ring

theorem seven_core_full_transitions (k ℓ : ℚ) :
    scoreVec M_seven (stateCoreStart k ℓ) (runCount (fun _ => 0) 0 (6 * ℓ + 1)) =
        stateCoreAfterR1 k ℓ ∧
      scoreVec M_seven (stateCoreAfterR1 k ℓ) (runCount (fun _ => 0) 1 (6 * ℓ + 3)) =
        stateCoreAfterR2 k ℓ ∧
      scoreVec M_seven (stateCoreAfterR2 k ℓ) (runCount (fun _ => 0) 2 (6 * ℓ + 5)) =
        stateCoreStart k (ℓ + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    rw [scoreVec_runCount M_seven (stateCoreStart k ℓ) (fun _ => 0) 0 i (6 * ℓ + 1)]
    simp [scoreVec, stateCoreAfterR1]
  · ext i
    rw [scoreVec_runCount M_seven (stateCoreAfterR1 k ℓ) (fun _ => 0) 1 i (6 * ℓ + 3)]
    simp [scoreVec, stateCoreAfterR2]
  · ext i
    rw [scoreVec_runCount M_seven (stateCoreAfterR2 k ℓ) (fun _ => 0) 2 i (6 * ℓ + 5)]
    fin_cases i <;>
      simp [scoreVec, stateCoreAfterR2, stateCoreAfterR1, stateCoreStart,
        Fin.sum_univ_three, M_seven, q_aux] <;> ring

theorem seven_guard_transitions (k : ℚ) :
    scoreVec M_seven (stateBeforeG1 k) (runCount (fun _ => 0) 3 (L_seven k 0)) =
        stateBeforeG2 k ∧
      scoreVec M_seven (stateBeforeG2 k) (runCount (fun _ => 0) 4 (L_seven k 1)) =
        stateBeforeG3 k ∧
      scoreVec M_seven (stateBeforeG3 k) (runCount (fun _ => 0) 5 (L_seven k 2)) =
        V_seven (k + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    rw [scoreVec_runCount M_seven (stateBeforeG1 k) (fun _ => 0) 3 i (L_seven k 0)]
    simp [scoreVec, stateBeforeG2]
    ring
  · ext i
    rw [scoreVec_runCount M_seven (stateBeforeG2 k) (fun _ => 0) 4 i (L_seven k 1)]
    simp [scoreVec, stateBeforeG3]
    ring
  · ext i
    rw [scoreVec_runCount M_seven (stateBeforeG3 k) (fun _ => 0) 5 i (L_seven k 2)]
    have hret := seven_phase_return k i
    fin_cases i <;>
      simp [scoreVec, stateBeforeG3, stateBeforeG2, stateBeforeG1,
        Fin.sum_univ_six, Fin.sum_univ_three, QL_seven] at hret ⊢ <;> linarith

set_option maxHeartbeats 800000 in
/-- **Full 6-Action Core `r_1^{6ℓ+1}` Validity (`seven_core_full_r1_valid`)**:
    Throughout `0 ≤ h ≤ 6ℓ` in sub-cycle `21k + 10 ≤ ℓ ≤ 28k + 15` (`k ≥ 20`),
    action `0` strictly beats all 5 rival actions `j ≠ 0` by margin `≥ 1/10000`. -/
theorem seven_core_full_r1_valid {k ℓ h : ℚ}
    (hk : 20 ≤ k) (hℓ1 : 21 * k + 10 ≤ ℓ) (hℓ2 : ℓ ≤ 28 * k + 15)
    (hh0 : 0 ≤ h) (hhL : h ≤ (6 * ℓ + 1) - 1) (j : Fin 6) (hj : j ≠ 0) :
    (1 / 10000 : ℚ) ≤
      scoreVec M_seven (stateCoreStart k ℓ) (runCount (fun _ => 0) 0 h) 0 -
        scoreVec M_seven (stateCoreStart k ℓ) (runCount (fun _ => 0) 0 h) j := by
  have hk0 : 0 ≤ k - 20 := by linarith
  have he0 : 0 ≤ ℓ - (21 * k + 10) := by linarith
  have hd0 : 0 ≤ 28 * k + 15 - ℓ := by linarith
  have hc1 := mul_nonneg hk0 hk0
  have hc2 := mul_nonneg he0 he0
  have hc3 := mul_nonneg hd0 hd0
  have hc4 := mul_nonneg hk0 he0
  have hc5 := mul_nonneg hk0 hd0
  have hc6 := mul_nonneg he0 hd0
  fin_cases j
  · contradiction
  · apply pure_run_margin_of_endpoints M_seven_skew (stateCoreStart k ℓ) (fun _ => 0) 0 1 hh0 hhL
    · simp [scoreVec, stateCoreStart, V_seven, W_seven, Fin.sum_univ_three, M_seven, q_aux]; nlinarith
    · simp [scoreVec, stateCoreStart, V_seven, W_seven, Fin.sum_univ_three, M_seven, q_aux]; nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateCoreStart k ℓ) (fun _ => 0) 0 2 hh0 hhL
    · simp [scoreVec, stateCoreStart, V_seven, W_seven, Fin.sum_univ_three, M_seven, q_aux]; nlinarith
    · simp [scoreVec, stateCoreStart, V_seven, W_seven, Fin.sum_univ_three, M_seven, q_aux]; nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateCoreStart k ℓ) (fun _ => 0) 0 3 hh0 hhL
    · simp [scoreVec, stateCoreStart, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven, q_aux]; nlinarith
    · simp [scoreVec, stateCoreStart, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven, q_aux]; nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateCoreStart k ℓ) (fun _ => 0) 0 4 hh0 hhL
    · simp [scoreVec, stateCoreStart, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven, q_aux]; nlinarith
    · simp [scoreVec, stateCoreStart, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven, q_aux]; nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateCoreStart k ℓ) (fun _ => 0) 0 5 hh0 hhL
    · simp [scoreVec, stateCoreStart, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven, q_aux]; nlinarith
    · simp [scoreVec, stateCoreStart, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven, q_aux]; nlinarith

set_option maxHeartbeats 800000 in
/-- **Full 6-Action Core `r_2^{6ℓ+3}` Validity (`seven_core_full_r2_valid`)**:
    Throughout `0 ≤ h ≤ 6ℓ + 2` in sub-cycle `21k + 10 ≤ ℓ ≤ 28k + 15` (`k ≥ 20`),
    action `1` strictly beats all 5 rival actions `j ≠ 1` by margin `≥ 1/10000`. -/
theorem seven_core_full_r2_valid {k ℓ h : ℚ}
    (hk : 20 ≤ k) (hℓ1 : 21 * k + 10 ≤ ℓ) (hℓ2 : ℓ ≤ 28 * k + 15)
    (hh0 : 0 ≤ h) (hhL : h ≤ (6 * ℓ + 3) - 1) (j : Fin 6) (hj : j ≠ 1) :
    (1 / 10000 : ℚ) ≤
      scoreVec M_seven (stateCoreAfterR1 k ℓ) (runCount (fun _ => 0) 1 h) 1 -
        scoreVec M_seven (stateCoreAfterR1 k ℓ) (runCount (fun _ => 0) 1 h) j := by
  have hk0 : 0 ≤ k - 20 := by linarith
  have he0 : 0 ≤ ℓ - (21 * k + 10) := by linarith
  have hd0 : 0 ≤ 28 * k + 15 - ℓ := by linarith
  have hc1 := mul_nonneg hk0 hk0
  have hc2 := mul_nonneg he0 he0
  have hc3 := mul_nonneg hd0 hd0
  have hc4 := mul_nonneg hk0 he0
  have hc5 := mul_nonneg hk0 hd0
  have hc6 := mul_nonneg he0 hd0
  fin_cases j
  · apply pure_run_margin_of_endpoints M_seven_skew (stateCoreAfterR1 k ℓ) (fun _ => 0) 1 0 hh0 hhL
    · simp [scoreVec, stateCoreAfterR1, stateCoreStart, V_seven, W_seven,
        Fin.sum_univ_three, M_seven, q_aux]; nlinarith
    · simp [scoreVec, stateCoreAfterR1, stateCoreStart, V_seven, W_seven,
        Fin.sum_univ_three, M_seven, q_aux]; nlinarith
  · contradiction
  · apply pure_run_margin_of_endpoints M_seven_skew (stateCoreAfterR1 k ℓ) (fun _ => 0) 1 2 hh0 hhL
    · simp [scoreVec, stateCoreAfterR1, stateCoreStart, V_seven, W_seven,
        Fin.sum_univ_three, M_seven, q_aux]; nlinarith
    · simp [scoreVec, stateCoreAfterR1, stateCoreStart, V_seven, W_seven,
        Fin.sum_univ_three, M_seven, q_aux]; nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateCoreAfterR1 k ℓ) (fun _ => 0) 1 3 hh0 hhL
    · simp [scoreVec, stateCoreAfterR1, stateCoreStart, V_seven, W_seven, Vg_seven, H_seven,
        s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven, q_aux]; nlinarith
    · simp [scoreVec, stateCoreAfterR1, stateCoreStart, V_seven, W_seven, Vg_seven, H_seven,
        s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven, q_aux]; nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateCoreAfterR1 k ℓ) (fun _ => 0) 1 4 hh0 hhL
    · simp [scoreVec, stateCoreAfterR1, stateCoreStart, V_seven, W_seven, Vg_seven, H_seven,
        s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven, q_aux]; nlinarith
    · simp [scoreVec, stateCoreAfterR1, stateCoreStart, V_seven, W_seven, Vg_seven, H_seven,
        s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven, q_aux]; nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateCoreAfterR1 k ℓ) (fun _ => 0) 1 5 hh0 hhL
    · simp [scoreVec, stateCoreAfterR1, stateCoreStart, V_seven, W_seven, Vg_seven, H_seven,
        s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven, q_aux]; nlinarith
    · simp [scoreVec, stateCoreAfterR1, stateCoreStart, V_seven, W_seven, Vg_seven, H_seven,
        s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven, q_aux]; nlinarith

set_option maxHeartbeats 800000 in
/-- **Full 6-Action Core `r_3^{6ℓ+5}` Validity (`seven_core_full_r3_valid`)**:
    Throughout `0 ≤ h ≤ 6ℓ + 4` in sub-cycle `21k + 10 ≤ ℓ ≤ 28k + 15` (`k ≥ 20`),
    action `2` strictly beats all 5 rival actions `j ≠ 2` by margin `≥ 1/10000`. -/
theorem seven_core_full_r3_valid {k ℓ h : ℚ}
    (hk : 20 ≤ k) (hℓ1 : 21 * k + 10 ≤ ℓ) (hℓ2 : ℓ ≤ 28 * k + 15)
    (hh0 : 0 ≤ h) (hhL : h ≤ (6 * ℓ + 5) - 1) (j : Fin 6) (hj : j ≠ 2) :
    (1 / 10000 : ℚ) ≤
      scoreVec M_seven (stateCoreAfterR2 k ℓ) (runCount (fun _ => 0) 2 h) 2 -
        scoreVec M_seven (stateCoreAfterR2 k ℓ) (runCount (fun _ => 0) 2 h) j := by
  have hk0 : 0 ≤ k - 20 := by linarith
  have he0 : 0 ≤ ℓ - (21 * k + 10) := by linarith
  have hd0 : 0 ≤ 28 * k + 15 - ℓ := by linarith
  have hc1 := mul_nonneg hk0 hk0
  have hc2 := mul_nonneg he0 he0
  have hc3 := mul_nonneg hd0 hd0
  have hc4 := mul_nonneg hk0 he0
  have hc5 := mul_nonneg hk0 hd0
  have hc6 := mul_nonneg he0 hd0
  fin_cases j
  · apply pure_run_margin_of_endpoints M_seven_skew (stateCoreAfterR2 k ℓ) (fun _ => 0) 2 0 hh0 hhL
    · simp [scoreVec, stateCoreAfterR2, stateCoreAfterR1, stateCoreStart, V_seven, W_seven,
        Fin.sum_univ_three, M_seven, q_aux]; nlinarith
    · simp [scoreVec, stateCoreAfterR2, stateCoreAfterR1, stateCoreStart, V_seven, W_seven,
        Fin.sum_univ_three, M_seven, q_aux]; nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateCoreAfterR2 k ℓ) (fun _ => 0) 2 1 hh0 hhL
    · simp [scoreVec, stateCoreAfterR2, stateCoreAfterR1, stateCoreStart, V_seven, W_seven,
        Fin.sum_univ_three, M_seven, q_aux]; nlinarith
    · simp [scoreVec, stateCoreAfterR2, stateCoreAfterR1, stateCoreStart, V_seven, W_seven,
        Fin.sum_univ_three, M_seven, q_aux]; nlinarith
  · contradiction
  · apply pure_run_margin_of_endpoints M_seven_skew (stateCoreAfterR2 k ℓ) (fun _ => 0) 2 3 hh0 hhL
    · simp [scoreVec, stateCoreAfterR2, stateCoreAfterR1, stateCoreStart, V_seven, W_seven,
        Vg_seven, H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard,
        L_seven, q_aux]; nlinarith
    · simp [scoreVec, stateCoreAfterR2, stateCoreAfterR1, stateCoreStart, V_seven, W_seven,
        Vg_seven, H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard,
        L_seven, q_aux]; nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateCoreAfterR2 k ℓ) (fun _ => 0) 2 4 hh0 hhL
    · simp [scoreVec, stateCoreAfterR2, stateCoreAfterR1, stateCoreStart, V_seven, W_seven,
        Vg_seven, H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard,
        L_seven, q_aux]; nlinarith
    · simp [scoreVec, stateCoreAfterR2, stateCoreAfterR1, stateCoreStart, V_seven, W_seven,
        Vg_seven, H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard,
        L_seven, q_aux]; nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateCoreAfterR2 k ℓ) (fun _ => 0) 2 5 hh0 hhL
    · simp [scoreVec, stateCoreAfterR2, stateCoreAfterR1, stateCoreStart, V_seven, W_seven,
        Vg_seven, H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard,
        L_seven, q_aux]; nlinarith
    · simp [scoreVec, stateCoreAfterR2, stateCoreAfterR1, stateCoreStart, V_seven, W_seven,
        Vg_seven, H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard,
        L_seven, q_aux]; nlinarith

/-- Active score positivity for all 6 run types in phase `k ≥ 20` (`21k + 10 ≤ ℓ ≤ 28k + 15`). -/
theorem seven_active_scores_pos {k ℓ : ℚ} (hk : 20 ≤ k) (hℓ1 : 21 * k + 10 ≤ ℓ) :
    0 < stateCoreStart k ℓ 0 ∧
      0 < stateCoreAfterR1 k ℓ 1 ∧
      0 < stateCoreAfterR2 k ℓ 2 ∧
      0 < stateBeforeG1 k 3 ∧
      0 < stateBeforeG2 k 4 ∧
      0 < stateBeforeG3 k 5 := by
  have hk0 : 0 ≤ k - 20 := by linarith
  have he0 : 0 ≤ ℓ - (21 * k + 10) := by linarith
  have hc1 := mul_nonneg hk0 hk0
  have hc2 := mul_nonneg he0 he0
  have hc4 := mul_nonneg hk0 he0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [stateCoreStart, V_seven, W_seven, Fin.sum_univ_three, M_seven, q_aux]; nlinarith
  · simp [stateCoreAfterR1, stateCoreStart, V_seven, W_seven, Fin.sum_univ_three, M_seven, q_aux]; nlinarith
  · simp [stateCoreAfterR2, stateCoreAfterR1, stateCoreStart, V_seven, W_seven, Fin.sum_univ_three, M_seven, q_aux]; nlinarith
  · simp [stateBeforeG1, V_seven, Vg_seven, H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
  · simp [stateBeforeG2, stateBeforeG1, V_seven, Vg_seven, H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
  · simp [stateBeforeG3, stateBeforeG2, stateBeforeG1, V_seven, Vg_seven, H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith

/-- Number of recurrent runs `21p + 441` in phase `p ∈ ℕ` (`k = p + 20`) of `M_seven`:
    `21p + 438 = 3(7p + 146)` core sub-runs followed by `3` guard runs. -/
def sevenPhaseRunCount (p : ℕ) : ℕ :=
  21 * p + 441

/-- Active recurrent action `Fin 6` for run `v` of phase `p` (`k = p + 20`) in `M_seven`. -/
def sevenPhaseAct (p v : ℕ) : Fin 6 :=
  if v < 21 * p + 438 then
    match v % 3 with
    | 0 => 0
    | 1 => 1
    | _ => 2
  else if v = 21 * p + 438 then 3
  else if v = 21 * p + 439 then 4
  else 5

/-- Positive integer run length for run `v` of phase `p` (`k = p + 20`) in `M_seven`. -/
def sevenPhaseLen (p v : ℕ) : ℕ :=
  if v < 21 * p + 438 then
    let ℓ_nat := 21 * (p + 20) + 10 + v / 3
    match v % 3 with
    | 0 => 6 * ℓ_nat + 1
    | 1 => 6 * ℓ_nat + 3
    | _ => 6 * ℓ_nat + 5
  else if v = 21 * p + 438 then 882 * p ^ 2 + 32976 * p + 319218
  else if v = 21 * p + 439 then 882 * p ^ 2 + 37680 * p + 403222
  else 882 * p ^ 2 + 21804 * p + 119722

/-- Recurrent 6-action entry score vector before run `v` of phase `p` (`k = p + 20`). -/
def sevenPhaseScore (p v : ℕ) : Fin 6 → ℚ :=
  let k : ℚ := (p : ℚ) + 20
  if v < 21 * p + 438 then
    let ℓ : ℚ := ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ)
    match v % 3 with
    | 0 => stateCoreStart k ℓ
    | 1 => stateCoreAfterR1 k ℓ
    | _ => stateCoreAfterR2 k ℓ
  else if v = 21 * p + 438 then stateBeforeG1 k
  else if v = 21 * p + 439 then stateBeforeG2 k
  else if v = 21 * p + 440 then stateBeforeG3 k
  else V_seven (((p + 1 : ℕ) : ℚ) + 20)

/-- The unrolled discrete-time trajectory `sevenTrajectory : ℕ → Option (Fin 6)` of `M7`. -/
def sevenTrajectory : ℕ → Option (Fin 6) :=
  unrollAction
    (setupFullAct (flatAct sevenPhaseRunCount sevenPhaseAct))
    (setupFullLen (flatLen sevenPhaseRunCount sevenPhaseLen))

set_option maxHeartbeats 800000 in
/-- **Hypothesis-Free Unrolled 7-Action Counterexample Refuting Karlin's Conjecture
    (`seven_unrolled_strict_fp_trajectory`, Theorem E.1 `beta7:main`)**:
    The 7×7 skew-symmetric rational game `M7` and explicit discrete-time sequence `sevenTrajectory`
    form a strictly tie-free Fictitious Play trajectory (`IsStrictFPTrajectory M7 sevenTrajectory`)
    at every integer step `t ≥ 1` starting from zero initial counts at `t = 0`. -/
theorem seven_unrolled_strict_fp_trajectory :
    IsSkewSymmetric M7 ∧
    IsStrictFPTrajectory M7 sevenTrajectory := by
  refine ⟨M7_skew, ?_⟩
  apply setup_phase_unroll_isStrictFPTrajectory M_seven w_seven (657497227 / 52500)
    sevenPhaseRunCount sevenPhaseAct sevenPhaseLen sevenPhaseScore
  · intro p
    unfold sevenPhaseRunCount
    omega
  · intro i
    have h1 := seven_setup_realization.1 i
    linarith
  · intro i
    have h2 := seven_setup_realization.2 i
    have h0 : sevenPhaseScore 0 0 = V_seven 20 := by
      simp [sevenPhaseScore]
      have h430 : (430 : ℚ) = 21 * (20 : ℚ) + 10 := by norm_num
      rw [h430]
      exact stateCoreStart_at_begin 20
    rw [h0]
    exact h2
  · intro p v _hv
    unfold sevenPhaseLen
    split_ifs with h1 h2 h3
    · have hmod : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
      rcases hmod with hm | hm | hm <;> simp [hm]
    · positivity
    · positivity
    · positivity
  · intro p v hv
    unfold sevenPhaseRunCount at hv
    by_cases hcore : v < 21 * p + 438
    · have hmod : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
      rcases hmod with hm0 | hm1 | hm2
      · have hv1 : v + 1 < 21 * p + 438 := by omega
        have hdiv : (v + 1) / 3 = v / 3 := by omega
        have hm_next : (v + 1) % 3 = 1 := by omega
        have hact : sevenPhaseAct p v = 0 := by simp [sevenPhaseAct, hcore, hm0]
        have hlen : (sevenPhaseLen p v : ℚ) =
            6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 1 := by
          simp [sevenPhaseLen, hcore, hm0]
        have hs0 : sevenPhaseScore p v =
            stateCoreStart ((p : ℚ) + 20) ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
          simp [sevenPhaseScore, hcore, hm0]
        have hs1 : sevenPhaseScore p (v + 1) =
            stateCoreAfterR1 ((p : ℚ) + 20) ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
          simp [sevenPhaseScore, hv1, hdiv, hm_next]
        rw [hs0, hs1, hact, hlen]
        exact (seven_core_full_transitions ((p : ℚ) + 20)
          ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ)).1.symm
      · have hv1 : v + 1 < 21 * p + 438 := by omega
        have hdiv : (v + 1) / 3 = v / 3 := by omega
        have hm_next : (v + 1) % 3 = 2 := by omega
        have hact : sevenPhaseAct p v = 1 := by simp [sevenPhaseAct, hcore, hm1]
        have hlen : (sevenPhaseLen p v : ℚ) =
            6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 3 := by
          simp [sevenPhaseLen, hcore, hm1]
        have hs0 : sevenPhaseScore p v =
            stateCoreAfterR1 ((p : ℚ) + 20) ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
          simp [sevenPhaseScore, hcore, hm1]
        have hs1 : sevenPhaseScore p (v + 1) =
            stateCoreAfterR2 ((p : ℚ) + 20) ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
          simp [sevenPhaseScore, hv1, hdiv, hm_next]
        rw [hs0, hs1, hact, hlen]
        exact (seven_core_full_transitions ((p : ℚ) + 20)
          ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ)).2.1.symm
      · have hdiv : (v + 1) / 3 = v / 3 + 1 := by omega
        have hm_next : (v + 1) % 3 = 0 := by omega
        have hact : sevenPhaseAct p v = 2 := by simp [sevenPhaseAct, hcore, hm2]
        have hlen : (sevenPhaseLen p v : ℚ) =
            6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 5 := by
          simp [sevenPhaseLen, hcore, hm2]
        have hs0 : sevenPhaseScore p v =
            stateCoreAfterR2 ((p : ℚ) + 20) ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
          simp [sevenPhaseScore, hcore, hm2]
        rw [hs0, hact, hlen]
        rw [(seven_core_full_transitions ((p : ℚ) + 20)
          ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ)).2.2]
        by_cases hv1 : v + 1 < 21 * p + 438
        · have hs1 : sevenPhaseScore p (v + 1) =
              stateCoreStart ((p : ℚ) + 20)
                ((21 * (p + 20) + 10 + (v + 1) / 3 : ℕ) : ℚ) := by
            simp [sevenPhaseScore, hv1, hm_next]
          rw [hs1, hdiv]
          have hcast : ((21 * (p + 20) + 10 + (v / 3 + 1) : ℕ) : ℚ) =
              ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 1 := by
            push_cast; ring
          rw [hcast]
        · have hv_end : v + 1 = 21 * p + 438 := by omega
          have hdiv_end : v / 3 = 7 * p + 145 := by omega
          have hs1 : sevenPhaseScore p (v + 1) = stateBeforeG1 ((p : ℚ) + 20) := by
            simp [sevenPhaseScore, hv_end]
          rw [hs1, hdiv_end]
          have hcast : ((21 * (p + 20) + 10 + (7 * p + 145) : ℕ) : ℚ) + 1 =
              28 * ((p : ℚ) + 20) + 16 := by
            push_cast; ring
          rw [hcast, stateCoreStart_at_end]
    · have hg : v = 21 * p + 438 ∨ v = 21 * p + 439 ∨ v = 21 * p + 440 := by omega
      rcases hg with hg1 | hg2 | hg3
      · subst hg1
        have hlen : (sevenPhaseLen p (21 * p + 438) : ℚ) = L_seven ((p : ℚ) + 20) 0 := by
          simp [sevenPhaseLen, L_seven]
          ring
        have hs0 : sevenPhaseScore p (21 * p + 438) = stateBeforeG1 ((p : ℚ) + 20) := by
          simp [sevenPhaseScore]
        have hs1 : sevenPhaseScore p (21 * p + 438 + 1) = stateBeforeG2 ((p : ℚ) + 20) := by
          have h1 : ¬ (21 * p + 438 + 1 < 21 * p + 438) := by omega
          have h3 : 21 * p + 438 + 1 = 21 * p + 439 := by omega
          simp [sevenPhaseScore, h1, h3]
        have hact : sevenPhaseAct p (21 * p + 438) = 3 := by simp [sevenPhaseAct]
        rw [hs0, hs1, hact, hlen]
        exact (seven_guard_transitions ((p : ℚ) + 20)).1.symm
      · subst hg2
        have hlen : (sevenPhaseLen p (21 * p + 439) : ℚ) = L_seven ((p : ℚ) + 20) 1 := by
          have h1 : ¬ (21 * p + 439 < 21 * p + 438) := by omega
          simp [sevenPhaseLen, h1, L_seven]
          ring
        have hs0 : sevenPhaseScore p (21 * p + 439) = stateBeforeG2 ((p : ℚ) + 20) := by
          have h1 : ¬ (21 * p + 439 < 21 * p + 438) := by omega
          simp [sevenPhaseScore, h1]
        have hs1 : sevenPhaseScore p (21 * p + 439 + 1) = stateBeforeG3 ((p : ℚ) + 20) := by
          have h1 : ¬ (21 * p + 439 + 1 < 21 * p + 438) := by omega
          have h4 : 21 * p + 439 + 1 = 21 * p + 440 := by omega
          simp [sevenPhaseScore, h1, h4]
        have hact : sevenPhaseAct p (21 * p + 439) = 4 := by
          have h1 : ¬ (21 * p + 439 < 21 * p + 438) := by omega
          simp [sevenPhaseAct, h1]
        rw [hs0, hs1, hact, hlen]
        exact (seven_guard_transitions ((p : ℚ) + 20)).2.1.symm
      · subst hg3
        have hlen : (sevenPhaseLen p (21 * p + 440) : ℚ) = L_seven ((p : ℚ) + 20) 2 := by
          have h1 : ¬ (21 * p + 440 < 21 * p + 438) := by omega
          simp [sevenPhaseLen, h1, L_seven]
          ring
        have hs0 : sevenPhaseScore p (21 * p + 440) = stateBeforeG3 ((p : ℚ) + 20) := by
          have h1 : ¬ (21 * p + 440 < 21 * p + 438) := by omega
          simp [sevenPhaseScore, h1]
        have hs1 : sevenPhaseScore p (21 * p + 440 + 1) =
            V_seven ((p : ℚ) + 20 + 1) := by
          have h1 : ¬ (21 * p + 440 + 1 < 21 * p + 438) := by omega
          simp [sevenPhaseScore, h1]
          congr 1
          ring
        have hact : sevenPhaseAct p (21 * p + 440) = 5 := by
          have h1 : ¬ (21 * p + 440 < 21 * p + 438) := by omega
          simp [sevenPhaseAct, h1]
        rw [hs0, hs1, hact, hlen]
        exact (seven_guard_transitions ((p : ℚ) + 20)).2.2.symm
  · intro p
    unfold sevenPhaseRunCount
    have h1 : ¬ (21 * p + 441 < 21 * p + 438) := by omega
    have lhs_eq : sevenPhaseScore p (21 * p + 441) = V_seven (((p + 1 : ℕ) : ℚ) + 20) := by
      simp [sevenPhaseScore, h1]
    have rhs_eq : sevenPhaseScore (p + 1) 0 = V_seven (((p + 1 : ℕ) : ℚ) + 20) := by
      have h0 : 0 < 21 * (p + 1) + 438 := by omega
      simp [sevenPhaseScore, h0]
      exact stateCoreStart_at_begin ((p : ℚ) + 1 + 20)
    rw [lhs_eq, rhs_eq]
  · intro p v hv h hh j hj
    unfold sevenPhaseRunCount at hv
    have hk : (20 : ℚ) ≤ (p : ℚ) + 20 := by
      have : (0 : ℚ) ≤ (p : ℚ) := Nat.cast_nonneg p
      linarith
    by_cases hcore : v < 21 * p + 438
    · have hℓ1 : 21 * ((p : ℚ) + 20) + 10 ≤ ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
        have hnat : 21 * (p + 20) + 10 ≤ 21 * (p + 20) + 10 + v / 3 := Nat.le_add_right _ _
        have hrat : ((21 * (p + 20) + 10 : ℕ) : ℚ) ≤ ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
          exact_mod_cast hnat
        have hcast : ((21 * (p + 20) + 10 : ℕ) : ℚ) = 21 * ((p : ℚ) + 20) + 10 := by
          push_cast; ring
        linarith
      have hℓ2 : ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) ≤ 28 * ((p : ℚ) + 20) + 15 := by
        have hnat : 21 * (p + 20) + 10 + v / 3 ≤ 28 * (p + 20) + 15 := by omega
        have hrat : ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) ≤ ((28 * (p + 20) + 15 : ℕ) : ℚ) := by
          exact_mod_cast hnat
        have hcast : ((28 * (p + 20) + 15 : ℕ) : ℚ) = 28 * ((p : ℚ) + 20) + 15 := by
          push_cast; ring
        linarith
      have hmod : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
      rcases hmod with hm0 | hm1 | hm2
      · have hact : sevenPhaseAct p v = 0 := by simp [sevenPhaseAct, hcore, hm0]
        have hs0 : sevenPhaseScore p v =
            stateCoreStart ((p : ℚ) + 20) ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
          simp [sevenPhaseScore, hcore, hm0]
        have hhL : (h : ℚ) ≤ (6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 1) - 1 := by
          simp [sevenPhaseLen, hcore, hm0] at hh
          have hnat : h ≤ 6 * (21 * (p + 20) + 10 + v / 3) := by omega
          have hrat : (h : ℚ) ≤ 6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by exact_mod_cast hnat
          linarith
        rw [hact] at hj ⊢
        rw [hs0]
        have hv0 := seven_core_full_r1_valid hk hℓ1 hℓ2 (Nat.cast_nonneg h) hhL j hj
        linarith
      · have hact : sevenPhaseAct p v = 1 := by simp [sevenPhaseAct, hcore, hm1]
        have hs0 : sevenPhaseScore p v =
            stateCoreAfterR1 ((p : ℚ) + 20) ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
          simp [sevenPhaseScore, hcore, hm1]
        have hhL : (h : ℚ) ≤ (6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 3) - 1 := by
          simp [sevenPhaseLen, hcore, hm1] at hh
          have hnat : h ≤ 6 * (21 * (p + 20) + 10 + v / 3) + 2 := by omega
          have hrat : (h : ℚ) ≤ 6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 2 := by
            exact_mod_cast hnat
          linarith
        rw [hact] at hj ⊢
        rw [hs0]
        have hv1 := seven_core_full_r2_valid hk hℓ1 hℓ2 (Nat.cast_nonneg h) hhL j hj
        linarith
      · have hact : sevenPhaseAct p v = 2 := by simp [sevenPhaseAct, hcore, hm2]
        have hs0 : sevenPhaseScore p v =
            stateCoreAfterR2 ((p : ℚ) + 20) ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
          simp [sevenPhaseScore, hcore, hm2]
        have hhL : (h : ℚ) ≤ (6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 5) - 1 := by
          simp [sevenPhaseLen, hcore, hm2] at hh
          have hnat : h ≤ 6 * (21 * (p + 20) + 10 + v / 3) + 4 := by omega
          have hrat : (h : ℚ) ≤ 6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 4 := by
            exact_mod_cast hnat
          linarith
        rw [hact] at hj ⊢
        rw [hs0]
        have hv2 := seven_core_full_r3_valid hk hℓ1 hℓ2 (Nat.cast_nonneg h) hhL j hj
        linarith
    · have hg : v = 21 * p + 438 ∨ v = 21 * p + 439 ∨ v = 21 * p + 440 := by omega
      rcases hg with hg1 | hg2 | hg3
      · subst hg1
        have hact : sevenPhaseAct p (21 * p + 438) = 3 := by simp [sevenPhaseAct]
        have hs0 : sevenPhaseScore p (21 * p + 438) = stateBeforeG1 ((p : ℚ) + 20) := by
          simp [sevenPhaseScore]
        have hhL : (h : ℚ) ≤ L_seven ((p : ℚ) + 20) 0 - 1 := by
          simp [sevenPhaseLen] at hh
          have hnat : h + 1 ≤ 882 * p ^ 2 + 32976 * p + 319218 := by omega
          have hrat : (h : ℚ) + 1 ≤ 882 * (p : ℚ) ^ 2 + 32976 * (p : ℚ) + 319218 := by
            exact_mod_cast hnat
          have hL : L_seven ((p : ℚ) + 20) 0 =
              882 * (p : ℚ) ^ 2 + 32976 * (p : ℚ) + 319218 := by
            simp [L_seven]; ring
          linarith
        rw [hact] at hj ⊢
        rw [hs0]
        have hvg1 := seven_guard1_run_valid hk (Nat.cast_nonneg h) hhL j hj
        linarith
      · subst hg2
        have h1 : ¬ (21 * p + 439 < 21 * p + 438) := by omega
        have hact : sevenPhaseAct p (21 * p + 439) = 4 := by simp [sevenPhaseAct, h1]
        have hs0 : sevenPhaseScore p (21 * p + 439) = stateBeforeG2 ((p : ℚ) + 20) := by
          simp [sevenPhaseScore, h1]
        have hhL : (h : ℚ) ≤ L_seven ((p : ℚ) + 20) 1 - 1 := by
          simp [sevenPhaseLen, h1] at hh
          have hnat : h + 1 ≤ 882 * p ^ 2 + 37680 * p + 403222 := by omega
          have hrat : (h : ℚ) + 1 ≤ 882 * (p : ℚ) ^ 2 + 37680 * (p : ℚ) + 403222 := by
            exact_mod_cast hnat
          have hL : L_seven ((p : ℚ) + 20) 1 =
              882 * (p : ℚ) ^ 2 + 37680 * (p : ℚ) + 403222 := by
            simp [L_seven]; ring
          linarith
        rw [hact] at hj ⊢
        rw [hs0]
        have hvg2 := seven_guard2_run_valid hk (Nat.cast_nonneg h) hhL j hj
        linarith
      · subst hg3
        have h1 : ¬ (21 * p + 440 < 21 * p + 438) := by omega
        have hact : sevenPhaseAct p (21 * p + 440) = 5 := by simp [sevenPhaseAct, h1]
        have hs0 : sevenPhaseScore p (21 * p + 440) = stateBeforeG3 ((p : ℚ) + 20) := by
          simp [sevenPhaseScore, h1]
        have hhL : (h : ℚ) ≤ L_seven ((p : ℚ) + 20) 2 - 1 := by
          simp [sevenPhaseLen, h1] at hh
          have hnat : h + 1 ≤ 882 * p ^ 2 + 21804 * p + 119722 := by omega
          have hrat : (h : ℚ) + 1 ≤ 882 * (p : ℚ) ^ 2 + 21804 * (p : ℚ) + 119722 := by
            exact_mod_cast hnat
          have hL : L_seven ((p : ℚ) + 20) 2 =
              882 * (p : ℚ) ^ 2 + 21804 * (p : ℚ) + 119722 := by
            simp [L_seven]; ring
          linarith
        rw [hact] at hj ⊢
        rw [hs0]
        have hvg3 := seven_guard3_run_valid hk (Nat.cast_nonneg h) hhL j hj
        linarith
  · intro p v hv h _hh
    unfold sevenPhaseRunCount at hv
    rw [scoreVec_runCount_self M_seven_skew]
    have hzero :
        scoreVec M_seven (sevenPhaseScore p v) (fun _ => 0) (sevenPhaseAct p v) =
          sevenPhaseScore p v (sevenPhaseAct p v) := by
      simp [scoreVec]
    rw [hzero]
    have hk : (20 : ℚ) ≤ (p : ℚ) + 20 := by
      have : (0 : ℚ) ≤ (p : ℚ) := Nat.cast_nonneg p
      linarith
    have hℓ1 : 21 * ((p : ℚ) + 20) + 10 ≤ ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
      have hnat : 21 * (p + 20) + 10 ≤ 21 * (p + 20) + 10 + v / 3 := Nat.le_add_right _ _
      have hrat : ((21 * (p + 20) + 10 : ℕ) : ℚ) ≤ ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
        exact_mod_cast hnat
      have hcast : ((21 * (p + 20) + 10 : ℕ) : ℚ) = 21 * ((p : ℚ) + 20) + 10 := by
        push_cast; ring
      linarith
    have hpos := seven_active_scores_pos hk hℓ1
    by_cases hcore : v < 21 * p + 438
    · have hmod : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
      rcases hmod with hm0 | hm1 | hm2
      · simp only [sevenPhaseScore, sevenPhaseAct, hcore, hm0, ↓reduceIte]; linarith [hpos.1]
      · simp only [sevenPhaseScore, sevenPhaseAct, hcore, hm1, ↓reduceIte]; linarith [hpos.2.1]
      · simp only [sevenPhaseScore, sevenPhaseAct, hcore, hm2, ↓reduceIte]; linarith [hpos.2.2.1]
    · have hg : v = 21 * p + 438 ∨ v = 21 * p + 439 ∨ v = 21 * p + 440 := by omega
      rcases hg with hg1 | hg2 | hg3
      · subst hg1
        simp only [sevenPhaseScore, sevenPhaseAct, hcore, ↓reduceIte]
        linarith [hpos.2.2.2.1]
      · subst hg2
        have h1 : ¬ (21 * p + 439 < 21 * p + 438) := by omega
        have h2 : 21 * p + 439 ≠ 21 * p + 438 := by omega
        simp only [sevenPhaseScore, sevenPhaseAct, h1, h2, ↓reduceIte]
        linarith [hpos.2.2.2.2.1]
      · subst hg3
        have h1 : ¬ (21 * p + 440 < 21 * p + 438) := by omega
        have h2 : 21 * p + 440 ≠ 21 * p + 438 := by omega
        have h3 : 21 * p + 440 ≠ 21 * p + 439 := by omega
        simp only [sevenPhaseScore, sevenPhaseAct, h1, h2, h3, ↓reduceIte]
        linarith [hpos.2.2.2.2.2]

end Karlin

#print axioms Karlin.colCumLoss_eq_neg_cumScore
#print axioms Karlin.colCumPayoff_eq_cumScore
#print axioms Karlin.isStrictTwoPlayerFPTrajectory_iff_isStrictFPTrajectory
#print axioms Karlin.unique_two_player_fp_trajectory
#print axioms Karlin.empiricalRowPayoff_eq_cumScore_div
#print axioms Karlin.empiricalColPayoff_eq_colCumLoss_div
#print axioms Karlin.standardDualityGap_eq_stepDualityGap
#print axioms Karlin.cumScore_succ
#print axioms Karlin.cumScore_succ_self
#print axioms Karlin.cumScore_active_mono_step
#print axioms Karlin.cumScore_active_mono
#print axioms Karlin.cumScore_active_nonneg
#print axioms Karlin.add_one_le_of_strictMono_tStart
#print axioms Karlin.findPhaseAux_spec
#print axioms Karlin.all_integer_time_power_gap_bounds
#print axioms Karlin.power_gap_phase_bounds_of_deg_bounds
#print axioms Karlin.runStart_zero
#print axioms Karlin.runStart_succ
#print axioms Karlin.runStart_mono
#print axioms Karlin.self_le_runStart
#print axioms Karlin.findRunAux_spec
#print axioms Karlin.findRunAux_eq_of_bounds
#print axioms Karlin.runIndexOfStep_spec
#print axioms Karlin.runIndexOfStep_at_offset
#print axioms Karlin.unrollAction_at_offset
#print axioms Karlin.cumScore_add_offset
#print axioms Karlin.cumScore_at_runStart
#print axioms Karlin.unroll_isStrictFPTrajectory
#print axioms Karlin.scoreVec_setupMatrix_some
#print axioms Karlin.scoreVec_setupMatrix_none
#print axioms Karlin.setup_unroll_isStrictFPTrajectory
#print axioms Karlin.rps_unrolled_strict_fp_trajectory
#print axioms Karlin.rps_phase_start_time
#print axioms Karlin.setup_phase_unroll_isStrictFPTrajectory
#print axioms Karlin.stateCoreStart_at_begin
#print axioms Karlin.stateCoreStart_at_end
#print axioms Karlin.seven_core_full_transitions
#print axioms Karlin.seven_guard_transitions
#print axioms Karlin.seven_core_full_r1_valid
#print axioms Karlin.seven_core_full_r2_valid
#print axioms Karlin.seven_core_full_r3_valid
#print axioms Karlin.seven_active_scores_pos
#print axioms Karlin.seven_unrolled_strict_fp_trajectory
