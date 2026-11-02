import Karlin.FaithfulMain
import Karlin.FaithfulSevenFamily
import Karlin.FaithfulResetPlateau
import Karlin.FaithfulGramSection

/-!
Literal intermediate statements from the v15 PDF, specialized to the existing
construction. The selected scales precede all phases and all prefix lengths.
No matrix, clock, word, or threshold is changed by these additions.
-/

namespace Karlin.FaithfulPaperCoverage
open Karlin
open scoped BigOperators Matrix
open Karlin.FaithfulClock Karlin.FaithfulAdmissible
open Karlin.FaithfulController Karlin.FaithfulNextClock.Lift
open Karlin.FaithfulParameters.AdmissibleParameters
open Karlin.FaithfulGain.AdmissibleGain
open Karlin.FaithfulActualWaiting
open Karlin.FaithfulWindow

variable {k : ℕ} {P : Clock k} (A : Admissible P)

theorem previous_counts_pos (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) (i : Res (k := k)) :
    0 < (countRat A T1 T2).mulVec (binomBasis (k + 1) (q - 1)) i := by
  have hh := (phaseCount_outer A T1 T2 q hv hq i).2
  have hc := FaithfulParameters.phaseCounts_cast (countInt A T1 T2) (q - 1) i
  change (FaithfulParameters.phaseCounts (countInt A T1 T2) (q - 1) i : ℚ) =
    (countRat A T1 T2).mulVec (binomBasis (k + 1) (q - 1)) i at hc
  rw [← hc]
  exact_mod_cast (show 0 < FaithfulParameters.phaseCounts (countInt A T1 T2) (q - 1) i by omega)

/-- PDF p54's initial strict comparison, for every nonlast reset (hence every
nonlast late reset). This is the actual constructed controller, not free scores. -/
theorem actual_initial_strict (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) (j : Res (k := k))
    (hj : j.val + 1 < (k + 1) + (k + 1)) :
    pullState A T1 T2 q (Sum.inr j) < P.entry (A.tau * q) P.b +
      FaithfulTables.parentTranslation P A.tau (selectedGain A (lam A) T1) (baseline P) q := by
  have hq1 : 1 ≤ q := (outerOnset_pos A T1 T2).trans hq
  have hh := FaithfulChronologyAlgebra.V_reset_eval_previous
    (J A T1 T2) (countRat A T1 T2) (zeta A T1) q hq1 j
  change pullState A T1 T2 q (Sum.inr j) =
    FaithfulTables.heightValue P A.tau (selectedGain A (lam A) T1) (baseline P) (q - 1) -
      (J A T1 T2)ᵀ.mulVec ((countRat A T1 T2).mulVec (binomBasis (k + 1) (q - 1))) j at hh
  let i : Res (k := k) := ⟨j.val + 1, hj⟩
  have hterm : 0 < J A T1 T2 i j *
      (countRat A T1 T2).mulVec (binomBasis (k + 1) (q - 1)) i :=
    mul_pos (J_positive A T1 T2 hv i j (by simp [i]))
      (previous_counts_pos A T1 T2 q hv hq i)
  have hsum : 0 < (J A T1 T2)ᵀ.mulVec
      ((countRat A T1 T2).mulVec (binomBasis (k + 1) (q - 1))) j := by
    apply lt_of_lt_of_le hterm
    exact Finset.single_le_sum (fun l _ => mul_nonneg (J_nonnegative A T1 T2 hv l j)
      (previous_counts_nonneg A T1 T2 q hv hq l)) (Finset.mem_univ i)
  have hp := FaithfulInheritance.parentTranslation_next P A.tau (q - 1)
    (selectedGain A (lam A) T1) (baseline P)
  rw [Nat.sub_add_cancel hq1] at hp
  linarith

/-- PDF p54's initial equality for the last reset. -/
theorem actual_initial_last_eq (T1 T2 q : ℕ) (_hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) (j : Res (k := k))
    (hj : j.val + 1 = (k + 1) + (k + 1)) :
    pullState A T1 T2 q (Sum.inr j) = P.entry (A.tau * q) P.b +
      FaithfulTables.parentTranslation P A.tau (selectedGain A (lam A) T1) (baseline P) q := by
  have hq1 : 1 ≤ q := (outerOnset_pos A T1 T2).trans hq
  have hh := FaithfulChronologyAlgebra.V_reset_eval_previous
    (J A T1 T2) (countRat A T1 T2) (zeta A T1) q hq1 j
  change pullState A T1 T2 q (Sum.inr j) =
    FaithfulTables.heightValue P A.tau (selectedGain A (lam A) T1) (baseline P) (q - 1) -
      (J A T1 T2)ᵀ.mulVec ((countRat A T1 T2).mulVec (binomBasis (k + 1) (q - 1))) j at hh
  have hsum : (J A T1 T2)ᵀ.mulVec
      ((countRat A T1 T2).mulVec (binomBasis (k + 1) (q - 1))) j = 0 := by
    change (∑ i : Res (k := k), J A T1 T2 i j *
      (countRat A T1 T2).mulVec (binomBasis (k + 1) (q - 1)) i) = 0
    apply Finset.sum_eq_zero
    intro i _
    have hi := i.isLt
    rw [Karlin.FaithfulNextClock.Lift.J_lower A T1 T2 i j (by omega), zero_mul]
  have hp := FaithfulInheritance.parentTranslation_next P A.tau (q - 1)
    (selectedGain A (lam A) T1) (baseline P)
  rw [Nat.sub_add_cancel hq1] at hp
  rw [hsum] at hh
  linarith

/-- PDF p54's strict separation at every nonempty parent prefix, including
the entire parent window immediately before the gateway. -/
theorem actual_late_strict_after_first (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) (j : Res (k := k)) (hj : k + 1 ≤ j.val)
    (r : ℕ) (hr0 : 0 < r)
    (hr : r ≤ (consecutiveWord P.word (A.tau * q) (A.tau * q)).length) :
    wordScore (liftedGameMat (FaithfulGateway.game P) (pullCoupling A T1 T2) (J A T1 T2))
      (pullState A T1 T2 q)
      (FaithfulWaiting.parentStage P ((consecutiveWord P.word (A.tau * q) (A.tau * q)).take r))
      (Sum.inr j) <
    height P.b (wordScore P.A (P.entry (A.tau * q))
      ((consecutiveWord P.word (A.tau * q) (A.tau * q)).take r)) +
      FaithfulTables.parentTranslation P A.tau (selectedGain A (lam A) T1) (baseline P) q := by
  have heps : 0 < FaithfulSynthesis.minimumWeight A / 4 :=
    div_pos (FaithfulSynthesis.minimumWeight_pos A) (by norm_num)
  have hb := outerOnset_bundle A T1 T2 q hq
  have ha : P.Q ≤ A.tau * q :=
    (P.threshold_onset _ heps).trans ((le_max_left _ _).trans hb)
  have hvalid := (consecutiveWord_valid_score P.A P.rank P.word P.entry P.Q
    P.valid P.phase_transition (A.tau * q) ha (A.tau * q)).1
  have hm := height_prefix_ge P.b P.A P.skew (P.entry (A.tau * q)) P.rank _ hvalid r hr
  rw [P.entry_height (A.tau * q) ha] at hm
  have hc : ∀ i : Fin P.m, 0 < pullCoupling A T1 T2 (Sum.inl i) j :=
    fun i => heps.trans (pull_late_sign A T1 T2 hv j hj (Sum.inl i))
  have hex : ∃ i : Fin P.m,
      0 < wordCountVec ((consecutiveWord P.word (A.tau * q) (A.tau * q)).take r) i := by
    have hlen : 0 < (((consecutiveWord P.word (A.tau * q) (A.tau * q)).take r).length) := by
      rw [List.length_take, Nat.min_eq_left hr]
      exact hr0
    cases hlist : (consecutiveWord P.word (A.tau * q) (A.tau * q)).take r with
    | nil => simp [hlist] at hlen
    | cons i rest =>
      refine ⟨i, ?_⟩
      simp [wordCountVec]
      positivity
  obtain ⟨i0, hi0⟩ := hex
  have hw := late_reset_waits_during_bundle (fun i => pullCoupling A T1 T2 (Sum.inl i) j)
    (wordCountVec ((consecutiveWord P.word (A.tau * q) (A.tau * q)).take r))
    (pullState A T1 T2 q (Sum.inr j))
    (P.entry (A.tau * q) P.b +
      FaithfulTables.parentTranslation P A.tau (selectedGain A (lam A) T1) (baseline P) q)
    (height P.b (wordScore P.A (P.entry (A.tau * q))
      ((consecutiveWord P.word (A.tau * q) (A.tau * q)).take r)) +
      FaithfulTables.parentTranslation P A.tau (selectedGain A (lam A) T1) (baseline P) q)
    (reset_initial_le_parent A T1 T2 q hv hq j) (by linarith)
    (fun i => (hc i).le) (fun i => Nat.cast_nonneg _)
  rw [FaithfulWaiting.reset_forward]
  exact hw.2 i0 (hc i0) hi0

/-- Fully chosen controller: scales are fixed before all phases and prefixes;
the caller supplies no ValidParameters premise. -/
theorem chosen_strictness :
    let T1 := firstScale A
    let T2 := secondScale A T1
    ∀ q : ℕ, outerOnset A T1 T2 ≤ q →
      let h := FaithfulTables.parentTranslation P A.tau (selectedGain A (lam A) T1) (baseline P) q
      let W := consecutiveWord P.word (A.tau * q) (A.tau * q)
      (∀ j : Res (k := k), j.val + 1 < (k + 1) + (k + 1) →
        pullState A T1 T2 q (Sum.inr j) < P.entry (A.tau * q) P.b + h) ∧
      (∀ j : Res (k := k), j.val + 1 = (k + 1) + (k + 1) →
        pullState A T1 T2 q (Sum.inr j) = P.entry (A.tau * q) P.b + h) ∧
      (∀ j : Res (k := k), k + 1 ≤ j.val → ∀ r : ℕ, 0 < r → r ≤ W.length →
        wordScore (liftedGameMat (FaithfulGateway.game P) (pullCoupling A T1 T2) (J A T1 T2))
          (pullState A T1 T2 q) (FaithfulWaiting.parentStage P (W.take r)) (Sum.inr j) <
        height P.b (wordScore P.A (P.entry (A.tau * q)) (W.take r)) + h) := by
  dsimp only
  intro q hq
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    exact actual_initial_strict A _ _ q (chosen_valid A) hq j hj
  · intro j hj
    exact actual_initial_last_eq A _ _ q (chosen_valid A) hq j hj
  · intro j hj r hr0 hr
    exact actual_late_strict_after_first A _ _ q (chosen_valid A) hq j hj r hr0 hr

end Karlin.FaithfulPaperCoverage

namespace Karlin.FaithfulPaperCoverage

/-- The smaller family inherits the same unit increment of the suffix
constant from its order-three seed. -/
theorem seven_iterate_remainder (n : ℕ) :
    (FaithfulSevenFamily.iterate n).clock.Arem = (n : ℚ) + 1 := by
  induction n with
  | zero =>
    change (1 : ℚ) = (0 : ℚ) + 1
    norm_num
  | succ n ih =>
    change (FaithfulLift.nextClock (FaithfulSevenFamily.iterate n).data).Arem = _
    rw [FaithfulLift.nextClock_remainder, ih]
    push_cast
    ring

theorem seven_family_remainder (k : ℕ) (hk : 3 ≤ k) :
    (FaithfulSevenFamily.clock k hk).Arem = (k : ℚ) - 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  change (FaithfulSevenFamily.iterate n).clock.Arem = _
  rw [seven_iterate_remainder]
  push_cast
  ring

end Karlin.FaithfulPaperCoverage


namespace Karlin.FaithfulPaperCoverage
open Karlin

theorem iterate_remainder (n : ℕ) :
    (FaithfulFamily.iterate FaithfulMain.step n).clock.Arem = (n : ℚ) + 1 := by
  induction n with
  | zero =>
    change (1 : ℚ) = (0 : ℚ) + 1
    norm_num
  | succ n ih =>
    change (FaithfulLift.nextClock (FaithfulFamily.iterate FaithfulMain.step n).data).Arem = _
    rw [FaithfulLift.nextClock_remainder, ih]
    push_cast
    ring

theorem family_remainder (k : ℕ) (hk : 2 ≤ k) :
    (FaithfulMain.clock k hk).Arem = (k : ℚ) - 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  change (FaithfulFamily.iterate FaithfulMain.step n).clock.Arem = _
  rw [iterate_remainder]
  push_cast
  ring

end Karlin.FaithfulPaperCoverage


namespace Karlin.FaithfulPaperCoverage
open Karlin
open Karlin.FaithfulClock Karlin.FaithfulAdmissible
open Karlin.FaithfulController Karlin.FaithfulNextClock
open Karlin.FaithfulNextClock.Lift Karlin.FaithfulNextClockAssembly

/-- The unrotated chronology, with the literal
chosen matrices, actual prefix validity, and exact endpoint.  -/
theorem raw_chronology {k : ℕ} {P : Clock k} (A : Admissible P)
    (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) :
    IsValidPriorityWord (game A T1 T2) (entryScore A T1 T2 q)
        (Karlin.FaithfulNextClockAssembly.rank (P := P))
        ((old A q).map Sum.inl ++ reset A T1 T2 q) ∧
      wordScore (game A T1 T2) (entryScore A T1 T2 q)
        ((old A q).map Sum.inl ++ reset A T1 T2 q) =
          entryScore A T1 T2 (q + 1) := by
  constructor
  · apply (isValidPriorityWord_append _ _ _ _ _).2
    constructor
    · exact Karlin.FaithfulActualWaiting.actual_oldWord_valid A T1 T2 q hv hq
    · rw [post_old A T1 T2 q hv hq]
      exact reset_valid A T1 T2 q hv hq
  · exact raw_end A T1 T2 q hv hq

/-- Parameter choices precede every phase and every reset prefix. This is the
paper's full chronology/plateau package specialized to the selected controller. -/
theorem selected_chronology {k : ℕ} {P : Clock k} (A : Admissible P) :
    let T1 := firstScale A
    let T2 := secondScale A T1
    ∀ q : ℕ, outerOnset A T1 T2 ≤ q →
      (IsValidPriorityWord (game A T1 T2) (entryScore A T1 T2 q)
        (Karlin.FaithfulNextClockAssembly.rank (P := P))
        ((old A q).map Sum.inl ++ reset A T1 T2 q)) ∧
      (wordScore (game A T1 T2) (entryScore A T1 T2 q)
        ((old A q).map Sum.inl ++ reset A T1 T2 q) = entryScore A T1 T2 (q + 1)) ∧
      ∀ r : ℕ, r ≤ (reset A T1 T2 q).length →
        Karlin.FaithfulInheritance.scoreHeight base
          (wordScore (game A T1 T2) (entryScore A T1 T2 q)
            ((old A q).map Sum.inl ++ (reset A T1 T2 q).take r)) =
          dotProduct (zeta A T1) (binomBasis (k + 1) q) := by
  dsimp only
  intro q hq
  have hv := chosen_valid A
  have hc := raw_chronology A _ _ q hv hq
  refine ⟨hc.1, hc.2, ?_⟩
  intro r hr
  exact Karlin.FaithfulResetPlateau.raw_reset_prefix_height A _ _ q hv hq r hr



end Karlin.FaithfulPaperCoverage


namespace Karlin.FaithfulPaperCoverage
open scoped BigOperators Matrix
open Karlin

-- The paper's full-column-rank formulation follows for arbitrary rational matrices,
-- not only the actual clock blocks. No supplied inverse or compatibility witness.
theorem full_rank_interpolation {m n w : Type*}
    [Fintype m] [Fintype n] [Fintype w] [DecidableEq w]
    (X : Matrix m w ℚ) (M : Matrix n w ℚ)
    (D : Matrix m w ℚ) (Q : Matrix n w ℚ)
    (hX : Function.Injective (fun x => X.mulVec x))
    (hM : Function.Injective (fun x => M.mulVec x)) :
    (∃ P : Matrix m n ℚ, P * M = D ∧ P.transpose * X = Q) ↔
      D.transpose * X = M.transpose * Q := by
  exact interpolate_iff X (FaithfulGramSection.gramLX X) M
    (FaithfulGramSection.gramLX M).transpose D Q 0
    (FaithfulGramSection.gramLX_spec X hX)
    (FaithfulGramSection.gramLX_transpose_spec M hM)

-- Expanded simultaneous comparisons use the same completed-round range on both sides.
theorem main_literal_simultaneous (k : ℕ) (hk : 2 ≤ k) :
    let M := FaithfulMain.matrix k hk
    let a := FaithfulMain.trajectory k hk
    ∀ t : ℕ, 1 ≤ t →
      (∀ i, i ≠ a t → (∑ s ∈ Finset.range t, M i (a s)) <
        ∑ s ∈ Finset.range t, M (a t) (a s)) ∧
      (∀ j, j ≠ a t → (∑ s ∈ Finset.range t, M (a s) (a t)) <
        ∑ s ∈ Finset.range t, M (a s) j) :=
  FaithfulMain.strict_simultaneous k hk

theorem seven_literal_simultaneous (k : ℕ) (hk : 3 ≤ k) :
    let M := FaithfulSevenFamily.matrix k hk
    let a := FaithfulSevenFamily.trajectory k hk
    ∀ t : ℕ, 1 ≤ t →
      (∀ i, i ≠ a t → (∑ s ∈ Finset.range t, M i (a s)) <
        ∑ s ∈ Finset.range t, M (a t) (a s)) ∧
      (∀ j, j ≠ a t → (∑ s ∈ Finset.range t, M (a s) (a t)) <
        ∑ s ∈ Finset.range t, M (a s) j) :=
  FaithfulSevenFamily.strict_simultaneous k hk


end Karlin.FaithfulPaperCoverage
