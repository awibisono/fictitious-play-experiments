import Karlin.FaithfulNextClock
import Karlin.FaithfulChronologyAlgebra
import Karlin.FaithfulStageBounds
import Karlin.FaithfulActualWaiting
import Karlin.FaithfulActualSuffix
import Karlin.FaithfulClockPackage

/-! Assembly of the actual next clock from earned parameters and same-word
chronology. No realized next clock is an input. -/
namespace Karlin.FaithfulNextClockAssembly
open scoped BigOperators Matrix
open FaithfulClock FaithfulAdmissible FaithfulParameters.AdmissibleParameters
open FaithfulController FaithfulNextClock FaithfulNextClock.Lift

variable {k : ℕ} {P : Clock k} (A : Admissible P)

noncomputable def entryScore (T1 T2 q : ℕ) : Lift.Act (P := P) → ℚ :=
  (entryTable A T1 T2).mulVec (binomBasis (k+1) q)

noncomputable def rotatedScore (T1 T2 q : ℕ) : Lift.Act (P := P) → ℚ :=
  (scoreTable A T1 T2).mulVec (binomBasis (k+1) q)

def reset (T1 T2 q : ℕ) : List (Lift.Act (P := P)) :=
  FaithfulChronology.resetWord (count A T1 T2 q)

def rank : Lift.Act (P := P) → Fin (P.m + 2 * (k+1) + 1) :=
  paperPriorityRank P.m k P.rank

theorem parent_onset (T1 T2 q : ℕ) (hq : outerOnset A T1 T2 ≤ q) : P.Q ≤ A.tau * q := by
  have heps : 0 < FaithfulSynthesis.minimumWeight A / 4 := div_pos (FaithfulSynthesis.minimumWeight_pos A) (by norm_num)
  exact (P.threshold_onset _ heps).trans
    ((le_max_left _ _).trans (outerOnset_bundle A T1 T2 q hq))

theorem reset_counts (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) :
    wordCountVec (reset A T1 T2 q) = Sum.elim (fun _ => 0)
      ((countRat A T1 T2).mulVec (binomBasis (k+1) q)) := by
  rw [reset, FaithfulChronology.resetWord_count]
  congr 1
  funext i
  exact count_cast_outer A T1 T2 q hv hq i

theorem post_old (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) :
    wordScore (game A T1 T2) (entryScore A T1 T2 q) ((old A q).map Sum.inl) =
      rotatedScore A T1 T2 q :=
  FaithfulChronologyAlgebra.post_old (G (P := P)) (coupling A T1 T2) (J A T1 T2)
    (oldS A T1) (oldX A) (countRat A T1 T2) (B_mat (k+1)) (zeta A T1)
    (binomBasis (k+1) q) (old A q) (old_count A q (parent_onset A T1 T2 q hq))
    (interpolation A T1 T2 hv).2

theorem post_reset (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) :
    wordScore (game A T1 T2) (rotatedScore A T1 T2 q) (reset A T1 T2 q) =
      entryScore A T1 T2 (q+1) :=
  FaithfulChronologyAlgebra.post_reset (G (P := P)) (coupling A T1 T2) (J A T1 T2)
    (oldS A T1) (oldX A) (countRat A T1 T2) (zeta A T1) q (old A q) (reset A T1 T2 q)
    (old_count A q (parent_onset A T1 T2 q hq)) (reset_counts A T1 T2 q hv hq)
    (interpolation A T1 T2 hv).1 (interpolation A T1 T2 hv).2

theorem raw_end (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) :
    wordScore (game A T1 T2) (entryScore A T1 T2 q)
      ((old A q).map Sum.inl ++ reset A T1 T2 q) = entryScore A T1 T2 (q+1) := by
  rw [wordScore_append, post_old A T1 T2 q hv hq, post_reset A T1 T2 q hv hq]

theorem rotated_end (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) :
    wordScore (game A T1 T2) (rotatedScore A T1 T2 q) (word A T1 T2 q) =
      rotatedScore A T1 T2 (q+1) := by
  change wordScore _ _ (reset A T1 T2 q ++ (old A (q+1)).map Sum.inl) = _
  rw [wordScore_append, post_reset A T1 T2 q hv hq, post_old A T1 T2 (q+1) hv (by omega)]

theorem early_coupling (T1 T2 : ℕ) (hv : ValidParameters A T1 T2)
    (i : Fin (P.m+1)) (j : Lift.Res (k := k)) (hj : j.val < k+1) :
    coupling A T1 T2 i j < 0 := by
  obtain ⟨x, rfl⟩ := resetEquiv.surjective j
  cases x with
  | inl x =>
    have h := (hv.coupling_signs (oldEquiv.symm i) x).1
    have hm := FaithfulSynthesis.minimumWeight_pos A
    change FaithfulSynthesis.coupling A (lam A) T1 T2 _ (oldEquiv.symm i)
      (resetEquiv.symm (resetEquiv (Sum.inl x))) < 0
    rw [Equiv.symm_apply_apply]
    linarith
  | inr x =>
    simp only [resetEquiv, finSumFinEquiv_apply_right, Fin.val_natAdd] at hj
    omega

theorem late_coupling (T1 T2 : ℕ) (hv : ValidParameters A T1 T2)
    (i : Fin (P.m+1)) (j : Lift.Res (k := k)) (hj : k+1 ≤ j.val) :
    0 < coupling A T1 T2 i j := by
  obtain ⟨x, rfl⟩ := resetEquiv.surjective j
  cases x with
  | inl x =>
    simp only [resetEquiv, finSumFinEquiv_apply_left, Fin.val_castAdd] at hj
    have := x.isLt
    omega
  | inr x =>
    have h := (hv.coupling_signs (oldEquiv.symm i) x).2
    have hm := FaithfulSynthesis.minimumWeight_pos A
    change 0 < FaithfulSynthesis.coupling A (lam A) T1 T2 _ (oldEquiv.symm i)
      (resetEquiv.symm (resetEquiv (Sum.inr x)))
    rw [Equiv.symm_apply_apply]
    linarith

theorem reset_start_scores (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) (i : Lift.Res (k := k)) :
    rotatedScore A T1 T2 q (Sum.inr i) = resetEntryScore (J A T1 T2)
      (fun j => (count A T1 T2 q j : ℚ)) (dotProduct (zeta A T1) (binomBasis (k+1) q)) i := by
  change (outerProd (fun _ => 1) (zeta A T1) - J A T1 T2 * countRat A T1 T2).mulVec _ i = _
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, outerProd, Matrix.of_apply, one_mul]
  unfold resetEntryScore
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [count_cast_outer A T1 T2 q hv hq j]
  rfl

theorem old_start_lt (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) (i : Fin (P.m+1)) :
    rotatedScore A T1 T2 q (Sum.inl i) < dotProduct (zeta A T1) (binomBasis (k+1) q) := by
  obtain ⟨j, rfl⟩ := oldEquiv.surjective i
  change dotProduct (scoreTable A T1 T2 (Sum.inl (oldEquiv j))) _ < _
  rw [score_old_row]
  exact FaithfulStageBounds.actual_old_post_lt_height A T1 T2 hv q hq j

theorem old_end_le (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) (i : Fin (P.m+1)) :
    entryScore A T1 T2 (q+1) (Sum.inl i) ≤ dotProduct (zeta A T1) (binomBasis (k+1) q) :=
  FaithfulStageBounds.actual_old_endpoint_le A T1 T2 hv q hq (oldEquiv.symm i)

theorem old_end_update (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) (i : Fin (P.m+1)) :
    entryScore A T1 T2 (q+1) (Sum.inl i) = rotatedScore A T1 T2 q (Sum.inl i) +
      ∑ j, coupling A T1 T2 i j * (count A T1 T2 q j : ℚ) := by
  have h := congrFun (post_reset A T1 T2 q hv hq) (Sum.inl i)
  rw [wordScore, scoreVec, reset, FaithfulChronology.resetWord_count] at h
  simpa [game, liftedGameMat, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using h.symm

/-- Entire literal reset chronology from the actual earned parameter signs and
exact endpoint states, with no per-prefix validity or waiting premise. -/
theorem reset_valid (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) :
    IsValidPriorityWord (game A T1 T2) (rotatedScore A T1 T2 q) (rank (P := P))
      (reset A T1 T2 q) := by
  apply FaithfulChronology.resetWord_valid_of_signs (G (P := P)) (coupling A T1 T2) (J A T1 T2)
    P.rank (rotatedScore A T1 T2 q) (count A T1 T2 q)
    (dotProduct (zeta A T1) (binomBasis (k+1) q))
    (fun i => entryScore A T1 T2 (q+1) (Sum.inl i))
  · exact count_ge_two_outer A T1 T2 q hv hq
  · exact Lift.J_lower A T1 T2
  · exact J_positive A T1 T2 hv
  · exact reset_start_scores A T1 T2 q hv hq
  · exact old_start_lt A T1 T2 q hv hq
  · exact old_end_update A T1 T2 q hv hq
  · exact old_end_le A T1 T2 q hv hq
  · intro i j hj
    exact (early_coupling A T1 T2 hv i j hj).le
  · exact late_coupling A T1 T2 hv


/-- The actual rotated phase is the same reset word followed by the next old
word; each complete stage is verified in the complete game. -/
theorem word_valid (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) :
    IsValidPriorityWord (game A T1 T2) (rotatedScore A T1 T2 q) (rank (P := P))
      (word A T1 T2 q) := by
  change IsValidPriorityWord _ _ _ (reset A T1 T2 q ++ (old A (q+1)).map Sum.inl)
  apply (isValidPriorityWord_append _ _ _ _ _).2
  refine ⟨reset_valid A T1 T2 q hv hq, ?_⟩
  rw [post_reset A T1 T2 q hv hq]
  exact FaithfulActualWaiting.actual_oldWord_valid A T1 T2 (q+1) hv (by omega)

theorem begins_twice (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) :
    ∃ tail, word A T1 T2 q = base :: base :: tail :=
  rotatedWord_begins_twice (by omega) (count A T1 T2) (old A) q
    (count_ge_two_outer A T1 T2 q hv hq 0)

theorem counts (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) :
    wordCountVec (word A T1 T2 q) = (Lift.countTable A T1 T2).mulVec (binomBasis (k+1) q) :=
  rotatedWord_counts (count A T1 T2) (old A) (oldX A) (countRat A T1 T2) q
    (old_count A (q+1) (parent_onset A T1 T2 (q+1) (by omega)))
    (count_cast_outer A T1 T2 q hv hq)

theorem entry_height (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) :
    FaithfulInheritance.scoreHeight base (rotatedScore A T1 T2 q) =
      FaithfulTables.heightValue P A.tau (FaithfulGain.AdmissibleGain.selectedGain A (lam A) T1)
        (baseline P) q := by
  have hb : rotatedScore A T1 T2 q base =
      FaithfulTables.heightValue P A.tau (FaithfulGain.AdmissibleGain.selectedGain A (lam A) T1)
        (baseline P) q := by
    change dotProduct (scoreTable A T1 T2 (Sum.inr 0)) _ = _
    rw [score_reset_zero]
    rfl
  rw [← hb]
  apply FaithfulInheritance.scoreHeight_eq
  intro i
  obtain ⟨tail, ht⟩ := begins_twice A T1 T2 q hv hq
  have hl : 0 < (word A T1 T2 q).length := by simp [ht]
  have hi := ((word_valid A T1 T2 q hv hq) 0 hl i).1
  simpa only [List.take_zero, wordScore_nil, ht, List.getElem_cons_zero] using hi

theorem final_height (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) :
    FaithfulInheritance.scoreHeight base
      (wordScore (game A T1 T2) (rotatedScore A T1 T2 q) (word A T1 T2 q)) =
      FaithfulTables.heightValue P A.tau (FaithfulGain.AdmissibleGain.selectedGain A (lam A) T1)
        (baseline P) (q+1) := by
  rw [rotated_end A T1 T2 q hv hq]
  exact entry_height A T1 T2 (q+1) hv (by omega)


def threshold (T1 T2 : ℕ) (eps : ℚ) : ℕ :=
  FaithfulInheritance.inheritedThreshold P A.tau (outerOnset A T1 T2)
    (FaithfulGain.AdmissibleGain.selectedGain A (lam A) T1) (baseline P) eps

theorem threshold_onset (T1 T2 : ℕ) (eps : ℚ) :
    outerOnset A T1 T2 ≤ threshold A T1 T2 eps := le_max_left _ _

/-- The complete inherited suffix estimate, with all structural premises
proved on the same literal trajectory and fixed additive constant Arem+1. -/
theorem suffix (T1 T2 : ℕ) (hv : ValidParameters A T1 T2) (eps : ℚ) (heps : 0 < eps)
    (q : ℕ) (hq : threshold A T1 T2 eps ≤ q) (r : ℕ) (hr : r ≤ (word A T1 T2 q).length) :
    FaithfulInheritance.scoreHeight base (rotatedScore A T1 T2 (q+1)) -
      FaithfulInheritance.scoreHeight base
        (wordScore (game A T1 T2) (rotatedScore A T1 T2 q) ((word A T1 T2 q).take r)) ≤
      eps * ((word A T1 T2 q).length - r : ℕ) + (P.Arem + 1) := by
  have hQ : outerOnset A T1 T2 ≤ q := (threshold_onset A T1 T2 eps).trans hq
  rw [entry_height A T1 T2 (q+1) hv (by omega)]
  exact FaithfulActualSuffix.actual_suffix A T1 T2 q hv eps heps hq
    (reset_valid A T1 T2 q hv hQ) (post_reset A T1 T2 q hv hQ)
    (final_height A T1 T2 q hv hQ) r hr

theorem word_valid_equiv_rank (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) :
    IsValidPriorityWord (game A T1 T2) (rotatedScore A T1 T2 q)
      (priorityEquiv P.m ((k+1)+(k+1)) P.rank) (word A T1 T2 q) := by
  intro r hr i
  obtain ⟨hi, ht⟩ := word_valid A T1 T2 q hv hq r hr i
  refine ⟨hi, ?_⟩
  intro hne heq
  simpa only [priorityEquiv_paper_val] using ht hne heq

/-- All literal clock fields are derived from the actual admissible parent
and the actual selected scales. The suffix threshold is the only eps-dependent data. -/
noncomputable def nextRaw (T1 T2 : ℕ) (hv : ValidParameters A T1 T2) :
    FaithfulClockPackage.Raw (k+1) ((P.m+1)+((k+1)+(k+1))) (Lift.Act (P := P)) where
  order_ge_two := by have := P.order_ge_two; omega
  A := game A T1 T2
  skew := game_skew A T1 T2
  rank := priorityEquiv P.m ((k+1)+(k+1)) P.rank
  R := scoreTable A T1 T2
  C := nextCountInt A T1 T2
  b := base
  v := counter
  Q := outerOnset A T1 T2
  onset_pos := outerOnset_pos A T1 T2
  word := word A T1 T2
  delta0 := 1
  marker_pos := by norm_num
  Arem := P.Arem + 1
  remainder_nonneg := by have := P.remainder_nonneg; linarith
  threshold := threshold A T1 T2
  threshold_onset := fun eps _ => threshold_onset A T1 T2 eps
  clock_eq := by
    unfold FaithfulClockPackage.rationalCounts
    rw [nextCountInt_cast]
    exact Lift.clock_equation A T1 T2 hv
  full_column_rank := by
    change Function.Injective (fun x => Matrix.mulVec (fun i j => (nextCountInt A T1 T2 i j : ℚ)) x)
    rw [nextCountInt_cast]
    exact count_full_rank A T1 T2 hv
  leading_height := by
    simpa only [Nat.add_sub_cancel] using score_leading_positive A T1 T2
  valid := fun q => word_valid_equiv_rank A T1 T2 q hv
  counts := by
    intro q hq
    change wordCountVec (word A T1 T2 q) =
      Matrix.mulVec (fun i j => (nextCountInt A T1 T2 i j : ℚ)) (binomBasis (k+1) q)
    rw [nextCountInt_cast]
    exact counts A T1 T2 q hv hq
  begins_twice := fun q => begins_twice A T1 T2 q hv
  counter_entry := counter_base
  counter_table := by
    change Matrix.vecMul counter (fun i j => (nextCountInt A T1 T2 i j : ℚ)) = _
    rw [nextCountInt_cast]
    exact counter_table A T1 T2
  marker := by
    intro q _ r hr
    exact word_marker A T1 T2 q r _ hr
  support_safe := fun q _ => Lift.support_safe A T1 T2 q hv
  suffix := suffix A T1 T2 hv

/-- The actual one-step clock, with only the conventional action labels changed. -/
noncomputable def nextClock (T1 T2 : ℕ) (hv : ValidParameters A T1 T2) : Clock (k+1) :=
  (nextRaw A T1 T2 hv).toClock finSumFinEquiv

@[simp] theorem nextClock_m (T1 T2 : ℕ) (hv : ValidParameters A T1 T2) :
    (nextClock A T1 T2 hv).m = (P.m+1)+((k+1)+(k+1)) := rfl

@[simp] theorem nextClock_R (T1 T2 : ℕ) (hv : ValidParameters A T1 T2) :
    (nextClock A T1 T2 hv).R = FaithfulReindex.rows finSumFinEquiv (scoreTable A T1 T2) := rfl

@[simp] theorem nextClock_C (T1 T2 : ℕ) (hv : ValidParameters A T1 T2) :
    (nextClock A T1 T2 hv).C = FaithfulReindex.rows finSumFinEquiv (nextCountInt A T1 T2) := rfl

@[simp] theorem nextClock_b (T1 T2 : ℕ) (hv : ValidParameters A T1 T2) :
    (nextClock A T1 T2 hv).b = finSumFinEquiv (base (P := P)) := rfl

@[simp] theorem nextClock_word (T1 T2 : ℕ) (hv : ValidParameters A T1 T2) (q : ℕ) :
    (nextClock A T1 T2 hv).word q = (word A T1 T2 q).map finSumFinEquiv := rfl

@[simp] theorem nextClock_Arem (T1 T2 : ℕ) (hv : ValidParameters A T1 T2) :
    (nextClock A T1 T2 hv).Arem = P.Arem + 1 := rfl

#print axioms nextClock
#print axioms reset_valid
#print axioms word_valid
#print axioms suffix


end Karlin.FaithfulNextClockAssembly
