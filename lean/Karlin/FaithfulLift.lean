import Karlin.FaithfulNextClock
import Karlin.FaithfulNextAdmissible
import Karlin.FaithfulClockPackage
import Karlin.FaithfulNextClockAssembly

/-! Final identification of the literal next tables and inherited admissibility. -/
namespace Karlin.FaithfulLift
open scoped BigOperators Matrix
open FaithfulClock FaithfulAdmissible FaithfulTables FaithfulNextTables
open FaithfulReindex FaithfulParameters.AdmissibleParameters
open FaithfulGain.AdmissibleGain FaithfulResetEquations

variable {k : ℕ} {P : Clock k} (A : Admissible P)

def normalizeEquiv : (OldAct P ⊕ (Fin (k + 1) ⊕ Fin (k + 1))) ≃
    FaithfulNextClock.Lift.Act (P := P) :=
  Equiv.sumCongr FaithfulNextClock.Lift.oldEquiv FaithfulNextClock.Lift.resetEquiv

noncomputable def originalScores (T1 T2 : ℕ) :=
  nextScores
    (S_mid P A.tau (selectedGain A (lam A) T1) (baseline P)
      (FaithfulSynthesis.endpointMargin A (lam A) T1))
    (FaithfulTables.zeta (P.R P.b) A.tau (selectedGain A (lam A) T1) (baseline P))
    (resetInteractions k T1 T2 (lam A) A.referenceHeight A.correction
      (momentTable A (lam A) T1) (paperLower k))
    (resetCounts k T1 T2 (lam A) A.referenceHeight A.correction)

noncomputable def originalCounts (T1 T2 : ℕ) :=
  nextCounts (X P A.tau) (resetCounts k T1 T2 (lam A) A.referenceHeight A.correction)

theorem nextScores_reindex {o r o' r' : Type*}
    [Fintype r] [Fintype r'] {w : ℕ} (e : o ≃ o') (f : r ≃ r')
    (Smid : Matrix o (Fin w) ℚ) (z : Fin w → ℚ)
    (J : Matrix r r ℚ) (M : Matrix r (Fin w) ℚ) :
    rows (Equiv.sumCongr e f) (nextScores Smid z J M) =
      nextScores (rows e Smid) z (matrix f f J) (rows f M) := by
  rw [nextScores, nextScores, rows_fromRows, matrix_mul_rows]
  congr 1

theorem nextCounts_reindex {o r o' r' : Type*} {w : ℕ} (e : o ≃ o') (f : r ≃ r')
    (X : Matrix o (Fin w) ℚ) (M : Matrix r (Fin w) ℚ) :
    rows (Equiv.sumCongr e f) (nextCounts X M) = nextCounts (rows e X) (rows f M) := by
  rw [nextCounts, nextCounts, rows_fromRows, rows_mul]

theorem resetInteractions_eq (T1 T2 : ℕ) :
    resetInteractions k T1 T2 (lam A) A.referenceHeight A.correction
      (momentTable A (lam A) T1) (paperLower k) =
    resetJ k T1 T2 (lam A) A.referenceHeight A.correction (momentTable A (lam A) T1) := rfl

theorem normalized_count_table (T1 T2 : ℕ) :
    FaithfulNextClock.Lift.countTable A T1 T2 =
      rows (normalizeEquiv (P := P)) (originalCounts A T1 T2) := by
  rw [originalCounts, normalizeEquiv, nextCounts_reindex]
  unfold FaithfulNextClock.Lift.countTable
  rw [FaithfulNextClock.Lift.countRat_eq]
  rfl

theorem normalized_score_table (T1 T2 : ℕ) :
    FaithfulNextClock.Lift.scoreTable A T1 T2 =
      rows (normalizeEquiv (P := P)) (originalScores A T1 T2) := by
  rw [originalScores, normalizeEquiv, nextScores_reindex, resetInteractions_eq]
  unfold FaithfulNextClock.Lift.scoreTable
  rw [FaithfulNextClock.Lift.countRat_eq]
  have hold : FaithfulNextClock.Lift.oldS A T1 +
      FaithfulNextClock.Lift.G (P := P) * FaithfulNextClock.Lift.oldX A =
      rows FaithfulNextClock.Lift.oldEquiv
        (S_mid P A.tau (selectedGain A (lam A) T1) (baseline P)
          (FaithfulSynthesis.endpointMargin A (lam A) T1)) := by
    change rows FaithfulNextClock.Lift.oldEquiv _ +
      matrix FaithfulNextClock.Lift.oldEquiv FaithfulNextClock.Lift.oldEquiv _ *
        rows FaithfulNextClock.Lift.oldEquiv _ = _
    rw [matrix_mul_rows]
    rfl
  rw [hold]
  rfl

/-- Original parent/gateway/reset labels to the conventional final Fin labels. -/
def actionEquiv : (OldAct P ⊕ (Fin (k + 1) ⊕ Fin (k + 1))) ≃
    Fin ((P.m + 1) + ((k + 1) + (k + 1))) :=
  (normalizeEquiv (P := P)).trans finSumFinEquiv

/-- The actual lift of an arbitrary admissible parent, at the prescribed
parameter choices. No validity or existence premise is supplied by the caller. -/
noncomputable def nextClock : Clock (k + 1) :=
  FaithfulNextClockAssembly.nextClock A (FaithfulController.firstScale A)
    (FaithfulController.secondScale A (FaithfulController.firstScale A))
    (FaithfulController.chosen_valid A)

theorem nextClock_m : (nextClock A).m = P.m + 2 * k + 3 := by
  change (P.m + 1) + ((k + 1) + (k + 1)) = _
  omega

/-- Exact table identification required by the admissibility transport. -/
noncomputable def nextTableMatch :
    FaithfulNextAdmissible.TableMatch P (nextClock A) A.tau
      (selectedGain A (lam A) (FaithfulController.firstScale A)) A.cref (baseline P)
      (FaithfulSynthesis.endpointMargin A (lam A) (FaithfulController.firstScale A))
      (FaithfulController.firstScale A) (lam A) A.correction
      (momentTable A (lam A) (FaithfulController.firstScale A)) (paperLower k) where
  equiv := actionEquiv (P := P)
  score := by
    change rows finSumFinEquiv (FaithfulNextClock.Lift.scoreTable A _ _) = _
    rw [normalized_score_table]
    rfl
  count := by
    change rows finSumFinEquiv
      (fun i j => (FaithfulNextClock.Lift.nextCountInt A _ _ i j : ℚ)) = _
    rw [FaithfulNextClock.Lift.nextCountInt_cast, normalized_count_table]
    rfl
  entry := by
    rfl

/-- Full next-order admissibility, including the fixed next correction and
the explicit positive weights at the prescribed least second scale. -/
noncomputable def nextAdmissible : Admissible (nextClock A) := by
  have hv := FaithfulController.chosen_valid A
  apply FaithfulNextAdmissible.admissible P (nextClock A) A.tau A.tau_pos
    (selectedGain A (lam A) (FaithfulController.firstScale A)) A.cref (baseline P)
    (FaithfulSynthesis.endpointMargin A (lam A) (FaithfulController.firstScale A))
    (FaithfulController.firstScale A) (lam A)
    (by exact_mod_cast hv.first_pos) (by exact_mod_cast lam_pos A)
    A.correction (momentTable A (lam A) (FaithfulController.firstScale A)) (paperLower k)
  · intro j
    simp [paperLower, L_strict]
  · have he := (hv.reset_leading (0 : Fin (k + 1))).1
    simpa only [Faithful.early_leading, Fin.val_zero, ite_true] using he
  · have hd := hv.inverse_denominator
    exact ne_of_gt (lt_trans (by norm_num : (0 : ℚ) < 1 / 2) hd)
  · exact nextTableMatch A

/-- The parent actions occur as a literal principal block of the new game. -/
def parentAction : Fin P.m ↪ Fin (nextClock A).m where
  toFun i := actionEquiv (P := P) (Sum.inl (Sum.inl i))
  inj' := by
    intro i j h
    exact Sum.inl.inj (Sum.inl.inj ((actionEquiv (P := P)).injective h))

theorem parent_payoff (i j : Fin P.m) :
    (nextClock A).A (parentAction A i) (parentAction A j) = P.A i j := by
  change FaithfulReindex.matrix finSumFinEquiv finSumFinEquiv
    (FaithfulNextClock.Lift.game A _ _)
    (finSumFinEquiv (normalizeEquiv (P := P) (Sum.inl (Sum.inl i))))
    (finSumFinEquiv (normalizeEquiv (P := P) (Sum.inl (Sum.inl j)))) = _
  rw [FaithfulReindex.matrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  change (FaithfulNextClock.Lift.G (P := P))
    (FaithfulNextClock.Lift.oldEquiv (Sum.inl i))
    (FaithfulNextClock.Lift.oldEquiv (Sum.inl j)) = _
  simp only [FaithfulNextClock.Lift.G, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rfl

theorem principal_parent : (nextClock A).A.submatrix (parentAction A) (parentAction A) = P.A := by
  ext i j
  exact parent_payoff A i j

@[simp] theorem nextClock_marker : (nextClock A).delta0 = 1 := rfl
@[simp] theorem nextClock_remainder : (nextClock A).Arem = P.Arem + 1 := rfl
@[simp] theorem nextClock_word (q : ℕ) :
    (nextClock A).word q =
      (FaithfulNextClock.Lift.word A (FaithfulController.firstScale A)
        (FaithfulController.secondScale A (FaithfulController.firstScale A)) q).map finSumFinEquiv := rfl

#print axioms nextClock
#print axioms nextAdmissible
#print axioms principal_parent

end Karlin.FaithfulLift
