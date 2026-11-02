import Karlin.FaithfulBounds
import Karlin.FaithfulGain
import Karlin.FaithfulGramSection

/-! Exact realization and interpolation equations for the literal v15 reset.
The fixed rational left inverse is the manuscript's prescribed Gram formula.
-/

namespace Karlin.FaithfulResetEquations
open scoped BigOperators Matrix
open Faithful

set_option maxHeartbeats 1200000

/-- The paper's strict lower-triangular all-ones matrix. -/
def paperLower (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ := L_strict (k + 1)

/-- The literal v15 choice LX = X (Xᵀ X)⁻¹, fixed from the parent table. -/
noncomputable def canonicalLX {m w : Type*} [Fintype m] [Fintype w]
    [DecidableEq m] [DecidableEq w] (X : Matrix m w ℚ) : Matrix m w ℚ :=
  X * (Xᵀ * X)⁻¹

theorem canonicalLX_spec {m w : Type*} [Fintype m] [Fintype w]
    [DecidableEq m] [DecidableEq w] (X : Matrix m w ℚ)
    (hX : Function.Injective (fun x => X.mulVec x)) : Xᵀ * canonicalLX X = 1 :=
  FaithfulGramSection.gramLX_spec X hX

theorem canonicalLX_eq_gram {m w : Type*} [Fintype m] [Fintype w]
    [DecidableEq m] [DecidableEq w] (X : Matrix m w ℚ) :
    canonicalLX X = X * (Xᵀ * X)⁻¹ := rfl

noncomputable def leftInverseLX {k : ℕ} (P : FaithfulClock.Clock k) (tau : ℕ) :=
  canonicalLX (FaithfulTables.X P tau)

theorem leftInverseLX_eq_gram {k : ℕ} (P : FaithfulClock.Clock k) (tau : ℕ) :
    leftInverseLX P tau = FaithfulTables.X P tau *
      ((FaithfulTables.X P tau)ᵀ * FaithfulTables.X P tau)⁻¹ := rfl

theorem leftInverseLX_spec {k : ℕ} (P : FaithfulClock.Clock k) (tau : ℕ) (htau : 0 < tau) :
    (FaithfulTables.X P tau)ᵀ * leftInverseLX P tau = 1 :=
  canonicalLX_spec _ (FaithfulTables.X_full_column_rank P tau htau)

def resetM (k : ℕ) (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ) :=
  Matrix.fromRows (WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar)
    (W_concrete k T1 T2 lam zeta0)

def resetRM (k : ℕ) (T1 T2 lam : ℚ) (zeta0 : Fin (k + 1) → ℚ) :=
  Matrix.fromCols (0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (Winv_concrete k T1 T2 lam zeta0)

def resetJ (k : ℕ) (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :=
  Matrix.fromBlocks ((1 / (T1 * T2 ^ 2)) • paperLower k) 0
    (paperCross k T1 T2 lam zeta0 ellStar E (paperLower k))
    ((1 / (T1 * T2 ^ 2)) • paperLower k)

theorem resetRM_mul_resetM (k : ℕ) (T1 T2 lam : ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0) (hlam : lam ≠ 0) (hzeta : zeta0 (lastIdx k) ≠ 0) :
    resetRM k T1 T2 lam zeta0 * resetM k T1 T2 lam zeta0 ellStar = 1 := by
  rw [resetRM, resetM, Matrix.fromCols_mul_fromRows, Matrix.zero_mul, zero_add]
  exact Winv_concrete_mul_W_concrete k T1 T2 lam hT1 hT2 hlam zeta0 hzeta

theorem resetM_rowSum (k : ℕ) (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ) :
    Matrix.vecMul (fun _ => 1) (resetM k T1 T2 lam zeta0 ellStar) =
      (2 * (k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar := by
  have hones : (fun _ : Fin (k + 1) ⊕ Fin (k + 1) => (1 : ℚ)) =
      Sum.elim (fun _ => 1) (fun _ => 1) := by
    funext i
    cases i <;> rfl
  rw [hones, resetM, Matrix.sumElim_vecMul_fromRows, early_row_sum, vecMul_one_W_concrete]
  ext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem resetJ_moment (k : ℕ) (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0) (hlam : lam ≠ 0) (hzeta : zeta0 (lastIdx k) ≠ 0)
    (hd : 1 + dotProduct ellStar
      (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (earlyUnit k)) ≠ 0) :
    (resetM k T1 T2 lam zeta0 ellStar)ᵀ * resetJ k T1 T2 lam zeta0 ellStar E *
      resetM k T1 T2 lam zeta0 ellStar = E :=
  exact_paper_moment k T1 T2 lam hT1 hT2 hlam zeta0 ellStar hzeta hd E (paperLower k)

/-- Moment compatibility is exactly the compatibility needed by interpolation. -/
theorem moment_compatibility {m n w : Type*} [Fintype m] [Fintype n] [Fintype w]
    (D X : Matrix m w ℚ) (M : Matrix n w ℚ) (J : Matrix n n ℚ)
    (E B : Matrix w w ℚ) (ell psi : w → ℚ)
    (hrows : Matrix.vecMul (fun _ => 1) M = ell) (hrealize : Mᵀ * J * M = E)
    (hmoment : E - Eᵀ * B = Dᵀ * X - outerProd ell psi) :
    Dᵀ * X = Mᵀ * (outerProd (fun _ => 1) psi + J * M - Jᵀ * M * B) := by
  have hj : Mᵀ * Jᵀ * M = Eᵀ := by
    rw [← hrealize]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.mul_add, mul_outerProd, Matrix.mulVec_transpose, hrows]
  simp only [← Matrix.mul_assoc]
  rw [hrealize, hj]
  rw [eq_sub_iff_add_eq] at hmoment
  rw [← hmoment]
  abel

/-- Both interpolation equations for the actual coupling, with compatibility
supplied by the moment equation rather than assumed as a second equation. -/
theorem paperCoupling_equations {m : Type*} [Fintype m]
    (k : ℕ) (T1 T2 lam dc : ℚ) (a : m → ℚ) (X LX D0 : Matrix m (Fin (k + 1)) ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hX : Xᵀ * LX = 1)
    (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0) (hlam : lam ≠ 0) (hzeta : zeta0 (lastIdx k) ≠ 0)
    (hd : 1 + dotProduct ellStar
      (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (earlyUnit k)) ≠ 0)
    (hmoment : E - Eᵀ * B =
      (D0 + dc • outerProd (fun _ => 1) (e0_row (k + 1)))ᵀ * X -
        outerProd ((2 * (k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar)
          (Matrix.vecMul zeta0 B - zeta0 - dc • e0_row (k + 1))) :
    let P := paperCoupling k T1 T2 lam dc a X LX D0 zeta0 ellStar E (paperLower k) B
    let M := resetM k T1 T2 lam zeta0 ellStar
    let J := resetJ k T1 T2 lam zeta0 ellStar E
    P * M = D0 + dc • outerProd (fun _ => 1) (e0_row (k + 1)) ∧
    Pᵀ * X = outerProd (fun _ => 1) (Matrix.vecMul zeta0 B - zeta0 - dc • e0_row (k + 1)) +
      J * M - Jᵀ * M * B := by
  intro P M J
  let D := D0 + dc • outerProd (fun _ : m => 1) (e0_row (k + 1))
  let psi := Matrix.vecMul zeta0 B - zeta0 - dc • e0_row (k + 1)
  let Q := resetScoreTarget psi (WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar)
    (W_concrete k T1 T2 lam zeta0) (paperLower k)
    (paperCross k T1 T2 lam zeta0 ellStar E (paperLower k)) (1 / (T1 * T2 ^ 2)) B
  have hQ : Q = outerProd (fun _ => 1) psi + J * M - Jᵀ * M * B :=
    resetScoreTarget_eq_blocks _ _ _ _ _ _ _
  have hcompat : Dᵀ * X = Mᵀ * Q := by
    rw [hQ]
    exact moment_compatibility D X M J E B _ psi
      (resetM_rowSum k T1 T2 lam zeta0 ellStar)
      (resetJ_moment k T1 T2 lam zeta0 ellStar E hT1 hT2 hlam hzeta hd) hmoment
  have hM := resetRM_mul_resetM k T1 T2 lam zeta0 ellStar hT1 hT2 hlam hzeta
  constructor
  · exact interpolate_PM X LX M (resetRM k T1 T2 lam zeta0) D Q (referenceCoupling a) hM hcompat
  · exact (interpolate_PtX X LX M (resetRM k T1 T2 lam zeta0) D Q (referenceCoupling a) hX).trans hQ

/-- The natural order is early resets followed by late resets. -/
def resetJFin (k : ℕ) (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :
    Matrix (Fin ((k + 1) + (k + 1))) (Fin ((k + 1) + (k + 1))) ℚ :=
  (resetJ k T1 T2 lam zeta0 ellStar E).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem resetJ_lower (k : ℕ) (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (i j : Fin (k + 1) ⊕ Fin (k + 1))
    (hij : (finSumFinEquiv i).val ≤ (finSumFinEquiv j).val) :
    resetJ k T1 T2 lam zeta0 ellStar E i j = 0 := by
  rcases i with i | i <;> rcases j with j | j
  · simp only [finSumFinEquiv_apply_left, Fin.val_castAdd] at hij
    change (1 / (T1 * T2 ^ 2)) * (if j.val < i.val then 1 else 0) = 0
    rw [if_neg (not_lt.mpr hij), mul_zero]
  · simp [resetJ]
  · simp only [finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
      Fin.val_natAdd, Fin.val_castAdd] at hij
    have := j.isLt
    omega
  · simp only [finSumFinEquiv_apply_right, Fin.val_natAdd] at hij
    change (1 / (T1 * T2 ^ 2)) * (if j.val < i.val then 1 else 0) = 0
    rw [if_neg (show ¬j.val < i.val by omega), mul_zero]

theorem resetJ_positive (k : ℕ) (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hT1 : 0 < T1) (hT2 : 0 < T2)
    (hC : ∀ i j, 0 < paperCross k T1 T2 lam zeta0 ellStar E (paperLower k) i j)
    (i j : Fin (k + 1) ⊕ Fin (k + 1))
    (hij : (finSumFinEquiv j).val < (finSumFinEquiv i).val) :
    0 < resetJ k T1 T2 lam zeta0 ellStar E i j := by
  have heta : (0 : ℚ) < 1 / (T1 * T2 ^ 2) := by positivity
  rcases i with i | i <;> rcases j with j | j
  · simp only [finSumFinEquiv_apply_left, Fin.val_castAdd] at hij
    change 0 < (1 / (T1 * T2 ^ 2)) * (if j.val < i.val then 1 else 0)
    simpa only [if_pos hij, mul_one] using heta
  · simp only [finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
      Fin.val_natAdd, Fin.val_castAdd] at hij
    have := i.isLt
    omega
  · exact hC i j
  · simp only [finSumFinEquiv_apply_right, Fin.val_natAdd] at hij
    change 0 < (1 / (T1 * T2 ^ 2)) * (if j.val < i.val then 1 else 0)
    simpa only [if_pos (show j.val < i.val by omega), mul_one] using heta

theorem resetJFin_lower (k : ℕ) (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (i j : Fin ((k + 1) + (k + 1))) (hij : i.val ≤ j.val) :
    resetJFin k T1 T2 lam zeta0 ellStar E i j = 0 := by
  apply resetJ_lower
  simpa using hij

theorem resetJFin_positive (k : ℕ) (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hT1 : 0 < T1) (hT2 : 0 < T2)
    (hC : ∀ i j, 0 < paperCross k T1 T2 lam zeta0 ellStar E (paperLower k) i j)
    (i j : Fin ((k + 1) + (k + 1))) (hij : j.val < i.val) :
    0 < resetJFin k T1 T2 lam zeta0 ellStar E i j := by
  apply resetJ_positive k T1 T2 lam zeta0 ellStar E hT1 hT2 hC
  simpa using hij

open FaithfulAdmissible FaithfulGain.AdmissibleGain

section Actual
variable {k : ℕ} {P : FaithfulClock.Clock k} (A : Admissible P)

theorem actual_D_eq (c delta : ℚ) :
    FaithfulTables.D P A.tau c (baseline P) delta =
      FaithfulTables.D P A.tau A.cref (baseline P) 0 +
        (c - A.cref) • outerProd (fun _ => 1) (e0_row (k + 1)) := by
  rw [FaithfulTables.D_independent_delta P A.tau c (baseline P) delta 0]
  have hh := FaithfulTables.D_sub_gain P A.tau c A.cref (baseline P) 0
  calc
    _ = (FaithfulTables.D P A.tau c (baseline P) 0 -
        FaithfulTables.D P A.tau A.cref (baseline P) 0) +
        FaithfulTables.D P A.tau A.cref (baseline P) 0 := by abel
    _ = _ := by rw [hh]; abel

theorem actual_psi_eq (c : ℚ) :
    FaithfulTables.psi (P.R P.b) A.tau c (baseline P) =
      Matrix.vecMul A.referenceHeight (B_mat (k + 1)) - A.referenceHeight -
        (c - A.cref) • e0_row (k + 1) := by
  have hh := FaithfulTables.psi_sub_gain (by have := P.order_ge_two; omega)
    (P.R P.b) A.tau c A.cref (baseline P)
  change FaithfulTables.psi (P.R P.b) A.tau c (baseline P) -
    (Matrix.vecMul A.referenceHeight (B_mat (k + 1)) - A.referenceHeight) =
    -(c - A.cref) • e0_row (k + 1) at hh
  rw [neg_smul] at hh
  calc
    _ = (FaithfulTables.psi (P.R P.b) A.tau c (baseline P) -
        (Matrix.vecMul A.referenceHeight (B_mat (k + 1)) - A.referenceHeight)) +
        (Matrix.vecMul A.referenceHeight (B_mat (k + 1)) - A.referenceHeight) := by abel
    _ = _ := by rw [hh]; abel

/-- The same fixed canonical left inverse used by the uniform synthesis. -/
noncomputable def actualCoupling (lam T1 T2 : ℕ) :=
  paperCoupling k T1 T2 lam (selectedGain A lam T1 - A.cref) A.weights
    (FaithfulTables.X P A.tau) (leftInverseLX P A.tau)
    (FaithfulTables.D P A.tau A.cref (baseline P) 0) A.referenceHeight A.correction
    (momentTable A lam T1) (paperLower k) (B_mat (k + 1))

/-- Both exact reset equations on the actual gain and compatible moment table.
The auxiliary endpoint margin delta is arbitrary and affects neither equation's
compatibility proof nor the selected coupling. -/
theorem actualCoupling_equations_of_moment (lam T1 T2 : ℕ) (delta : ℚ)
    (hT1 : 0 < T1) (hT2 : 0 < T2) (hlam : 0 < lam)
    (hd : 1 + dotProduct A.correction
      (Matrix.mulVec (Winv_concrete k T1 T2 lam A.referenceHeight) (earlyUnit k)) ≠ 0)
    (hmoment : L_moment (B_mat (k + 1)) (momentTable A lam T1) =
      (FaithfulTables.D P A.tau (selectedGain A lam T1) (baseline P) delta)ᵀ *
        FaithfulTables.X P A.tau -
      outerProd (FaithfulGain.totalCounts (baselineCounts A lam) A.correction T1)
        (FaithfulTables.psi (P.R P.b) A.tau (selectedGain A lam T1) (baseline P))) :
    let M := resetM k T1 T2 lam A.referenceHeight A.correction
    let J := resetJ k T1 T2 lam A.referenceHeight A.correction (momentTable A lam T1)
    actualCoupling A lam T1 T2 * M =
      FaithfulTables.D P A.tau (selectedGain A lam T1) (baseline P) delta ∧
    (actualCoupling A lam T1 T2)ᵀ * FaithfulTables.X P A.tau =
      Q_reset J M (B_mat (k + 1))
        (FaithfulTables.zeta (P.R P.b) A.tau (selectedGain A lam T1) (baseline P)) := by
  intro M J
  have htotal : FaithfulGain.totalCounts (baselineCounts A lam) A.correction T1 =
      (2 * (k + 1 : ℚ) * T1 * lam) • A.referenceHeight + A.correction := by
    ext j
    simp only [FaithfulGain.totalCounts, baselineCounts, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hm := hmoment
  rw [actual_D_eq A, actual_psi_eq A, htotal] at hm
  have ht1 : (T1 : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT1
  have ht2 : (T2 : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT2
  have hl : (lam : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hlam
  have hz : A.referenceHeight (lastIdx k) ≠ 0 := ne_of_gt A.reference_leading_pos
  have hx := leftInverseLX_spec P A.tau (by have := A.tau_pos; omega)
  have heq := paperCoupling_equations k T1 T2 lam (selectedGain A lam T1 - A.cref)
    A.weights (FaithfulTables.X P A.tau) (leftInverseLX P A.tau)
    (FaithfulTables.D P A.tau A.cref (baseline P) 0) A.referenceHeight A.correction
    (momentTable A lam T1) (B_mat (k + 1)) hx ht1 ht2 hl hz hd hm
  refine ⟨?_, ?_⟩
  · rw [actual_D_eq A]
    exact heq.1
  · have hQ : Q_reset J M (B_mat (k + 1))
        (FaithfulTables.zeta (P.R P.b) A.tau (selectedGain A lam T1) (baseline P)) =
        outerProd (fun _ => 1)
          (FaithfulTables.psi (P.R P.b) A.tau (selectedGain A lam T1) (baseline P)) +
          J * M - Jᵀ * M * B_mat (k + 1) := by
      unfold Q_reset FaithfulTables.psi
      have ho (z : Fin (k + 1) → ℚ) :
          one_zeta (Fin (k + 1) ⊕ Fin (k + 1)) z = outerProd (fun _ => 1) z := by
        ext i j
        simp [one_zeta, outerProd]
      rw [ho, outerProd_mul]
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, outerProd, Matrix.of_apply,
        Pi.sub_apply, one_mul]
    rw [hQ, actual_psi_eq A]
    exact heq.2

/-- The moment premise is discharged by the actual selected gain. -/
theorem actualCoupling_equations (lam T1 T2 : ℕ) (delta : ℚ)
    (hT1 : 0 < T1) (hT2 : 0 < T2) (hlam : 0 < lam)
    (hd : 1 + dotProduct A.correction
      (Matrix.mulVec (Winv_concrete k T1 T2 lam A.referenceHeight) (earlyUnit k)) ≠ 0)
    (hgain : Even k → baselineCounts A lam ⟨k, by omega⟩ * T1 +
      (oldTotals A ⟨k, by omega⟩ + A.correction ⟨k, by omega⟩) ≠ 0) :
    let M := resetM k T1 T2 lam A.referenceHeight A.correction
    let J := resetJ k T1 T2 lam A.referenceHeight A.correction (momentTable A lam T1)
    actualCoupling A lam T1 T2 * M =
      FaithfulTables.D P A.tau (selectedGain A lam T1) (baseline P) delta ∧
    (actualCoupling A lam T1 T2)ᵀ * FaithfulTables.X P A.tau =
      Q_reset J M (B_mat (k + 1))
        (FaithfulTables.zeta (P.R P.b) A.tau (selectedGain A lam T1) (baseline P)) :=
  actualCoupling_equations_of_moment A lam T1 T2 delta hT1 hT2 hlam hd
    (momentTable_solves A lam T1 delta hgain)

/-- The full simultaneous phase-return equations, with no reset equation left
as an input to the construction. -/
theorem actualCoupling_phase_equations (lam T1 T2 : ℕ) (delta : ℚ)
    (hT1 : 0 < T1) (hT2 : 0 < T2) (hlam : 0 < lam)
    (hd : 1 + dotProduct A.correction
      (Matrix.mulVec (Winv_concrete k T1 T2 lam A.referenceHeight) (earlyUnit k)) ≠ 0)
    (hgain : Even k → baselineCounts A lam ⟨k, by omega⟩ * T1 +
      (oldTotals A ⟨k, by omega⟩ + A.correction ⟨k, by omega⟩) ≠ 0) :
    let M := resetM k T1 T2 lam A.referenceHeight A.correction
    let J := resetJ k T1 T2 lam A.referenceHeight A.correction (momentTable A lam T1)
    FaithfulTables.oldGame P * FaithfulTables.X P A.tau + actualCoupling A lam T1 T2 * M =
      FaithfulTables.S P A.tau (selectedGain A lam T1) (baseline P) delta * N_mat (k + 1) ∧
    -(actualCoupling A lam T1 T2)ᵀ * FaithfulTables.X P A.tau + (J - Jᵀ) * M =
      V_reset J M (B_mat (k + 1))
        (FaithfulTables.zeta (P.R P.b) A.tau (selectedGain A lam T1) (baseline P)) *
        N_mat (k + 1) := by
  intro M J
  have hBT : B_mat (k + 1) * (1 + N_mat (k + 1)) = 1 := (B_mat_mul_T_mat (k + 1)).1
  apply (reset_identity_iff (FaithfulTables.oldGame P) (actualCoupling A lam T1 T2) J
    (FaithfulTables.S P A.tau (selectedGain A lam T1) (baseline P) delta)
    (FaithfulTables.X P A.tau) M (B_mat (k + 1)) (N_mat (k + 1))
    (FaithfulTables.zeta (P.R P.b) A.tau (selectedGain A lam T1) (baseline P)) hBT).mpr
  exact actualCoupling_equations A lam T1 T2 delta hT1 hT2 hlam hd hgain

noncomputable def actualGame (lam T1 T2 : ℕ) :=
  liftedGameMat (FaithfulTables.oldGame P) (actualCoupling A lam T1 T2)
    (resetJ k T1 T2 lam A.referenceHeight A.correction (momentTable A lam T1))

theorem actualGame_skew (lam T1 T2 : ℕ) : IsSkewSymmetric (actualGame A lam T1 T2) :=
  liftedGameMat_skew _ _ _ (FaithfulTables.oldGame_skew P)

end Actual

#print axioms actualCoupling_equations_of_moment
#print axioms actualCoupling_equations
#print axioms actualCoupling_phase_equations
#print axioms actualGame_skew
#print axioms resetJFin_lower
#print axioms resetJFin_positive
#print axioms leftInverseLX_spec
#print axioms resetJ_moment
#print axioms paperCoupling_equations
end Karlin.FaithfulResetEquations
