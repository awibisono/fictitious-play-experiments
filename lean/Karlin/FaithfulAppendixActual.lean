import Karlin.FaithfulAppendixBounds
import Karlin.FaithfulEffectiveLift

/-! The literal Appendix candidate tests on the actual admissible parent,
actual gain and moment correction, and prescribed Gram interpolation. -/
namespace Karlin.FaithfulAppendix.Actual
open scoped BigOperators Matrix
open Faithful FaithfulClock FaithfulAdmissible FaithfulSynthesis
open FaithfulGain.AdmissibleGain FaithfulResetEquations
set_option maxHeartbeats 1600000
variable {k : ℕ} {P : Clock k} (A : Admissible P)

def actualPsi (lam T : ℕ) : Fin (k+1) → ℚ :=
  FaithfulTables.psi (P.R P.b) A.tau (selectedGain A lam T) (baseline P)
def actualD (lam T : ℕ) : Matrix (FaithfulTables.OldAct P) (Fin (k+1)) ℚ :=
  FaithfulTables.D P A.tau (selectedGain A lam T) (baseline P) 0
def gainDenominator (lam T : ℕ) : ℚ :=
  baselineCounts A lam (lastIdx k) * T + oldTotals A (lastIdx k) + A.correction (lastIdx k)
def crossCap (lam T : ℕ) : ℚ :=
  bCross k T lam A.referenceHeight A.correction (momentTable A lam T) (paperLower k)
def scoreCap (lam T : ℕ) : ℚ :=
  bQ k T lam A.referenceHeight A.correction (actualPsi A lam T)
    (momentTable A lam T) (paperLower k) (B_mat (k+1))
def couplingCap (lam T : ℕ) : ℚ :=
  bP k T lam A.referenceHeight A.correction (actualPsi A lam T)
    (momentTable A lam T) (paperLower k) (B_mat (k+1)) A.weights
    (FaithfulTables.X P A.tau) (leftInverseLX P A.tau) (actualD A lam T)

/-- Exactly the positive-integer Appendix tests. The gain denominator gate is
required only for even k. All entries are finite rational expressions at T1;
the predicate contains no T2, phase index, or universal trajectory search. -/
def Candidate (lam T : ℕ) : Prop :=
  1 ≤ T ∧ (Even k → 0 < gainDenominator A lam T) ∧
  0 < selectedGain A lam T ∧ selectedGain A lam T < 1 ∧
  0 < (T : ℚ) * lam * A.referenceHeight (lastIdx k) + A.correction (lastIdx k) ∧
  nu k T lam A.referenceHeight A.correction < 1/2 ∧
  crossCap A lam T < paperKappa k T lam / 2 ∧
  couplingCap A lam T < min (minimumWeight A / 4) ((A.weights (Sum.inr 0) - P.Arem - 1)/2)

instance candidateDecidable (lam T : ℕ) : Decidable (Candidate A lam T) := by
  unfold Candidate
  infer_instance

theorem actual_cross_bound (lam T1 T2 : ℕ) (ht1 : 0 < T1) (ht2 : T1 ≤ T2)
    (hnu : nu k T1 lam A.referenceHeight A.correction < 1/2) :
    normStar (paperCross k T1 T2 lam A.referenceHeight A.correction
      (momentTable A lam T1) (paperLower k) -
      paperKappa k T1 lam • outerProd (fun _ => 1) (fun _ => 1)) ≤ crossCap A lam T1 :=
  cross_bound k T1 T2 lam A.referenceHeight A.correction (momentTable A lam T1) (paperLower k)
    (by exact_mod_cast ht1) (by exact_mod_cast ht2) hnu

theorem actual_Q_eq (lam T1 T2 : ℕ) :
    Q_reset (resetJ k T1 T2 lam A.referenceHeight A.correction (momentTable A lam T1))
      (resetM k T1 T2 lam A.referenceHeight A.correction) (B_mat (k+1))
      (FaithfulTables.zeta (P.R P.b) A.tau (selectedGain A lam T1) (baseline P)) =
    resetScoreTarget (actualPsi A lam T1)
      (WE_concrete k T1 T2 lam A.referenceHeight (earlyUnit k) A.correction)
      (W_concrete k T1 T2 lam A.referenceHeight) (paperLower k)
      (paperCross k T1 T2 lam A.referenceHeight A.correction (momentTable A lam T1) (paperLower k))
      (1/(T1*T2^2)) (B_mat (k+1)) := by
  rw [resetScoreTarget_eq_blocks]
  unfold Q_reset actualPsi FaithfulTables.psi
  have ho (z : Fin (k+1) → ℚ) : one_zeta (Fin (k+1) ⊕ Fin (k+1)) z = outerProd (fun _ => 1) z := by
    ext i j
    simp [one_zeta, outerProd]
  rw [ho, outerProd_mul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, outerProd, Matrix.of_apply, Pi.sub_apply, one_mul]
  rfl

theorem actual_score_bound (lam T1 T2 : ℕ) (hlam : 0 < lam) (ht1 : 0 < T1) (ht2 : T1 ≤ T2)
    (hnu : nu k T1 lam A.referenceHeight A.correction < 1/2) :
    normStar (Q_reset (resetJ k T1 T2 lam A.referenceHeight A.correction (momentTable A lam T1))
      (resetM k T1 T2 lam A.referenceHeight A.correction) (B_mat (k+1))
      (FaithfulTables.zeta (P.R P.b) A.tau (selectedGain A lam T1) (baseline P)) -
      (referenceCoupling A.weights)ᵀ * FaithfulTables.X P A.tau) ≤ scoreCap A lam T1 := by
  rw [actual_Q_eq, referenceCoupling_transpose_mul A.weights (FaithfulTables.X P A.tau)
    A.referenceHeight (B_mat (k+1)) A.reference_cone]
  exact score_bound k T1 T2 lam A.referenceHeight A.correction (actualPsi A lam T1)
    (momentTable A lam T1) (paperLower k) (B_mat (k+1))
    (by exact_mod_cast ht1) (by exact_mod_cast ht2) (by exact_mod_cast hlam) A.reference_leading_pos hnu

theorem actual_coupling_bound (lam T1 T2 : ℕ) (hlam : 0 < lam) (ht1 : 0 < T1) (ht2 : T1 ≤ T2)
    (hnu : nu k T1 lam A.referenceHeight A.correction < 1/2) :
    normStar (actualCoupling A lam T1 T2 - referenceCoupling A.weights) ≤ couplingCap A lam T1 := by
  have h := coupling_bound k T1 T2 lam A.referenceHeight A.correction (actualPsi A lam T1)
    (momentTable A lam T1) (paperLower k) (B_mat (k+1)) A.weights
    (FaithfulTables.X P A.tau) (leftInverseLX P A.tau) (actualD A lam T1) A.reference_cone
    (by exact_mod_cast ht1) (by exact_mod_cast ht2) (by exact_mod_cast hlam) A.reference_leading_pos hnu
  change normStar _ ≤ couplingCap A lam T1 at h
  have hd : actualD A lam T1 = FaithfulTables.D P A.tau A.cref (baseline P) 0 +
      (selectedGain A lam T1 - A.cref) • outerProd (fun _ => 1) (e0_row (k+1)) :=
    actual_D_eq A _ 0
  have hp : actualPsi A lam T1 = Matrix.vecMul A.referenceHeight (B_mat (k+1)) - A.referenceHeight -
      (selectedGain A lam T1 - A.cref) • e0_row (k+1) := actual_psi_eq A _
  rw [hd, hp] at h
  exact h

theorem candidate_inverse_denominator (lam T1 : ℕ) (hc : Candidate A lam T1)
    (T2 : ℕ) (ht2 : T1 ≤ T2) :
    (1/2 : ℚ) < 1 + dotProduct A.correction
      ((Winv_concrete k T1 T2 lam A.referenceHeight).mulVec (earlyUnit k)) := by
  have ht : (0 : ℚ) < T1 := by exact_mod_cast (show 0 < T1 by have := hc.1; omega)
  have hh := inverse_denominator k T1 T2 lam A.referenceHeight A.correction ht (by exact_mod_cast ht2)
  have hn := hc.2.2.2.2.2.1
  linarith

theorem candidate_cross_positive (lam T1 : ℕ) (hlam : 0 < lam) (hc : Candidate A lam T1)
    (T2 : ℕ) (ht2 : T1 ≤ T2) (i j : Fin (k+1)) :
    0 < paperCross k T1 T2 lam A.referenceHeight A.correction (momentTable A lam T1) (paperLower k) i j := by
  rcases hc with ⟨ht, _, _, _, _, hnu, hcross, _⟩
  have hnorm := actual_cross_bound A lam T1 T2 (by omega) ht2 hnu
  have hh := (abs_entry_le _ i j).trans hnorm
  have he := abs_lt.mp (hh.trans_lt hcross)
  simp only [Matrix.sub_apply, Matrix.smul_apply, outerProd, Matrix.of_apply, smul_eq_mul, mul_one] at he
  have hk : 0 < paperKappa k T1 lam := by
    unfold paperKappa
    have htq : (0 : ℚ) < T1 := by exact_mod_cast (show 0 < T1 by omega)
    have hlq : (0 : ℚ) < lam := by exact_mod_cast hlam
    positivity
  linarith [he.1]

/-- Literal Appendix bP tests imply every early/late sign and both waiting
margins, with the actual coupling and prescribed reference weights. -/
theorem candidate_coupling_signs (lam T1 : ℕ) (hlam : 0 < lam) (hc : Candidate A lam T1)
    (T2 : ℕ) (ht2 : T1 ≤ T2) :
    (∀ i j, actualCoupling A lam T1 T2 i (Sum.inl j) < -(minimumWeight A / 4) ∧
      minimumWeight A / 4 < actualCoupling A lam T1 T2 i (Sum.inr j)) ∧
    (∀ j, P.Arem < -actualCoupling A lam T1 T2 (Sum.inr 0) (Sum.inl j) - selectedGain A lam T1) := by
  rcases hc with ⟨ht, _, _, hcu, _, hnu, _, hp⟩
  exact coupling_signs_of_bound k (actualCoupling A lam T1 T2) A.weights (Sum.inr 0)
    (couplingCap A lam T1) (minimumWeight A) P.Arem (selectedGain A lam T1)
    (actual_coupling_bound A lam T1 T2 hlam (by omega) ht2 hnu)
    (minimumWeight_pos A) (minimumWeight_le A) A.gateway_weight_margin hcu
    (hp.trans_le (min_le_left _ _)) (hp.trans_le (min_le_right _ _))

theorem candidate_reset_leading (lam T1 : ℕ) (hlam : 0 < lam) (hc : Candidate A lam T1)
    (T2 : ℕ) : ∀ i : Fin (k+1),
    0 < WE_concrete k T1 T2 lam A.referenceHeight (earlyUnit k) A.correction i (lastIdx k) ∧
    0 < W_concrete k T1 T2 lam A.referenceHeight i (lastIdx k) := by
  have htq : (0 : ℚ) < T1 := by exact_mod_cast (show 0 < T1 by have := hc.1; omega)
  have hlq : (0 : ℚ) < lam := by exact_mod_cast hlam
  exact reset_leading_positive k T1 lam A.referenceHeight A.correction
    (mul_pos (mul_pos htq hlq) A.reference_leading_pos) hc.2.2.2.2.1 T2

theorem candidate_J_positive (lam T1 : ℕ) (hlam : 0 < lam) (hc : Candidate A lam T1)
    (T2 : ℕ) (ht2 : T1 ≤ T2) (i j : Fin ((k+1)+(k+1))) (hij : j.val < i.val) :
    0 < resetJFin k T1 T2 lam A.referenceHeight A.correction (momentTable A lam T1) i j := by
  apply resetJFin_positive k T1 T2 lam A.referenceHeight A.correction (momentTable A lam T1)
  · exact_mod_cast (show 0 < T1 by have := hc.1; omega)
  · exact_mod_cast (show 0 < T2 by have := hc.1; omega)
  · exact candidate_cross_positive A lam T1 hlam hc T2 ht2
  · exact hij

/-- Passing the literal finite test also yields both exact reset equations;
the parity gate discharges the selected gain's only possible denominator. -/
theorem candidate_equations (lam T1 : ℕ) (hlam : 0 < lam) (hc : Candidate A lam T1)
    (T2 : ℕ) (ht2 : T1 ≤ T2) (delta : ℚ) :
    let M := resetM k T1 T2 lam A.referenceHeight A.correction
    let J := resetJ k T1 T2 lam A.referenceHeight A.correction (momentTable A lam T1)
    actualCoupling A lam T1 T2 * M =
      FaithfulTables.D P A.tau (selectedGain A lam T1) (baseline P) delta ∧
    (actualCoupling A lam T1 T2)ᵀ * FaithfulTables.X P A.tau =
      Q_reset J M (B_mat (k+1))
        (FaithfulTables.zeta (P.R P.b) A.tau (selectedGain A lam T1) (baseline P)) := by
  apply actualCoupling_equations A lam T1 T2 delta (by have := hc.1; omega)
    (by have := hc.1; omega) hlam
  · exact (lt_trans (by norm_num) (candidate_inverse_denominator A lam T1 hc T2 ht2)).ne'
  · intro he
    have hh := (hc.2.1 he).ne'
    simpa only [gainDenominator, add_assoc] using hh

/-- The leading total old count is nonnegative, independently of parity. -/
theorem oldTotals_top_nonneg : 0 ≤ oldTotals A (lastIdx k) := by
  unfold oldTotals Matrix.vecMul dotProduct
  apply Finset.sum_nonneg
  intro i _
  simp only [one_mul]
  have hh := FaithfulNextTables.shifted_X_leading_nonneg P A.tau i
  have ht : (FaithfulTables.X P A.tau * T_mat (k+1)) i (lastIdx k) =
      FaithfulTables.X P A.tau i (lastIdx k) := by
    rw [T_mat, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, mul_N_mat_apply]
    simp [lastIdx]
  rwa [ht] at hh

/-- Positive leading reset counts make the total denominator positive even
in odd degree, where the literal candidate need not explicitly test it. -/
theorem candidate_gain_denominator (lam T1 : ℕ) (hlam : 0 < lam)
    (hc : Candidate A lam T1) : 0 < gainDenominator A lam T1 := by
  have ht : (0 : ℚ) < T1 := by exact_mod_cast (show 0 < T1 by have := hc.1; omega)
  have hl : (0 : ℚ) < lam := by exact_mod_cast hlam
  have hu := mul_pos (mul_pos ht hl) A.reference_leading_pos
  have hr : (1 : ℚ) ≤ k+1 := by have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k; linarith
  have ho := oldTotals_top_nonneg A
  have hp := hc.2.2.2.2.1
  have he : gainDenominator A lam T1 =
      2*(k+1 : ℚ)*((T1 : ℚ)*lam*A.referenceHeight (lastIdx k))+
        oldTotals A (lastIdx k)+A.correction (lastIdx k) := by
    simp only [gainDenominator, baselineCounts, Pi.smul_apply, smul_eq_mul]
    ring
  change 0 < (T1 : ℚ)*lam*A.referenceHeight (lastIdx k) at hu
  have hm := mul_le_mul_of_nonneg_right (show (1 : ℚ) ≤ 2*(k+1 : ℚ) by linarith) hu.le
  simp only [one_mul] at hm
  rw [he]
  linarith

/-- The literal finite Appendix certificate feeds the same actual scale
record used by the complete clock lift. Its moment and sign fields are earned. -/
theorem candidate_validScales (lam T1 : ℕ) (hlam : 0 < lam)
    (hc : Candidate A lam T1) (T2 : ℕ) (ht2 : T1 ≤ T2) :
    ValidScales A lam T1 T2 (leftInverseLX P A.tau) := by
  have hpos := hc.2.2.1
  have hlt := hc.2.2.2.1
  have hsign := candidate_coupling_signs A lam T1 hlam hc T2 ht2
  refine ⟨by have := hc.1; omega, by have := hc.1; omega, ?_, hpos, hlt,
    ?_, ?_, ?_, candidate_reset_leading A lam T1 hlam hc T2,
    candidate_inverse_denominator A lam T1 hc T2 ht2, ?_, hsign.1, hsign.2, ?_⟩
  · simpa only [gainDenominator, add_assoc] using candidate_gain_denominator A lam T1 hlam hc
  · exact lt_min (by positivity) (by have := P.marker_pos; positivity)
  · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  · exact lt_of_le_of_lt (min_le_right _ _) (by have := P.marker_pos; linarith)
  · exact candidate_cross_positive A lam T1 hlam hc T2 ht2
  · intro delta
    exact momentTable_solves A lam T1 delta (fun he => by
      have hh := (hc.2.1 he).ne'
      simpa only [gainDenominator, add_assoc] using hh)

#print axioms candidate_validScales

#print axioms actual_cross_bound
#print axioms actual_score_bound
#print axioms actual_coupling_bound
#print axioms candidate_coupling_signs
#print axioms candidate_J_positive
#print axioms candidate_equations
end Karlin.FaithfulAppendix.Actual
