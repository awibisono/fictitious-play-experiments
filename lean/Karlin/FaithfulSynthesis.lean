import Karlin.FaithfulGain

/-! Uniform synthesis from the actual admissible parent. The first scale is
chosen before the second; the conclusions hold for every larger second scale.
The interpolation left section is a fixed parameter here; its exact inverse
identity is supplied separately for the reset equations. -/
namespace Karlin.FaithfulSynthesis
open scoped BigOperators Matrix
open FaithfulClock FaithfulAdmissible FaithfulGain.AdmissibleGain
variable {k : ℕ} {P : Clock k} (A : Admissible P)

def minimumWeight : ℚ := Finset.univ.inf' Finset.univ_nonempty A.weights

theorem minimumWeight_pos : 0 < minimumWeight A := by
  rw [minimumWeight, Finset.lt_inf'_iff]
  intro i _
  exact A.weights_positive i

theorem minimumWeight_le (i : FaithfulTables.OldAct P) : minimumWeight A ≤ A.weights i :=
  Finset.inf'_le A.weights (Finset.mem_univ i)

def endpointMargin (lam T : ℕ) : ℚ := min (selectedGain A lam T / 2) (P.delta0 / 2)

theorem endpointMargin_eq_paper (lam T : ℕ) : endpointMargin A lam T =
    (1/2 : ℚ) * min P.delta0 (selectedGain A lam T) := by
  unfold endpointMargin
  by_cases h : P.delta0 ≤ selectedGain A lam T
  · rw [min_eq_left h, min_eq_right (by linarith)]
    ring
  · rw [min_eq_right (le_of_not_ge h), min_eq_left (by linarith)]
    ring

noncomputable def cross (lam T1 T2 : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) ℚ :=
  Faithful.paperCross k T1 T2 lam A.referenceHeight A.correction
    (momentTable A lam T1) (L_strict (k+1))

noncomputable def coupling (lam T1 T2 : ℕ) (LX : Matrix (FaithfulTables.OldAct P) (Fin (k+1)) ℚ) :=
  Faithful.paperCoupling k T1 T2 lam (selectedGain A lam T1 - A.cref) A.weights
    (FaithfulTables.X P A.tau) LX (FaithfulTables.D P A.tau A.cref (baseline P) 0)
    A.referenceHeight A.correction (momentTable A lam T1) (L_strict (k+1)) (B_mat (k+1))

/-- Earned facts for the literal reset formulas, not additional parent premises. -/
structure ValidScales (lam T1 T2 : ℕ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k+1)) ℚ) : Prop where
  first_pos : 0 < T1
  second_pos : 0 < T2
  gain_denominator : 0 < baselineCounts A lam ⟨k, by omega⟩ * T1 +
    (oldTotals A ⟨k, by omega⟩ + A.correction ⟨k, by omega⟩)
  gain_pos : 0 < selectedGain A lam T1
  gain_lt_one : selectedGain A lam T1 < 1
  margin_pos : 0 < endpointMargin A lam T1
  margin_lt_gain : endpointMargin A lam T1 < selectedGain A lam T1
  margin_lt_parent : endpointMargin A lam T1 < P.delta0
  reset_leading : ∀ j,
    0 < WE_concrete k T1 T2 lam A.referenceHeight (Faithful.earlyUnit k) A.correction j (lastIdx k) ∧
    0 < W_concrete k T1 T2 lam A.referenceHeight j (lastIdx k)
  inverse_denominator : (1/2 : ℚ) < 1 + dotProduct A.correction
    ((Winv_concrete k T1 T2 lam A.referenceHeight).mulVec (Faithful.earlyUnit k))
  cross_positive : ∀ i j, 0 < cross A lam T1 T2 i j
  coupling_signs : ∀ i j,
    coupling A lam T1 T2 LX i (Sum.inl j) < -(minimumWeight A / 4) ∧
    minimumWeight A / 4 < coupling A lam T1 T2 LX i (Sum.inr j)
  early_reserve : ∀ j, P.Arem <
    -coupling A lam T1 T2 LX (Sum.inr 0) (Sum.inl j) - selectedGain A lam T1
  moment : ∀ delta : ℚ,
    L_moment (B_mat (k+1)) (momentTable A lam T1) =
      (FaithfulTables.D P A.tau (selectedGain A lam T1) (baseline P) delta).transpose *
        FaithfulTables.X P A.tau -
      outerProd (FaithfulGain.totalCounts (baselineCounts A lam) A.correction T1)
        (FaithfulTables.psi (P.R P.b) A.tau (selectedGain A lam T1) (baseline P))

/-- One first-scale threshold works for every second scale T2>=T1. There is
no assumption on the last correction coordinate and no phase-index parameter. -/
theorem uniform_validScales (lam : ℕ) (hlam : 1 ≤ lam)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k+1)) ℚ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ T1 : ℕ, N ≤ T1 → ∀ T2 : ℕ, T1 ≤ T2 →
      ValidScales A lam T1 T2 LX := by
  obtain ⟨Kd, KE, N0, _, _, hN0, hmoment⟩ := eventually_momentTable A lam hlam
  have hlamq : (0 : ℚ) < lam := by exact_mod_cast (show 0 < lam by omega)
  obtain ⟨N1, _, hsign⟩ := Faithful.uniform_actual_reset_signs k lam KE Kd A.weights
    (FaithfulTables.X P A.tau) LX (FaithfulTables.D P A.tau A.cref (baseline P) 0)
    A.referenceHeight A.correction (L_strict (k+1)) (B_mat (k+1)) (Sum.inr 0)
    (minimumWeight A) P.Arem A.reference_cone hlamq A.reference_leading_pos
    (minimumWeight_pos A) (minimumWeight_le A) A.gateway_weight_margin
  refine ⟨max N0 N1, le_trans hN0 (le_max_left _ _), ?_⟩
  intro T1 hT1 T2 hT2
  obtain ⟨hgainDen, hcpos, hcone, hdc, hm, hE⟩ := hmoment T1 (le_trans (le_max_left _ _) hT1)
  have hN1 : (N1 : ℚ) ≤ T1 := by exact_mod_cast le_trans (le_max_right N0 N1) hT1
  have hT2q : (T1 : ℚ) ≤ T2 := by exact_mod_cast hT2
  obtain ⟨ht1, ht2, hlead, hden, hrest⟩ := hsign T1 hN1 T2 hT2q
  obtain ⟨hcross, hcoupling, hreserve⟩ := hrest (momentTable A lam T1)
    (selectedGain A lam T1 - A.cref) (selectedGain A lam T1) hE hdc hcone
  refine ⟨by exact_mod_cast ht1, by exact_mod_cast ht2, hgainDen, hcpos, hcone, ?_, ?_, ?_,
    hlead, hden, hcross, hcoupling, hreserve, hm⟩
  · exact lt_min (by positivity) (by have := P.marker_pos; positivity)
  · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  · exact lt_of_le_of_lt (min_le_right _ _) (by have := P.marker_pos; linarith)

#print axioms uniform_validScales
end Karlin.FaithfulSynthesis
