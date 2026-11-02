import Karlin.FaithfulSynthesis
import Karlin.FaithfulParameters
import Karlin.FaithfulNextTables
import Karlin.FaithfulResetEquations
import Karlin.FaithfulEffectiveParameters

/-! The actual parameter order: parent admissibility fixes tau and correction;
least lambda and the rational left section are then fixed; one first-scale
threshold precedes every second scale; finally the exact phase onset is computed.
-/
namespace Karlin.FaithfulController
open scoped BigOperators Matrix
open FaithfulClock FaithfulAdmissible FaithfulSynthesis FaithfulParameters
open FaithfulParameters.AdmissibleParameters FaithfulResetEquations
variable {k : ℕ} {P : Clock k} (A : Admissible P)

abbrev ValidParameters (T1 T2 : ℕ) :=
  ValidScales A (lam A) T1 T2 (leftInverseLX P A.tau)

theorem uniform_parameters : ∃ N : ℕ, 1 ≤ N ∧
    ∀ T1 : ℕ, N ≤ T1 → ∀ T2 : ℕ, T1 ≤ T2 → ValidParameters A T1 T2 :=
  uniform_validScales A (lam A) (lam_pos A) (leftInverseLX P A.tau)

/-- A fixed first scale, selected before T2 and every phase/time index. -/
def firstScale : ℕ := FaithfulEffectiveParameters.canonicalFirstScale A

theorem firstScale_pos : 1 ≤ firstScale A :=
  FaithfulEffectiveParameters.canonicalFirstScale_pos A

theorem firstScale_spec (T1 : ℕ) (hT1 : firstScale A ≤ T1)
    (T2 : ℕ) (hT2 : T1 ≤ T2) : ValidParameters A T1 T2 :=
  FaithfulEffectiveParameters.canonicalFirstScale_spec A T1 hT1 T2 hT2

/-- Literal equation Qout. It is evaluated only after T1 and T2 are fixed. -/
def outerOnset (T1 T2 : ℕ) : ℕ :=
  max 1 (max (resetOnset (resetTable A T1 T2) + 1)
    ⌈(FaithfulGrowth.Clock.bundleThreshold P (minimumWeight A / 4) : ℚ) / (A.tau : ℚ)⌉₊)

theorem outerOnset_pos (T1 T2 : ℕ) : 1 ≤ outerOnset A T1 T2 := le_max_left _ _

theorem outerOnset_previous (T1 T2 q : ℕ) (hq : outerOnset A T1 T2 ≤ q) :
    resetOnset (resetTable A T1 T2) ≤ q - 1 := by
  have h : resetOnset (resetTable A T1 T2) + 1 ≤ q :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hq)
  omega

theorem outerOnset_bundle (T1 T2 q : ℕ) (hq : outerOnset A T1 T2 ≤ q) :
    FaithfulGrowth.Clock.bundleThreshold P (minimumWeight A / 4) ≤ A.tau * q := by
  have hb : ⌈(FaithfulGrowth.Clock.bundleThreshold P (minimumWeight A / 4) : ℚ) /
      (A.tau : ℚ)⌉₊ ≤ q := (le_max_right _ _).trans ((le_max_right _ _).trans hq)
  have ht : (0 : ℚ) < A.tau := by exact_mod_cast (show 0 < A.tau by have := A.tau_pos; omega)
  have hd : (FaithfulGrowth.Clock.bundleThreshold P (minimumWeight A / 4) : ℚ) /
      (A.tau : ℚ) ≤ (q : ℚ) := (Nat.le_ceil _).trans (by exact_mod_cast hb)
  have hm := (div_le_iff₀ ht).mp hd
  rw [mul_comm] at hm
  exact_mod_cast hm

theorem actual_integer_leading (T1 T2 : ℕ) (hv : ValidParameters A T1 T2)
    (i : Fin (k+1) ⊕ Fin (k+1)) : 0 < resetTable A T1 T2 i (Fin.last k) := by
  have he := congrFun (congrFun (resetTable_cast A T1 T2) i) (Fin.last k)
  have hp : (0 : ℚ) < resetTable A T1 T2 i (Fin.last k) := by
    rw [he]
    cases i with
    | inl i => exact (hv.reset_leading i).1
    | inr i => exact (hv.reset_leading i).2
  exact_mod_cast hp

theorem outerOnset_counts (T1 T2 : ℕ) (hv : ValidParameters A T1 T2)
    (q : ℕ) (hq : outerOnset A T1 T2 ≤ q) (i : Fin (k+1) ⊕ Fin (k+1)) :
    2 ≤ phaseCounts (resetTable A T1 T2) q i ∧
    2 ≤ phaseCounts (resetTable A T1 T2) (q - 1) i := by
  have hh := outerOnset_previous A T1 T2 q hq
  have hk : 0 < k := by have := P.order_ge_two; omega
  constructor
  · exact resetCounts_ge_two hk _ (actual_integer_leading A T1 T2 hv) q (by omega) i
  · exact resetCounts_ge_two hk _ (actual_integer_leading A T1 T2 hv) (q-1) hh i

/-- Both exact reset equations, with every denominator and compatibility
premise discharged by the actual scale-selection theorem. -/
theorem reset_equations (T1 T2 : ℕ) (hv : ValidParameters A T1 T2) (delta : ℚ) :
    let M := resetM k T1 T2 (lam A) A.referenceHeight A.correction
    let J := resetJ k T1 T2 (lam A) A.referenceHeight A.correction
      (FaithfulGain.AdmissibleGain.momentTable A (lam A) T1)
    actualCoupling A (lam A) T1 T2 * M =
      FaithfulTables.D P A.tau (FaithfulGain.AdmissibleGain.selectedGain A (lam A) T1)
        (baseline P) delta ∧
    (actualCoupling A (lam A) T1 T2)ᵀ * FaithfulTables.X P A.tau =
      Q_reset J M (B_mat (k+1))
        (FaithfulTables.zeta (P.R P.b) A.tau
          (FaithfulGain.AdmissibleGain.selectedGain A (lam A) T1) (baseline P)) := by
  apply actualCoupling_equations A (lam A) T1 T2 delta hv.first_pos hv.second_pos
    (by have := lam_pos A; omega)
  · have := hv.inverse_denominator
    linarith
  · intro _
    exact hv.gain_denominator.ne'

noncomputable def nextScale (T1 : ℕ) : ℕ :=
  FaithfulNextTables.nextScale k (by have := P.order_ge_two; omega)
    (FaithfulTables.S_mid P A.tau (FaithfulGain.AdmissibleGain.selectedGain A (lam A) T1)
      (baseline P) (endpointMargin A (lam A) T1)) (FaithfulTables.X P A.tau)
    (FaithfulTables.zeta (P.R P.b) A.tau
      (FaithfulGain.AdmissibleGain.selectedGain A (lam A) T1) (baseline P))
    A.referenceHeight A.correction T1 (lam A) (FaithfulGain.AdmissibleGain.momentTable A (lam A) T1)

/-- Exactly the least integer above the prescribed v15 radius. -/
noncomputable def secondScale (T1 : ℕ) : ℕ :=
  FaithfulNextTables.prescribedT2 P A.tau (FaithfulGain.AdmissibleGain.selectedGain A (lam A) T1)
    A.cref (baseline P) (endpointMargin A (lam A) T1) T1 (lam A) A.correction
    (FaithfulGain.AdmissibleGain.momentTable A (lam A) T1)

noncomputable def nextWeights (T1 : ℕ) :
    FaithfulTables.OldAct P ⊕ (Fin (k+1) ⊕ Fin (k+1)) → ℚ :=
  FaithfulNextTables.prescribedWeights P A.tau (FaithfulGain.AdmissibleGain.selectedGain A (lam A) T1)
    A.cref (baseline P) (endpointMargin A (lam A) T1) T1 (lam A) A.correction
    (FaithfulGain.AdmissibleGain.momentTable A (lam A) T1)

theorem secondScale_spec (T1 : ℕ) (hT1 : firstScale A ≤ T1) :
    T1 < secondScale A T1 ∧
    (T1 : ℚ) * lam A * A.referenceHeight (lastIdx k) < (secondScale A T1 : ℚ) ∧
    1 < secondScale A T1 ∧ (∀ i, 0 < nextWeights A T1 i) ∧ ∀ Hnext : ℚ,
      Matrix.vecMul (nextWeights A T1)
        (FaithfulNextTables.nextCounts (FaithfulTables.X P A.tau)
          (FaithfulNextTables.resetCounts k T1 (secondScale A T1) (lam A)
            A.referenceHeight A.correction)) =
      FaithfulNextTables.target (FaithfulTables.zeta (P.R P.b) A.tau
        (FaithfulGain.AdmissibleGain.selectedGain A (lam A) T1) (baseline P))
        (nextScale A T1) (1/2) Hnext := by
  have hv := firstScale_spec A T1 hT1 T1 le_rfl
  have hearly : 0 < (T1 : ℚ) * lam A * A.referenceHeight (lastIdx k) +
      A.correction (lastIdx k) := by
    have hh := (hv.reset_leading (0 : Fin (k+1))).1
    simpa only [Faithful.early_leading, Fin.val_zero, ite_true] using hh
  have hh := FaithfulNextTables.prescribedT2_weights_spec P A.tau A.tau_pos
    (FaithfulGain.AdmissibleGain.selectedGain A (lam A) T1) A.cref (baseline P)
    (endpointMargin A (lam A) T1) T1 (lam A)
    (by exact_mod_cast hv.first_pos) (by exact_mod_cast (lam_pos A : 0 < lam A))
    A.correction (FaithfulGain.AdmissibleGain.momentTable A (lam A) T1) hearly
  refine ⟨by exact_mod_cast hh.1, hh.2.1, by exact_mod_cast hh.2.2.1,
    hh.2.2.2.1, hh.2.2.2.2⟩

/-- Fully fixed reset scales with all parameter obligations discharged. -/
theorem chosen_valid : ValidParameters A (firstScale A) (secondScale A (firstScale A)) :=
  firstScale_spec A (firstScale A) le_rfl _ (secondScale_spec A _ le_rfl).1.le

noncomputable def chosenOnset : ℕ := outerOnset A (firstScale A) (secondScale A (firstScale A))

#print axioms uniform_parameters
#print axioms outerOnset_counts
#print axioms reset_equations
#print axioms secondScale_spec
#print axioms chosen_valid
end Karlin.FaithfulController
