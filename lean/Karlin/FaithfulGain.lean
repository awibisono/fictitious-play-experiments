import Karlin.FaithfulPaperCokernel
import Karlin.FaithfulBounds
import Karlin.FaithfulAdmissible

/-!
# v15 parity gain and bounded compatibility correction

The correction row is arbitrary, including its last coordinate. The first
part proves the exact border perturbation and all-test cancellation. The
quantitative part chooses one threshold before every reset scale.
Compatibility of the unchanged executable section is certified through the
PDF's nilpotent/exponential cokernel route.
-/
namespace Karlin.FaithfulGain
open scoped BigOperators Matrix
open FaithfulCokernel
set_option maxHeartbeats 1200000

def border {k : ℕ} (u v : Fin (k + 1) → ℚ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  outerProd (e0_row (k + 1)) u + outerProd v (e0_row (k + 1))

theorem border_pairing {k : ℕ}
    (Z : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) (u v : Fin (k + 1) → ℚ) :
    matInnerProd Z (border u v) =
      (∑ j, Z 0 j * u j) + ∑ i, Z i 0 * v i := by
  have he : ∀ i : Fin (k + 1), e0_row (k + 1) i = if i = 0 then 1 else 0 := by
    intro i
    simp only [e0_row, Fin.ext_iff, Fin.val_zero]
  rw [border, matInnerProd_add_right]
  congr 1
  · simp [matInnerProd, outerProd, he, ite_mul, mul_ite]
  · simp [matInnerProd, outerProd, he, mul_ite]

theorem higher_border_pairing_zero {k h : ℕ} (hh : k < h)
    (u v : Fin (k + 1) → ℚ) :
    matInnerProd (Z_binom_concrete (k + 1) h) (border u v) = 0 := by
  rw [border_pairing]
  have hr : ∀ j : Fin (k + 1), Z_binom_concrete (k + 1) h 0 j = 0 := by
    intro j
    apply Z_binom_concrete_support
    have := j.isLt
    simp only [Fin.val_zero]
    omega
  have hc : ∀ i : Fin (k + 1), Z_binom_concrete (k + 1) h i 0 = 0 := by
    intro i
    apply Z_binom_concrete_support
    have := i.isLt
    simp only [Fin.val_zero]
    omega
  simp only [hr, hc, zero_mul, Finset.sum_const_zero, add_zero]

theorem lowest_border_pairing {k : ℕ} (hk : Even k) (u v : Fin (k + 1) → ℚ) :
    matInnerProd (Z_binom_concrete (k + 1) k) (border u v) =
      u ⟨k, by omega⟩ + v ⟨k, by omega⟩ := by
  rw [border_pairing]
  have hr : (∑ j : Fin (k + 1), Z_binom_concrete (k + 1) k 0 j * u j) =
      u ⟨k, by omega⟩ := by
    rw [Finset.sum_eq_single ⟨k, by omega⟩]
    · rw [Z_binom_concrete_leading 0 ⟨k, by omega⟩ (by simp), Fin.val_zero, pow_zero, one_mul]
    · intro j _ hj
      have hne : j.val ≠ k := fun e => hj (Fin.ext e)
      rw [Z_binom_concrete_support 0 j (by simp only [Fin.val_zero]; have := j.isLt; omega), zero_mul]
    · simp
  have hc : (∑ i : Fin (k + 1), Z_binom_concrete (k + 1) k i 0 * v i) =
      v ⟨k, by omega⟩ := by
    rw [Finset.sum_eq_single ⟨k, by omega⟩]
    · rw [Z_binom_concrete_leading ⟨k, by omega⟩ 0 (by simp)]
      simp only [hk.neg_one_pow, one_mul]
    · intro i _ hi
      have hne : i.val ≠ k := fun e => hi (Fin.ext e)
      rw [Z_binom_concrete_support i 0 (by simp only [Fin.val_zero]; have := i.isLt; omega), zero_mul]
    · simp
  rw [hr, hc]

def totalCounts {k : ℕ} (ell0 ellStar : Fin (k + 1) → ℚ) (T : ℕ) : Fin (k + 1) → ℚ :=
  (T : ℚ) • ell0 + ellStar

def gainShift (k : ℕ) (N a b : ℚ) (T : ℕ) : ℚ :=
  if Even k then -N / (a * T + b) else 0

def gain (k : ℕ) (cref N a b : ℚ) (T : ℕ) : ℚ :=
  cref + gainShift k N a b T

def correctedResidual {k : ℕ}
    (F0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (u ell0 ellStar : Fin (k + 1) → ℚ) (T : ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  F0 + gainShift k (matInnerProd (Z_binom_concrete (k + 1) k) F0)
    (ell0 ⟨k, by omega⟩) (u ⟨k, by omega⟩ + ellStar ⟨k, by omega⟩) T •
      border u (totalCounts ell0 ellStar T)

/-- Exactly the higher tests supplied by admissibility, with no assumption on
ellStar's last coordinate, imply every corrected test. -/
theorem correctedResidual_all_tests {k : ℕ}
    (F0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (u ell0 ellStar : Fin (k + 1) → ℚ) (T : ℕ)
    (higher : ∀ h, k < h → h ≤ 2 * k → Even h →
      matInnerProd (Z_binom_concrete (k + 1) h) F0 = 0)
    (hden : Even k → ell0 ⟨k, by omega⟩ * T +
      (u ⟨k, by omega⟩ + ellStar ⟨k, by omega⟩) ≠ 0) :
    ∀ h, k ≤ h → h ≤ 2 * k → Even h →
      matInnerProd (Z_binom_concrete (k + 1) h)
        (correctedResidual F0 u ell0 ellStar T) = 0 := by
  intro h hlo hhi heven
  rw [correctedResidual, matInnerProd_add_right, matInnerProd_smul_right]
  by_cases hgt : k < h
  · rw [higher h hgt hhi heven, higher_border_pairing_zero hgt, mul_zero, add_zero]
  · have heq : h = k := by omega
    subst h
    rw [lowest_border_pairing heven, gainShift, if_pos heven]
    have hd : u ⟨k, by omega⟩ + totalCounts ell0 ellStar T ⟨k, by omega⟩ =
        ell0 ⟨k, by omega⟩ * T + (u ⟨k, by omega⟩ + ellStar ⟨k, by omega⟩) := by
      simp only [totalCounts, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hd, div_mul_cancel₀ _ (hden heven)]
    ring

#print axioms Karlin.FaithfulGain.correctedResidual_all_tests

/-- One integer threshold makes the affine parity denominator positive, the
actual gain admissible, and the gain error bounded by K/T. The intercept b is
arbitrary, so ellStar's last coordinate need not vanish. -/
theorem eventually_gain_bounds (k : ℕ) (cref N a b : ℚ)
    (hcref : 0 < cref ∧ cref < 1) (ha : 0 < a) :
    ∃ (K : ℚ) (T0 : ℕ), 0 ≤ K ∧ 1 ≤ T0 ∧ ∀ T : ℕ, T0 ≤ T →
      0 < a * T + b ∧ 0 < gain k cref N a b T ∧ gain k cref N a b T < 1 ∧
        |gainShift k N a b T| ≤ K / T := by
  let δ := min cref (1 - cref)
  have hδ : 0 < δ := lt_min hcref.1 (by linarith)
  let K := 2 * |N| / a
  have hK : 0 ≤ K := div_nonneg (by positivity) ha.le
  obtain ⟨T0, hT0⟩ := exists_nat_gt (max 1 (max (2 * |b| / a) (K / δ)))
  have hT01 : (1 : ℚ) < T0 := (le_max_left _ _).trans_lt hT0
  refine ⟨K, T0, hK, by exact_mod_cast hT01.le, ?_⟩
  intro T hT
  have hTcast : (T0 : ℚ) ≤ T := by exact_mod_cast hT
  have hTmax := hT0.trans_le hTcast
  have hTpos : (0 : ℚ) < T := by linarith
  have hTb : 2 * |b| / a < T :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hTmax
  have hTb' : 2 * |b| < (T : ℚ) * a := (div_lt_iff₀ ha).mp hTb
  have hdenlower : a * T / 2 ≤ a * T + b := by
    have hb := neg_abs_le b
    nlinarith
  have hden : 0 < a * T + b := lt_of_lt_of_le (by positivity) hdenlower
  have hKexact : K * a = 2 * |N| := by dsimp [K]; field_simp
  have hdc : |gainShift k N a b T| ≤ K / T := by
    by_cases hk : Even k
    · rw [gainShift, if_pos hk, abs_div, abs_neg, abs_of_pos hden]
      apply (div_le_div_iff₀ hden hTpos).mpr
      calc |N| * (T : ℚ) = (2 * |N|) * T / 2 := by ring
        _ = (K * a) * T / 2 := by rw [hKexact]
        _ = K * (a * T / 2) := by ring
        _ ≤ K * (a * T + b) := mul_le_mul_of_nonneg_left hdenlower hK
    · rw [gainShift, if_neg hk, abs_zero]
      exact div_nonneg hK hTpos.le
  have hTd : K / δ < T :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hTmax
  have hsmall : K / (T : ℚ) < δ := by
    apply (div_lt_iff₀ hTpos).mpr
    have hh := (div_lt_iff₀ hδ).mp hTd
    nlinarith
  have hdcsmall := abs_lt.mp (hdc.trans_lt hsmall)
  have hd1 : δ ≤ cref := min_le_left _ _
  have hd2 : δ ≤ 1 - cref := min_le_right _ _
  refine ⟨hden, ?_, ?_, hdc⟩ <;> dsimp [gain] <;> linarith

#print axioms Karlin.FaithfulGain.eventually_gain_bounds

/-- The exact residual identity, for arbitrary correction row. -/
theorem compatibility_residual_identity {o : Type*} [Fintype o] {k : ℕ}
    (D0 X : Matrix o (Fin (k + 1)) ℚ)
    (ell0 ellStar psi0 : Fin (k + 1) → ℚ)
    (E0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) (dc : ℚ) (T : ℕ)
    (hE0 : L_moment (B_mat (k + 1)) E0 = -outerProd ell0 psi0) :
    (D0 + dc • outerProd (fun _ : o => (1 : ℚ)) (e0_row (k + 1))).transpose * X -
        outerProd (totalCounts ell0 ellStar T) (psi0 - dc • e0_row (k + 1)) -
        (T : ℚ) • L_moment (B_mat (k + 1)) E0 =
      D0.transpose * X - outerProd ellStar psi0 +
        dc • border (Matrix.vecMul (fun _ : o => (1 : ℚ)) X) (totalCounts ell0 ellStar T) := by
  rw [hE0, Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul,
    Matrix.smul_mul, outerProd_transpose, outerProd_mul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.neg_apply, smul_eq_mul, border, outerProd, Matrix.of_apply,
    totalCounts, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

def residualBound {k : ℕ}
    (F0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (u ell0 ellStar : Fin (k + 1) → ℚ) (K : ℚ) : ℚ :=
  Faithful.entrySum F0 + K * (Faithful.entrySum (border u ellStar) +
    Faithful.entrySum (outerProd ell0 (e0_row (k + 1))))

theorem residualBound_nonneg {k : ℕ}
    (F0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (u ell0 ellStar : Fin (k + 1) → ℚ) (K : ℚ) (hK : 0 ≤ K) :
    0 ≤ residualBound F0 u ell0 ellStar K := by
  unfold residualBound
  exact add_nonneg (Faithful.entrySum_nonneg _)
    (mul_nonneg hK (add_nonneg (Faithful.entrySum_nonneg _) (Faithful.entrySum_nonneg _)))

/-- The gain estimate bounds the actual residual uniformly in T. -/
theorem correctedResidual_bound {k : ℕ}
    (F0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (u ell0 ellStar : Fin (k + 1) → ℚ) (T : ℕ) (K : ℚ)
    (hT : 1 ≤ T) (hK : 0 ≤ K)
    (hdc : |gainShift k (matInnerProd (Z_binom_concrete (k + 1) k) F0)
      (ell0 ⟨k, by omega⟩) (u ⟨k, by omega⟩ + ellStar ⟨k, by omega⟩) T| ≤ K / T) :
    Faithful.entrySum (correctedResidual F0 u ell0 ellStar T) ≤
      residualBound F0 u ell0 ellStar K := by
  let dc := gainShift k (matInnerProd (Z_binom_concrete (k + 1) k) F0)
    (ell0 ⟨k, by omega⟩) (u ⟨k, by omega⟩ + ellStar ⟨k, by omega⟩) T
  have hTq : (1 : ℚ) ≤ T := by exact_mod_cast hT
  have hTp : (0 : ℚ) < T := by linarith
  have hdc' : |dc| ≤ K := hdc.trans (div_le_self hK hTq)
  have hdcT : |dc * T| ≤ K := by
    rw [abs_mul, abs_of_pos hTp]
    have hh := mul_le_mul_of_nonneg_right hdc hTp.le
    rwa [div_mul_cancel₀ _ hTp.ne'] at hh
  have hexp : correctedResidual F0 u ell0 ellStar T =
      (F0 + dc • border u ellStar) + (dc * T) • outerProd ell0 (e0_row (k + 1)) := by
    ext i j
    simp only [correctedResidual, border, totalCounts, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, outerProd, Matrix.of_apply, Pi.add_apply,
      Pi.smul_apply, dc]
    ring
  rw [hexp]
  calc Faithful.entrySum ((F0 + dc • border u ellStar) +
      (dc * T) • outerProd ell0 (e0_row (k + 1)))
      ≤ Faithful.entrySum (F0 + dc • border u ellStar) +
        Faithful.entrySum ((dc * T) • outerProd ell0 (e0_row (k + 1))) :=
          Faithful.entrySum_add_le _ _
    _ ≤ (Faithful.entrySum F0 + |dc| * Faithful.entrySum (border u ellStar)) +
        |dc * T| * Faithful.entrySum (outerProd ell0 (e0_row (k + 1))) := by
      rw [Faithful.entrySum_smul]
      have hb := Faithful.entrySum_add_le F0 (dc • border u ellStar)
      rw [Faithful.entrySum_smul] at hb
      exact add_le_add hb le_rfl
    _ ≤ (Faithful.entrySum F0 + K * Faithful.entrySum (border u ellStar)) +
        K * Faithful.entrySum (outerProd ell0 (e0_row (k + 1))) := by
      exact add_le_add
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hdc' (Faithful.entrySum_nonneg _)))
        (mul_le_mul_of_nonneg_right hdcT (Faithful.entrySum_nonneg _))
    _ = residualBound F0 u ell0 ellStar K := by unfold residualBound; ring

#print axioms Karlin.FaithfulGain.compatibility_residual_identity
#print axioms Karlin.FaithfulGain.correctedResidual_bound

/-- Uniform Proposition 7.1 algebra: all choices precede all integer reset
scales; compatibility and the bounded correction are derived together. -/
theorem eventually_gain_and_bounded_correction {k : ℕ}
    (F0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (u ell0 ellStar : Fin (k + 1) → ℚ) (cref : ℚ)
    (hcref : 0 < cref ∧ cref < 1) (htop : 0 < ell0 ⟨k, by omega⟩)
    (higher : ∀ h, k < h → h ≤ 2 * k → Even h →
      matInnerProd (Z_binom_concrete (k + 1) h) F0 = 0) :
    let N := matInnerProd (Z_binom_concrete (k + 1) k) F0
    let a := ell0 ⟨k, by omega⟩
    let b := u ⟨k, by omega⟩ + ellStar ⟨k, by omega⟩
    ∃ (K KE : ℚ) (T0 : ℕ), 0 ≤ K ∧ 0 ≤ KE ∧ 1 ≤ T0 ∧ ∀ T : ℕ, T0 ≤ T →
      0 < a * T + b ∧ 0 < gain k cref N a b T ∧ gain k cref N a b T < 1 ∧
      |gainShift k N a b T| ≤ K / T ∧
      L_moment (B_mat (k + 1)) (momentSection k (correctedResidual F0 u ell0 ellStar T)) =
        correctedResidual F0 u ell0 ellStar T ∧
      Faithful.entrySum (momentSection k (correctedResidual F0 u ell0 ellStar T)) ≤ KE := by
  intro N a b
  obtain ⟨K, T0, hK, hT0, hall⟩ := eventually_gain_bounds k cref N a b hcref htop
  let M := residualBound F0 u ell0 ellStar K
  let KE := momentSectionBound k * M
  have hM : 0 ≤ M := residualBound_nonneg F0 u ell0 ellStar K hK
  have hKE : 0 ≤ KE := mul_nonneg (momentSectionBound_nonneg k) hM
  refine ⟨K, KE, T0, hK, hKE, hT0, ?_⟩
  intro T hT
  obtain ⟨hden, hcl, hcu, hdc⟩ := hall T hT
  have ht := correctedResidual_all_tests F0 u ell0 ellStar T higher (fun _ => hden.ne')
  have hsolve := FaithfulPaperCokernel.paper_momentSection_solves k _ ht
  have hr := correctedResidual_bound F0 u ell0 ellStar T K (hT0.trans hT) hK hdc
  have hb := momentSection_bound k (correctedResidual F0 u ell0 ellStar T)
  refine ⟨hden, hcl, hcu, hdc, hsolve, ?_⟩
  exact hb.trans (mul_le_mul_of_nonneg_left hr (momentSectionBound_nonneg k))

/-- The paper keeps the T*E0 leading term and applies the section only to the
explicit corrected residual. -/
noncomputable def correctedMoment {k : ℕ}
    (E0 F0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (u ell0 ellStar : Fin (k + 1) → ℚ) (T : ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  (T : ℚ) • E0 + momentSection k (correctedResidual F0 u ell0 ellStar T)

theorem correctedMoment_spec {k : ℕ}
    (E0 F0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (u ell0 ellStar : Fin (k + 1) → ℚ) (T : ℕ)
    (higher : ∀ h, k < h → h ≤ 2 * k → Even h →
      matInnerProd (Z_binom_concrete (k + 1) h) F0 = 0)
    (hden : Even k → ell0 ⟨k, by omega⟩ * T +
      (u ⟨k, by omega⟩ + ellStar ⟨k, by omega⟩) ≠ 0) :
    L_moment (B_mat (k + 1)) (correctedMoment E0 F0 u ell0 ellStar T) =
      (T : ℚ) • L_moment (B_mat (k + 1)) E0 + correctedResidual F0 u ell0 ellStar T := by
  change momentLinear (B_mat (k + 1))
    ((T : ℚ) • E0 + momentSection k (correctedResidual F0 u ell0 ellStar T)) = _
  rw [map_add, map_smul]
  change (T : ℚ) • L_moment (B_mat (k + 1)) E0 +
    L_moment (B_mat (k + 1)) (momentSection k (correctedResidual F0 u ell0 ellStar T)) = _
  rw [FaithfulPaperCokernel.paper_momentSection_solves k _
    (correctedResidual_all_tests F0 u ell0 ellStar T higher hden)]

/-- Exact compatibility for the explicitly gain-perturbed score/count tables. -/
theorem correctedMoment_solves_perturbed_tables {o : Type*} [Fintype o] {k : ℕ}
    (D0 X : Matrix o (Fin (k + 1)) ℚ)
    (ell0 ellStar psi0 : Fin (k + 1) → ℚ)
    (E0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) (T : ℕ)
    (hE0 : L_moment (B_mat (k + 1)) E0 = -outerProd ell0 psi0)
    (higher : ∀ h, k < h → h ≤ 2 * k → Even h →
      matInnerProd (Z_binom_concrete (k + 1) h) (D0.transpose * X - outerProd ellStar psi0) = 0)
    (hden : Even k → ell0 ⟨k, by omega⟩ * T +
      ((Matrix.vecMul (fun _ : o => (1 : ℚ)) X) ⟨k, by omega⟩ + ellStar ⟨k, by omega⟩) ≠ 0) :
    let F0 := D0.transpose * X - outerProd ellStar psi0
    let u := Matrix.vecMul (fun _ : o => (1 : ℚ)) X
    let dc := gainShift k (matInnerProd (Z_binom_concrete (k + 1) k) F0)
      (ell0 ⟨k, by omega⟩) (u ⟨k, by omega⟩ + ellStar ⟨k, by omega⟩) T
    L_moment (B_mat (k + 1)) (correctedMoment E0 F0 u ell0 ellStar T) =
      (D0 + dc • outerProd (fun _ : o => (1 : ℚ)) (e0_row (k + 1))).transpose * X -
        outerProd (totalCounts ell0 ellStar T) (psi0 - dc • e0_row (k + 1)) := by
  intro F0 u dc
  rw [correctedMoment_spec E0 F0 u ell0 ellStar T higher hden]
  have hi := compatibility_residual_identity D0 X ell0 ellStar psi0 E0 dc T hE0
  change _ - (T : ℚ) • L_moment (B_mat (k + 1)) E0 =
    correctedResidual F0 u ell0 ellStar T at hi
  rw [← hi]
  abel

#print axioms Karlin.FaithfulGain.eventually_gain_and_bounded_correction
#print axioms Karlin.FaithfulGain.correctedMoment_solves_perturbed_tables

namespace AdmissibleGain
open FaithfulAdmissible
variable {k : ℕ} {P : FaithfulClock.Clock k} (A : Admissible P)

/-- The manuscript's reference residual, on the actual old-action tables. -/
def referenceResidual : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  (FaithfulTables.D P A.tau A.cref (baseline P) 0).transpose * FaithfulTables.X P A.tau -
    outerProd A.correction (FaithfulTables.psi (P.R P.b) A.tau A.cref (baseline P))

def oldTotals : Fin (k + 1) → ℚ :=
  Matrix.vecMul (fun _ : FaithfulTables.OldAct P => (1 : ℚ)) (FaithfulTables.X P A.tau)

def baselineCounts (lam : ℕ) : Fin (k + 1) → ℚ :=
  (2 * (k + 1 : ℚ) * lam) • A.referenceHeight

def selectedGain (lam T : ℕ) : ℚ :=
  gain k A.cref (matInnerProd (Z_binom_concrete (k + 1) k) (referenceResidual A))
    (baselineCounts A lam ⟨k, by omega⟩)
    (oldTotals A ⟨k, by omega⟩ + A.correction ⟨k, by omega⟩) T

noncomputable def momentTable (lam T : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  correctedMoment (Faithful.paperE0 k lam A.referenceHeight) (referenceResidual A)
    (oldTotals A) (baselineCounts A lam) A.correction T

theorem baselineCounts_top_positive (lam : ℕ) (hlam : 1 ≤ lam) :
    0 < baselineCounts A lam ⟨k, by omega⟩ := by
  have hz := A.reference_leading_pos
  have hl : (0 : ℚ) < lam := by exact_mod_cast (show 0 < lam by omega)
  change 0 < (2 * (k + 1 : ℚ) * lam) * A.referenceHeight (Fin.last k)
  exact mul_pos (mul_pos (by positivity) hl) hz

theorem baseline_moment (lam : ℕ) :
    L_moment (B_mat (k + 1)) (Faithful.paperE0 k lam A.referenceHeight) =
      -outerProd (baselineCounts A lam)
        (FaithfulTables.psi (P.R P.b) A.tau A.cref (baseline P)) := by
  have he : Faithful.paperE0 k lam A.referenceHeight =
      outerProd (baselineCounts A lam) A.referenceHeight := by
    ext i j
    simp only [Faithful.paperE0, baselineCounts, Matrix.smul_apply,
      Pi.smul_apply, smul_eq_mul, outerProd, Matrix.of_apply]
    ring
  rw [he]
  exact L_moment_rank1_symmetric (B_mat (k + 1)) A.referenceHeight (2 * (k + 1 : ℚ) * lam)

theorem selectedGain_sub_reference (lam T : ℕ) :
    selectedGain A lam T - A.cref =
      gainShift k (matInnerProd (Z_binom_concrete (k + 1) k) (referenceResidual A))
        (baselineCounts A lam ⟨k, by omega⟩)
        (oldTotals A ⟨k, by omega⟩ + A.correction ⟨k, by omega⟩) T := by
  unfold selectedGain gain
  ring

/-- Exact moment equation for the actual v15 D and psi, independently of the
endpoint margin delta. Higher tests come directly from Admissible. -/
theorem momentTable_solves (lam T : ℕ) (delta : ℚ)
    (hden : Even k → baselineCounts A lam ⟨k, by omega⟩ * T +
      (oldTotals A ⟨k, by omega⟩ + A.correction ⟨k, by omega⟩) ≠ 0) :
    L_moment (B_mat (k + 1)) (momentTable A lam T) =
      (FaithfulTables.D P A.tau (selectedGain A lam T) (baseline P) delta).transpose *
        FaithfulTables.X P A.tau -
      outerProd (totalCounts (baselineCounts A lam) A.correction T)
        (FaithfulTables.psi (P.R P.b) A.tau (selectedGain A lam T) (baseline P)) := by
  let dc := selectedGain A lam T - A.cref
  have hd : FaithfulTables.D P A.tau (selectedGain A lam T) (baseline P) delta =
      FaithfulTables.D P A.tau A.cref (baseline P) 0 +
        dc • outerProd (fun _ : FaithfulTables.OldAct P => (1 : ℚ)) (e0_row (k + 1)) := by
    rw [FaithfulTables.D_independent_delta P A.tau (selectedGain A lam T) (baseline P) delta 0]
    have hh := FaithfulTables.D_sub_gain P A.tau (selectedGain A lam T) A.cref (baseline P) 0
    calc _ = (FaithfulTables.D P A.tau (selectedGain A lam T) (baseline P) 0 -
        FaithfulTables.D P A.tau A.cref (baseline P) 0) +
        FaithfulTables.D P A.tau A.cref (baseline P) 0 := by abel
      _ = _ := by rw [hh]; abel
  have hp : FaithfulTables.psi (P.R P.b) A.tau (selectedGain A lam T) (baseline P) =
      FaithfulTables.psi (P.R P.b) A.tau A.cref (baseline P) - dc • e0_row (k + 1) := by
    have hh := FaithfulTables.psi_sub_gain (by have := P.order_ge_two; omega)
      (P.R P.b) A.tau (selectedGain A lam T) A.cref (baseline P)
    calc _ = (FaithfulTables.psi (P.R P.b) A.tau (selectedGain A lam T) (baseline P) -
        FaithfulTables.psi (P.R P.b) A.tau A.cref (baseline P)) +
        FaithfulTables.psi (P.R P.b) A.tau A.cref (baseline P) := by abel
      _ = _ := by rw [hh]; simp only [neg_smul]; dsimp [dc]; abel
  rw [hd, hp]
  have hs := correctedMoment_solves_perturbed_tables
    (FaithfulTables.D P A.tau A.cref (baseline P) 0) (FaithfulTables.X P A.tau)
    (baselineCounts A lam) A.correction
    (FaithfulTables.psi (P.R P.b) A.tau A.cref (baseline P))
    (Faithful.paperE0 k lam A.referenceHeight) T (baseline_moment A lam) A.higher_tests hden
  dsimp only at hs
  rw [show dc = _ from selectedGain_sub_reference A lam T]
  exact hs

/-- Proposition 7.1 on actual admissible parent data, with fixed constants and
one threshold before all scales, and no zero-last correction restriction. -/
theorem eventually_momentTable (lam : ℕ) (hlam : 1 ≤ lam) :
    ∃ (K KE : ℚ) (T0 : ℕ), 0 ≤ K ∧ 0 ≤ KE ∧ 1 ≤ T0 ∧ ∀ T : ℕ, T0 ≤ T →
      0 < baselineCounts A lam ⟨k, by omega⟩ * T +
        (oldTotals A ⟨k, by omega⟩ + A.correction ⟨k, by omega⟩) ∧
      0 < selectedGain A lam T ∧ selectedGain A lam T < 1 ∧
      |selectedGain A lam T - A.cref| ≤ K / T ∧
      (∀ delta : ℚ, L_moment (B_mat (k + 1)) (momentTable A lam T) =
        (FaithfulTables.D P A.tau (selectedGain A lam T) (baseline P) delta).transpose *
          FaithfulTables.X P A.tau -
        outerProd (totalCounts (baselineCounts A lam) A.correction T)
          (FaithfulTables.psi (P.R P.b) A.tau (selectedGain A lam T) (baseline P))) ∧
      Faithful.entrySum (momentTable A lam T -
        (T : ℚ) • Faithful.paperE0 k lam A.referenceHeight) ≤ KE := by
  obtain ⟨K, KE, T0, hK, hKE, hT0, hall⟩ :=
    eventually_gain_and_bounded_correction (referenceResidual A) (oldTotals A)
      (baselineCounts A lam) A.correction A.cref ⟨A.cref_pos, A.cref_lt_one⟩
      (baselineCounts_top_positive A lam hlam) A.higher_tests
  refine ⟨K, KE, T0, hK, hKE, hT0, ?_⟩
  intro T hT
  obtain ⟨hden, hcl, hcu, hdc, _, hb⟩ := hall T hT
  refine ⟨hden, hcl, hcu, ?_, ?_, ?_⟩
  · rwa [selectedGain_sub_reference]
  · intro delta
    exact momentTable_solves A lam T delta (fun _ => hden.ne')
  · have he : momentTable A lam T - (T : ℚ) • Faithful.paperE0 k lam A.referenceHeight =
        momentSection k (correctedResidual (referenceResidual A) (oldTotals A)
          (baselineCounts A lam) A.correction T) := by
      unfold momentTable correctedMoment
      abel
    rwa [he]

#print axioms Karlin.FaithfulGain.AdmissibleGain.eventually_momentTable
end AdmissibleGain
end Karlin.FaithfulGain
