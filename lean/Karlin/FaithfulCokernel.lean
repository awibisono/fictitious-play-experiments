import Karlin.PaperProof
import Mathlib.LinearAlgebra.Dual.Lemmas
import Karlin.FaithfulEffectiveLinear

/-!
# Complete rational compatibility tests

This file proves the full rational basis and solvability statement of v15 Lemma `lem:cokernel`.
The completeness proof works in binomial coordinates, using `T = I + N`
and anti-diagonal elimination. This is an algebraic proof of the paper's
stated basis and solvability criterion, with no solvability premise.

It also constructs a fixed rational linear section by terminating search over
a decidable finite rational certificate, and proves an explicit finite coefficient
bound. Existence proofs are erased; the section data are selected by executable
Encodable.choose (Nat.find), not Classical.choose.
-/

namespace Karlin
namespace FaithfulCokernel

open scoped BigOperators Matrix

theorem leading_support_mul {w h : ℕ} (A Z : Matrix (Fin w) (Fin w) ℚ)
    (hA : ∀ i j : Fin w, i.val < j.val → A i j = 0)
    (hZ : ∀ i j : Fin w, i.val + j.val < h → Z i j = 0)
    (i j : Fin w) (hij : i.val + j.val < h) : (A * Z) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hil : i.val < l.val
  · rw [hA i l hil, zero_mul]
  · rw [hZ l j (by omega), mul_zero]

theorem leading_support_mul_transpose {w h : ℕ} (A Z : Matrix (Fin w) (Fin w) ℚ)
    (hA : ∀ i j : Fin w, i.val < j.val → A i j = 0)
    (hZ : ∀ i j : Fin w, i.val + j.val < h → Z i j = 0)
    (i j : Fin w) (hij : i.val + j.val < h) : (Z * A.transpose) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hjl : j.val < l.val
  · rw [Matrix.transpose_apply, hA j l hjl, mul_zero]
  · rw [hZ i l (by omega), zero_mul]

theorem leading_value_mul {w h : ℕ} (A Z : Matrix (Fin w) (Fin w) ℚ)
    (hA : ∀ i j : Fin w, i.val < j.val → A i j = 0)
    (hdiag : ∀ i, A i i = 1)
    (hZ : ∀ i j : Fin w, i.val + j.val < h → Z i j = 0)
    (i j : Fin w) (hij : i.val + j.val = h) : (A * Z) i j = Z i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hdiag, one_mul]
  · intro l _ hli
    by_cases hil : i.val < l.val
    · rw [hA i l hil, zero_mul]
    · have hlt : l.val < i.val := by
        have hne : l.val ≠ i.val := fun e => hli (Fin.ext e)
        omega
      rw [hZ l j (by omega), mul_zero]
  · simp

theorem leading_value_mul_transpose {w h : ℕ} (A Z : Matrix (Fin w) (Fin w) ℚ)
    (hA : ∀ i j : Fin w, i.val < j.val → A i j = 0)
    (hdiag : ∀ i, A i i = 1)
    (hZ : ∀ i j : Fin w, i.val + j.val < h → Z i j = 0)
    (i j : Fin w) (hij : i.val + j.val = h) : (Z * A.transpose) i j = Z i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.transpose_apply, hdiag, mul_one]
  · intro l _ hlj
    by_cases hjl : j.val < l.val
    · rw [Matrix.transpose_apply, hA j l hjl, mul_zero]
    · have hlt : l.val < j.val := by
        have hne : l.val ≠ j.val := fun e => hlj (Fin.ext e)
        omega
      rw [hZ i l (by omega), zero_mul]
  · simp

theorem Z_binom_concrete_support {w h : ℕ} (i j : Fin w)
    (hij : i.val + j.val < h) : Z_binom_concrete w h i j = 0 := by
  apply leading_support_mul_transpose (S_mat w) (S_mat w * Z_DP w h)
    (fun _ _ hlt => S_mat_eq_zero_of_lt hlt)
  · exact leading_support_mul (S_mat w) (Z_DP w h)
      (fun _ _ hlt => S_mat_eq_zero_of_lt hlt)
      (fun _ _ hlt => Z_DP_apply_of_add_lt hlt)
  · exact hij

theorem Z_binom_concrete_leading {w h : ℕ} (i j : Fin w)
    (hij : i.val + j.val = h) : Z_binom_concrete w h i j = (-1 : ℚ) ^ i.val := by
  change ((S_mat w * Z_DP w h) * (S_mat w).transpose) i j = _
  rw [leading_value_mul_transpose (S_mat w) (S_mat w * Z_DP w h)
    (fun _ _ hlt => S_mat_eq_zero_of_lt hlt) (S_mat_diag_eq_one)
    (leading_support_mul (S_mat w) (Z_DP w h)
      (fun _ _ hlt => S_mat_eq_zero_of_lt hlt)
      (fun _ _ hlt => Z_DP_apply_of_add_lt hlt)) i j hij]
  rw [leading_value_mul (S_mat w) (Z_DP w h)
    (fun _ _ hlt => S_mat_eq_zero_of_lt hlt) (S_mat_diag_eq_one)
    (fun _ _ hlt => Z_DP_apply_of_add_lt hlt) i j hij]
  exact Z_DP_apply_antidiag hij

/-- Multiplying the adjoint equation by the forward shift. -/
theorem transpose_eq_shift_mul {w : ℕ} (Z : Matrix (Fin w) (Fin w) ℚ)
    (hZ : L_adjoint (B_mat w) Z = 0) :
    Z.transpose = (1 + N_mat w) * Z := by
  have hz : Z = B_mat w * Z.transpose := sub_eq_zero.mp hZ
  calc Z.transpose = 1 * Z.transpose := (Matrix.one_mul _).symm
    _ = ((1 + N_mat w) * B_mat w) * Z.transpose := by rw [one_add_N_mul_B_mat]
    _ = (1 + N_mat w) * Z := by rw [Matrix.mul_assoc, ← hz]

theorem adjoint_recurrence_matrix {w : ℕ} (Z : Matrix (Fin w) (Fin w) ℚ)
    (hZ : L_adjoint (B_mat w) Z = 0) :
    N_mat w * Z + Z * (N_mat w).transpose +
      N_mat w * Z * (N_mat w).transpose = 0 := by
  have ht := transpose_eq_shift_mul Z hZ
  have ht' := congrArg Matrix.transpose ht
  simp only [Matrix.transpose_transpose, Matrix.transpose_mul,
    Matrix.transpose_add, Matrix.transpose_one] at ht'
  rw [ht] at ht'
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one,
    Matrix.add_mul] at ht'
  apply add_left_cancel (a := Z)
  rw [add_zero]
  calc Z + (N_mat w * Z + Z * (N_mat w).transpose +
      N_mat w * Z * (N_mat w).transpose) =
      Z + N_mat w * Z + (Z * (N_mat w).transpose +
        N_mat w * Z * (N_mat w).transpose) := by abel
    _ = Z := ht'.symm


/-- Rational linear moment operator, with no compatibility premises. -/
def momentLinear {w : Type*} [Fintype w] (B : Matrix w w ℚ) :
    Matrix w w ℚ →ₗ[ℚ] Matrix w w ℚ where
  toFun := L_moment B
  map_add' E F := by
    dsimp [L_moment]
    rw [Matrix.transpose_add, Matrix.add_mul]
    abel
  map_smul' c E := by
    dsimp [L_moment]
    rw [Matrix.transpose_smul, Matrix.smul_mul, smul_sub]

/-- Standard matrix unit. -/
def matrixUnit {w : Type*} [DecidableEq w] (i j : w) : Matrix w w ℚ :=
  fun a b => if a = i ∧ b = j then 1 else 0

theorem matrixUnit_pairing {w : Type*} [Fintype w] [DecidableEq w]
    (Z : Matrix w w ℚ) (i j : w) : matInnerProd Z (matrixUnit i j) = Z i j := by
  simp [matInnerProd, matrixUnit, ite_and, mul_ite]

theorem matrixUnit_expansion {w : Type*} [Fintype w] [DecidableEq w]
    (E : Matrix w w ℚ) : (∑ i, ∑ j, E i j • matrixUnit i j) = E := by
  ext a b
  simp [matrixUnit, ite_and, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    mul_ite]

/-- Every rational dual functional is represented by the matrix pairing. -/
theorem dual_matrix_representation {w : Type*} [Fintype w] [DecidableEq w]
    (φ : Module.Dual ℚ (Matrix w w ℚ)) (E : Matrix w w ℚ) :
    matInnerProd (fun i j => φ (matrixUnit i j)) E = φ E := by
  conv_rhs => rw [← matrixUnit_expansion E]
  simp only [map_sum, map_smul, smul_eq_mul, matInnerProd]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The full adjoint-kernel criterion is sufficient over the original field ℚ. -/
theorem moment_solvable_iff_all_adjoint_tests {w : Type*} [Fintype w]
    (B F : Matrix w w ℚ) :
    (∃ E : Matrix w w ℚ, L_moment B E = F) ↔
      ∀ Z : Matrix w w ℚ, L_adjoint B Z = 0 → matInnerProd Z F = 0 := by
  classical
  constructor
  · rintro ⟨E, rfl⟩ Z hZ
    exact L_orthogonality B E Z hZ
  · intro h
    have hmem : F ∈ LinearMap.range (momentLinear B) := by
      apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
        (LinearMap.range (momentLinear B)) F).mp
      intro φ hφ
      let Z : Matrix w w ℚ := fun i j => φ (matrixUnit i j)
      have hZ : L_adjoint B Z = 0 := by
        ext i j
        have hz := (Submodule.mem_dualAnnihilator φ).mp hφ
          (L_moment B (matrixUnit i j)) ⟨matrixUnit i j, rfl⟩
        rw [← dual_matrix_representation φ, matInnerProd_L_adjoint,
          matrixUnit_pairing] at hz
        exact hz
      simpa only [Z, dual_matrix_representation] using h Z hZ
    exact hmem

#print axioms Karlin.FaithfulCokernel.moment_solvable_iff_all_adjoint_tests


/-- Entrywise subdiagonal action, including the boundary row. -/
theorem N_mul_entry {w : ℕ} (Z : Matrix (Fin w) (Fin w) ℚ) (i j : Fin w) :
    (N_mat w * Z) i j =
      if hi : 0 < i.val then Z ⟨i.val - 1, by omega⟩ j else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : 0 < i.val
  · rw [dif_pos hi]
    exact sum_single_pred i hi (fun a => Z a j)
  · rw [dif_neg hi]
    apply Finset.sum_eq_zero
    intro a _
    have ha : i.val ≠ a.val + 1 := by omega
    simp [N_mat, ha]

theorem mul_N_transpose_entry {w : ℕ} (Z : Matrix (Fin w) (Fin w) ℚ) (i j : Fin w) :
    (Z * (N_mat w).transpose) i j =
      if hj : 0 < j.val then Z i ⟨j.val - 1, by omega⟩ else 0 := by
  rw [Matrix.mul_apply]
  by_cases hj : 0 < j.val
  · rw [dif_pos hj]
    exact sum_single_pred_right j hj (fun a => Z i a)
  · rw [dif_neg hj]
    apply Finset.sum_eq_zero
    intro a _
    have ha : j.val ≠ a.val + 1 := by omega
    simp [N_mat, ha]

def leadingSlice {w : ℕ} (Z : Matrix (Fin w) (Fin w) ℚ) (h : ℕ) :
    Matrix (Fin w) (Fin w) ℚ := fun i j => if i.val + j.val = h then Z i j else 0

theorem leadingSlice_symmetric {w h : ℕ} (Z : Matrix (Fin w) (Fin w) ℚ)
    (hZ : L_adjoint (B_mat w) Z = 0)
    (hlow : ∀ i j : Fin w, i.val + j.val < h → Z i j = 0) :
    (leadingSlice Z h).transpose = leadingSlice Z h := by
  ext i j
  have ht := congrArg (fun M : Matrix (Fin w) (Fin w) ℚ => M i j)
    (transpose_eq_shift_mul Z hZ)
  dsimp only at ht
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, N_mul_entry] at ht
  simp only [Matrix.transpose_apply, leadingSlice]
  by_cases hij : i.val + j.val = h
  · rw [if_pos hij, if_pos (by omega : j.val + i.val = h)]
    by_cases hi : 0 < i.val
    · have hp : Z ⟨i.val - 1, by omega⟩ j = 0 := hlow _ _ (by change i.val - 1 + j.val < h; omega)
      rw [dif_pos hi, hp, add_zero] at ht
      exact ht
    · simpa only [dif_neg hi, add_zero] using ht
  · rw [if_neg hij, if_neg (by omega : j.val + i.val ≠ h)]

theorem leadingSlice_derivation {w h : ℕ} (Z : Matrix (Fin w) (Fin w) ℚ)
    (hZ : L_adjoint (B_mat w) Z = 0)
    (hlow : ∀ i j : Fin w, i.val + j.val < h → Z i j = 0) :
    N0_mat w * leadingSlice Z h + leadingSlice Z h * (N0_mat w).transpose = 0 := by
  change N_mat w * leadingSlice Z h + leadingSlice Z h * (N_mat w).transpose = 0
  ext i j
  have hr := congrArg (fun M : Matrix (Fin w) (Fin w) ℚ => M i j)
    (adjoint_recurrence_matrix Z hZ)
  simp only [Matrix.add_apply, Matrix.zero_apply] at hr ⊢
  rw [N_mul_entry, mul_N_transpose_entry] at hr ⊢
  rw [mul_N_transpose_entry] at hr
  by_cases hi : 0 < i.val <;> by_cases hj : 0 < j.val
  · simp only [dif_pos hi, dif_pos hj] at hr ⊢
    rw [N_mul_entry, dif_pos hi] at hr
    by_cases hij : i.val + j.val = h + 1
    · have hh : Z ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ = 0 :=
        hlow _ _ (by dsimp; omega)
      rw [hh, add_zero] at hr
      simpa only [leadingSlice, if_pos (by omega : i.val - 1 + j.val = h),
        if_pos (by omega : i.val + (j.val - 1) = h)] using hr
    · simp only [leadingSlice, if_neg (by omega : i.val - 1 + j.val ≠ h),
        if_neg (by omega : i.val + (j.val - 1) ≠ h), add_zero]
  · simp only [dif_pos hi, dif_neg hj, add_zero] at hr ⊢
    by_cases hij : i.val - 1 + j.val = h
    · simpa only [leadingSlice, if_pos hij] using hr
    · simp only [leadingSlice, if_neg hij]
  · simp only [dif_neg hi, dif_pos hj, zero_add] at hr ⊢
    rw [N_mul_entry, dif_neg hi, add_zero] at hr
    by_cases hij : i.val + (j.val - 1) = h
    · simpa only [leadingSlice, if_pos hij] using hr
    · simp only [leadingSlice, if_neg hij]
  · simp only [dif_neg hi, dif_neg hj, add_zero]


/-- Propagate the alternating recurrence any finite distance along an anti-diagonal. -/
theorem N0_chain {w : ℕ} (V : Matrix (Fin w) (Fin w) ℚ)
    (hD : N0_mat w * V + V * (N0_mat w).transpose = 0)
    (t : ℕ) (i j : Fin w) (ht : t ≤ j.val) (hi : i.val + t < w) :
    V i j = (-1 : ℚ) ^ t * V ⟨i.val + t, hi⟩ ⟨j.val - t, by omega⟩ := by
  induction t generalizing i j with
  | zero => simp
  | succ t ih =>
    have hi1 : i.val + 1 < w := by omega
    have hj : 0 < j.val := by omega
    have hs := N0_step V hD i hi1 j
    rw [dif_pos hj] at hs
    have hc := ih ⟨i.val + 1, hi1⟩ ⟨j.val - 1, by omega⟩
      (by change t ≤ j.val - 1; omega) (by change i.val + 1 + t < w; omega)
    have hei : i.val + 1 + t = i.val + (t + 1) := by omega
    have hej : j.val - 1 - t = j.val - (t + 1) := by omega
    simp only [hei, hej] at hc
    rw [hc] at hs
    rw [pow_succ]
    linarith

/-- Symmetry removes every odd anti-diagonal of the derivation kernel. -/
theorem symmetric_derivation_odd_zero {w : ℕ} (V : Matrix (Fin w) (Fin w) ℚ)
    (hS : V.transpose = V)
    (hD : N0_mat w * V + V * (N0_mat w).transpose = 0)
    (i j : Fin w) (hodd : ¬ Even (i.val + j.val)) : V i j = 0 := by
  have aux : ∀ (a b : Fin w), a.val ≤ b.val → ¬ Even (a.val + b.val) → V a b = 0 := by
    intro a b hab ho
    have hc := N0_chain V hD (b.val - a.val) a b (by omega) (by omega)
    have ha : a.val + (b.val - a.val) = b.val := by omega
    have hb : b.val - (b.val - a.val) = a.val := by omega
    simp only [ha, hb, Fin.eta] at hc
    have hn : ¬ Even (b.val - a.val) := by
      rintro ⟨n, hn⟩
      apply ho
      exact ⟨n + a.val, by omega⟩
    rw [neg_one_pow_eq_ite, if_neg hn] at hc
    have hs : V b a = V a b := congrArg (fun M : Matrix (Fin w) (Fin w) ℚ => M a b) hS
    rw [hs] at hc
    linarith
  by_cases hij : i.val ≤ j.val
  · exact aux i j hij hodd
  · have hz := aux j i (by omega) (by simpa only [Nat.add_comm] using hodd)
    have hs : V j i = V i j := congrArg (fun M : Matrix (Fin w) (Fin w) ℚ => M i j) hS
    rwa [hs] at hz

/-- Even anti-diagonals are determined by their central diagonal entry. -/
theorem symmetric_derivation_even_value {w m : ℕ} (V : Matrix (Fin w) (Fin w) ℚ)
    (hS : V.transpose = V)
    (hD : N0_mat w * V + V * (N0_mat w).transpose = 0)
    (hm : m < w) (i j : Fin w) (hij : i.val + j.val = m + m) :
    V i j = ((-1 : ℚ) ^ m * V ⟨m, hm⟩ ⟨m, hm⟩) * (-1 : ℚ) ^ i.val := by
  have aux : ∀ (a b : Fin w), a.val ≤ m → a.val + b.val = m + m →
      V a b = ((-1 : ℚ) ^ m * V ⟨m, hm⟩ ⟨m, hm⟩) * (-1 : ℚ) ^ a.val := by
    intro a b ham hab
    have hc := N0_chain V hD (m - a.val) a b (by omega) (by omega)
    have ha : a.val + (m - a.val) = m := by omega
    have hb : b.val - (m - a.val) = m := by omega
    simp only [ha, hb] at hc
    rw [hc]
    have hp : (-1 : ℚ) ^ (m - a.val) = (-1 : ℚ) ^ m * (-1 : ℚ) ^ a.val := by
      rw [← pow_add]
      apply neg_one_pow_eq_of_add_even
      exact ⟨m, by omega⟩
    rw [hp]
    ring
  by_cases hi : i.val ≤ m
  · exact aux i j hi hij
  · have hc := aux j i (by omega) (by omega)
    have hs : V j i = V i j := congrArg (fun M : Matrix (Fin w) (Fin w) ℚ => M i j) hS
    rw [hs] at hc
    have hp : (-1 : ℚ) ^ j.val = (-1 : ℚ) ^ i.val :=
      neg_one_pow_eq_of_add_even ⟨m, by omega⟩
    rwa [hp] at hc


/-- Rational adjoint map. -/
def adjointLinear {w : Type*} [Fintype w] (B : Matrix w w ℚ) :
    Matrix w w ℚ →ₗ[ℚ] Matrix w w ℚ where
  toFun := L_adjoint B
  map_add' E F := by
    dsimp [L_adjoint]
    rw [Matrix.transpose_add, Matrix.mul_add]
    abel
  map_smul' c E := by
    dsimp [L_adjoint]
    rw [Matrix.transpose_smul, Matrix.mul_smul, smul_sub]

/-- Exactly the paper's allowed indices. -/
def TestIndex (k : ℕ) := {h : ℕ // k ≤ h ∧ h ≤ 2 * k ∧ Even h}

def testSpan (k : ℕ) : Submodule ℚ (Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :=
  Submodule.span ℚ (Set.range (fun h : TestIndex k => Z_binom_concrete (k + 1) h.val))

theorem leading_elimination (k h : ℕ) (hh : h ≤ 2 * k)
    (Z : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hZ : L_adjoint (B_mat (k + 1)) Z = 0)
    (hlow : ∀ i j : Fin (k + 1), i.val + j.val < h → Z i j = 0) :
    ∃ Q ∈ testSpan k, L_adjoint (B_mat (k + 1)) Q = 0 ∧
      ∀ i j : Fin (k + 1), i.val + j.val < h + 1 → (Z - Q) i j = 0 := by
  let W := leadingSlice Z h
  have hS : W.transpose = W := leadingSlice_symmetric Z hZ hlow
  have hD : N0_mat (k + 1) * W + W * (N0_mat (k + 1)).transpose = 0 :=
    leadingSlice_derivation Z hZ hlow
  by_cases hsmall : h < k
  · refine ⟨0, (testSpan k).zero_mem, ?_, ?_⟩
    · simp [L_adjoint]
    · intro i j hij
      rw [sub_zero]
      by_cases hlt : i.val + j.val < h
      · exact hlow i j hlt
      · have heq : i.val + j.val = h := by omega
        have hz := V_eq_zero_of_add_lt W hD (i := i) (j := j) (by omega)
        simpa only [W, leadingSlice, if_pos heq] using hz
  by_cases heven : Even h
  · obtain ⟨m, hm⟩ := heven
    have hm_lt : m < k + 1 := by omega
    let c := (-1 : ℚ) ^ m * W ⟨m, hm_lt⟩ ⟨m, hm_lt⟩
    let Q := c • Z_binom_concrete (k + 1) h
    have hQ : Q ∈ testSpan k := by
      apply (testSpan k).smul_mem
      apply Submodule.subset_span
      exact ⟨⟨h, by omega, hh, ⟨m, hm⟩⟩, rfl⟩
    have hK : L_adjoint (B_mat (k + 1)) Q = 0 := by
      change adjointLinear (B_mat (k + 1)) (c • Z_binom_concrete (k + 1) h) = 0
      rw [map_smul]
      change c • L_adjoint (B_mat (k + 1)) (Z_binom_concrete (k + 1) h) = 0
      rw [Z_binom_concrete_in_adjoint_kernel _ _ (by omega) ⟨m, hm⟩, smul_zero]
    refine ⟨Q, hQ, hK, ?_⟩
    intro i j hij
    change Z i j - c * Z_binom_concrete (k + 1) h i j = 0
    by_cases hlt : i.val + j.val < h
    · rw [hlow i j hlt, Z_binom_concrete_support i j hlt, mul_zero, sub_self]
    · have heq : i.val + j.val = h := by omega
      rw [Z_binom_concrete_leading i j heq]
      have hv := symmetric_derivation_even_value W hS hD hm_lt i j (by omega)
      have hv' : Z i j = c * (-1 : ℚ) ^ i.val := by
        simpa only [W, leadingSlice, if_pos heq] using hv
      rw [hv', sub_self]
  · refine ⟨0, (testSpan k).zero_mem, ?_, ?_⟩
    · simp [L_adjoint]
    · intro i j hij
      rw [sub_zero]
      by_cases hlt : i.val + j.val < h
      · exact hlow i j hlt
      · have heq : i.val + j.val = h := by omega
        have hz := symmetric_derivation_odd_zero W hS hD i j (by rwa [heq])
        simpa only [W, leadingSlice, if_pos heq] using hz

/-- Completeness: no adjoint-kernel matrices lie outside the paper's test span. -/
theorem adjoint_kernel_mem_testSpan (k : ℕ)
    (Z : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hZ : L_adjoint (B_mat (k + 1)) Z = 0) : Z ∈ testSpan k := by
  have aux : ∀ d : ℕ, d ≤ 2 * k + 1 →
      ∀ Y : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ,
        L_adjoint (B_mat (k + 1)) Y = 0 →
        (∀ i j : Fin (k + 1), i.val + j.val < 2 * k + 1 - d → Y i j = 0) →
        Y ∈ testSpan k := by
    intro d
    induction d with
    | zero =>
      intro _ Y _ hlow
      have hy : Y = 0 := by
        ext i j
        apply hlow i j
        have := i.isLt
        have := j.isLt
        omega
      rw [hy]
      exact (testSpan k).zero_mem
    | succ d ih =>
      intro hd Y hY hlow
      let h := 2 * k + 1 - (d + 1)
      obtain ⟨Q, hQ, hK, hnext⟩ := leading_elimination k h (by dsimp [h]; omega) Y hY hlow
      have hR : L_adjoint (B_mat (k + 1)) (Y - Q) = 0 := by
        change adjointLinear (B_mat (k + 1)) (Y - Q) = 0
        rw [map_sub]
        change L_adjoint (B_mat (k + 1)) Y - L_adjoint (B_mat (k + 1)) Q = 0
        rw [hY, hK, sub_self]
      have hm := ih (by omega) (Y - Q) hR (by
        intro i j hij
        apply hnext i j
        dsimp [h]
        omega)
      have heq : Y = (Y - Q) + Q := by abel
      rw [heq]
      exact (testSpan k).add_mem hm hQ
  exact aux (2 * k + 1) (by omega) Z hZ (by intro i j hij; omega)

/-- The finite v15 scalar tests are sufficient and necessary over ℚ. -/
theorem moment_solvable_iff_listed_tests (k : ℕ)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :
    (∃ E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ,
      L_moment (B_mat (k + 1)) E = F) ↔
    ∀ h : ℕ, k ≤ h → h ≤ 2 * k → Even h →
      matInnerProd (Z_binom_concrete (k + 1) h) F = 0 := by
  rw [moment_solvable_iff_all_adjoint_tests]
  constructor
  · intro h hidx hlo _ heven
    exact h _ (Z_binom_concrete_in_adjoint_kernel _ _ (by omega) heven)
  · intro ht Z hZ
    have hm := adjoint_kernel_mem_testSpan k Z hZ
    change Z ∈ Submodule.span ℚ _ at hm
    clear hZ
    induction hm using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨h, rfl⟩ := hQ
      exact ht h.val h.property.1 h.property.2.1 h.property.2.2
    | zero => simp [matInnerProd]
    | add Q R _ _ hQ hR => rw [matInnerProd_add_left, hQ, hR, add_zero]
    | smul c Q _ hQ => rw [matInnerProd_smul_left, hQ, mul_zero]

#print axioms Karlin.FaithfulCokernel.adjoint_kernel_mem_testSpan
#print axioms Karlin.FaithfulCokernel.moment_solvable_iff_listed_tests


noncomputable instance testIndexFintype (k : ℕ) : Fintype (TestIndex k) :=
  Fintype.ofInjective (fun h : TestIndex k =>
    (⟨h.val, by have := h.property.2.1; omega⟩ : Fin (2 * k + 1)))
    (by intro a b hab; apply Subtype.ext; exact congrArg Fin.val hab)

/-- Distinct leading anti-diagonals make all the listed tests independent. -/
theorem listed_tests_linearIndependent (k : ℕ) :
    LinearIndependent ℚ (fun h : TestIndex k => Z_binom_concrete (k + 1) h.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have aux : ∀ n : ℕ, ∀ h : TestIndex k, h.val = n → c h = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro h hn
      obtain ⟨m, hm⟩ := h.property.2.2
      have hm_lt : m < k + 1 := by have := h.property.2.1; omega
      let i : Fin (k + 1) := ⟨m, hm_lt⟩
      have heq : i.val + i.val = h.val := by dsimp [i]; omega
      have hv := congrArg (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ => M i i) hc
      dsimp only at hv
      rw [Matrix.sum_apply, Finset.sum_eq_single h] at hv
      · change c h * Z_binom_concrete (k + 1) h.val i i = 0 at hv
        rw [Z_binom_concrete_leading i i heq] at hv
        exact (mul_eq_zero.mp hv).resolve_right (pow_ne_zero _ (by norm_num))
      · intro g _ hgh
        by_cases hlt : g.val < h.val
        · rw [ih g.val (by omega) g rfl, zero_smul]
          rfl
        · have hne : g.val ≠ h.val := fun e => hgh (Subtype.ext e)
          have hgt : i.val + i.val < g.val := by omega
          change c g * Z_binom_concrete (k + 1) g.val i i = 0
          rw [Z_binom_concrete_support i i hgt, mul_zero]
      · simp
  intro h
  exact aux h.val h rfl

/-- Exact identification of the adjoint kernel with the span of the listed tests. -/
theorem adjoint_kernel_eq_testSpan (k : ℕ) :
    LinearMap.ker (adjointLinear (B_mat (k + 1))) = testSpan k := by
  apply le_antisymm
  · intro Z hZ
    exact adjoint_kernel_mem_testSpan k Z hZ
  · apply Submodule.span_le.mpr
    rintro Z ⟨h, rfl⟩
    exact Z_binom_concrete_in_adjoint_kernel _ _ (by have := h.property.1; omega)
      h.property.2.2

#print axioms Karlin.FaithfulCokernel.listed_tests_linearIndependent
#print axioms Karlin.FaithfulCokernel.adjoint_kernel_eq_testSpan


/-- Congruence by a fixed matrix as a rational linear map. -/
def congruenceLinear {w : Type*} [Fintype w] (A : Matrix w w ℚ) :
    Matrix w w ℚ →ₗ[ℚ] Matrix w w ℚ where
  toFun Z := A * Z * A.transpose
  map_add' Z W := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c Z := by
    change A * (c • Z) * A.transpose = c • (A * Z * A.transpose)
    rw [Matrix.mul_smul, Matrix.smul_mul]

theorem pull_push_congruence (w : ℕ) (Z : Matrix (Fin w) (Fin w) ℚ) :
    congruenceLinear (S_inv_mat w) (congruenceLinear (S_mat w) Z) = Z := by
  change S_inv_mat w * (S_mat w * Z * (S_mat w).transpose) * (S_inv_mat w).transpose = Z
  calc _ = (S_inv_mat w * S_mat w) * Z *
      ((S_mat w).transpose * (S_inv_mat w).transpose) := by simp only [Matrix.mul_assoc]
    _ = Z := by rw [← Matrix.transpose_mul, S_inv_mat_mul_S_mat,
      Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem adjoint_congruence (w : ℕ) (Z : Matrix (Fin w) (Fin w) ℚ) :
    L_adjoint (B_mat w) (congruenceLinear (S_mat w) Z) =
      congruenceLinear (S_mat w) (L_adjoint_DP w Z) := by
  have ht : B_mat w * (S_mat w * Z * (S_mat w).transpose).transpose =
      S_mat w * (expN0 w (-1) * Z.transpose) * (S_mat w).transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc _ = (B_mat w * S_mat w) * Z.transpose * (S_mat w).transpose := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [B_mat_mul_S_mat]; simp only [Matrix.mul_assoc]
  change S_mat w * Z * (S_mat w).transpose -
    B_mat w * (S_mat w * Z * (S_mat w).transpose).transpose =
    S_mat w * (Z - expN0 w (-1) * Z.transpose) * (S_mat w).transpose
  rw [ht, Matrix.mul_sub, Matrix.sub_mul]

/-- The divided-power test span, with the same exact index set. -/
def dpTestSpan (k : ℕ) : Submodule ℚ (Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :=
  Submodule.span ℚ (Set.range (fun h : TestIndex k => Z_DP (k + 1) h.val))

theorem dp_adjoint_kernel_mem_testSpan (k : ℕ)
    (Z : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hZ : L_adjoint_DP (k + 1) Z = 0) : Z ∈ dpTestSpan k := by
  have hQ : L_adjoint (B_mat (k + 1)) (congruenceLinear (S_mat (k + 1)) Z) = 0 := by
    rw [adjoint_congruence, hZ, map_zero]
  have hm := adjoint_kernel_mem_testSpan k _ hQ
  have pull : ∀ Q ∈ testSpan k,
      congruenceLinear (S_inv_mat (k + 1)) Q ∈ dpTestSpan k := by
    intro Q hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨h, rfl⟩ := hQ
      change congruenceLinear (S_inv_mat (k + 1))
        (congruenceLinear (S_mat (k + 1)) (Z_DP (k + 1) h.val)) ∈ _
      rw [pull_push_congruence]
      exact Submodule.subset_span ⟨h, rfl⟩
    | zero => rw [map_zero]; exact (dpTestSpan k).zero_mem
    | add Q R _ _ hQ hR => rw [map_add]; exact (dpTestSpan k).add_mem hQ hR
    | smul c Q _ hQ => rw [map_smul]; exact (dpTestSpan k).smul_mem c hQ
  have hh := pull _ hm
  rwa [pull_push_congruence] at hh

theorem dp_listed_tests_linearIndependent (k : ℕ) :
    LinearIndependent ℚ (fun h : TestIndex k => Z_DP (k + 1) h.val) := by
  apply LinearIndependent.of_comp (congruenceLinear (S_mat (k + 1)))
  exact listed_tests_linearIndependent k

theorem dp_adjoint_kernel_eq_testSpan (k : ℕ) :
    LinearMap.ker (adjointLinear (expN0 (k + 1) (-1))) = dpTestSpan k := by
  apply le_antisymm
  · intro Z hZ
    exact dp_adjoint_kernel_mem_testSpan k Z hZ
  · apply Submodule.span_le.mpr
    rintro Z ⟨h, rfl⟩
    exact Z_DP_in_adjoint_kernel (by have := h.property.1; omega) h.property.2.2

#print axioms Karlin.FaithfulCokernel.dp_listed_tests_linearIndependent
#print axioms Karlin.FaithfulCokernel.dp_adjoint_kernel_eq_testSpan


/-- A single linear solution operator on the moment range extends to the whole
matrix space. Its choice depends only on `k`, before any right-hand side. -/
theorem exists_moment_section (k : ℕ) :
    ∃ S : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ →ₗ[ℚ]
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ,
      ∀ F ∈ LinearMap.range (momentLinear (B_mat (k + 1))),
        L_moment (B_mat (k + 1)) (S F) = F := by
  let L := momentLinear (B_mat (k + 1))
  obtain ⟨s, hs⟩ := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  obtain ⟨q, hq⟩ := exists_isCompl (LinearMap.range L)
  refine ⟨s.comp ((LinearMap.range L).linearProjOfIsCompl q hq), ?_⟩
  intro F hF
  change L (s ((LinearMap.range L).linearProjOfIsCompl q hq F)) = F
  have hp : (LinearMap.range L).linearProjOfIsCompl q hq F = ⟨F, hF⟩ :=
    Submodule.linearProjOfIsCompl_apply_left hq ⟨F, hF⟩
  rw [hp]
  have hh := LinearMap.congr_fun hs ⟨F, hF⟩
  exact congrArg Subtype.val hh

def momentSection (k : ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ →ₗ[ℚ]
      Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  FaithfulEffectiveLinear.linearSection (momentLinear (B_mat (k + 1)))
    (exists_moment_section k)

theorem momentSection_solves (k : ℕ)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hF : ∀ h : ℕ, k ≤ h → h ≤ 2 * k → Even h →
      matInnerProd (Z_binom_concrete (k + 1) h) F = 0) :
    L_moment (B_mat (k + 1)) (momentSection k F) = F := by
  apply FaithfulEffectiveLinear.section_on_range
    (momentLinear (B_mat (k + 1))) (exists_moment_section k)
  exact (moment_solvable_iff_listed_tests k F).mpr hF

#print axioms Karlin.FaithfulCokernel.momentSection_solves


/-- The displayed binomial matrices, as an actual basis of the adjoint kernel. -/
noncomputable def binomialKernelBasis (k : ℕ) :
    Module.Basis (TestIndex k) ℚ (LinearMap.ker (adjointLinear (B_mat (k + 1)))) :=
  (Module.Basis.span (listed_tests_linearIndependent k)).map
    (LinearEquiv.ofEq (testSpan k) _ (adjoint_kernel_eq_testSpan k).symm)

/-- The displayed divided-power matrices, as an actual basis of its adjoint kernel. -/
noncomputable def dividedPowerKernelBasis (k : ℕ) :
    Module.Basis (TestIndex k) ℚ (LinearMap.ker (adjointLinear (expN0 (k + 1) (-1)))) :=
  (Module.Basis.span (dp_listed_tests_linearIndependent k)).map
    (LinearEquiv.ofEq (dpTestSpan k) _ (dp_adjoint_kernel_eq_testSpan k).symm)

/-- The finite entrywise absolute-sum norm, written locally to avoid import cycles. -/
def entryAbsSum {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℚ) : ℚ :=
  ∑ i, ∑ j, |A i j|

theorem entryAbsSum_nonneg {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℚ) :
    0 ≤ entryAbsSum A := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem abs_entry_le_entryAbsSum {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) (i : m) (j : n) : |A i j| ≤ entryAbsSum A := by
  apply le_trans (Finset.single_le_sum (fun b _ => abs_nonneg (A i b)) (Finset.mem_univ j))
  exact Finset.single_le_sum
    (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg (A a b))) (Finset.mem_univ i)

theorem entryAbsSum_smul {m n : Type*} [Fintype m] [Fintype n]
    (c : ℚ) (A : Matrix m n ℚ) : entryAbsSum (c • A) = |c| * entryAbsSum A := by
  simp only [entryAbsSum, Matrix.smul_apply, smul_eq_mul, abs_mul, ← Finset.mul_sum]

theorem entryAbsSum_sum {m n a : Type*} [Fintype m] [Fintype n]
    (s : Finset a) (A : a → Matrix m n ℚ) :
    entryAbsSum (∑ x ∈ s, A x) ≤ ∑ x ∈ s, entryAbsSum (A x) := by
  simp only [entryAbsSum, Matrix.sum_apply]
  calc (∑ i, ∑ j, |∑ x ∈ s, A x i j|)
      ≤ ∑ i, ∑ j, ∑ x ∈ s, |A x i j| := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ x ∈ s, ∑ j, |A x i j| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ x ∈ s, ∑ i, ∑ j, |A x i j| := by rw [Finset.sum_comm]

/-- Explicit finite rational bound determined solely by a linear operator's coefficients. -/
def linearCoefficientBound {w : Type*} [Fintype w] [DecidableEq w]
    (S : Matrix w w ℚ →ₗ[ℚ] Matrix w w ℚ) : ℚ :=
  ∑ i, ∑ j, entryAbsSum (S (matrixUnit i j))

theorem linearCoefficientBound_nonneg {w : Type*} [Fintype w] [DecidableEq w]
    (S : Matrix w w ℚ →ₗ[ℚ] Matrix w w ℚ) : 0 ≤ linearCoefficientBound S := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => entryAbsSum_nonneg _))

/-- Every rational linear map satisfies its fixed finite coefficient bound. -/
theorem linear_entryAbsSum_bound {w : Type*} [Fintype w] [DecidableEq w]
    (S : Matrix w w ℚ →ₗ[ℚ] Matrix w w ℚ) (F : Matrix w w ℚ) :
    entryAbsSum (S F) ≤ linearCoefficientBound S * entryAbsSum F := by
  have hexp : S F = ∑ i, ∑ j, F i j • S (matrixUnit i j) := by
    conv_lhs => rw [← matrixUnit_expansion F]
    simp only [map_sum, map_smul]
  rw [hexp]
  calc entryAbsSum (∑ i, ∑ j, F i j • S (matrixUnit i j))
      ≤ ∑ i, entryAbsSum (∑ j, F i j • S (matrixUnit i j)) := entryAbsSum_sum _ _
    _ ≤ ∑ i, ∑ j, entryAbsSum (F i j • S (matrixUnit i j)) := by
      apply Finset.sum_le_sum
      intro i _
      exact entryAbsSum_sum _ _
    _ = ∑ i, ∑ j, |F i j| * entryAbsSum (S (matrixUnit i j)) := by
      simp only [entryAbsSum_smul]
    _ ≤ ∑ i, ∑ j, entryAbsSum F * entryAbsSum (S (matrixUnit i j)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (abs_entry_le_entryAbsSum F i j) (entryAbsSum_nonneg _)
    _ = linearCoefficientBound S * entryAbsSum F := by
      simp only [← Finset.mul_sum, linearCoefficientBound]
      ring

/-- A uniform section constant: depends on `k` only, before reset scales or residuals. -/
def momentSectionBound (k : ℕ) : ℚ := linearCoefficientBound (momentSection k)

theorem momentSectionBound_nonneg (k : ℕ) : 0 ≤ momentSectionBound k :=
  linearCoefficientBound_nonneg _

theorem momentSection_bound (k : ℕ)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :
    entryAbsSum (momentSection k F) ≤ momentSectionBound k * entryAbsSum F :=
  linear_entryAbsSum_bound _ _

/-- Bounded compatible residuals produce bounded rational corrections via one
fixed linear section. No bound on an unknown solution is assumed. -/
theorem bounded_moment_solution (k : ℕ)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) (M : ℚ)
    (hF : ∀ h : ℕ, k ≤ h → h ≤ 2 * k → Even h →
      matInnerProd (Z_binom_concrete (k + 1) h) F = 0)
    (hbound : entryAbsSum F ≤ M) :
    L_moment (B_mat (k + 1)) (momentSection k F) = F ∧
      entryAbsSum (momentSection k F) ≤ momentSectionBound k * M := by
  refine ⟨momentSection_solves k F hF, ?_⟩
  exact (momentSection_bound k F).trans
    (mul_le_mul_of_nonneg_left hbound (momentSectionBound_nonneg k))

#print axioms Karlin.FaithfulCokernel.binomialKernelBasis
#print axioms Karlin.FaithfulCokernel.dividedPowerKernelBasis
#print axioms Karlin.FaithfulCokernel.bounded_moment_solution


@[simp] theorem binomialKernelBasis_apply (k : ℕ) (h : TestIndex k) :
    (binomialKernelBasis k h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) =
      Z_binom_concrete (k + 1) h.val := by
  change ((Module.Basis.span (listed_tests_linearIndependent k)) h :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) = _
  exact Module.Basis.span_apply _ _

@[simp] theorem dividedPowerKernelBasis_apply (k : ℕ) (h : TestIndex k) :
    (dividedPowerKernelBasis k h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) =
      Z_DP (k + 1) h.val := by
  change ((Module.Basis.span (dp_listed_tests_linearIndependent k)) h :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) = _
  exact Module.Basis.span_apply _ _

/-- All choices precede all right-hand sides. -/
theorem exists_fixed_bounded_moment_section (k : ℕ) :
    ∃ (S : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ →ₗ[ℚ]
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) (C : ℚ),
      0 ≤ C ∧ ∀ F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ,
        (∀ h : ℕ, k ≤ h → h ≤ 2 * k → Even h →
          matInnerProd (Z_binom_concrete (k + 1) h) F = 0) →
        L_moment (B_mat (k + 1)) (S F) = F ∧ entryAbsSum (S F) ≤ C * entryAbsSum F := by
  refine ⟨momentSection k, momentSectionBound k, momentSectionBound_nonneg k, ?_⟩
  intro F hF
  exact ⟨momentSection_solves k F hF, momentSection_bound k F⟩

#print axioms Karlin.FaithfulCokernel.exists_fixed_bounded_moment_section

end FaithfulCokernel
end Karlin
