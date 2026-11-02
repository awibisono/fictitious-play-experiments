import Karlin.FaithfulCokernel
import Mathlib.RingTheory.Nilpotent.Exp

/-!
# The nilpotent-operator route to the divided-power cokernel

This file follows the finite-exponential argument on page 39 of v15. All
matrices and antidiagonal witnesses are the existing rational definitions.
-/

namespace Karlin.FaithfulPaperCokernel
open scoped BigOperators Matrix
open FaithfulCokernel

abbrev Mat (w : ℕ) := Matrix (Fin w) (Fin w) ℚ

/-- Right multiplication by the transpose is an algebra homomorphism. -/
def rightTranspose (w : ℕ) : Mat w →ₐ[ℚ] Module.End ℚ (Mat w) where
  toFun A :=
    { toFun := fun Z => Z * A.transpose
      map_add' := fun X Y => Matrix.add_mul X Y _
      map_smul' := fun c Z => Matrix.smul_mul c Z _ }
  map_one' := by ext Z i j; simp
  map_mul' A B := by ext Z i j; simp [Matrix.transpose_mul, Matrix.mul_assoc]
  map_zero' := by ext Z i j; simp
  map_add' A B := by ext Z i j; simp [Matrix.transpose_add, Matrix.mul_add]
  commutes' c := by ext Z i j; simp [Algebra.algebraMap_eq_smul_one]

/-- The paper's actual operator `D(Z) = N₀Z + ZN₀ᵀ`. -/
def D (w : ℕ) : Module.End ℚ (Mat w) :=
  Algebra.lmul ℚ (Mat w) (N0_mat w) + rightTranspose w (N0_mat w)

@[simp] theorem D_apply (w : ℕ) (Z : Mat w) :
    D w Z = N0_mat w * Z + Z * (N0_mat w).transpose := rfl

theorem left_right_commute (w : ℕ) (A B : Mat w) :
    Commute (Algebra.lmul ℚ (Mat w) A) (rightTranspose w B) := by
  ext Z i j
  simp [rightTranspose, Matrix.mul_assoc]

theorem N0_pow_zero (w : ℕ) : N0_mat w ^ w = 0 := by
  apply strictly_lower_tri_pow_eq_zero
  intro i j hij
  simp [N0_mat, show i.val ≠ j.val + 1 by omega]

theorem D_pow_zero (k : ℕ) : D (k + 1) ^ (2 * k + 1) = 0 := by
  apply (left_right_commute (k + 1) _ _).add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero
  · rw [← map_pow, N0_pow_zero, map_zero]
  · rw [← map_pow, N0_pow_zero, map_zero]
  · omega

theorem N0_pow_entry (w n : ℕ) (i j : Fin w) :
    (N0_mat w ^ n) i j = if i.val = j.val + n then 1 else 0 := by
  induction n generalizing i j with
  | zero => simp [Matrix.one_apply, Fin.ext_iff]
  | succ n ih =>
    rw [pow_succ']
    change (N_mat w * N0_mat w ^ n) i j = _
    rw [N_mul_entry]
    by_cases hi : 0 < i.val
    · rw [dif_pos hi, ih]
      dsimp only
      have he : (i.val - 1 = j.val + n) ↔ i.val = j.val + (n + 1) := by omega
      simp only [he]
    · rw [dif_neg hi, if_neg (by omega)]

/-- The boundary-aware coordinate recurrence printed in the PDF. -/
theorem D_entry (w : ℕ) (V : Mat w) (i j : Fin w) :
    D w V i j =
      (if hi : 0 < i.val then V ⟨i.val - 1, by omega⟩ j else 0) +
      (if hj : 0 < j.val then V i ⟨j.val - 1, by omega⟩ else 0) := by
  change (N_mat w * V) i j + (V * (N_mat w).transpose) i j = _
  rw [N_mul_entry, mul_N_transpose_entry]

/-- The coordinate exponential is exactly the nilpotent finite sum. -/
theorem expN0_eq_sum (w : ℕ) (t : ℚ) :
    expN0 w t = ∑ n ∈ Finset.range w, (t ^ n / (n.factorial : ℚ)) • N0_mat w ^ n := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, N0_pow_entry]
  by_cases hji : j.val ≤ i.val
  · rw [Finset.sum_eq_single (i.val - j.val)]
    · simp [expN0, show j ≤ i from hji, Nat.add_sub_of_le hji]
    · intro b hb hne
      rw [if_neg (by omega), mul_zero]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · have hz : ∀ n, i.val ≠ j.val + n := by omega
    simp [expN0, show ¬ j ≤ i from hji, hz]

theorem expN0_eq_nilpotent_exp (w : ℕ) (t : ℚ) :
    expN0 w t = IsNilpotent.exp (t • N0_mat w) := by
  have hn : (t • N0_mat w) ^ w = 0 := by rw [smul_pow, N0_pow_zero, smul_zero]
  rw [IsNilpotent.exp_eq_sum hn, expN0_eq_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [smul_pow, smul_smul]
  congr 1
  ring

/-- The two commuting multiplication operators give the paper's exponential identity. -/
theorem exp_D_apply (k : ℕ) (t : ℚ) (Z : Mat (k + 1)) :
    IsNilpotent.exp (t • D (k + 1)) Z =
      expN0 (k + 1) t * Z * (expN0 (k + 1) t).transpose := by
  have hn : IsNilpotent (t • N0_mat (k + 1)) := (show IsNilpotent (N0_mat (k + 1)) from ⟨_, N0_pow_zero _⟩).smul t
  have he : t • D (k + 1) =
      Algebra.lmul ℚ (Mat (k + 1)) (t • N0_mat (k + 1)) +
      rightTranspose (k + 1) (t • N0_mat (k + 1)) := by simp [D]
  rw [he, IsNilpotent.exp_add_of_commute (left_right_commute _ _ _)
    (hn.map (Algebra.lmul ℚ (Mat (k + 1)))) (hn.map (rightTranspose (k + 1))),
    ← hn.map_exp (Algebra.lmul ℚ (Mat (k + 1))),
    ← hn.map_exp (rightTranspose (k + 1)), ← expN0_eq_nilpotent_exp]
  change expN0 (k + 1) t * (Z * (expN0 (k + 1) t).transpose) = _
  rw [Matrix.mul_assoc]

/-- No analytic convergence is used: this is the exact finite sum through `2k`. -/
theorem exp_D_finite (k : ℕ) (t : ℚ) :
    IsNilpotent.exp (t • D (k + 1)) =
      ∑ n ∈ Finset.range (2 * k + 1), (t ^ n / (n.factorial : ℚ)) • D (k + 1) ^ n := by
  have hn : (t • D (k + 1)) ^ (2 * k + 1) = 0 := by
    rw [smul_pow, D_pow_zero, smul_zero]
  rw [IsNilpotent.exp_eq_sum hn]
  apply Finset.sum_congr rfl
  intro n hn
  rw [smul_pow, smul_smul]
  congr 1
  ring

section PolynomialFactor
variable {R : Type*} [Ring R] [Algebra ℚ R]

/-- The paper's polynomial factor, with `n` terms. -/
def expFactor (a : R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range n, ((-1 : ℚ) ^ j / ((j + 1).factorial : ℚ)) • a ^ j

theorem expFactor_commute (a : R) (n : ℕ) : Commute a (expFactor a n) := by
  apply Commute.sum_right
  intro i hi
  exact (Commute.refl a).pow_right i |>.smul_right _

/-- The factor has constant term one; its remaining polynomial is nilpotent. -/
theorem expFactor_sub_one_nilpotent {a : R} (ha : IsNilpotent a) {n : ℕ} (hn : 0 < n) :
    IsNilpotent (expFactor a n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [expFactor, Finset.sum_range_succ']
  simp only [zero_add, pow_zero, Nat.factorial_one, Nat.cast_one, div_one, one_smul,
    add_sub_cancel_right]
  apply Commute.isNilpotent_sum
  · intro i hi
    exact (ha.pow_of_pos (by omega : i + 1 ≠ 0)).smul _
  · intro i j hi hj
    exact ((Commute.refl a).pow_pow (i + 1) (j + 1)).smul_left _ |>.smul_right _

/-- Exact factorization of the finite exponential, over a rational algebra. -/
theorem one_sub_exp_neg (a : R) (n : ℕ) (ha : a ^ (n + 1) = 0) :
    1 - IsNilpotent.exp (-a) = a * expFactor a n := by
  have hna : (-a) ^ (n + 1) = 0 := by rw [neg_pow, ha, mul_zero]
  rw [IsNilpotent.exp_eq_sum hna, Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  rw [show (1 : R) - ((∑ j ∈ Finset.range n,
    ((j + 1).factorial : ℚ)⁻¹ • (-a) ^ (j + 1)) + 1) =
    -(∑ j ∈ Finset.range n, ((j + 1).factorial : ℚ)⁻¹ • (-a) ^ (j + 1)) by abel]
  rw [← Finset.sum_neg_distrib, expFactor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show -a = (-1 : ℚ) • a by simp, smul_pow, smul_smul,
    mul_smul_comm, ← pow_succ', ← neg_smul]
  congr 1
  simp only [pow_succ, div_eq_mul_inv]
  ring

/-- A zero-constant polynomial in `a` has the same usable nilpotence bound. -/
theorem expFactor_sub_one_pow_zero (a : R) {n r : ℕ} (hn : 0 < n) (ha : a ^ r = 0) :
    (expFactor a n - 1) ^ r = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let Q : R := ∑ j ∈ Finset.range m,
    ((-1 : ℚ) ^ (j + 1) / ((j + 2).factorial : ℚ)) • a ^ j
  have hQ : Commute a Q := by
    apply Commute.sum_right
    intro j hj
    exact (Commute.refl a).pow_right j |>.smul_right _
  have he : expFactor a (m + 1) - 1 = a * Q := by
    rw [expFactor, Finset.sum_range_succ']
    simp only [zero_add, pow_zero, Nat.factorial_one, Nat.cast_one, div_one, one_smul,
      add_sub_cancel_right]
    rw [show a * Q = ∑ j ∈ Finset.range m,
      a * (((-1 : ℚ) ^ (j + 1) / ((j + 2).factorial : ℚ)) • a ^ j) by
      simp only [Q, Finset.mul_sum]]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_smul_comm, ← pow_succ']
  rw [he, hQ.mul_pow, ha, zero_mul]

/-- The explicit finite geometric inverse used in the PDF. -/
theorem expFactor_geometric_inverse (a : R) {n r : ℕ} (hn : 0 < n) (ha : a ^ r = 0) :
    let K := expFactor a n - 1
    (expFactor a n * ∑ j ∈ Finset.range r, (-K) ^ j = 1) ∧
    ((∑ j ∈ Finset.range r, (-K) ^ j) * expFactor a n = 1) := by
  dsimp only
  have hK : (-(expFactor a n - 1)) ^ r = 0 := by
    rw [neg_pow, expFactor_sub_one_pow_zero a hn ha, mul_zero]
  have he : expFactor a n = 1 - (-(expFactor a n - 1)) := by abel
  constructor
  · nth_rw 1 [he]
    rw [mul_neg_geom_sum, hK, sub_zero]
  · nth_rw 2 [he]
    rw [geom_sum_mul_neg, hK, sub_zero]

/-- Invertibility is witnessed by that finite geometric inverse. -/
theorem expFactor_isUnit {a : R} (ha : IsNilpotent a) {n : ℕ} (hn : 0 < n) :
    IsUnit (expFactor a n) := by
  obtain ⟨r, hr⟩ := ha
  have hi := expFactor_geometric_inverse a hn hr
  exact ⟨⟨expFactor a n, ∑ j ∈ Finset.range r, (-(expFactor a n - 1)) ^ j,
    hi.1, hi.2⟩, rfl⟩

end PolynomialFactor

/-- The invertible polynomial factor proves the fixed-vector equivalence. -/
theorem exp_neg_fixed_iff {M : Type*} [AddCommGroup M] [Module ℚ M]
    (a : Module.End ℚ M) {n : ℕ} (hn : 0 < n) (ha : a ^ (n + 1) = 0) (v : M) :
    IsNilpotent.exp (-a) v = v ↔ a v = 0 := by
  have hu : Function.Injective (⇑(expFactor a n)) :=
    ((Module.End.isUnit_iff _).mp (expFactor_isUnit ⟨n + 1, ha⟩ hn)).1
  have he : v - IsNilpotent.exp (-a) v = expFactor a n (a v) := by
    have hf := LinearMap.congr_fun (one_sub_exp_neg a n ha) v
    rw [(expFactor_commute a n).eq] at hf
    exact hf
  constructor
  · intro h
    apply hu
    rw [map_zero, ← he, h, sub_self]
  · intro h
    rw [h, map_zero] at he
    exact (sub_eq_zero.mp he).symm

/-- The PDF's fixed-point reduction for its concrete nilpotent operator. -/
theorem exp_neg_D_fixed_iff (k : ℕ) (hk : 0 < k) (Z : Mat (k + 1)) :
    expN0 (k + 1) (-1) * Z * (expN0 (k + 1) (-1)).transpose = Z ↔
      D (k + 1) Z = 0 := by
  have he := exp_neg_fixed_iff (D (k + 1)) (by omega : 0 < 2 * k) (D_pow_zero k) Z
  rw [show -(D (k + 1)) = (-1 : ℚ) • D (k + 1) from (neg_one_smul ℚ _).symm,
    exp_D_apply] at he
  exact he

theorem N0_commute_expN0 (w : ℕ) (t : ℚ) : Commute (N0_mat w) (expN0 w t) := by
  rw [expN0_eq_sum]
  apply Commute.sum_right
  intro i hi
  exact (Commute.refl _).pow_right i |>.smul_right _

/-- Left multiplication by the half exponential commutes with `D`. -/
theorem D_exp_left (w : ℕ) (t : ℚ) (Z : Mat w) :
    D w (expN0 w t * Z) = expN0 w t * D w Z := by
  simp only [D_apply, Matrix.mul_add]
  rw [← Matrix.mul_assoc (N0_mat w), (N0_commute_expN0 w t).eq]
  simp only [Matrix.mul_assoc]

/-- Every scalar exponential fixes a vector killed by `D`. -/
theorem exp_D_fixed (k : ℕ) (hk : 0 < k) (t : ℚ) (Z : Mat (k + 1))
    (hD : D (k + 1) Z = 0) :
    expN0 (k + 1) t * Z * (expN0 (k + 1) t).transpose = Z := by
  have hn : ((-t) • D (k + 1)) ^ (2 * k + 1) = 0 := by
    rw [smul_pow, D_pow_zero, smul_zero]
  have he := (exp_neg_fixed_iff ((-t) • D (k + 1)) (by omega : 0 < 2 * k) hn Z).mpr
    (by simp [hD])
  have hs : (-((-t) • D (k + 1)) : Module.End ℚ (Mat (k + 1))) = t • D (k + 1) := by
    ext X i j
    simp
    ring
  rw [hs, exp_D_apply] at he
  exact he

/-- The exponential intertwining identity for every derivation-kernel vector. -/
theorem derivation_intertwine (k : ℕ) (hk : 0 < k) (t : ℚ) (Z : Mat (k + 1))
    (hD : D (k + 1) Z = 0) :
    Z * (expN0 (k + 1) t).transpose = expN0 (k + 1) (-t) * Z := by
  have he := congrArg (fun W => expN0 (k + 1) (-t) * W) (exp_D_fixed k hk t Z hD)
  simpa only [← Matrix.mul_assoc, expN0_neg_mul_cancel, Matrix.one_mul] using he

/-- The adjoint equation supplies both the transposed equation and the fixed point. -/
theorem adjoint_conditions (k : ℕ) (hk : 0 < k) (Z : Mat (k + 1))
    (hZ : L_adjoint_DP (k + 1) Z = 0) :
    Z.transpose = expN0 (k + 1) 1 * Z ∧ D (k + 1) Z = 0 := by
  have hz : Z = expN0 (k + 1) (-1) * Z.transpose := sub_eq_zero.mp hZ
  have ht : Z.transpose = expN0 (k + 1) 1 * Z := by
    calc Z.transpose = (expN0 (k + 1) 1 * expN0 (k + 1) (-1)) * Z.transpose := by
          rw [expN0_mul_neg_cancel, Matrix.one_mul]
      _ = expN0 (k + 1) 1 * Z := by rw [Matrix.mul_assoc, ← hz]
  refine ⟨ht, (exp_neg_D_fixed_iff k hk Z).mp ?_⟩
  have hzt := congrArg Matrix.transpose hz
  rw [Matrix.transpose_mul, Matrix.transpose_transpose] at hzt
  calc expN0 (k + 1) (-1) * Z * (expN0 (k + 1) (-1)).transpose
      = expN0 (k + 1) (-1) * Z.transpose := by rw [Matrix.mul_assoc, ← hzt]
    _ = Z := hz.symm

/-- The forward half-exponential conjugation gives exactly symmetry and the recurrence. -/
theorem conjugate_adjoint (k : ℕ) (hk : 0 < k) (Z : Mat (k + 1))
    (hZ : L_adjoint_DP (k + 1) Z = 0) :
    (expN0 (k + 1) (1/2) * Z).transpose = expN0 (k + 1) (1/2) * Z ∧
      D (k + 1) (expN0 (k + 1) (1/2) * Z) = 0 := by
  obtain ⟨ht, hd⟩ := adjoint_conditions k hk Z hZ
  constructor
  · rw [Matrix.transpose_mul, ht, Matrix.mul_assoc,
      derivation_intertwine k hk (1/2) Z hd, ← Matrix.mul_assoc, expN0_mul_expN0]
    norm_num
  · rw [D_exp_left, hd, Matrix.mul_zero]

/-- The transformations are reversible, with the very same half exponential. -/
theorem unconjugate_symmetric (k : ℕ) (hk : 0 < k) (V : Mat (k + 1))
    (hS : V.transpose = V) (hD : D (k + 1) V = 0) :
    L_adjoint_DP (k + 1) (expN0 (k + 1) (-1/2) * V) = 0 := by
  dsimp only [L_adjoint_DP]
  rw [Matrix.transpose_mul, hS,
    derivation_intertwine k hk (-1/2) V hD, ← Matrix.mul_assoc, expN0_mul_expN0]
  norm_num

/-- The paper's two conditions are equivalent to its original adjoint equation. -/
theorem adjoint_iff_symmetric_derivation (k : ℕ) (hk : 0 < k) (Z : Mat (k + 1)) :
    L_adjoint_DP (k + 1) Z = 0 ↔
      (expN0 (k + 1) (1/2) * Z).transpose = expN0 (k + 1) (1/2) * Z ∧
      D (k + 1) (expN0 (k + 1) (1/2) * Z) = 0 := by
  constructor
  · exact conjugate_adjoint k hk Z
  · rintro ⟨hS, hD⟩
    have he := unconjugate_symmetric k hk _ hS hD
    rw [← Matrix.mul_assoc, expN0_mul_expN0] at he
    norm_num [expN0_zero] at he
    exact he

/-- The free scalar on each allowed antidiagonal, read from its central entry. -/
def antidiagonalCoefficient (k : ℕ) (V : Mat (k + 1)) (h : TestIndex k) : ℚ :=
  (-1 : ℚ) ^ (h.val / 2) *
    V ⟨h.val / 2, by have := h.property.2.1; omega⟩
      ⟨h.val / 2, by have := h.property.2.1; omega⟩

/-- Solving the recurrence gives exactly the displayed alternating antidiagonals. -/
theorem symmetric_derivation_expansion (k : ℕ) (V : Mat (k + 1))
    (hS : V.transpose = V) (hD : D (k + 1) V = 0) :
    V = ∑ h : TestIndex k, antidiagonalCoefficient k V h • V_antidiag (k + 1) h.val := by
  classical
  ext i j
  rw [Matrix.sum_apply]
  by_cases hlow : i.val + j.val < k
  · have hz : V i j = 0 := V_eq_zero_of_add_lt V hD (by omega)
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro h hh
    have hne : i.val + j.val ≠ h.val := by have := h.property.1; omega
    simp [Matrix.smul_apply, V_antidiag, hne]
  by_cases heven : Even (i.val + j.val)
  · let h : TestIndex k := ⟨i.val + j.val, by omega,
      by have := i.isLt; have := j.isLt; omega, heven⟩
    rw [Finset.sum_eq_single h]
    · change V i j = antidiagonalCoefficient k V h * V_antidiag (k + 1) h.val i j
      have heq : i.val + j.val = h.val := rfl
      simp only [V_antidiag, Matrix.of_apply, if_pos heq]
      obtain ⟨m, hm⟩ := heven
      have hm_lt : m < k + 1 := by have := i.isLt; have := j.isLt; omega
      have hhalf : h.val / 2 = m := by dsimp [h]; omega
      simpa only [antidiagonalCoefficient, hhalf] using
        symmetric_derivation_even_value V hS hD hm_lt i j hm
    · intro g hg hgh
      have hne : i.val + j.val ≠ g.val := by
        intro heq
        apply hgh
        exact Subtype.ext heq.symm
      simp [Matrix.smul_apply, V_antidiag, hne]
    · simp
  · rw [symmetric_derivation_odd_zero V hS hD i j heven]
    symm
    apply Finset.sum_eq_zero
    intro h hh
    have hne : i.val + j.val ≠ h.val := by
      intro heq
      exact heven (heq.symm ▸ h.property.2.2)
    simp [Matrix.smul_apply, V_antidiag, hne]

/-- Undoing the half exponential yields the same existing `Z_DP` witnesses. -/
theorem adjoint_expansion (k : ℕ) (hk : 0 < k) (Z : Mat (k + 1))
    (hZ : L_adjoint_DP (k + 1) Z = 0) :
    Z = ∑ h : TestIndex k,
      antidiagonalCoefficient k (expN0 (k + 1) (1/2) * Z) h • Z_DP (k + 1) h.val := by
  obtain ⟨hS, hD⟩ := conjugate_adjoint k hk Z hZ
  have he := congrArg (fun V => expN0 (k + 1) (-1/2) * V)
    (symmetric_derivation_expansion k _ hS hD)
  dsimp only at he
  rw [← Matrix.mul_assoc, expN0_mul_expN0] at he
  norm_num [expN0_zero] at he
  simpa only [Matrix.mul_sum, Matrix.mul_smul, Z_DP, neg_div] using he

/-- Distinct antidiagonals give independence before conjugation. -/
theorem antidiagonal_linearIndependent (k : ℕ) :
    LinearIndependent ℚ (fun h : TestIndex k => V_antidiag (k + 1) h.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc h
  obtain ⟨m, hm⟩ := h.property.2.2
  have hm_lt : m < k + 1 := by have := h.property.2.1; omega
  let i : Fin (k + 1) := ⟨m, hm_lt⟩
  have heq : i.val + i.val = h.val := by dsimp [i]; omega
  have he := congrArg (fun V : Mat (k + 1) => V i i) hc
  dsimp only at he
  rw [Matrix.sum_apply, Finset.sum_eq_single h] at he
  · change c h * V_antidiag (k + 1) h.val i i = 0 at he
    simp only [V_antidiag, Matrix.of_apply, if_pos heq] at he
    exact (mul_eq_zero.mp he).resolve_right (pow_ne_zero _ (by norm_num))
  · intro g hg hgh
    have hne : i.val + i.val ≠ g.val := by
      intro hh
      apply hgh
      exact Subtype.ext (hh.symm.trans heq)
    simp [Matrix.smul_apply, V_antidiag, hne]
  · simp

/-- Conjugation preserves the independence of the same displayed test matrices. -/
theorem paper_dp_linearIndependent (k : ℕ) :
    LinearIndependent ℚ (fun h : TestIndex k => Z_DP (k + 1) h.val) := by
  apply LinearIndependent.of_comp (Algebra.lmul ℚ (Mat (k + 1)) (expN0 (k + 1) (1/2)))
  convert antidiagonal_linearIndependent k using 1
  funext h
  change expN0 (k + 1) (1/2) * (expN0 (k + 1) (-1/2) * V_antidiag (k + 1) h.val) = _
  rw [← Matrix.mul_assoc, expN0_mul_expN0]
  norm_num [expN0_zero]

/-- Completeness via the PDF's nilpotent reduction, independent of binomial elimination. -/
theorem paper_dp_kernel_eq_span (k : ℕ) (hk : 0 < k) :
    LinearMap.ker (adjointLinear (expN0 (k + 1) (-1))) = dpTestSpan k := by
  apply le_antisymm
  · intro Z hZ
    rw [adjoint_expansion k hk Z hZ]
    apply Submodule.sum_mem
    intro h hh
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨h, rfl⟩
  · apply Submodule.span_le.mpr
    rintro Z ⟨h, rfl⟩
    exact Z_DP_in_adjoint_kernel (by have := h.property.1; omega) h.property.2.2

/-- The actual basis obtained by the PDF route. -/
noncomputable def paperDividedPowerKernelBasis (k : ℕ) (hk : 0 < k) :
    Module.Basis (TestIndex k) ℚ (LinearMap.ker (adjointLinear (expN0 (k + 1) (-1)))) :=
  (Module.Basis.span (paper_dp_linearIndependent k)).map
    (LinearEquiv.ofEq (dpTestSpan k) _ (paper_dp_kernel_eq_span k hk).symm)

/-- The PDF route changes no basis vector or kernel witness. -/
theorem paperBasis_eq_existing (k : ℕ) (hk : 0 < k) :
    paperDividedPowerKernelBasis k hk = dividedPowerKernelBasis k := by
  apply DFunLike.ext
  intro h
  apply Subtype.ext
  simp [paperDividedPowerKernelBasis, dividedPowerKernelBasis]

/-- The paper's exact polynomial factorization, with the constant term one. -/
theorem paper_factorization (k : ℕ) :
    1 - IsNilpotent.exp (-D (k + 1)) =
      D (k + 1) * expFactor (D (k + 1)) (2 * k) :=
  one_sub_exp_neg _ _ (D_pow_zero k)

/-- The PDF's `K` has its stated nilpotence bound, with no existential exponent. -/
theorem paper_K_pow_zero (k : ℕ) (hk : 0 < k) :
    (expFactor (D (k + 1)) (2 * k) - 1) ^ (2 * k + 1) = 0 :=
  expFactor_sub_one_pow_zero _ (by omega) (D_pow_zero k)

/-- The paper's inverse is the sum through `2k`, on both sides. -/
theorem paper_factor_inverse (k : ℕ) (hk : 0 < k) :
    let P := expFactor (D (k + 1)) (2 * k)
    let K := P - 1
    (P * ∑ j ∈ Finset.range (2 * k + 1), (-K) ^ j = 1) ∧
    ((∑ j ∈ Finset.range (2 * k + 1), (-K) ^ j) * P = 1) :=
  expFactor_geometric_inverse _ (by omega) (D_pow_zero k)

/-- The inverse coordinate map followed by the forward map is literally identity. -/
theorem push_pull_congruence (w : ℕ) (Z : Mat w) :
    congruenceLinear (S_mat w) (congruenceLinear (S_inv_mat w) Z) = Z := by
  change S_mat w * (S_inv_mat w * Z * (S_inv_mat w).transpose) * (S_mat w).transpose = Z
  calc _ = (S_mat w * S_inv_mat w) * Z *
      ((S_inv_mat w).transpose * (S_mat w).transpose) := by simp only [Matrix.mul_assoc]
    _ = Z := by rw [← Matrix.transpose_mul, S_mat_mul_S_inv_mat,
      Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

/-- Coordinate transport of the divided-power completeness proof. -/
theorem paper_binomial_kernel_mem_span (k : ℕ) (hk : 0 < k) (Z : Mat (k + 1))
    (hZ : L_adjoint (B_mat (k + 1)) Z = 0) : Z ∈ testSpan k := by
  let Y := congruenceLinear (S_inv_mat (k + 1)) Z
  have hY : L_adjoint_DP (k + 1) Y = 0 := by
    have he := adjoint_congruence (k + 1) Y
    rw [show congruenceLinear (S_mat (k + 1)) Y = Z from push_pull_congruence _ _, hZ] at he
    have hp := congrArg (congruenceLinear (S_inv_mat (k + 1))) he
    rw [map_zero, pull_push_congruence] at hp
    exact hp.symm
  have hexp := congrArg (congruenceLinear (S_mat (k + 1))) (adjoint_expansion k hk Y hY)
  rw [show congruenceLinear (S_mat (k + 1)) Y = Z from push_pull_congruence _ _, map_sum] at hexp
  rw [hexp]
  apply Submodule.sum_mem
  intro h hh
  rw [map_smul]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨h, rfl⟩

/-- The operator equation transports under the PDF's stated `Sᵀ E S` coordinates. -/
theorem moment_coordinate_identity (w : ℕ) (E : Mat w) :
    L_moment (expN0 w (-1)) ((S_mat w).transpose * E * S_mat w) =
      (S_mat w).transpose * L_moment (B_mat w) E * S_mat w := by
  simp only [L_moment, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, ← B_mat_mul_S_mat]

/-- The corresponding scalar test is the same rational number in either coordinates. -/
theorem test_coordinate_identity (w h : ℕ) (F : Mat w) :
    matInnerProd (Z_DP w h) ((S_mat w).transpose * F * S_mat w) =
      matInnerProd (Z_binom_concrete w h) F :=
  (matInnerProd_Z_binom_eq_Z_DP (S_mat w) h F).symm

/-- Exact binomial-coordinate kernel equality obtained from the divided-power route. -/
theorem paper_binomial_kernel_eq_span (k : ℕ) (hk : 0 < k) :
    LinearMap.ker (adjointLinear (B_mat (k + 1))) = testSpan k := by
  apply le_antisymm
  · intro Z hZ
    exact paper_binomial_kernel_mem_span k hk Z hZ
  · apply Submodule.span_le.mpr
    rintro Z ⟨h, rfl⟩
    exact Z_binom_concrete_in_adjoint_kernel _ _ (by have := h.property.1; omega)
      h.property.2.2

theorem paper_binomial_linearIndependent (k : ℕ) :
    LinearIndependent ℚ (fun h : TestIndex k => Z_binom_concrete (k + 1) h.val) := by
  apply LinearIndependent.of_comp (congruenceLinear (S_inv_mat (k + 1)))
  convert paper_dp_linearIndependent k using 1
  funext h
  exact pull_push_congruence _ _

/-- The same binomial basis constructed from the paper-route completeness proof. -/
noncomputable def paperBinomialKernelBasis (k : ℕ) (hk : 0 < k) :
    Module.Basis (TestIndex k) ℚ (LinearMap.ker (adjointLinear (B_mat (k + 1)))) :=
  (Module.Basis.span (paper_binomial_linearIndependent k)).map
    (LinearEquiv.ofEq (testSpan k) _ (paper_binomial_kernel_eq_span k hk).symm)

theorem paperBinomialBasis_eq_existing (k : ℕ) (hk : 0 < k) :
    paperBinomialKernelBasis k hk = binomialKernelBasis k := by
  apply DFunLike.ext
  intro h
  apply Subtype.ext
  simp [paperBinomialKernelBasis, binomialKernelBasis]

/-- Solvability using the PDF route and the unchanged rational test matrices. -/
theorem paper_moment_solvable_iff (k : ℕ) (hk : 0 < k) (F : Mat (k + 1)) :
    (∃ E : Mat (k + 1), L_moment (B_mat (k + 1)) E = F) ↔
      ∀ h : ℕ, k ≤ h → h ≤ 2 * k → Even h →
        matInnerProd (Z_binom_concrete (k + 1) h) F = 0 := by
  rw [moment_solvable_iff_all_adjoint_tests]
  constructor
  · intro h hidx hlo hhi heven
    exact h _ (Z_binom_concrete_in_adjoint_kernel _ _ (by omega) heven)
  · intro ht Z hZ
    have hm := paper_binomial_kernel_mem_span k hk Z hZ
    change Z ∈ Submodule.span ℚ _ at hm
    clear hZ
    induction hm using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨h, rfl⟩ := hQ
      exact ht h.val h.property.1 h.property.2.1 h.property.2.2
    | zero => simp [matInnerProd]
    | add Q R _ _ hQ hR => rw [matInnerProd_add_left, hQ, hR, add_zero]
    | smul c Q _ hQ => rw [matInnerProd_smul_left, hQ, mul_zero]

/-- The existing executable section solves compatible residuals by the PDF
completeness argument. The scalar order-zero case is direct, so this has the
same unrestricted order domain as the original section specification. No
section coefficients, search predicate, or right-hand side are changed. -/
theorem paper_momentSection_solves (k : ℕ) (F : Mat (k + 1))
    (hF : ∀ h : ℕ, k ≤ h → h ≤ 2 * k → Even h →
      matInnerProd (Z_binom_concrete (k + 1) h) F = 0) :
    L_moment (B_mat (k + 1)) (momentSection k F) = F := by
  cases k with
  | zero =>
    have htest := hF 0 (by omega) (by omega) (by decide)
    have hZ : Z_binom_concrete 1 0 (0 : Fin 1) (0 : Fin 1) = 1 := by
      simpa using Z_binom_concrete_leading (0 : Fin 1) (0 : Fin 1) (by decide)
    have hzero : F = 0 := by
      ext i j
      have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
      have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
      subst i
      subst j
      simpa [matInnerProd, hZ] using htest
    rw [hzero, map_zero]
    simp [L_moment]
  | succ k =>
    apply FaithfulEffectiveLinear.section_on_range
      (momentLinear (B_mat (k + 1 + 1))) (exists_moment_section (k + 1))
    exact (paper_moment_solvable_iff (k + 1) (by omega) F).mpr hF

#print axioms paper_momentSection_solves
#print axioms paper_moment_solvable_iff
#print axioms paper_factor_inverse
#print axioms paperBasis_eq_existing

end Karlin.FaithfulPaperCokernel
