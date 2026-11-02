import Karlin.FaithfulFiniteDifference

/-!
# Integer scale for the v15 higher-test correction

This file separates the arithmetic of v15 Lemma `lem:scale` from the
identification of its polynomial inputs with the manuscript's reference tables.
These arithmetic lemmas do not depend on the final family theorem.
-/

namespace Karlin.FaithfulScale

open scoped BigOperators
open Polynomial

/-- A rational number is an integer multiple of a specified natural number. -/
def IntegerMultiple (d : ℕ) (q : ℚ) : Prop := ∃ z : ℤ, q = (d : ℚ) * z

theorem integerMultiple_zero (d : ℕ) : IntegerMultiple d 0 := ⟨0, by simp⟩

theorem integerMultiple_sum {ι : Type*} (s : Finset ι) (d : ℕ) (f : ι → ℚ)
    (h : ∀ x ∈ s, IntegerMultiple d (f x)) : IntegerMultiple d (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using integerMultiple_zero d
  | @insert a s ha ih =>
    obtain ⟨u, hu⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨v, hv⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    refine ⟨u + v, ?_⟩
    rw [Finset.sum_insert ha, hu, hv]
    push_cast
    ring

/-- The finite least common multiple in `eq:scalechoice`.
An empty support contributes one. -/
noncomputable def scaleDenominator {ι : Type*} [Fintype ι]
    (L : ι → ℚ[X]) : ℕ :=
  Finset.univ.lcm fun i => (L i).support.lcm fun r => ((L i).coeff r).den

theorem scaleDenominator_pos {ι : Type*} [Fintype ι] (L : ι → ℚ[X]) :
    0 < scaleDenominator L := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro i _
  apply Finset.lcm_ne_zero_iff.mpr
  intro r _
  exact Rat.den_ne_zero _

theorem coefficient_den_dvd_scaleDenominator {ι : Type*} [Fintype ι]
    (L : ι → ℚ[X]) (i : ι) (r : ℕ) (hr : r ∈ (L i).support) :
    ((L i).coeff r).den ∣ scaleDenominator L := by
  have h₁ : ((L i).coeff r).den ∣ (L i).support.lcm (fun r => ((L i).coeff r).den) :=
    Finset.dvd_lcm hr
  have h₂ : (L i).support.lcm (fun r => ((L i).coeff r).den) ∣ scaleDenominator L :=
    Finset.dvd_lcm (f := fun j => (L j).support.lcm fun r => ((L j).coeff r).den)
      (Finset.mem_univ i)
  exact h₁.trans h₂

/-- Fixed from the rational polynomials before any phase/time quantifier. -/
noncomputable def integerScale (k : ℕ) {ι : Type*} [Fintype ι]
    (L : ι → ℚ[X]) : ℕ := scaleDenominator L * k.factorial

theorem integerScale_pos (k : ℕ) {ι : Type*} [Fintype ι] (L : ι → ℚ[X]) :
    0 < integerScale k L :=
  Nat.mul_pos (scaleDenominator_pos L) (Nat.factorial_pos k)

/-- Positive degree is essential: a coefficient of degree `r ≥ i ≥ 1`
clears its denominator at `D*M` and retains the factor `M^i`. -/
theorem coefficient_scaled_integerMultiple (a : ℚ) (D M i r : ℕ)
    (hi : 1 ≤ i) (hir : i ≤ r) (ha : a.den ∣ D) :
    IntegerMultiple (M ^ i) (a * ((D * M : ℕ) : ℚ) ^ r) := by
  obtain ⟨n, hn⟩ := ha.trans (dvd_pow_self D (by omega : r ≠ 0))
  obtain ⟨s, hs⟩ := pow_dvd_pow M hir
  refine ⟨a.num * (n : ℤ) * (s : ℤ), ?_⟩
  have hnQ : (D : ℚ) ^ r = (a.den : ℚ) * n := by exact_mod_cast hn
  have hsQ : (M : ℚ) ^ r = (M : ℚ) ^ i * s := by exact_mod_cast hs
  push_cast
  rw [mul_pow, ← mul_assoc, hnQ, ← mul_assoc, Rat.mul_den_eq_num, hsQ]
  ring

/-- Polynomial evaluation retains an integer multiple of `(k!)^i`. -/
theorem polynomial_scaled_integerMultiple {ι : Type*} [Fintype ι]
    (L : ι → ℚ[X]) (j : ι) (k i : ℕ) (hi : 1 ≤ i)
    (hvanish : ∀ r < i, (L j).coeff r = 0) :
    IntegerMultiple (k.factorial ^ i) ((L j).eval (integerScale k L : ℚ)) := by
  rw [Polynomial.eval_eq_sum]
  change IntegerMultiple (k.factorial ^ i)
    (∑ r ∈ (L j).support, (L j).coeff r * (integerScale k L : ℚ) ^ r)
  apply integerMultiple_sum
  intro r hr
  have hir : i ≤ r := by
    by_contra h
    have hz := hvanish r (by omega)
    exact (Polynomial.mem_support_iff.mp hr) hz
  exact coefficient_scaled_integerMultiple ((L j).coeff r)
    (scaleDenominator L) k.factorial i r hi hir
    (coefficient_den_dvd_scaleDenominator L j r hr)

theorem integerMultiple_of_dvd {a b : ℕ} {q : ℚ} (hab : a ∣ b)
    (hq : IntegerMultiple b q) : IntegerMultiple a q := by
  obtain ⟨n, hn⟩ := hab
  obtain ⟨z, hz⟩ := hq
  refine ⟨(n : ℤ) * z, ?_⟩
  rw [hz, hn]
  push_cast
  ring

/-- Includes the zero coordinate, which cannot be handled by clearing
denominators alone. -/
theorem correction_factorial_integrality (k : ℕ) (L : Fin (k + 1) → ℚ[X])
    (hzero : L ⟨0, by omega⟩ = 0)
    (hvanish : ∀ (i : Fin (k + 1)) r, r < i.val → (L i).coeff r = 0)
    (i : Fin (k + 1)) :
    IntegerMultiple i.val.factorial ((L i).eval (integerScale k L : ℚ)) := by
  by_cases hi : i.val = 0
  · have he : i = ⟨0, by omega⟩ := Fin.ext hi
    rw [he, hzero, Polynomial.eval_zero]
    exact integerMultiple_zero _
  · apply integerMultiple_of_dvd
      ((Nat.factorial_dvd_factorial (by omega : i.val ≤ k)).trans
        (dvd_pow_self k.factorial hi))
    exact polynomial_scaled_integerMultiple L i k i.val (by omega) (hvanish i)

/-- Ordinary monomial coefficients of the scaled divided-power row are integers. -/
theorem correction_ordinary_coefficient_integral (k : ℕ)
    (L : Fin (k + 1) → ℚ[X]) (hzero : L ⟨0, by omega⟩ = 0)
    (hvanish : ∀ (i : Fin (k + 1)) r, r < i.val → (L i).coeff r = 0)
    (i : Fin (k + 1)) :
    ∃ z : ℤ, (L i).eval (integerScale k L : ℚ) / i.val.factorial = z := by
  obtain ⟨z, hz⟩ := correction_factorial_integrality k L hzero hvanish i
  refine ⟨z, ?_⟩
  rw [hz]
  have hn : (i.val.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i.val
  field_simp

/-- Finite differences at zero recover the given row's integral binomial
coefficients from its integral values at `0,…,w-1`. -/
theorem binomial_row_integral_of_values (w : ℕ) (row : Fin w → ℚ)
    (hvalues : ∀ n < w, IntegerMultiple 1 (∑ j : Fin w, row j * (n.choose j.val : ℚ))) :
    ∀ i : Fin w, IntegerMultiple 1 (row i) := by
  intro i
  rw [FaithfulFiniteDifference.binomial_row_eq_forward_difference row i,
    FaithfulFiniteDifference.forward_difference_formula]
  apply integerMultiple_sum
  intro h hh
  obtain ⟨z, hz⟩ := hvalues h (by have := Finset.mem_range.mp hh; omega)
  refine ⟨(-1 : ℤ) ^ (i.val-h) * (i.val.choose h : ℤ) * z, ?_⟩
  simp [hz]

/-- The actual inverse basis matrix sends binomial evaluation to divided-power
evaluation; this fixes the coefficient convention used in the integer proof. -/
theorem S_inv_mulVec_binomBasis (w q : ℕ) :
    (S_inv_mat w).mulVec (binomBasis w q) = divPowerBasis w q := by
  rw [← S_mat_mulVec_divPowerBasis w q]
  rw [Matrix.mulVec_mulVec, S_inv_mat_mul_S_mat, Matrix.one_mulVec]

/-- The binomial row `ellhat * S⁻¹`, not an unrelated integer witness, is integral. -/
theorem divided_power_to_binomial_integral (w : ℕ) (ellhat : Fin w → ℚ)
    (hfactorial : ∀ i : Fin w, IntegerMultiple i.val.factorial (ellhat i)) :
    ∀ j : Fin w, IntegerMultiple 1 (Matrix.vecMul ellhat (S_inv_mat w) j) := by
  apply binomial_row_integral_of_values
  intro q _
  change IntegerMultiple 1 (Matrix.vecMul ellhat (S_inv_mat w) ⬝ᵥ binomBasis w q)
  rw [← Matrix.dotProduct_mulVec, S_inv_mulVec_binomBasis]
  change IntegerMultiple 1 (∑ i : Fin w, ellhat i * ((q : ℚ) ^ i.val / i.val.factorial))
  apply integerMultiple_sum
  intro i _
  obtain ⟨z, hz⟩ := hfactorial i
  refine ⟨z * (q : ℤ) ^ i.val, ?_⟩
  have hfac : (i.val.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i.val
  rw [hz]
  push_cast
  field_simp

/-- The complete denominator-clearing conclusion in the manuscript's actual
binomial-coordinate convention.  Polynomial valuation is an explicit input
here; subsequent lemmas establish its preservation by the symbolic pivots. -/
theorem correction_binomial_integrality (k : ℕ) (L : Fin (k + 1) → ℚ[X])
    (hzero : L ⟨0, by omega⟩ = 0)
    (hvanish : ∀ (i : Fin (k + 1)) r, r < i.val → (L i).coeff r = 0) :
    ∀ j : Fin (k + 1), IntegerMultiple 1
      (Matrix.vecMul (fun i => (L i).eval (integerScale k L : ℚ)) (S_inv_mat (k + 1)) j) :=
  divided_power_to_binomial_integral (k + 1) _
    (correction_factorial_integrality k L hzero hvanish)

/-- Exact polynomial division used in the symbolic pivot. -/
noncomputable def monomialPivot (N : ℚ[X]) (d : ℕ) (beta : ℚ) : ℚ[X] :=
  C beta⁻¹ * (N /ₘ X ^ d)

/-- Division by the nonzero pivot retains the required power of the scale.
This uses monic polynomial division, not evaluation at a selected rational scale. -/
theorem monomialPivot_spec (N : ℚ[X]) (i d : ℕ) (beta : ℚ) (hbeta : beta ≠ 0)
    (hN : X ^ (i + d) ∣ N) :
    X ^ i ∣ monomialPivot N d beta ∧
      (C beta * X ^ d) * monomialPivot N d beta = N := by
  obtain ⟨Q, rfl⟩ := hN
  have hdiv : (X ^ (i + d) * Q : ℚ[X]) /ₘ X ^ d = X ^ i * Q := by
    rw [show (X ^ (i + d) * Q : ℚ[X]) = X ^ d * (X ^ i * Q) by rw [pow_add]; ring]
    exact Polynomial.mul_divByMonic_cancel_left _ (Polynomial.monic_X.pow d)
  simp only [monomialPivot, hdiv]
  constructor
  · exact ⟨C beta⁻¹ * Q, by ring⟩
  · calc
      (C beta * X ^ d) * (C beta⁻¹ * (X ^ i * Q)) =
          (C beta * C beta⁻¹) * (X ^ (i + d) * Q) := by rw [pow_add]; ring
      _ = X ^ (i + d) * Q := by rw [← C_mul, mul_inv_cancel₀ hbeta, C_1, one_mul]

/-- Evaluation of the symbolic pivot is exactly the rational pivot quotient. -/
theorem monomialPivot_eval (N : ℚ[X]) (i d : ℕ) (beta t : ℚ)
    (hbeta : beta ≠ 0) (ht : t ≠ 0) (hN : X ^ (i + d) ∣ N) :
    (monomialPivot N d beta).eval t = N.eval t / (beta * t ^ d) := by
  have h := congrArg (Polynomial.eval t) (monomialPivot_spec N i d beta hbeta hN).2
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at h
  apply (eq_div_iff (mul_ne_zero hbeta (pow_ne_zero d ht))).2
  simpa only [mul_comm] using h

/-- Polynomial version of the divided-power test, with precisely the same
constant test matrices as the evaluated rational solver. -/
noncomputable def polynomialInner (k h : ℕ)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X]) : ℚ[X] :=
  ∑ a, ∑ b, C (Z_DP (k + 1) h a b) * F a b

noncomputable def polynomialTail (k : ℕ) (psi ell : Fin (k + 1) → ℚ[X]) (i : ℕ) : ℚ[X] :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin (k + 1) => a.val > i),
    ∑ b ∈ Finset.univ.filter (fun b : Fin (k + 1) => b.val < k),
      C (Z_DP (k + 1) (i + k - 1) a b) * ell a * psi b

noncomputable def polynomialNumerator (k : ℕ)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X])
    (psi ell : Fin (k + 1) → ℚ[X]) (i : ℕ) : ℚ[X] :=
  polynomialInner k (i + k - 1) F - polynomialTail k psi ell i

/-- Only interior entries are needed: support of a higher test excludes the
first row and column. -/
theorem polynomialInner_divisible {k h : ℕ} (hkh : k < h)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X])
    (hF : ∀ a b, 0 < a.val → 0 < b.val → X ^ (a.val + b.val) ∣ F a b) :
    X ^ h ∣ polynomialInner k h F := by
  apply Finset.dvd_sum
  intro a _
  apply Finset.dvd_sum
  intro b _
  by_cases hab : a.val + b.val < h
  · simp [Z_DP_apply_of_add_lt hab]
  · have ha : 0 < a.val := by omega
    have hb : 0 < b.val := by omega
    exact dvd_mul_of_dvd_right
      ((pow_dvd_pow (X : ℚ[X]) (by omega : h ≤ a.val + b.val)).trans (hF a b ha hb)) _

theorem polynomialTail_divisible {k i : ℕ}
    (psi ell : Fin (k + 1) → ℚ[X])
    (hpsi : ∀ b, X ^ b.val ∣ psi b) (hell : ∀ a, X ^ a.val ∣ ell a) :
    X ^ (i + k - 1) ∣ polynomialTail k psi ell i := by
  apply Finset.dvd_sum
  intro a _
  apply Finset.dvd_sum
  intro b _
  by_cases hab : a.val + b.val < i + k - 1
  · simp [Z_DP_apply_of_add_lt hab]
  · have hprod : X ^ (a.val + b.val) ∣ ell a * psi b := by
      rw [pow_add]
      exact mul_dvd_mul (hell a) (hpsi b)
    have hdiv := (pow_dvd_pow (X : ℚ[X]) (by omega : i + k - 1 ≤ a.val + b.val)).trans hprod
    simpa only [mul_assoc] using dvd_mul_of_dvd_right hdiv (C (Z_DP (k + 1) (i + k - 1) a b))

theorem polynomialNumerator_divisible {k i : ℕ} (hi : 1 < i) (hik : i < k)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X]) (psi ell : Fin (k + 1) → ℚ[X])
    (hF : ∀ a b, 0 < a.val → 0 < b.val → X ^ (a.val + b.val) ∣ F a b)
    (hpsi : ∀ b, X ^ b.val ∣ psi b) (hell : ∀ a, X ^ a.val ∣ ell a) :
    X ^ (i + (k - 1)) ∣ polynomialNumerator k F psi ell i := by
  have hiadd : i + (k - 1) = i + k - 1 := by omega
  rw [hiadd]
  exact dvd_sub (polynomialInner_divisible (by omega) F hF)
    (polynomialTail_divisible psi ell hpsi hell)

/-- A symbolic pivot with the manuscript's sign and the fixed leading
coefficient of `psi_(k-1)`. -/
noncomputable def polynomialPivot (k : ℕ)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X]) (psi ell : Fin (k + 1) → ℚ[X])
    (beta : ℚ) (i : ℕ) : ℚ[X] :=
  monomialPivot (polynomialNumerator k F psi ell i) (k - 1) ((-1 : ℚ) ^ i * beta)

noncomputable def polynomialHelper (k : ℕ)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X]) (psi : Fin (k + 1) → ℚ[X])
    (beta : ℚ) : ℕ → (Fin (k + 1) → ℚ[X])
  | 0 => fun _ => 0
  | s + 1 =>
    let prev := polynomialHelper k F psi beta s
    let i := k - 1 - s
    if 1 < i ∧ i < k ∧ (i + k - 1) % 2 = 0 then
      fun x => if x.val = i then polynomialPivot k F psi prev beta i else prev x
    else prev

noncomputable def polynomialSolver (k : ℕ)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X]) (psi : Fin (k + 1) → ℚ[X])
    (beta : ℚ) : Fin (k + 1) → ℚ[X] := polynomialHelper k F psi beta (k - 1)

/-- Every stage retains the scale valuation, before any scale is chosen. -/
theorem polynomialHelper_divisible (k : ℕ)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X]) (psi : Fin (k + 1) → ℚ[X])
    (beta : ℚ) (hbeta : beta ≠ 0)
    (hF : ∀ a b, 0 < a.val → 0 < b.val → X ^ (a.val + b.val) ∣ F a b)
    (hpsi : ∀ b, X ^ b.val ∣ psi b) :
    ∀ s a, X ^ a.val ∣ polynomialHelper k F psi beta s a := by
  intro s
  induction s with
  | zero => intro a; exact dvd_zero _
  | succ s ih =>
    intro a
    by_cases hp : 1 < k - 1 - s ∧ k - 1 - s < k ∧ (k - 1 - s + k - 1) % 2 = 0
    · rw [polynomialHelper, if_pos hp]
      by_cases ha : a.val = k - 1 - s
      · rw [if_pos ha, ha]
        exact (monomialPivot_spec _ _ _ _ (mul_ne_zero (pow_ne_zero _ (by norm_num)) hbeta)
          (polynomialNumerator_divisible hp.1 hp.2.1 F psi _ hF hpsi ih)).1
      · rw [if_neg ha]
        exact ih a
    · rw [polynomialHelper, if_neg hp]
      exact ih a

/-- All unselected coordinates, in particular zero, one, and the top, stay zero. -/
theorem polynomialHelper_unselected (k : ℕ)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X]) (psi : Fin (k + 1) → ℚ[X])
    (beta : ℚ) (a : Fin (k + 1)) (ha : a.val ≤ 1 ∨ k ≤ a.val) :
    ∀ s, polynomialHelper k F psi beta s a = 0 := by
  intro s
  induction s with
  | zero => rfl
  | succ s ih =>
    by_cases hp : 1 < k - 1 - s ∧ k - 1 - s < k ∧ (k - 1 - s + k - 1) % 2 = 0
    · rw [polynomialHelper, if_pos hp]
      rw [if_neg (by omega : a.val ≠ k - 1 - s)]
      exact ih
    · rw [polynomialHelper, if_neg hp]
      exact ih

theorem polynomialNumerator_eval (k i : ℕ)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X])
    (psi ell : Fin (k + 1) → ℚ[X]) (t : ℚ) :
    (polynomialNumerator k F psi ell i).eval t =
      matInnerProd (Z_DP (k + 1) (i + k - 1)) (fun a b => (F a b).eval t) -
        pivotTail k (fun b => (psi b).eval t) (fun a => (ell a).eval t) i := by
  simp [polynomialNumerator, polynomialInner, polynomialTail, matInnerProd, pivotTail,
    Polynomial.eval_finset_sum]

theorem polynomialPivot_eval {k i : ℕ} (hi : 1 < i) (hik : i < k)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X]) (psi ell : Fin (k + 1) → ℚ[X])
    (beta t : ℚ) (hbeta : beta ≠ 0) (ht : t ≠ 0)
    (hF : ∀ a b, 0 < a.val → 0 < b.val → X ^ (a.val + b.val) ∣ F a b)
    (hpsi : ∀ b, X ^ b.val ∣ psi b) (hell : ∀ a, X ^ a.val ∣ ell a)
    (hprev : psi ⟨k - 1, by omega⟩ = C beta * X ^ (k - 1)) :
    (polynomialPivot k F psi ell beta i).eval t =
      pivotTerm k (fun b => (psi b).eval t) (fun a b => (F a b).eval t)
        (fun a => (ell a).eval t) i := by
  have hs : (-1 : ℚ) ^ i ≠ 0 := pow_ne_zero _ (by norm_num)
  have hp : beta * t ^ (k - 1) ≠ 0 := mul_ne_zero hbeta (pow_ne_zero _ ht)
  have hsign : (-1 : ℚ) ^ i * (-1 : ℚ) ^ i = 1 := by rw [← mul_pow]; norm_num
  have hsign2 : ((-1 : ℚ) ^ i) ^ 2 = 1 := by nlinarith [hsign]
  rw [polynomialPivot, monomialPivot_eval _ i _ _ t (mul_ne_zero hs hbeta) ht
    (polynomialNumerator_divisible hi hik F psi ell hF hpsi hell)]
  rw [polynomialNumerator_eval]
  simp only [pivotTerm, hprev, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  rw [mul_assoc]
  field_simp
  simp only [hsign2, mul_one]

/-- A single polynomial family evaluates to the existing rational solver at
every nonzero scale, not just at the eventual selected scale. -/
theorem polynomialHelper_eval (k : ℕ)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X]) (psi : Fin (k + 1) → ℚ[X])
    (beta t : ℚ) (hbeta : beta ≠ 0) (ht : t ≠ 0)
    (hF : ∀ a b, 0 < a.val → 0 < b.val → X ^ (a.val + b.val) ∣ F a b)
    (hpsi : ∀ b, X ^ b.val ∣ psi b)
    (hprev : psi ⟨k - 1, by omega⟩ = C beta * X ^ (k - 1)) :
    ∀ s a, (polynomialHelper k F psi beta s a).eval t =
      solveHelper k (fun b => (psi b).eval t) (fun a b => (F a b).eval t) s a := by
  intro s
  induction s with
  | zero => intro a; simp [polynomialHelper, solveHelper]
  | succ s ih =>
    intro a
    by_cases hp : 1 < k - 1 - s ∧ k - 1 - s < k ∧ (k - 1 - s + k - 1) % 2 = 0
    · rw [polynomialHelper, solveHelper, if_pos hp, if_pos hp]
      by_cases ha : a.val = k - 1 - s
      · rw [if_pos ha, if_pos ha]
        rw [polynomialPivot_eval hp.1 hp.2.1 F psi _ beta t hbeta ht hF hpsi
          (polynomialHelper_divisible k F psi beta hbeta hF hpsi s) hprev]
        congr 1
        exact funext ih
      · rw [if_neg ha, if_neg ha]
        exact ih a
    · rw [polynomialHelper, solveHelper, if_neg hp, if_neg hp]
      exact ih a

/-- The selected integer scale and the actual binomial row are fixed together.
This packages no compatibility assumptions: those are proved separately below. -/
theorem polynomialSolver_integer_scale (k : ℕ)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X]) (psi : Fin (k + 1) → ℚ[X])
    (beta : ℚ) (hbeta : beta ≠ 0)
    (hF : ∀ a b, 0 < a.val → 0 < b.val → X ^ (a.val + b.val) ∣ F a b)
    (hpsi : ∀ b, X ^ b.val ∣ psi b) :
    let L := polynomialSolver k F psi beta
    0 < integerScale k L ∧ ∀ j : Fin (k + 1), IntegerMultiple 1
      (Matrix.vecMul (fun i => (L i).eval (integerScale k L : ℚ)) (S_inv_mat (k + 1)) j) := by
  intro L
  refine ⟨integerScale_pos k L, correction_binomial_integrality k L ?_ ?_⟩
  · exact polynomialHelper_unselected k F psi beta ⟨0, by omega⟩ (Or.inl (by simp)) (k - 1)
  · intro i r hr
    exact Polynomial.X_pow_dvd_iff.mp
      (polynomialHelper_divisible k F psi beta hbeta hF hpsi (k - 1) i) r hr

/-- All higher tests hold at the single integer scale selected from the
symbolic solution.  The top test is included using its separately supplied
zero entries, exactly as in the manuscript. -/
theorem polynomialSolver_higher_tests (k : ℕ) (hk : 0 < k)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X]) (psi : Fin (k + 1) → ℚ[X])
    (beta : ℚ) (hbeta : beta ≠ 0)
    (hF : ∀ a b, 0 < a.val → 0 < b.val → X ^ (a.val + b.val) ∣ F a b)
    (hpsi : ∀ b, X ^ b.val ∣ psi b)
    (hprev : psi ⟨k - 1, by omega⟩ = C beta * X ^ (k - 1))
    (hpsitop : psi ⟨k, by omega⟩ = 0) (hFtop : F ⟨k, by omega⟩ ⟨k, by omega⟩ = 0) :
    let L := polynomialSolver k F psi beta
    let t : ℚ := integerScale k L
    ∀ h, k < h → h ≤ 2 * k → Even h →
      matInnerProd (Z_DP (k + 1) h)
        ((Matrix.of fun a b => (F a b).eval t) - outerProd (fun a => (L a).eval t)
          (fun b => (psi b).eval t)) = 0 := by
  intro L t h hkh hht heven
  have ht : t ≠ 0 := by
    dsimp [t]
    exact_mod_cast Nat.ne_of_gt (integerScale_pos k L)
  have heq : (fun a => (L a).eval t) =
      solveHigherTestsDP k (fun b => (psi b).eval t) (fun a b => (F a b).eval t) :=
    funext (polynomialHelper_eval k F psi beta t hbeta ht hF hpsi hprev (k - 1))
  rw [heq]
  apply solveHigherTestsDP_solves_all_higher_tests hk hkh hht heven
  · simp [hpsitop]
  · simp only [hprev, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    exact mul_ne_zero hbeta (pow_ne_zero _ ht)
  · simp [hFtop]

theorem polynomialInner_congr_interior {k h : ℕ} (hkh : k < h)
    (F G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X])
    (hFG : ∀ a b, 0 < a.val → 0 < b.val → F a b = G a b) :
    polynomialInner k h F = polynomialInner k h G := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a.val + b.val < h
  · simp [Z_DP_apply_of_add_lt hab]
  · rw [hFG a b (by omega) (by omega)]

theorem polynomialTail_congr_positive {k i : ℕ} (hi : 1 < i)
    (psi phi ell : Fin (k + 1) → ℚ[X])
    (hpsi : ∀ b, 0 < b.val → psi b = phi b) :
    polynomialTail k psi ell i = polynomialTail k phi ell i := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a.val + b.val < i + k - 1
  · simp [Z_DP_apply_of_add_lt hab]
  · rw [hpsi b (by omega)]

/-- The actual algorithm, not just existence of some witness, ignores all
boundary entries of `F` and the constant coefficient of `psi`. -/
theorem polynomialHelper_congr_interior (k : ℕ)
    (F G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X])
    (psi phi : Fin (k + 1) → ℚ[X]) (beta : ℚ)
    (hFG : ∀ a b, 0 < a.val → 0 < b.val → F a b = G a b)
    (hpsi : ∀ b, 0 < b.val → psi b = phi b) :
    ∀ s, polynomialHelper k F psi beta s = polynomialHelper k G phi beta s := by
  intro s
  induction s with
  | zero => rfl
  | succ s ih =>
    by_cases hp : 1 < k - 1 - s ∧ k - 1 - s < k ∧ (k - 1 - s + k - 1) % 2 = 0
    · rw [polynomialHelper, polynomialHelper, if_pos hp, if_pos hp]
      rw [ih]
      have hInner := polynomialInner_congr_interior (by omega : k < k - 1 - s + k - 1) F G hFG
      have hTail := polynomialTail_congr_positive hp.1 psi phi
        (polynomialHelper k G phi beta s) hpsi
      simp only [polynomialPivot, polynomialNumerator, hInner, hTail]
    · rw [polynomialHelper, polynomialHelper, if_neg hp, if_neg hp, ih]

/-- Equality of the interior data fixes the scale and the whole polynomial
correction simultaneously, before all later parameter choices. -/
theorem polynomialSolver_scale_congr (k : ℕ)
    (F G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X])
    (psi phi : Fin (k + 1) → ℚ[X]) (beta : ℚ)
    (hFG : ∀ a b, 0 < a.val → 0 < b.val → F a b = G a b)
    (hpsi : ∀ b, 0 < b.val → psi b = phi b) :
    polynomialSolver k F psi beta = polynomialSolver k G phi beta ∧
      integerScale k (polynomialSolver k F psi beta) =
        integerScale k (polynomialSolver k G phi beta) := by
  have h := polynomialHelper_congr_interior k F G psi phi beta hFG hpsi (k - 1)
  exact ⟨h, congrArg (integerScale k) h⟩

/-! ## Symbolic versions of the manuscript's actual transfer tables -/

/-- `E_(u*tau) S`, with the scale left as the formal variable `X`. -/
noncomputable def endpointHat (k u : ℕ) : Matrix (Fin k) (Fin (k + 1)) ℚ[X] :=
  fun a j => C (S_mat (k + 1) ⟨a.val, by omega⟩ j * (u : ℚ) ^ j.val) * X ^ j.val

/-- `F_tau S`, with the scale left symbolic. -/
noncomputable def bundleHat (k : ℕ) : Matrix (Fin k) (Fin (k + 1)) ℚ[X] :=
  fun a j => C (S_mat (k + 1) ⟨a.val + 1, by omega⟩ j * ((2 : ℚ) ^ j.val - 1)) * X ^ j.val

/-- `(E_tau T - E_(2*tau)) S`, with the scale left symbolic. -/
noncomputable def LHat (k : ℕ) : Matrix (Fin k) (Fin (k + 1)) ℚ[X] :=
  fun a j => (∑ r, endpointHat k 1 a r * C (expN0 (k + 1) 1 r j)) - endpointHat k 2 a j

theorem E_tilde_mul_S_apply (w tau : ℕ) (a j : Fin w) :
    (E_tilde w tau * S_mat w) a j = S_mat w a j * (tau : ℚ) ^ j.val := by
  rw [E_tilde, Matrix.mul_assoc, S_inv_mat_mul_S_mat, Matrix.mul_one]
  simp [scaleDiag, Matrix.mul_diagonal]

theorem endpointHat_eval (k u tau : ℕ) (a : Fin k) (j : Fin (k + 1)) :
    (endpointHat k u a j).eval (tau : ℚ) = (E_tau_mat k (u * tau) * S_mat (k + 1)) a j := by
  have he : (E_tau_mat k (u * tau) * S_mat (k + 1)) a j =
      S_mat (k + 1) ⟨a.val, by omega⟩ j * ((u * tau : ℕ) : ℚ) ^ j.val :=
    E_tilde_mul_S_apply (k + 1) (u * tau) ⟨a.val, by omega⟩ j
  rw [he]
  simp [endpointHat, mul_pow, mul_assoc]

theorem bundleHat_eval (k tau : ℕ) (a : Fin k) (j : Fin (k + 1)) :
    (bundleHat k a j).eval (tau : ℚ) = (F_tau_mat k tau * S_mat (k + 1)) a j := by
  have h : (F_tau_mat k tau * S_mat (k + 1)) a j =
      (E_tilde (k + 1) (2 * tau) * S_mat (k + 1)) ⟨a.val + 1, by omega⟩ j -
      (E_tilde (k + 1) tau * S_mat (k + 1)) ⟨a.val + 1, by omega⟩ j := by
    simp only [Matrix.mul_apply, F_tau_mat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib]
  rw [h, E_tilde_mul_S_apply, E_tilde_mul_S_apply]
  simp only [bundleHat, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Nat.cast_mul, Nat.cast_ofNat, mul_pow]
  ring

theorem LHat_eval (k tau : ℕ) (a : Fin k) (j : Fin (k + 1)) :
    (LHat k a j).eval (tau : ℚ) =
      ((E_tau_mat k tau * T_mat (k + 1) - E_2tau_mat k tau) * S_mat (k + 1)) a j := by
  simp only [LHat, Polynomial.eval_sub, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, endpointHat_eval, one_mul]
  change ((E_tau_mat k tau * S_mat (k + 1)) * expN0 (k + 1) 1) a j -
    (E_tau_mat k (2 * tau) * S_mat (k + 1)) a j = _
  rw [Matrix.sub_mul]
  simp only [Matrix.sub_apply, E_2tau_mat]
  rw [Matrix.mul_assoc, ← T_mat_mul_S_mat, ← Matrix.mul_assoc]

theorem endpointHat_divisible (k u : ℕ) (a : Fin k) (j : Fin (k + 1)) :
    X ^ j.val ∣ endpointHat k u a j := by
  exact ⟨C (S_mat (k + 1) ⟨a.val, by omega⟩ j * (u : ℚ) ^ j.val), mul_comm _ _⟩

theorem bundleHat_divisible (k : ℕ) (a : Fin k) (j : Fin (k + 1)) :
    X ^ j.val ∣ bundleHat k a j := by
  exact ⟨C (S_mat (k + 1) ⟨a.val + 1, by omega⟩ j * ((2 : ℚ) ^ j.val - 1)), mul_comm _ _⟩

theorem LHat_divisible (k : ℕ) (a : Fin k) (j : Fin (k + 1)) :
    X ^ j.val ∣ LHat k a j := by
  apply dvd_sub _ (endpointHat_divisible k 2 a j)
  apply Finset.dvd_sum
  intro r _
  by_cases hrj : r.val < j.val
  · have he : expN0 (k + 1) 1 r j = 0 := by simp [expN0, show ¬ j ≤ r by omega]
    simp [he]
  · exact dvd_mul_of_dvd_left
      ((pow_dvd_pow (X : ℚ[X]) (by omega : j.val ≤ r.val)).trans (endpointHat_divisible k 1 a r)) _

theorem endpointHat_eq_zero_of_lt (k u : ℕ) (a : Fin k) (j : Fin (k + 1))
    (h : a.val < j.val) : endpointHat k u a j = 0 := by
  have hs := S_mat_eq_zero_of_lt (i := (⟨a.val, by omega⟩ : Fin (k + 1))) (j := j) h
  simp [endpointHat, hs]

theorem LHat_eq_zero_of_lt (k : ℕ) (a : Fin k) (j : Fin (k + 1))
    (h : a.val < j.val) : LHat k a j = 0 := by
  rw [LHat, endpointHat_eq_zero_of_lt k 2 a j h, sub_zero]
  apply Finset.sum_eq_zero
  intro r _
  by_cases har : a.val < r.val
  · rw [endpointHat_eq_zero_of_lt k 1 a r har, zero_mul]
  · have hnr : ¬ j ≤ r := by omega
    simp [expN0, hnr]

theorem endpointHat_row_zero (k u : ℕ) (hk : 0 < k) (j : Fin (k + 1)) :
    endpointHat k u ⟨0, hk⟩ j = if j = ⟨0, by omega⟩ then 1 else 0 := by
  by_cases hj : j = ⟨0, by omega⟩
  · rw [if_pos hj, hj]
    simp [endpointHat, S_mat_diag_eq_one]
  · rw [if_neg hj]
    apply endpointHat_eq_zero_of_lt
    have : j.val ≠ 0 := fun h => hj (Fin.ext h)
    change 0 < j.val
    omega

theorem LHat_row_zero (k : ℕ) (hk : 0 < k) (j : Fin (k + 1)) :
    LHat k ⟨0, hk⟩ j = 0 := by
  simp only [LHat, endpointHat_row_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hj : j = ⟨0, by omega⟩
  · rw [if_pos hj, hj]
    simp [expN0]
  · rw [if_neg hj]
    have hj0 : j ≠ 0 := hj
    simp [expN0, hj0]

/-- Constant row, in divided-power coordinates. -/
noncomputable def constantRow (k : ℕ) (c : ℚ) (j : Fin (k + 1)) : ℚ[X] :=
  if j.val = 0 then C c else 0

theorem constantRow_divisible (k : ℕ) (c : ℚ) (j : Fin (k + 1)) :
    X ^ j.val ∣ constantRow k c j := by
  by_cases hj : j.val = 0
  · simp [constantRow, hj]
  · simp [constantRow, hj]

/-- The reference difference row `psi° S` from the manuscript. -/
noncomputable def referencePsi (k : ℕ) (chi : Fin k → ℚ) (cref : ℚ)
    (j : Fin (k + 1)) : ℚ[X] :=
  -(∑ a, C (chi a) * (endpointHat k 2 a j - endpointHat k 1 a j)) - constantRow k cref j

/-- The summary row `f S`. -/
noncomputable def referenceFRow (k : ℕ) (chi : Fin k → ℚ) (cref : ℚ)
    (j : Fin (k + 1)) : ℚ[X] :=
  constantRow k cref j - ∑ a, C (chi a) * LHat k a j

/-- The parent's total-count row after the moving-window transfer. -/
noncomputable def referenceCountRow (k : ℕ) (lengthRow : Fin k → ℚ)
    (j : Fin (k + 1)) : ℚ[X] := ∑ b, C (lengthRow b) * bundleHat k b j

/-- The first two products of the exact summary equation `eq:summary`, in
divided-power coordinates.  The omitted two products have boundary support
and cannot enter the higher tests. -/
noncomputable def referenceInterior (k : ℕ) (M : Matrix (Fin k) (Fin k) ℚ)
    (lengthRow chi : Fin k → ℚ) (cref : ℚ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ[X] :=
  fun i j => (∑ a, ∑ b, LHat k a i * C (M a b) * bundleHat k b j) +
    referenceFRow k chi cref i * referenceCountRow k lengthRow j

theorem referencePsi_divisible (k : ℕ) (chi : Fin k → ℚ) (cref : ℚ)
    (j : Fin (k + 1)) : X ^ j.val ∣ referencePsi k chi cref j := by
  apply dvd_sub _ (constantRow_divisible k cref j)
  apply dvd_neg.mpr
  apply Finset.dvd_sum
  intro a _
  exact dvd_mul_of_dvd_right
    (dvd_sub (endpointHat_divisible k 2 a j) (endpointHat_divisible k 1 a j)) _

theorem referenceFRow_divisible (k : ℕ) (chi : Fin k → ℚ) (cref : ℚ)
    (j : Fin (k + 1)) : X ^ j.val ∣ referenceFRow k chi cref j := by
  apply dvd_sub (constantRow_divisible k cref j)
  apply Finset.dvd_sum
  intro a _
  exact dvd_mul_of_dvd_right (LHat_divisible k a j) _

theorem referenceCountRow_divisible (k : ℕ) (lengthRow : Fin k → ℚ)
    (j : Fin (k + 1)) : X ^ j.val ∣ referenceCountRow k lengthRow j := by
  apply Finset.dvd_sum
  intro b _
  exact dvd_mul_of_dvd_right (bundleHat_divisible k b j) _

theorem referenceInterior_divisible (k : ℕ) (M : Matrix (Fin k) (Fin k) ℚ)
    (lengthRow chi : Fin k → ℚ) (cref : ℚ) (i j : Fin (k + 1)) :
    X ^ (i.val + j.val) ∣ referenceInterior k M lengthRow chi cref i j := by
  apply dvd_add
  · apply Finset.dvd_sum
    intro a _
    apply Finset.dvd_sum
    intro b _
    rw [pow_add]
    exact mul_dvd_mul (dvd_mul_of_dvd_left (LHat_divisible k a i) _) (bundleHat_divisible k b j)
  · rw [pow_add]
    exact mul_dvd_mul (referenceFRow_divisible k chi cref i)
      (referenceCountRow_divisible k lengthRow j)

theorem referencePsi_top_zero (k : ℕ) (hk : 0 < k) (chi : Fin k → ℚ) (cref : ℚ) :
    referencePsi k chi cref ⟨k, by omega⟩ = 0 := by
  simp only [referencePsi]
  have hs : (∑ a : Fin k, C (chi a) *
      (endpointHat k 2 a ⟨k, by omega⟩ - endpointHat k 1 a ⟨k, by omega⟩)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    rw [endpointHat_eq_zero_of_lt k 2 a _ a.isLt, endpointHat_eq_zero_of_lt k 1 a _ a.isLt]
    simp
  simp [hs, constantRow, Nat.ne_of_gt hk]

theorem referenceInterior_top_zero (k : ℕ) (hk : 0 < k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (cref : ℚ) :
    referenceInterior k M lengthRow chi cref ⟨k, by omega⟩ ⟨k, by omega⟩ = 0 := by
  have hL : ∀ a : Fin k, LHat k a ⟨k, by omega⟩ = 0 := fun a => LHat_eq_zero_of_lt k a _ a.isLt
  simp [referenceInterior, referenceFRow, hL, constantRow, Nat.ne_of_gt hk]

/-- The exact leading pivot coefficient claimed in v15. -/
theorem referencePsi_prev (k : ℕ) (hk : 2 ≤ k) (chi : Fin k → ℚ) (cref : ℚ) :
    referencePsi k chi cref ⟨k - 1, by omega⟩ =
      C (-chi ⟨k - 1, by omega⟩ * ((2 : ℚ) ^ (k - 1) - 1)) * X ^ (k - 1) := by
  let a₀ : Fin k := ⟨k - 1, by omega⟩
  let j₀ : Fin (k + 1) := ⟨k - 1, by omega⟩
  have hsum : (∑ a : Fin k, C (chi a) * (endpointHat k 2 a j₀ - endpointHat k 1 a j₀)) =
      C (chi a₀) * (endpointHat k 2 a₀ j₀ - endpointHat k 1 a₀ j₀) := by
    apply Finset.sum_eq_single a₀
    · intro a _ ha
      have hlt : a.val < j₀.val := by
        have hne : a.val ≠ k - 1 := fun h => ha (Fin.ext h)
        dsimp [j₀]
        omega
      rw [endpointHat_eq_zero_of_lt k 2 a j₀ hlt, endpointHat_eq_zero_of_lt k 1 a j₀ hlt]
      simp
    · simp
  change -(∑ a : Fin k, C (chi a) * (endpointHat k 2 a j₀ - endpointHat k 1 a j₀)) -
      constantRow k cref j₀ = _
  rw [hsum]
  have hs : S_mat (k + 1) ⟨a₀.val, by omega⟩ j₀ = 1 := S_mat_diag_eq_one j₀
  simp only [endpointHat, hs, one_mul, Nat.cast_one, one_pow, Polynomial.C_1]
  have hjnz : j₀.val ≠ 0 := by dsimp [j₀]; omega
  simp only [constantRow, hjnz, if_false, sub_zero]
  dsimp [a₀, j₀]
  rw [Polynomial.C_mul, Polynomial.C_neg, Polynomial.C_sub, Polynomial.C_1]
  ring

theorem referencePivot_ne_zero (k : ℕ) (hk : 2 ≤ k) (chi : Fin k → ℚ)
    (hchi : chi ⟨k - 1, by omega⟩ ≠ 0) :
    -chi ⟨k - 1, by omega⟩ * ((2 : ℚ) ^ (k - 1) - 1) ≠ 0 := by
  apply mul_ne_zero (neg_ne_zero.mpr hchi)
  have hpow : (1 : ℚ) < 2 ^ (k - 1) := one_lt_pow₀ (by norm_num) (by omega)
  exact ne_of_gt (sub_pos.mpr hpow)

theorem referencePsi_congr_positive (k : ℕ) (chi chi' : Fin k → ℚ) (c c' : ℚ)
    (hchi : ∀ a, 0 < a.val → chi a = chi' a) (j : Fin (k + 1)) (hj : 0 < j.val) :
    referencePsi k chi c j = referencePsi k chi' c' j := by
  have hconst : constantRow k c j = 0 ∧ constantRow k c' j = 0 := by
    simp [constantRow, Nat.ne_of_gt hj]
  simp only [referencePsi, hconst.1, hconst.2, sub_zero, neg_inj]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : 0 < a.val
  · rw [hchi a ha]
  · have haz : a = ⟨0, by omega⟩ := Fin.ext (show a.val = 0 by omega)
    rw [haz, endpointHat_row_zero, endpointHat_row_zero, sub_self]
    simp

theorem referenceFRow_congr_positive (k : ℕ) (chi chi' : Fin k → ℚ) (c c' : ℚ)
    (hchi : ∀ a, 0 < a.val → chi a = chi' a) (j : Fin (k + 1)) (hj : 0 < j.val) :
    referenceFRow k chi c j = referenceFRow k chi' c' j := by
  have hconst : constantRow k c j = 0 ∧ constantRow k c' j = 0 := by
    simp [constantRow, Nat.ne_of_gt hj]
  simp only [referenceFRow, hconst.1, hconst.2, zero_sub, neg_inj]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : 0 < a.val
  · rw [hchi a ha]
  · have haz : a = ⟨0, by omega⟩ := Fin.ext (show a.val = 0 by omega)
    rw [haz, LHat_row_zero]
    simp

/-- Row zero of `Rᵀ C` and the constant parent score disappear from the
interior reference table, by the actual transfer identities. -/
theorem referenceInterior_congr_interior (k : ℕ)
    (M M' : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi chi' : Fin k → ℚ) (c c' : ℚ)
    (hM : ∀ a b, 0 < a.val → M a b = M' a b)
    (hchi : ∀ a, 0 < a.val → chi a = chi' a)
    (i j : Fin (k + 1)) (hi : 0 < i.val) :
    referenceInterior k M lengthRow chi c i j = referenceInterior k M' lengthRow chi' c' i j := by
  simp only [referenceInterior, referenceFRow_congr_positive k chi chi' c c' hchi i hi]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : 0 < a.val
  · rw [hM a b ha]
  · have haz : a = ⟨0, by omega⟩ := Fin.ext (show a.val = 0 by omega)
    rw [haz, LHat_row_zero]
    simp

/-- The manuscript's deterministic correction from precisely its algebraic
parent summaries.  No trajectory or late reset parameter is an input. -/
noncomputable def referenceSolver (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (cref : ℚ) :
    Fin (k + 1) → ℚ[X] :=
  polynomialSolver k (referenceInterior k M lengthRow chi cref) (referencePsi k chi cref)
    (-chi ⟨k - 1, by omega⟩ * ((2 : ℚ) ^ (k - 1) - 1))

/-- Independence of the chosen polynomial correction and scale from row zero
of `RᵀC`, from `chi_0`, and even from the reference gain's boundary terms. -/
theorem referenceSolver_scale_independent (k : ℕ) (hk : 2 ≤ k)
    (M M' : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi chi' : Fin k → ℚ) (c c' : ℚ)
    (hM : ∀ a b, 0 < a.val → M a b = M' a b)
    (hchi : ∀ a, 0 < a.val → chi a = chi' a) :
    referenceSolver k hk M lengthRow chi c = referenceSolver k hk M' lengthRow chi' c' ∧
      integerScale k (referenceSolver k hk M lengthRow chi c) =
        integerScale k (referenceSolver k hk M' lengthRow chi' c') := by
  have hp := hchi ⟨k - 1, by omega⟩ (by dsimp; omega)
  simp only [referenceSolver, hp]
  exact polynomialSolver_scale_congr k _ _ _ _ _
    (fun i j hi _ => referenceInterior_congr_interior k M M' lengthRow chi chi' c c' hM hchi i j hi)
    (referencePsi_congr_positive k chi chi' c c' hchi)

/-- Scale and integer correction for the literal algebraic summaries.
There is no assumed integrality, symbolic-solver condition, or test condition.
The only nondegeneracy input is the parent's nonzero leading score coefficient. -/
theorem reference_integer_scale (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (cref : ℚ)
    (hchi : chi ⟨k - 1, by omega⟩ ≠ 0) :
    let L := referenceSolver k hk M lengthRow chi cref
    let tau := integerScale k L
    0 < tau ∧ ∃ ell : Fin (k + 1) → ℤ,
      Matrix.vecMul (fun j => (ell j : ℚ)) (S_mat (k + 1)) =
        (fun j => (L j).eval (tau : ℚ)) ∧
      ∀ h, k < h → h ≤ 2 * k → Even h →
        matInnerProd (Z_DP (k + 1) h)
          ((Matrix.of fun a b => (referenceInterior k M lengthRow chi cref a b).eval (tau : ℚ)) -
            outerProd (Matrix.vecMul (fun j => (ell j : ℚ)) (S_mat (k + 1)))
              (fun b => (referencePsi k chi cref b).eval (tau : ℚ))) = 0 := by
  intro L tau
  have hbeta := referencePivot_ne_zero k hk chi hchi
  have hF := fun a b (_ : 0 < a.val) (_ : 0 < b.val) =>
    referenceInterior_divisible k M lengthRow chi cref a b
  have hInt := polynomialSolver_integer_scale k (referenceInterior k M lengthRow chi cref)
    (referencePsi k chi cref) _ hbeta hF (referencePsi_divisible k chi cref)
  have hz : ∀ j : Fin (k + 1), ∃ z : ℤ,
      Matrix.vecMul (fun i => (L i).eval (tau : ℚ)) (S_inv_mat (k + 1)) j = (z : ℚ) := by
    intro j
    obtain ⟨z, hz⟩ := hInt.2 j
    exact ⟨z, by simpa only [Nat.cast_one, one_mul] using hz⟩
  choose ell hell using hz
  have hrow : (fun j => (ell j : ℚ)) =
      Matrix.vecMul (fun i => (L i).eval (tau : ℚ)) (S_inv_mat (k + 1)) := (funext hell).symm
  have hDP : Matrix.vecMul (fun j => (ell j : ℚ)) (S_mat (k + 1)) =
      (fun j => (L j).eval (tau : ℚ)) := by
    rw [hrow, Matrix.vecMul_vecMul, S_inv_mat_mul_S_mat, Matrix.vecMul_one]
  refine ⟨hInt.1, ell, hDP, ?_⟩
  rw [hDP]
  exact polynomialSolver_higher_tests k (by omega) (referenceInterior k M lengthRow chi cref)
    (referencePsi k chi cref) _ hbeta hF (referencePsi_divisible k chi cref)
    (referencePsi_prev k hk chi cref) (referencePsi_top_zero k (by omega) chi cref)
    (referenceInterior_top_zero k (by omega) M lengthRow chi cref)

/-- The shift-minus-double-endpoint matrix used literally in `eq:summary`. -/
noncomputable def rationalL (k tau : ℕ) : Matrix (Fin k) (Fin (k + 1)) ℚ :=
  E_tau_mat k tau * T_mat (k + 1) - E_2tau_mat k tau

theorem e0_vecMul_S (k : ℕ) :
    Matrix.vecMul (e0_row (k + 1)) (S_mat (k + 1)) = e0_row (k + 1) := by
  ext j
  have hrow : S_mat (k + 1) ⟨0, by omega⟩ j = e0_row (k + 1) j := by
    by_cases hj : j.val = 0
    · have he : j = ⟨0, by omega⟩ := Fin.ext hj
      rw [he, S_mat_diag_eq_one]
      simp [e0_row]
    · rw [S_mat_eq_zero_of_lt (show (⟨0, by omega⟩ : Fin (k + 1)).val < j.val by
        change 0 < j.val; omega)]
      simp [e0_row, hj]
  simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, e0_row] using hrow

theorem referenceFRow_eval (k tau : ℕ) (chi : Fin k → ℚ) (c : ℚ) :
    (fun j => (referenceFRow k chi c j).eval (tau : ℚ)) =
      Matrix.vecMul (c • e0_row (k + 1) - Matrix.vecMul chi (rationalL k tau)) (S_mat (k + 1)) := by
  rw [Matrix.sub_vecMul, Matrix.smul_vecMul, e0_vecMul_S, Matrix.vecMul_vecMul]
  ext j
  simp [referenceFRow, constantRow, Polynomial.eval_finset_sum, LHat_eval,
    Matrix.vecMul, dotProduct, rationalL, e0_row, apply_ite]

theorem referencePsi_eval (k tau : ℕ) (chi : Fin k → ℚ) (c : ℚ) :
    (fun j => (referencePsi k chi c j).eval (tau : ℚ)) =
      Matrix.vecMul (-Matrix.vecMul chi (E_2tau_mat k tau - E_tau_mat k tau) -
        c • e0_row (k + 1)) (S_mat (k + 1)) := by
  rw [Matrix.sub_vecMul, Matrix.neg_vecMul, Matrix.smul_vecMul, e0_vecMul_S,
    Matrix.vecMul_vecMul, Matrix.sub_mul]
  ext j
  by_cases hj : j = 0 <;>
    simp [referencePsi, constantRow, Polynomial.eval_finset_sum, endpointHat_eval,
      Matrix.vecMul, dotProduct, E_2tau_mat, e0_row, Finset.sum_sub_distrib, mul_sub, hj]

/-- Exact evaluation of the first two products in `eq:summary`, expressed in
the manuscript's divided-power coordinates. -/
theorem referenceInterior_eval (k tau : ℕ) (M : Matrix (Fin k) (Fin k) ℚ)
    (lengthRow chi : Fin k → ℚ) (c : ℚ) :
    (Matrix.of fun i j => (referenceInterior k M lengthRow chi c i j).eval (tau : ℚ)) =
      (rationalL k tau * S_mat (k + 1)).transpose * M * (F_tau_mat k tau * S_mat (k + 1)) +
      outerProd (Matrix.vecMul (c • e0_row (k + 1) - Matrix.vecMul chi (rationalL k tau)) (S_mat (k + 1)))
        (Matrix.vecMul lengthRow (F_tau_mat k tau * S_mat (k + 1))) := by
  ext i j
  have hf := congrFun (referenceFRow_eval k tau chi c) i
  simp only [Matrix.of_apply, referenceInterior, Polynomial.eval_add, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C, LHat_eval, bundleHat_eval, hf,
    referenceCountRow, Matrix.add_apply, outerProd, Matrix.of_apply]
  congr 1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, rationalL]
  rw [Finset.sum_comm]

/-- Basis change for the correction's rank-one matrix. -/
theorem outerProd_basis_change {w : ℕ} (S : Matrix (Fin w) (Fin w) ℚ)
    (ell psi : Fin w → ℚ) :
    S.transpose * outerProd ell psi * S =
      outerProd (Matrix.vecMul ell S) (Matrix.vecMul psi S) := by
  rw [mul_outerProd, outerProd_mul]
  congr 1
  ext i
  simp [Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]

/-- A higher test sees only interior entries.  This is the interface used by
the old-score/count-table summary identity, including its boundary terms. -/
theorem higher_test_congr_interior {k h : ℕ} (hkh : k < h)
    (F G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hFG : ∀ i j, 0 < i.val → 0 < j.val → F i j = G i j) :
    matInnerProd (Z_DP (k + 1) h) F = matInnerProd (Z_DP (k + 1) h) G := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i.val + j.val < h
  · simp [Z_DP_apply_of_add_lt hij]
  · rw [hFG i j (by omega) (by omega)]

/-- Interface to literal old-score/count tables.  The hypotheses are exact
coordinate identities, never solvability or integrality assumptions.  Once
those identities are proved for `DᵀX` and `psi°`, this gives the integer row
and the binomial-coordinate tests appearing in Definition `def:admissible`.
The selected scale is still exactly the canonical `D_* k!`. -/
theorem reference_integer_scale_for_tables (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (cref : ℚ)
    (hchi : chi ⟨k - 1, by omega⟩ ≠ 0)
    (F : ℕ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) (psi : ℕ → Fin (k + 1) → ℚ)
    (hF : ∀ tau : ℕ, 0 < tau → ∀ i j : Fin (k + 1), 0 < i.val → 0 < j.val →
      ((S_mat (k + 1)).transpose * F tau * S_mat (k + 1)) i j =
        (referenceInterior k M lengthRow chi cref i j).eval (tau : ℚ))
    (hpsi : ∀ tau : ℕ, 0 < tau → ∀ j : Fin (k + 1), 0 < j.val →
      Matrix.vecMul (psi tau) (S_mat (k + 1)) j = (referencePsi k chi cref j).eval (tau : ℚ)) :
    let L := referenceSolver k hk M lengthRow chi cref
    let tau := integerScale k L
    0 < tau ∧ ∃ ell : Fin (k + 1) → ℤ, ∀ h, k < h → h ≤ 2 * k → Even h →
      matInnerProd (Z_binom (S_mat (k + 1)) h)
        (F tau - outerProd (fun j => (ell j : ℚ)) (psi tau)) = 0 := by
  intro L tau
  obtain ⟨htau, ell, _, htests⟩ := reference_integer_scale k hk M lengthRow chi cref hchi
  refine ⟨htau, ell, ?_⟩
  intro h hkh hht heven
  rw [matInnerProd_Z_binom_eq_Z_DP, Matrix.mul_sub, Matrix.sub_mul, outerProd_basis_change]
  calc
    matInnerProd (Z_DP (k + 1) h)
        ((S_mat (k + 1)).transpose * F tau * S_mat (k + 1) -
          outerProd (Matrix.vecMul (fun j => (ell j : ℚ)) (S_mat (k + 1)))
            (Matrix.vecMul (psi tau) (S_mat (k + 1)))) =
      matInnerProd (Z_DP (k + 1) h)
        ((Matrix.of fun i j => (referenceInterior k M lengthRow chi cref i j).eval (tau : ℚ)) -
          outerProd (Matrix.vecMul (fun j => (ell j : ℚ)) (S_mat (k + 1)))
            (fun j => (referencePsi k chi cref j).eval (tau : ℚ))) := by
      apply higher_test_congr_interior hkh
      intro i j hi hj
      simp only [Matrix.sub_apply, outerProd, Matrix.of_apply]
      rw [hF tau htau i j hi hj, hpsi tau htau j hj]
    _ = 0 := htests h hkh hht heven

/-- Canonical binomial correction row, before taking its integral numerators. -/
noncomputable def referenceCorrection (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (cref : ℚ) :
    Fin (k + 1) → ℚ :=
  let L := referenceSolver k hk M lengthRow chi cref
  Matrix.vecMul (fun i => (L i).eval (integerScale k L : ℚ)) (S_inv_mat (k + 1))

/-- A deterministic integer output of the finite rational calculation.
Integrality is proved below, so taking the numerator loses no denominator. -/
noncomputable def referenceCorrectionInt (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (cref : ℚ) :
    Fin (k + 1) → ℤ := fun j => (referenceCorrection k hk M lengthRow chi cref j).num

theorem referenceCorrectionInt_cast (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (cref : ℚ)
    (hchi : chi ⟨k - 1, by omega⟩ ≠ 0) (j : Fin (k + 1)) :
    (referenceCorrectionInt k hk M lengthRow chi cref j : ℚ) =
      referenceCorrection k hk M lengthRow chi cref j := by
  have hbeta := referencePivot_ne_zero k hk chi hchi
  have hF := fun a b (_ : 0 < a.val) (_ : 0 < b.val) =>
    referenceInterior_divisible k M lengthRow chi cref a b
  obtain ⟨z, hz⟩ := (polynomialSolver_integer_scale k (referenceInterior k M lengthRow chi cref)
    (referencePsi k chi cref) _ hbeta hF (referencePsi_divisible k chi cref)).2 j
  have heq : referenceCorrection k hk M lengthRow chi cref j = (z : ℚ) := by
    simpa only [Nat.cast_one, one_mul] using hz
  simp [referenceCorrectionInt, heq]

/-- Independence holds for the actual integer output as well as the scale;
there is no selection of a new existential witness after a late parameter changes. -/
theorem referenceCorrectionInt_scale_independent (k : ℕ) (hk : 2 ≤ k)
    (M M' : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi chi' : Fin k → ℚ) (c c' : ℚ)
    (hM : ∀ a b, 0 < a.val → M a b = M' a b)
    (hchi : ∀ a, 0 < a.val → chi a = chi' a) :
    integerScale k (referenceSolver k hk M lengthRow chi c) =
        integerScale k (referenceSolver k hk M' lengthRow chi' c') ∧
      referenceCorrectionInt k hk M lengthRow chi c = referenceCorrectionInt k hk M' lengthRow chi' c' := by
  obtain ⟨hL, htau⟩ := referenceSolver_scale_independent k hk M M' lengthRow chi chi' c c' hM hchi
  refine ⟨htau, ?_⟩
  unfold referenceCorrectionInt referenceCorrection
  rw [hL]

#print axioms reference_integer_scale
#print axioms referenceCorrectionInt_cast
#print axioms referenceCorrectionInt_scale_independent
#print axioms referenceInterior_eval
#print axioms referencePsi_eval
#print axioms reference_integer_scale_for_tables

end Karlin.FaithfulScale
