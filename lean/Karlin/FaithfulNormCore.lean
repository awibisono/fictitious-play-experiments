import Karlin.FaithfulReset

/-! Shared rational coefficient bounds, below both the literal matrix norm and
its conservative entry-sum certificate constants. -/
namespace Karlin.Faithful
open scoped BigOperators Matrix
/-- Rational sum of absolute matrix entries. -/
def entrySum {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℚ) : ℚ :=
  ∑ i, ∑ j, |A i j|

/-- Rational sum of absolute row entries. -/
def rowAbs {n : Type*} [Fintype n] (v : n → ℚ) : ℚ := ∑ j, |v j|

theorem entrySum_nonneg {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℚ) :
    0 ≤ entrySum A := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem rowAbs_nonneg {n : Type*} [Fintype n] (v : n → ℚ) : 0 ≤ rowAbs v :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem rowSum_le_entrySum {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) (i : m) : (∑ j, |A i j|) ≤ entrySum A := by
  unfold entrySum
  exact Finset.single_le_sum
    (fun r _ => Finset.sum_nonneg (fun c _ => abs_nonneg (A r c))) (Finset.mem_univ i)

theorem abs_entry_le_entrySum {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) (i : m) (j : n) : |A i j| ≤ entrySum A := by
  have hj : |A i j| ≤ ∑ l, |A i l| :=
    Finset.single_le_sum (fun l _ => abs_nonneg (A i l)) (Finset.mem_univ j)
  exact le_trans hj (rowSum_le_entrySum A i)

theorem entrySum_zero {m n : Type*} [Fintype m] [Fintype n] :
    entrySum (0 : Matrix m n ℚ) = 0 := by simp [entrySum]

theorem entrySum_add_le {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n ℚ) :
    entrySum (A + B) ≤ entrySum A + entrySum B := by
  simp only [entrySum, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => abs_add_le _ _))

theorem entrySum_neg {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℚ) :
    entrySum (-A) = entrySum A := by simp [entrySum]

theorem entrySum_sub_le {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n ℚ) :
    entrySum (A - B) ≤ entrySum A + entrySum B := by
  simpa only [sub_eq_add_neg, entrySum_neg] using entrySum_add_le A (-B)

theorem entrySum_smul {m n : Type*} [Fintype m] [Fintype n] (c : ℚ) (A : Matrix m n ℚ) :
    entrySum (c • A) = |c| * entrySum A := by
  simp only [entrySum, Matrix.smul_apply, smul_eq_mul, abs_mul, ← Finset.mul_sum]

theorem entrySum_transpose {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℚ) :
    entrySum Aᵀ = entrySum A := by
  exact Finset.sum_comm

theorem entrySum_mul_le {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (A : Matrix m n ℚ) (B : Matrix n p ℚ) :
    entrySum (A * B) ≤ entrySum A * entrySum B := by
  calc
    entrySum (A * B) ≤ ∑ i, ∑ j, ∑ l, |A i l| * |B l j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [Matrix.mul_apply, abs_mul] using
        (Finset.abs_sum_le_sum_abs (s := Finset.univ) (fun l => A i l * B l j))
    _ = ∑ i, ∑ l, |A i l| * (∑ j, |B l j|) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ i, ∑ l, |A i l| * entrySum B := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro l _
      exact mul_le_mul_of_nonneg_left (rowSum_le_entrySum B l) (abs_nonneg _)
    _ = entrySum A * entrySum B := by
      simp only [entrySum, Finset.sum_mul]

theorem entrySum_fromRows {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (A : Matrix m p ℚ) (B : Matrix n p ℚ) :
    entrySum (Matrix.fromRows A B) = entrySum A + entrySum B := by
  simp [entrySum, Fintype.sum_sum_type]

theorem entrySum_fromCols {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (A : Matrix m n ℚ) (B : Matrix m p ℚ) :
    entrySum (Matrix.fromCols A B) = entrySum A + entrySum B := by
  simp [entrySum, Fintype.sum_sum_type, Finset.sum_add_distrib]

theorem entrySum_outer {m n : Type*} [Fintype m] [Fintype n] (u : m → ℚ) (v : n → ℚ) :
    entrySum (outerProd u v) = rowAbs u * rowAbs v := by
  simp only [entrySum, rowAbs, outerProd, Matrix.of_apply, abs_mul, Finset.sum_mul_sum]

theorem rowAbs_earlyUnit (k : ℕ) : rowAbs (earlyUnit k) = 1 := by
  unfold rowAbs
  have hterm (i : Fin (k + 1)) : |earlyUnit k i| = if i = 0 then 1 else 0 := by
    unfold earlyUnit
    by_cases h : i = 0
    · subst i; simp
    · have hv : i.val ≠ 0 := by simpa using h
      simp [h, hv]
  simp_rw [hterm]
  simp


end Karlin.Faithful
