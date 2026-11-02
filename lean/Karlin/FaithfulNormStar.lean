import Karlin.FaithfulNormCore

/-! The literal rational coefficient norm of v15: maximum of the maximum
absolute row sum and maximum absolute column sum. -/
namespace Karlin.FaithfulAppendix
open scoped BigOperators Matrix
open Faithful
set_option maxHeartbeats 1200000

def normStar {m n : Type*} [Fintype m] [Fintype n] [Nonempty m] [Nonempty n]
    (A : Matrix m n ℚ) : ℚ :=
  max (Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, |A i j|))
    (Finset.univ.sup' Finset.univ_nonempty (fun j => ∑ i, |A i j|))

section Norm
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [Nonempty m] [Nonempty n] [Nonempty p]

theorem normStar_le_iff (A : Matrix m n ℚ) (b : ℚ) :
    normStar A ≤ b ↔ (∀ i, (∑ j, |A i j|) ≤ b) ∧ (∀ j, (∑ i, |A i j|) ≤ b) := by
  simp only [normStar, max_le_iff, Finset.sup'_le_iff, Finset.mem_univ, true_implies]

theorem row_le (A : Matrix m n ℚ) (i : m) : (∑ j, |A i j|) ≤ normStar A :=
  ((normStar_le_iff A _).mp le_rfl).1 i

theorem col_le (A : Matrix m n ℚ) (j : n) : (∑ i, |A i j|) ≤ normStar A :=
  ((normStar_le_iff A _).mp le_rfl).2 j

theorem nonneg (A : Matrix m n ℚ) : 0 ≤ normStar A := by
  classical
  exact (Finset.sum_nonneg (fun j _ => abs_nonneg (A (Classical.choice inferInstance) j))).trans
    (row_le A _)

theorem abs_entry_le (A : Matrix m n ℚ) (i : m) (j : n) : |A i j| ≤ normStar A :=
  (Finset.single_le_sum (fun l _ => abs_nonneg (A i l)) (Finset.mem_univ j)).trans (row_le A i)

theorem transpose (A : Matrix m n ℚ) : normStar Aᵀ = normStar A := by
  unfold normStar
  exact max_comm _ _

theorem le_entrySum (A : Matrix m n ℚ) : normStar A ≤ entrySum A := by
  apply (normStar_le_iff A _).mpr
  exact ⟨rowSum_le_entrySum A, fun j => (rowSum_le_entrySum Aᵀ j).trans_eq (entrySum_transpose A)⟩

theorem add_le (A B : Matrix m n ℚ) : normStar (A + B) ≤ normStar A + normStar B := by
  apply (normStar_le_iff _ _).mpr
  constructor
  · intro i
    calc (∑ j, |(A+B) i j|) ≤ ∑ j, (|A i j| + |B i j|) :=
        Finset.sum_le_sum (fun j _ => abs_add_le _ _)
      _ = (∑ j, |A i j|) + ∑ j, |B i j| := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (row_le A i) (row_le B i)
  · intro j
    calc (∑ i, |(A+B) i j|) ≤ ∑ i, (|A i j| + |B i j|) :=
        Finset.sum_le_sum (fun i _ => abs_add_le _ _)
      _ = (∑ i, |A i j|) + ∑ i, |B i j| := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (col_le A j) (col_le B j)

theorem neg (A : Matrix m n ℚ) : normStar (-A) = normStar A := by
  simp only [normStar, Matrix.neg_apply, abs_neg]

theorem sub_le (A B : Matrix m n ℚ) : normStar (A-B) ≤ normStar A + normStar B := by
  simpa only [sub_eq_add_neg, neg] using add_le A (-B)

theorem smul_le (c : ℚ) (A : Matrix m n ℚ) : normStar (c • A) ≤ |c| * normStar A := by
  apply (normStar_le_iff _ _).mpr
  constructor
  · intro i
    simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (row_le A i) (abs_nonneg c)
  · intro j
    simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (col_le A j) (abs_nonneg c)

theorem row_mul_le (A : Matrix m n ℚ) (B : Matrix n p ℚ) (i : m) :
    (∑ j, |(A*B) i j|) ≤ normStar A * normStar B := by
  calc
    (∑ j, |(A*B) i j|) ≤ ∑ j, ∑ l, |A i l| * |B l j| := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Matrix.mul_apply, abs_mul] using
        Finset.abs_sum_le_sum_abs (s := Finset.univ) (fun l => A i l * B l j)
    _ = ∑ l, |A i l| * ∑ j, |B l j| := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ l, |A i l| * normStar B :=
      Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (row_le B l) (abs_nonneg _))
    _ = (∑ l, |A i l|) * normStar B := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (row_le A i) (nonneg B)

theorem mul_le (A : Matrix m n ℚ) (B : Matrix n p ℚ) :
    normStar (A*B) ≤ normStar A * normStar B := by
  apply (normStar_le_iff _ _).mpr
  refine ⟨row_mul_le A B, ?_⟩
  intro j
  have h := row_mul_le Bᵀ Aᵀ j
  simpa only [← Matrix.transpose_mul, Matrix.transpose_apply, transpose, mul_comm] using h

theorem mul_bound (A : Matrix m n ℚ) (B : Matrix n p ℚ) (a b : ℚ)
    (hA : normStar A ≤ a) (hB : normStar B ≤ b) : normStar (A*B) ≤ a*b :=
  (mul_le A B).trans (mul_le_mul hA hB (nonneg B) ((nonneg A).trans hA))

theorem fromRows_le (A : Matrix m p ℚ) (B : Matrix n p ℚ) :
    normStar (Matrix.fromRows A B) ≤ normStar A + normStar B := by
  apply (normStar_le_iff _ _).mpr
  constructor
  · intro i
    cases i with
    | inl i => exact (row_le A i).trans (le_add_of_nonneg_right (nonneg B))
    | inr i => exact (row_le B i).trans (le_add_of_nonneg_left (nonneg A))
  · intro j
    simpa only [Fintype.sum_sum_type, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
      using add_le_add (col_le A j) (col_le B j)

theorem fromCols_zero_le (A : Matrix m n ℚ) :
    normStar (Matrix.fromCols (0 : Matrix m p ℚ) A) ≤ normStar A := by
  apply (normStar_le_iff _ _).mpr
  constructor
  · intro i
    simpa only [Fintype.sum_sum_type, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
      Matrix.zero_apply, abs_zero, Finset.sum_const_zero, zero_add] using row_le A i
  · intro j
    cases j with
    | inl j => simpa using nonneg A
    | inr j => exact col_le A j

theorem outer_ones_le (v : n → ℚ) :
    normStar (outerProd (fun _ : m => (1 : ℚ)) v) ≤ (Fintype.card m : ℚ) * rowAbs v := by
  have h := le_entrySum (outerProd (fun _ : m => (1 : ℚ)) v)
  simpa only [entrySum_outer, rowAbs, abs_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] using h

end Norm

theorem outer_early_le (k : ℕ) (v : Fin (k+1) → ℚ) :
    normStar (outerProd (earlyUnit k) v) ≤ rowAbs v := by
  exact (le_entrySum _).trans_eq (by rw [entrySum_outer, rowAbs_earlyUnit, one_mul])

theorem dot_inverse_le (k : ℕ) (WI : Matrix (Fin (k+1)) (Fin (k+1)) ℚ)
    (ell : Fin (k+1) → ℚ) :
    |dotProduct ell (WI.mulVec (earlyUnit k))| ≤ normStar WI * rowAbs ell := by
  have he (i : Fin (k+1)) : WI.mulVec (earlyUnit k) i = WI i 0 := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (0 : Fin (k+1))]
    · simp [earlyUnit]
    · intro j _ hj
      have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp only [earlyUnit, if_neg hv, mul_zero]
    · simp
  simp_rw [dotProduct, he]
  calc |∑ i, ell i * WI i 0| ≤ ∑ i, |ell i * WI i 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |ell i| * normStar WI := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_entry_le WI i 0) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; exact mul_comm _ _

/-- The two internal terms separately retain the sharper `1/(T1*T2)` scale.
Only the bound on `Z/T2` is used, so this applies to either count block. -/
theorem internal_norm_sum_bound {r w : Type*} [Fintype r] [Fintype w]
    [Nonempty r] [Nonempty w] (Z : Matrix r w ℚ) (L : Matrix r r ℚ)
    (B : Matrix w w ℚ) (T1 T2 C : ℚ) (ht1 : 0 < T1) (ht2 : 0 < T2)
    (hz : normStar Z ≤ T2 * C) :
    normStar ((1 / (T1 * T2 ^ 2)) • (L * Z)) +
      normStar ((1 / (T1 * T2 ^ 2)) • (Lᵀ * Z * B)) ≤
      normStar L * C * (1 + normStar B) / (T1 * T2) := by
  have hlz := mul_bound L Z _ _ le_rfl hz
  have hltz := mul_bound Lᵀ Z _ _ (transpose L).le hz
  have hlb := mul_bound (Lᵀ * Z) B _ _ hltz le_rfl
  have heta : 0 < 1 / (T1 * T2 ^ 2) := by positivity
  have h1 := smul_le (1 / (T1 * T2 ^ 2)) (L * Z)
  have h2 := smul_le (1 / (T1 * T2 ^ 2)) (Lᵀ * Z * B)
  rw [abs_of_pos heta] at h1 h2
  calc
    _ ≤ (1 / (T1 * T2 ^ 2)) *
        (normStar (L * Z) + normStar (Lᵀ * Z * B)) := by linarith
    _ ≤ (1 / (T1 * T2 ^ 2)) *
        (normStar L * (T2 * C) + (normStar L * (T2 * C)) * normStar B) :=
      mul_le_mul_of_nonneg_left (add_le_add hlz hlb) heta.le
    _ = _ := by field_simp

/-- The same sum of norms is `O(T1⁻²)` once `T2 ≥ T1`. -/
theorem internal_norm_sum_square_bound {r w : Type*} [Fintype r] [Fintype w]
    [Nonempty r] [Nonempty w] (Z : Matrix r w ℚ) (L : Matrix r r ℚ)
    (B : Matrix w w ℚ) (T1 T2 C : ℚ) (ht1 : 0 < T1) (ht2 : T1 ≤ T2)
    (hz : normStar Z ≤ T2 * C) :
    normStar ((1 / (T1 * T2 ^ 2)) • (L * Z)) +
      normStar ((1 / (T1 * T2 ^ 2)) • (Lᵀ * Z * B)) ≤
      normStar L * C * (1 + normStar B) / T1 ^ 2 := by
  have ht2p : 0 < T2 := ht1.trans_le ht2
  have hC : 0 ≤ C := by nlinarith [nonneg Z]
  have hn : 0 ≤ normStar L * C * (1 + normStar B) :=
    mul_nonneg (mul_nonneg (nonneg L) hC) (by linarith [nonneg B])
  exact (internal_norm_sum_bound Z L B T1 T2 C ht1 ht2p hz).trans
    (div_le_div_of_nonneg_left hn (sq_pos_of_pos ht1) (by nlinarith))


end Karlin.FaithfulAppendix
