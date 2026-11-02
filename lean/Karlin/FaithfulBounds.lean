import Karlin.FaithfulNormStar

/-!
# Explicit rational bounds for the v15 reset construction

The executable constants remain the original rational sums of absolute
entries. The actual sign certificate carries score and coupling errors in the
paper's transpose-invariant `normStar`, including its sharp internal sum bound;
explicit forward norm comparisons justify the unchanged constants and scales.
The original entry-sum estimates remain available with unchanged statements.
-/
namespace Karlin.Faithful
open scoped BigOperators Matrix
set_option maxHeartbeats 1200000

/-- Both terms of the concrete late inverse are bounded before T2 is chosen. -/
theorem late_inverse_bound (k : ℕ) (T1 T2 lam : ℚ) (zeta0 : Fin (k + 1) → ℚ)
    (hT1 : 0 < T1) (hT2 : T1 ≤ T2) :
    entrySum (Winv_concrete k T1 T2 lam zeta0) ≤
      (entrySum (Phi0_concrete k lam zeta0) + entrySum (Phi1_concrete k zeta0)) / T1 := by
  have hT2pos : 0 < T2 := lt_of_lt_of_le hT1 hT2
  have hi1 : 0 < T1⁻¹ := inv_pos.mpr hT1
  have hi2 : 0 < T2⁻¹ := inv_pos.mpr hT2pos
  have hi21 : T2⁻¹ ≤ T1⁻¹ := (inv_le_inv₀ hT2pos hT1).mpr hT2
  calc
    _ ≤ entrySum (T1⁻¹ • Phi0_concrete k lam zeta0) +
        entrySum (T2⁻¹ • Phi1_concrete k zeta0) := entrySum_add_le _ _
    _ = T1⁻¹ * entrySum (Phi0_concrete k lam zeta0) +
        T2⁻¹ * entrySum (Phi1_concrete k zeta0) := by
      rw [entrySum_smul, entrySum_smul, abs_of_pos hi1, abs_of_pos hi2]
    _ ≤ T1⁻¹ * entrySum (Phi0_concrete k lam zeta0) +
        T1⁻¹ * entrySum (Phi1_concrete k zeta0) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hi21 (entrySum_nonneg _))
    _ = _ := by ring

/-- Multiplication propagates actual entry-sum bounds. -/
theorem entrySum_mul_bound {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (A : Matrix m n ℚ) (B : Matrix n p ℚ) (a b : ℚ)
    (hA : entrySum A ≤ a) (hB : entrySum B ≤ b) : entrySum (A * B) ≤ a * b :=
  le_trans (entrySum_mul_le A B)
    (mul_le_mul hA hB (entrySum_nonneg B) (le_trans (entrySum_nonneg A) hA))

/-- Sherman--Morrison's inverse correction is small from the actual inverse
formula, rather than from an assumed bound on the final inverse. -/
theorem sherman_entrySum_bound (k : ℕ)
    (WI : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (ellStar : Fin (k + 1) → ℚ) (d b : ℚ)
    (hWI : entrySum WI ≤ b) (hd : (1 / 2 : ℚ) < d)
    (hsmall : 2 * b * rowAbs ellStar ≤ 1) :
    entrySum (WI - d⁻¹ • (WI * (outerProd (earlyUnit k) ellStar * WI))) ≤ 2 * b := by
  have hb : 0 ≤ b := le_trans (entrySum_nonneg WI) hWI
  have hL : 0 ≤ rowAbs ellStar := rowAbs_nonneg ellStar
  have hdpos : 0 < d := lt_trans (by norm_num) hd
  have hi : d⁻¹ ≤ 2 := by
    have h := (inv_le_inv₀ hdpos (by norm_num : (0 : ℚ) < 1 / 2)).mpr hd.le
    norm_num at h
    exact h
  have houter : entrySum (outerProd (earlyUnit k) ellStar) = rowAbs ellStar := by
    rw [entrySum_outer, rowAbs_earlyUnit, one_mul]
  have hprod : entrySum (WI * (outerProd (earlyUnit k) ellStar * WI)) ≤
      b * (rowAbs ellStar * b) := by
    exact entrySum_mul_bound _ _ _ _ hWI
      (entrySum_mul_bound _ _ _ _ houter.le hWI)
  have hbound := entrySum_sub_le WI
    (d⁻¹ • (WI * (outerProd (earlyUnit k) ellStar * WI)))
  rw [entrySum_smul, abs_of_pos (inv_pos.mpr hdpos)] at hbound
  have herr : d⁻¹ * entrySum (WI * (outerProd (earlyUnit k) ellStar * WI)) ≤
      2 * (b * (rowAbs ellStar * b)) :=
    mul_le_mul hi hprod (entrySum_nonneg _) (by norm_num)
  have hscale := mul_le_mul_of_nonneg_right hsmall hb
  nlinarith

/-- The paper's uniform O(1/T1) inverse estimate, with explicit fixed constant. -/
theorem early_inverse_bound (k : ℕ) (T1 T2 lam : ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ) (hT1 : 0 < T1) (hT2 : T1 ≤ T2)
    (hd : (1 / 2 : ℚ) < 1 + dotProduct ellStar
      (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (earlyUnit k)))
    (hlarge : 2 * (entrySum (Phi0_concrete k lam zeta0) +
      entrySum (Phi1_concrete k zeta0)) * rowAbs ellStar ≤ T1) :
    entrySum (WE_inv_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar) ≤
      2 * (entrySum (Phi0_concrete k lam zeta0) + entrySum (Phi1_concrete k zeta0)) / T1 := by
  have hsmall : 2 * ((entrySum (Phi0_concrete k lam zeta0) +
      entrySum (Phi1_concrete k zeta0)) / T1) * rowAbs ellStar ≤ 1 := by
    apply (le_of_eq (by ring : 2 * ((entrySum (Phi0_concrete k lam zeta0) +
      entrySum (Phi1_concrete k zeta0)) / T1) * rowAbs ellStar =
        (2 * (entrySum (Phi0_concrete k lam zeta0) + entrySum (Phi1_concrete k zeta0)) *
          rowAbs ellStar) / T1)).trans
    exact (div_le_iff₀ hT1).mpr (by simpa using hlarge)
  have h := sherman_entrySum_bound k (Winv_concrete k T1 T2 lam zeta0) ellStar
    (1 + dotProduct ellStar (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (earlyUnit k)))
    ((entrySum (Phi0_concrete k lam zeta0) + entrySum (Phi1_concrete k zeta0)) / T1)
    (late_inverse_bound k T1 T2 lam zeta0 hT1 hT2) hd hsmall
  convert h using 1
  ring

/-- Fixed constant bounding both count tables divided by T2. -/
def countConstant (k : ℕ) (lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ) : ℚ :=
  entrySum (outerProd (fun _ : Fin (k + 1) => 1) (lam • zeta0)) +
    entrySum (V0_paper k) + rowAbs ellStar

/-- Count table growth is at most linear in the still-free T2. -/
theorem count_table_bounds (k : ℕ) (T1 T2 lam : ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ) (hT1 : 1 ≤ T1) (hT2 : T1 ≤ T2) :
    entrySum (W_concrete k T1 T2 lam zeta0) ≤ T2 * countConstant k lam zeta0 ellStar ∧
    entrySum (WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar) ≤
      T2 * countConstant k lam zeta0 ellStar := by
  let A := outerProd (fun _ : Fin (k + 1) => (1 : ℚ)) (lam • zeta0)
  let V := V0_paper k
  have ht1 : 0 ≤ T1 := le_trans (by norm_num) hT1
  have ht2 : 0 ≤ T2 := le_trans ht1 hT2
  have hW : W_concrete k T1 T2 lam zeta0 = T1 • A + T2 • V := by
    ext i j
    simp only [W_concrete, W_paper, A, V, outerProd, Matrix.of_apply,
      Matrix.add_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hnW : entrySum (W_concrete k T1 T2 lam zeta0) ≤
      T2 * (entrySum A + entrySum V) := by
    rw [hW]
    have h := entrySum_add_le (T1 • A) (T2 • V)
    rw [entrySum_smul, entrySum_smul, abs_of_nonneg ht1, abs_of_nonneg ht2] at h
    have hscale := mul_le_mul_of_nonneg_right hT2 (entrySum_nonneg A)
    nlinarith
  have hcor : entrySum (outerProd (earlyUnit k) ellStar) = rowAbs ellStar := by
    rw [entrySum_outer, rowAbs_earlyUnit, one_mul]
  have hL := rowAbs_nonneg ellStar
  have hscale : rowAbs ellStar ≤ T2 * rowAbs ellStar := by
    have h12 : (1 : ℚ) ≤ T2 := le_trans hT1 hT2
    nlinarith
  have hWE := entrySum_add_le (W_concrete k T1 T2 lam zeta0)
    (outerProd (earlyUnit k) ellStar)
  rw [hcor] at hWE
  unfold countConstant
  change entrySum (W_concrete k T1 T2 lam zeta0) ≤
    T2 * (entrySum A + entrySum V + rowAbs ellStar) ∧ _
  constructor
  · nlinarith
  · change entrySum (W_concrete k T1 T2 lam zeta0 + outerProd (earlyUnit k) ellStar) ≤
      T2 * (entrySum A + entrySum V + rowAbs ellStar)
    nlinarith

/-- The concrete residual from equation (J). -/
def paperResidual (k : ℕ) (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :=
  let W := W_concrete k T1 T2 lam zeta0
  let WE := WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar
  E - paperEbase k T1 lam zeta0 ellStar -
    (1 / (T1 * T2 ^ 2)) • (WEᵀ * L * WE + Wᵀ * L * W)

/-- The concrete cross-group matrix from equation (J). -/
def paperCross (k : ℕ) (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :=
  paperKappa k T1 lam • outerProd (fun _ : Fin (k + 1) => 1) (fun _ => 1) +
    (Winv_concrete k T1 T2 lam zeta0)ᵀ * paperResidual k T1 T2 lam zeta0 ellStar E L *
      WE_inv_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar

/-- The internal quadratic reset contribution stays small even though W and
WE themselves grow with T2; eta cancels that growth exactly. -/
theorem internal_quadratic_bound {r : Type*} [Fintype r]
    (W WE L : Matrix r r ℚ) (T1 T2 C : ℚ)
    (hT1 : 0 < T1) (hT2 : 0 < T2)
    (hW : entrySum W ≤ T2 * C) (hWE : entrySum WE ≤ T2 * C) :
    entrySum ((1 / (T1 * T2 ^ 2)) • (WEᵀ * L * WE + Wᵀ * L * W)) ≤
      2 * entrySum L * C ^ 2 / T1 := by
  have h1 : entrySum (WEᵀ * L * WE) ≤ (T2 * C * entrySum L) * (T2 * C) :=
    entrySum_mul_bound _ _ _ _
      (entrySum_mul_bound _ _ _ _ (by simpa only [entrySum_transpose] using hWE) le_rfl) hWE
  have h2 : entrySum (Wᵀ * L * W) ≤ (T2 * C * entrySum L) * (T2 * C) :=
    entrySum_mul_bound _ _ _ _
      (entrySum_mul_bound _ _ _ _ (by simpa only [entrySum_transpose] using hW) le_rfl) hW
  have hsum := entrySum_add_le (WEᵀ * L * WE) (Wᵀ * L * W)
  have hs : entrySum (WEᵀ * L * WE + Wᵀ * L * W) ≤
      2 * (T2 * C * entrySum L) * (T2 * C) := by linarith
  have heta : 0 < 1 / (T1 * T2 ^ 2) := by positivity
  rw [entrySum_smul, abs_of_pos heta]
  calc
    _ ≤ (1 / (T1 * T2 ^ 2)) * (2 * (T2 * C * entrySum L) * (T2 * C)) :=
      mul_le_mul_of_nonneg_left hs heta.le
    _ = _ := by field_simp

/-- A fixed residual bound obtained from the upstream compatibility correction
bound; no estimate on the final residual is assumed. -/
def residualConstant (k : ℕ) (lam KE : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ)
    (L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :=
  KE + 2 * entrySum (outerProd zeta0 ellStar) +
    2 * entrySum L * (countConstant k lam zeta0 ellStar) ^ 2

theorem residual_bound (k : ℕ) (T1 T2 lam KE : ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hT1 : 1 ≤ T1) (hT2 : T1 ≤ T2)
    (hE : entrySum (E - T1 • paperE0 k lam zeta0) ≤ KE) :
    entrySum (paperResidual k T1 T2 lam zeta0 ellStar E L) ≤
      residualConstant k lam KE zeta0 ellStar L := by
  have hT1pos : 0 < T1 := lt_of_lt_of_le (by norm_num) hT1
  have hT2pos : 0 < T2 := lt_of_lt_of_le hT1pos hT2
  let W := W_concrete k T1 T2 lam zeta0
  let WE := WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar
  let C := countConstant k lam zeta0 ellStar
  obtain ⟨hW, hWE⟩ := count_table_bounds k T1 T2 lam zeta0 ellStar hT1 hT2
  have hquad := internal_quadratic_bound W WE L T1 T2 C hT1pos hT2pos hW hWE
  have hcoef : 0 ≤ 2 * entrySum L * C ^ 2 := by
    exact mul_nonneg (mul_nonneg (by norm_num) (entrySum_nonneg L)) (sq_nonneg C)
  have hreduce : 2 * entrySum L * C ^ 2 / T1 ≤ 2 * entrySum L * C ^ 2 := by
    apply (div_le_iff₀ hT1pos).mpr
    nlinarith
  have hbase : E - paperEbase k T1 lam zeta0 ellStar =
      (E - T1 • paperE0 k lam zeta0) - (2 : ℚ) • outerProd zeta0 ellStar := by
    unfold paperEbase
    abel
  have hb := entrySum_sub_le (E - T1 • paperE0 k lam zeta0)
    ((2 : ℚ) • outerProd zeta0 ellStar)
  rw [entrySum_smul] at hb
  norm_num at hb
  rw [← hbase] at hb
  have hf := entrySum_sub_le (E - paperEbase k T1 lam zeta0 ellStar)
    ((1 / (T1 * T2 ^ 2)) • (WEᵀ * L * WE + Wᵀ * L * W))
  change entrySum ((E - paperEbase k T1 lam zeta0 ellStar) -
      (1 / (T1 * T2 ^ 2)) • (WEᵀ * L * WE + Wᵀ * L * W)) ≤
    KE + 2 * entrySum (outerProd zeta0 ellStar) + 2 * entrySum L * C ^ 2
  linarith

/-- The fixed inverse constant in the paper's two-scale decomposition. -/
def inverseConstant (k : ℕ) (lam : ℚ) (zeta0 : Fin (k + 1) → ℚ) :=
  entrySum (Phi0_concrete k lam zeta0) + entrySum (Phi1_concrete k zeta0)

/-- The fixed coefficient of the cross-block error. -/
def crossConstant (k : ℕ) (lam KE : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ)
    (L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :=
  2 * (inverseConstant k lam zeta0) ^ 2 * residualConstant k lam KE zeta0 ellStar L

/-- Actual cross-block error is bounded by a fixed constant / T1², uniformly in
T2. The only upstream analytic premise concerns E-T1 E0. -/
theorem cross_error_bound (k : ℕ) (T1 T2 lam KE : ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hT1 : 1 ≤ T1) (hT2 : T1 ≤ T2)
    (hd : (1 / 2 : ℚ) < 1 + dotProduct ellStar
      (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (earlyUnit k)))
    (hlarge : 2 * inverseConstant k lam zeta0 * rowAbs ellStar ≤ T1)
    (hE : entrySum (E - T1 • paperE0 k lam zeta0) ≤ KE) :
    entrySum (paperCross k T1 T2 lam zeta0 ellStar E L -
      paperKappa k T1 lam • outerProd (fun _ => 1) (fun _ => 1)) ≤
      crossConstant k lam KE zeta0 ellStar L / T1 ^ 2 := by
  have ht1 : 0 < T1 := lt_of_lt_of_le (by norm_num) hT1
  have hw := late_inverse_bound k T1 T2 lam zeta0 ht1 hT2
  have hwe := early_inverse_bound k T1 T2 lam zeta0 ellStar ht1 hT2 hd hlarge
  have hf := residual_bound k T1 T2 lam KE zeta0 ellStar E L hT1 hT2 hE
  have hwt : entrySum (Winv_concrete k T1 T2 lam zeta0)ᵀ ≤
      inverseConstant k lam zeta0 / T1 := by
    rw [entrySum_transpose]
    exact hw
  have hfirst : entrySum ((Winv_concrete k T1 T2 lam zeta0)ᵀ *
      paperResidual k T1 T2 lam zeta0 ellStar E L) ≤
      (inverseConstant k lam zeta0 / T1) * residualConstant k lam KE zeta0 ellStar L :=
    entrySum_mul_bound _ _ _ _ hwt hf
  have hmul : entrySum ((Winv_concrete k T1 T2 lam zeta0)ᵀ *
      paperResidual k T1 T2 lam zeta0 ellStar E L *
      WE_inv_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar) ≤
      ((inverseConstant k lam zeta0 / T1) * residualConstant k lam KE zeta0 ellStar L) *
        (2 * inverseConstant k lam zeta0 / T1) :=
    entrySum_mul_bound _ _ _ _ hfirst hwe
  unfold paperCross
  rw [add_sub_cancel_left]
  refine le_trans hmul ?_
  unfold crossConstant inverseConstant
  exact le_of_eq (by ring)

/-- Exact cancellation of the growing early table from the cross interaction.
Only its fixed row sum and an inverse-times-residual error remain. -/
theorem cross_mul_early (k : ℕ) (T1 T2 lam : ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0) (hlam : lam ≠ 0)
    (hzeta : zeta0 (lastIdx k) ≠ 0)
    (hd : 1 + dotProduct ellStar
      (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (earlyUnit k)) ≠ 0) :
    paperCross k T1 T2 lam zeta0 ellStar E L *
      WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar =
      (2 : ℚ) • outerProd (fun _ => 1) zeta0 +
        paperKappa k T1 lam • outerProd (fun _ => 1) ellStar +
        (Winv_concrete k T1 T2 lam zeta0)ᵀ *
          paperResidual k T1 T2 lam zeta0 ellStar E L := by
  have hwe := WE_inv_concrete_mul_WE k T1 T2 lam hT1 hT2 hlam zeta0 hzeta
    (earlyUnit k) ellStar hd
  unfold paperCross
  rw [Matrix.add_mul, Matrix.mul_assoc _ (WE_inv_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar),
    hwe, Matrix.mul_one, Matrix.smul_mul, outerProd_mul, early_row_sum]
  congr 1
  ext i j
  simp only [outerProd, Matrix.of_apply, Matrix.smul_apply, Pi.add_apply,
    Pi.smul_apply, Matrix.add_apply, smul_eq_mul, one_mul, paperKappa]
  have hr : (k + 1 : ℚ) ≠ 0 := by positivity
  field_simp

/-- Exact cancellation of the growing late table from the transposed cross
interaction. This identity is essential for uniformity over unbounded T2. -/
theorem cross_transpose_mul_late (k : ℕ) (T1 T2 lam : ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E L B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0) (hlam : lam ≠ 0)
    (hzeta : zeta0 (lastIdx k) ≠ 0) :
    (paperCross k T1 T2 lam zeta0 ellStar E L)ᵀ * W_concrete k T1 T2 lam zeta0 * B =
      (2 : ℚ) • (outerProd (fun _ => 1) zeta0 * B) +
        (WE_inv_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar)ᵀ *
          (paperResidual k T1 T2 lam zeta0 ellStar E L)ᵀ * B := by
  have hw := Winv_concrete_mul_W_concrete k T1 T2 lam hT1 hT2 hlam zeta0 hzeta
  have hc : (paperCross k T1 T2 lam zeta0 ellStar E L)ᵀ * W_concrete k T1 T2 lam zeta0 =
      (2 : ℚ) • outerProd (fun _ => 1) zeta0 +
        (WE_inv_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar)ᵀ *
          (paperResidual k T1 T2 lam zeta0 ellStar E L)ᵀ := by
    unfold paperCross
    rw [Matrix.transpose_add, Matrix.transpose_smul, outerProd_transpose,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.add_mul]
    rw [← Matrix.mul_assoc, Matrix.mul_assoc _ (Winv_concrete k T1 T2 lam zeta0), hw,
      Matrix.mul_one, Matrix.smul_mul, outerProd_mul, vecMul_one_W_concrete]
    congr 1
    ext i j
    simp only [outerProd, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply,
      smul_eq_mul, one_mul, paperKappa]
    have hr : (k + 1 : ℚ) ≠ 0 := by positivity
    field_simp
  rw [hc, Matrix.add_mul, Matrix.smul_mul]

/-- The early/late expansion of the reset score target, prior to estimates. -/
def resetScoreTarget {r w : Type*} [Fintype r] [Fintype w]
    (psi : w → ℚ) (WE W : Matrix r w ℚ) (L C : Matrix r r ℚ)
    (eta : ℚ) (B : Matrix w w ℚ) : Matrix (r ⊕ r) w ℚ :=
  Matrix.fromRows
    (outerProd (fun _ => 1) psi + eta • (L * WE) - eta • (Lᵀ * WE * B) - Cᵀ * W * B)
    (outerProd (fun _ => 1) psi + C * WE + eta • (L * W) - eta • (Lᵀ * W * B))

/-- The displayed block target is the literal full J/M target. -/
theorem resetScoreTarget_eq_blocks {r w : Type*} [Fintype r] [Fintype w]
    (psi : w → ℚ) (WE W : Matrix r w ℚ) (L C : Matrix r r ℚ)
    (eta : ℚ) (B : Matrix w w ℚ) :
    resetScoreTarget psi WE W L C eta B =
      outerProd (fun _ : r ⊕ r => 1) psi +
      (Matrix.fromBlocks (eta • L) 0 C (eta • L)) * Matrix.fromRows WE W -
      (Matrix.fromBlocks (eta • L) 0 C (eta • L))ᵀ * Matrix.fromRows WE W * B := by
  rw [Matrix.fromBlocks_transpose]
  simp only [Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.transpose_smul,
    Matrix.transpose_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.smul_mul, Matrix.add_mul]
  ext i j
  rcases i with i | i <;>
    simp only [resetScoreTarget, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.add_apply, Matrix.sub_apply, outerProd, Matrix.of_apply]
  · ring
  · ring

/-- The reference old/reset coupling from equation (P0). -/
def referenceCoupling {m r : Type*} (a : m → ℚ) : Matrix m (r ⊕ r) ℚ :=
  Matrix.fromCols (-outerProd a (fun _ => 1)) (outerProd a (fun _ => 1))

/-- The parent positive-weight identity determines the reference Q exactly. -/
theorem referenceCoupling_transpose_mul {m r w : Type*} [Fintype m] [Fintype w]
    (a : m → ℚ) (X : Matrix m w ℚ) (zeta0 : w → ℚ) (B : Matrix w w ℚ)
    (ha : Matrix.vecMul a X = zeta0 + Matrix.vecMul zeta0 B) :
    (referenceCoupling (r := r) a)ᵀ * X =
      Matrix.fromRows (-(outerProd (fun _ : r => 1) zeta0 +
        outerProd (fun _ : r => 1) zeta0 * B))
      (outerProd (fun _ : r => 1) zeta0 + outerProd (fun _ : r => 1) zeta0 * B) := by
  unfold referenceCoupling
  rw [Matrix.transpose_fromCols, Matrix.transpose_neg, outerProd_transpose,
    Matrix.fromRows_mul, Matrix.neg_mul, outerProd_mul, ha]
  have hsum : outerProd (fun _ : r => (1 : ℚ)) (zeta0 + Matrix.vecMul zeta0 B) =
      outerProd (fun _ : r => (1 : ℚ)) zeta0 + outerProd (fun _ : r => (1 : ℚ)) zeta0 * B := by
    rw [outerProd_mul]
    ext i j
    simp [outerProd]
  rw [hsum]

/-- Exact error formula after cancellation. H is the perturbation of the
one-row psi table and is small because the gain correction is small. -/
theorem resetScoreTarget_error {r w : Type*} [Fintype r] [Fintype w]
    (psi zeta0 : w → ℚ) (WE W : Matrix r w ℚ) (L C : Matrix r r ℚ)
    (eta : ℚ) (B : Matrix w w ℚ) (H EL EE : Matrix r w ℚ)
    (hpsi : outerProd (fun _ : r => 1) psi =
      outerProd (fun _ : r => 1) zeta0 * B - outerProd (fun _ : r => 1) zeta0 + H)
    (hcross : C * WE = (2 : ℚ) • outerProd (fun _ : r => 1) zeta0 + EL)
    (hcrossT : Cᵀ * W * B = (2 : ℚ) • (outerProd (fun _ : r => 1) zeta0 * B) + EE) :
    resetScoreTarget psi WE W L C eta B -
      Matrix.fromRows (-(outerProd (fun _ : r => 1) zeta0 + outerProd (fun _ => 1) zeta0 * B))
        (outerProd (fun _ : r => 1) zeta0 + outerProd (fun _ => 1) zeta0 * B) =
      Matrix.fromRows (H + eta • (L * WE) - eta • (Lᵀ * WE * B) - EE)
        (H + EL + eta • (L * W) - eta • (Lᵀ * W * B)) := by
  unfold resetScoreTarget
  rw [hpsi, hcross, hcrossT]
  ext i j
  rcases i with i | i <;>
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
  · ring
  · ring

/-- Bounding the literal interpolation correction uses only input residual
bounds and fixed X/LX; it does not assume a final bound on P. -/
theorem interpolation_correction_bound {m n w : Type*} [Fintype m] [Fintype n] [Fintype w]
    (X LX : Matrix m w ℚ) (M : Matrix n w ℚ) (RM : Matrix w n ℚ)
    (D : Matrix m w ℚ) (Q : Matrix n w ℚ) (P0 : Matrix m n ℚ) :
    entrySum (P_interp X LX M RM D Q P0 - P0) ≤
      entrySum (D - P0 * M) * entrySum RM + entrySum LX *
        (entrySum (Q - P0ᵀ * X) + entrySum X * entrySum (D - P0 * M) * entrySum RM) := by
  let DR := D - P0 * M
  let QR := Q - P0ᵀ * X
  have hP : P_interp X LX M RM D Q P0 - P0 =
      DR * RM + LX * (QRᵀ - Xᵀ * DR * RM) := by
    change (P0 + DR * RM + LX * (QRᵀ - Xᵀ * DR * RM)) - P0 = _
    abel
  rw [hP]
  have h1 := entrySum_mul_le DR RM
  have hX : entrySum Xᵀ = entrySum X := entrySum_transpose X
  have hQR : entrySum QRᵀ = entrySum QR := entrySum_transpose QR
  have hxdr : entrySum (Xᵀ * DR * RM) ≤ entrySum X * entrySum DR * entrySum RM := by
    exact entrySum_mul_bound _ _ _ _
      (by simpa only [entrySum_transpose] using entrySum_mul_le Xᵀ DR) le_rfl
  have hinner : entrySum (QRᵀ - Xᵀ * DR * RM) ≤
      entrySum QR + entrySum X * entrySum DR * entrySum RM := by
    have h := entrySum_sub_le QRᵀ (Xᵀ * DR * RM)
    rw [hQR] at h
    linarith
  have h2 := entrySum_mul_bound LX (QRᵀ - Xᵀ * DR * RM) _ _ le_rfl hinner
  have hsum := entrySum_add_le (DR * RM) (LX * (QRᵀ - Xᵀ * DR * RM))
  change entrySum (DR * RM + LX * (QRᵀ - Xᵀ * DR * RM)) ≤
    entrySum DR * entrySum RM + entrySum LX *
      (entrySum QR + entrySum X * entrySum DR * entrySum RM)
  linarith

/-- The internal linear terms also lose their potentially growing T2 factor. -/
theorem internal_linear_bound {r w : Type*} [Fintype r] [Fintype w]
    (Z : Matrix r w ℚ) (L : Matrix r r ℚ) (B : Matrix w w ℚ) (T1 T2 C : ℚ)
    (hT1 : 0 < T1) (hT2 : 1 ≤ T2) (hZ : entrySum Z ≤ T2 * C) :
    entrySum ((1 / (T1 * T2 ^ 2)) • (L * Z) -
      (1 / (T1 * T2 ^ 2)) • (Lᵀ * Z * B)) ≤
      entrySum L * C * (1 + entrySum B) / T1 := by
  have ht2 : 0 < T2 := lt_of_lt_of_le (by norm_num) hT2
  have hC : 0 ≤ C := by nlinarith [entrySum_nonneg Z]
  have hn : 0 ≤ entrySum L * C * (1 + entrySum B) := by
    exact mul_nonneg (mul_nonneg (entrySum_nonneg L) hC) (by linarith [entrySum_nonneg B])
  have hLZ : entrySum (L * Z) ≤ entrySum L * (T2 * C) :=
    entrySum_mul_bound _ _ _ _ le_rfl hZ
  have hLtZ : entrySum (Lᵀ * Z) ≤ entrySum L * (T2 * C) :=
    entrySum_mul_bound _ _ _ _ (entrySum_transpose L).le hZ
  have hLB : entrySum (Lᵀ * Z * B) ≤ (entrySum L * (T2 * C)) * entrySum B :=
    entrySum_mul_bound _ _ _ _ hLtZ le_rfl
  have heta : 0 < 1 / (T1 * T2 ^ 2) := by positivity
  have hs := entrySum_sub_le ((1 / (T1 * T2 ^ 2)) • (L * Z))
    ((1 / (T1 * T2 ^ 2)) • (Lᵀ * Z * B))
  rw [entrySum_smul, entrySum_smul, abs_of_pos heta] at hs
  have hscaled := mul_le_mul_of_nonneg_left (add_le_add hLZ hLB) heta.le
  have hformula : (1 / (T1 * T2 ^ 2)) *
      (entrySum L * (T2 * C) + entrySum L * (T2 * C) * entrySum B) =
      (entrySum L * C * (1 + entrySum B) / T1) / T2 := by
    field_simp
  have hreduce : (entrySum L * C * (1 + entrySum B) / T1) / T2 ≤
      entrySum L * C * (1 + entrySum B) / T1 := by
    apply (div_le_iff₀ ht2).mpr
    have hnonneg : 0 ≤ entrySum L * C * (1 + entrySum B) / T1 := div_nonneg hn hT1.le
    nlinarith
  rw [hformula] at hscaled
  linarith

/-- The baseline psi identity and actual gain perturbation, as a matrix identity. -/
theorem psi_table_identity (k : ℕ) (zeta0 : Fin (k + 1) → ℚ)
    (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) (dc : ℚ) :
    outerProd (fun _ : Fin (k + 1) => 1)
      (Matrix.vecMul zeta0 B - zeta0 - dc • e0_row (k + 1)) =
      outerProd (fun _ : Fin (k + 1) => 1) zeta0 * B -
        outerProd (fun _ : Fin (k + 1) => 1) zeta0 +
        (-dc) • outerProd (fun _ : Fin (k + 1) => 1) (e0_row (k + 1)) := by
  rw [outerProd_mul]
  ext i j
  simp only [outerProd, Matrix.of_apply, Pi.sub_apply, Pi.smul_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, one_mul]
  ring

theorem psi_error_bound (k : ℕ) (T1 dc Kd : ℚ) (hdc : |dc| ≤ Kd / T1) :
    entrySum ((-dc) • outerProd (fun _ : Fin (k + 1) => 1) (e0_row (k + 1))) ≤
      (k + 1 : ℚ) * Kd / T1 := by
  have he0 : rowAbs (e0_row (k + 1)) = 1 := rowAbs_earlyUnit k
  rw [entrySum_smul, abs_neg, entrySum_outer, he0, mul_one]
  have hones : rowAbs (fun _ : Fin (k + 1) => (1 : ℚ)) = (k + 1 : ℚ) := by
    simp [rowAbs]
  rw [hones]
  have h := mul_le_mul_of_nonneg_right hdc (by positivity : (0 : ℚ) ≤ k + 1)
  convert h using 1
  ring

/-- Fixed explicit bound for the full Q error after the exact cancellations. -/
def scoreConstant (k : ℕ) (lam KE Kd : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ)
    (L B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :=
  2 * (k + 1 : ℚ) * Kd + 2 * rowAbs ellStar / lam +
    2 * entrySum L * countConstant k lam zeta0 ellStar * (1 + entrySum B) +
    inverseConstant k lam zeta0 * residualConstant k lam KE zeta0 ellStar L * (1 + 2 * entrySum B)

/-- Every step in the actual Q error bound is uniform in T2. The only analytic
input bounds concern the gain correction and the compatible moment correction. -/
theorem score_error_bound (k : ℕ) (T1 T2 lam KE Kd dc : ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E L B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hT1 : 1 ≤ T1) (hT2 : T1 ≤ T2) (hlam : 0 < lam) (hzeta : 0 < zeta0 (lastIdx k))
    (hd : (1 / 2 : ℚ) < 1 + dotProduct ellStar
      (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (earlyUnit k)))
    (hlarge : 2 * inverseConstant k lam zeta0 * rowAbs ellStar ≤ T1)
    (hE : entrySum (E - T1 • paperE0 k lam zeta0) ≤ KE) (hdc : |dc| ≤ Kd / T1) :
    let Z := outerProd (fun _ : Fin (k + 1) => (1 : ℚ)) zeta0
    entrySum (resetScoreTarget (Matrix.vecMul zeta0 B - zeta0 - dc • e0_row (k + 1))
      (WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar) (W_concrete k T1 T2 lam zeta0)
      L (paperCross k T1 T2 lam zeta0 ellStar E L) (1 / (T1 * T2 ^ 2)) B -
      Matrix.fromRows (-(Z + Z * B)) (Z + Z * B)) ≤
      scoreConstant k lam KE Kd zeta0 ellStar L B / T1 := by
  intro Z
  let W := W_concrete k T1 T2 lam zeta0
  let WE := WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar
  let WI := Winv_concrete k T1 T2 lam zeta0
  let WEI := WE_inv_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar
  let F := paperResidual k T1 T2 lam zeta0 ellStar E L
  let H := (-dc) • outerProd (fun _ : Fin (k + 1) => (1 : ℚ)) (e0_row (k + 1))
  let EL := paperKappa k T1 lam • outerProd (fun _ : Fin (k + 1) => (1 : ℚ)) ellStar + WIᵀ * F
  let EE := WEIᵀ * Fᵀ * B
  let eta := 1 / (T1 * T2 ^ 2)
  let KW := inverseConstant k lam zeta0
  let KF := residualConstant k lam KE zeta0 ellStar L
  let KC := countConstant k lam zeta0 ellStar
  let KI := entrySum L * KC * (1 + entrySum B)
  have ht1 : 0 < T1 := lt_of_lt_of_le (by norm_num) hT1
  have ht2 : 0 < T2 := lt_of_lt_of_le ht1 hT2
  have hdn : 1 + dotProduct ellStar (Matrix.mulVec WI (earlyUnit k)) ≠ 0 := by
    have : 0 < 1 + dotProduct ellStar (Matrix.mulVec WI (earlyUnit k)) :=
      lt_trans (by norm_num) hd
    exact ne_of_gt this
  have hce : paperCross k T1 T2 lam zeta0 ellStar E L * WE = (2 : ℚ) • Z + EL := by
    have h := cross_mul_early k T1 T2 lam zeta0 ellStar E L
      (ne_of_gt ht1) (ne_of_gt ht2) (ne_of_gt hlam) (ne_of_gt hzeta) hdn
    change _ = (2 : ℚ) • Z + _ + _ at h
    rw [h]
    exact add_assoc _ _ _
  have hcl : (paperCross k T1 T2 lam zeta0 ellStar E L)ᵀ * W * B =
      (2 : ℚ) • (Z * B) + EE :=
    cross_transpose_mul_late k T1 T2 lam zeta0 ellStar E L B
      (ne_of_gt ht1) (ne_of_gt ht2) (ne_of_gt hlam) (ne_of_gt hzeta)
  rw [resetScoreTarget_error _ zeta0 WE W L _ eta B H EL EE
    (psi_table_identity k zeta0 B dc) hce hcl, entrySum_fromRows]
  have hw : entrySum WI ≤ KW / T1 := late_inverse_bound k T1 T2 lam zeta0 ht1 hT2
  have hwe : entrySum WEI ≤ 2 * KW / T1 :=
    early_inverse_bound k T1 T2 lam zeta0 ellStar ht1 hT2 hd hlarge
  have hf : entrySum F ≤ KF := residual_bound k T1 T2 lam KE zeta0 ellStar E L hT1 hT2 hE
  have hwt : entrySum WIᵀ ≤ KW / T1 := by rw [entrySum_transpose]; exact hw
  have hwet : entrySum WEIᵀ ≤ 2 * KW / T1 := by rw [entrySum_transpose]; exact hwe
  have hft : entrySum Fᵀ ≤ KF := by rw [entrySum_transpose]; exact hf
  have hwf : entrySum (WIᵀ * F) ≤ KW / T1 * KF := entrySum_mul_bound _ _ _ _ hwt hf
  have hwef : entrySum (WEIᵀ * Fᵀ) ≤ (2 * KW / T1) * KF :=
    entrySum_mul_bound _ _ _ _ hwet hft
  have hee : entrySum EE ≤ (2 * KW / T1) * KF * entrySum B :=
    entrySum_mul_bound _ _ _ _ hwef le_rfl
  have hkappa : 0 < paperKappa k T1 lam := by unfold paperKappa; positivity
  have hlead : entrySum (paperKappa k T1 lam •
      outerProd (fun _ : Fin (k + 1) => (1 : ℚ)) ellStar) = 2 * rowAbs ellStar / (lam * T1) := by
    rw [entrySum_smul, abs_of_pos hkappa, entrySum_outer]
    have hones : rowAbs (fun _ : Fin (k + 1) => (1 : ℚ)) = (k + 1 : ℚ) := by simp [rowAbs]
    rw [hones]
    unfold paperKappa
    have hr : (k + 1 : ℚ) ≠ 0 := by positivity
    field_simp
  have hel : entrySum EL ≤ 2 * rowAbs ellStar / (lam * T1) + KW / T1 * KF := by
    have h := entrySum_add_le (paperKappa k T1 lam •
      outerProd (fun _ : Fin (k + 1) => (1 : ℚ)) ellStar) (WIᵀ * F)
    rw [hlead] at h
    exact le_trans h (add_le_add le_rfl hwf)
  obtain ⟨hW, hWE⟩ := count_table_bounds k T1 T2 lam zeta0 ellStar hT1 hT2
  have hiw : entrySum (eta • (L * W) - eta • (Lᵀ * W * B)) ≤ KI / T1 :=
    internal_linear_bound W L B T1 T2 KC ht1 (le_trans hT1 hT2) hW
  have hiwe : entrySum (eta • (L * WE) - eta • (Lᵀ * WE * B)) ≤ KI / T1 :=
    internal_linear_bound WE L B T1 T2 KC ht1 (le_trans hT1 hT2) hWE
  have hh : entrySum H ≤ (k + 1 : ℚ) * Kd / T1 := psi_error_bound k T1 dc Kd hdc
  have hearly : entrySum (H + eta • (L * WE) - eta • (Lᵀ * WE * B) - EE) ≤
      (k + 1 : ℚ) * Kd / T1 + KI / T1 + (2 * KW / T1) * KF * entrySum B := by
    have hform : H + eta • (L * WE) - eta • (Lᵀ * WE * B) - EE =
      (H + (eta • (L * WE) - eta • (Lᵀ * WE * B))) - EE := by abel
    rw [hform]
    have h := entrySum_sub_le (H + (eta • (L * WE) - eta • (Lᵀ * WE * B))) EE
    have h' := entrySum_add_le H (eta • (L * WE) - eta • (Lᵀ * WE * B))
    linarith
  have hlate : entrySum (H + EL + eta • (L * W) - eta • (Lᵀ * W * B)) ≤
      (k + 1 : ℚ) * Kd / T1 + (2 * rowAbs ellStar / (lam * T1) + KW / T1 * KF) + KI / T1 := by
    have hform : H + EL + eta • (L * W) - eta • (Lᵀ * W * B) =
      H + EL + (eta • (L * W) - eta • (Lᵀ * W * B)) := by abel
    rw [hform]
    have h := entrySum_add_le (H + EL) (eta • (L * W) - eta • (Lᵀ * W * B))
    have h' := entrySum_add_le H EL
    linarith
  refine le_trans (add_le_add hearly hlate) ?_
  unfold scoreConstant
  dsimp only [KI, KC, KW, KF]
  exact le_of_eq (by ring)

/-- The T1-growing baseline row sums cancel in P0 M exactly. -/
theorem referenceCoupling_mul_reset {m : Type*} (k : ℕ) (a : m → ℚ)
    (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ) :
    referenceCoupling (r := Fin (k + 1)) a *
      Matrix.fromRows (WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar)
        (W_concrete k T1 T2 lam zeta0) = -outerProd a ellStar := by
  have he0 : dotProduct (fun _ : Fin (k + 1) => (1 : ℚ)) (earlyUnit k) = 1 := by
    simp [dotProduct, earlyUnit]
  unfold referenceCoupling
  rw [Matrix.fromCols_mul_fromRows]
  exact P0_mul_M_eq_neg_a_ell_star a (W_concrete k T1 T2 lam zeta0) ellStar (earlyUnit k) he0


/-- A decaying gain estimate also provides its uniform constant bound. -/
theorem gain_abs_le_constant (T1 dc Kd : ℚ) (hT1 : 1 ≤ T1) (hdc : |dc| ≤ Kd / T1) :
    |dc| ≤ Kd := by
  have ht : 0 < T1 := lt_of_lt_of_le (by norm_num) hT1
  have hn : 0 ≤ Kd := by
    have hdiv : 0 ≤ Kd / T1 := le_trans (abs_nonneg dc) hdc
    simpa using (le_div_iff₀ ht).mp hdiv
  have hred : Kd / T1 ≤ Kd := (div_le_iff₀ ht).mpr (by nlinarith)
  exact le_trans hdc hred



/-- A fixed constant for the actual D residual. -/
def deficitConstant {m : Type*} [Fintype m] (k : ℕ) (Kd : ℚ)
    (a : m → ℚ) (D0 : Matrix m (Fin (k + 1)) ℚ) (ellStar : Fin (k + 1) → ℚ) :=
  entrySum (D0 + outerProd a ellStar) +
    Kd * entrySum (outerProd (fun _ : m => (1 : ℚ)) (e0_row (k + 1)))

theorem deficit_error_bound {m : Type*} [Fintype m] (k : ℕ) (T1 T2 lam dc Kd : ℚ)
    (a : m → ℚ) (D0 : Matrix m (Fin (k + 1)) ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ)
    (hT1 : 1 ≤ T1) (hdc : |dc| ≤ Kd / T1) :
    entrySum ((D0 + dc • outerProd (fun _ : m => (1 : ℚ)) (e0_row (k + 1))) -
      referenceCoupling (r := Fin (k + 1)) a *
        Matrix.fromRows (WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar)
          (W_concrete k T1 T2 lam zeta0)) ≤ deficitConstant k Kd a D0 ellStar := by
  rw [referenceCoupling_mul_reset]
  have hid : (D0 + dc • outerProd (fun _ : m => (1 : ℚ)) (e0_row (k + 1))) -
      -outerProd a ellStar = D0 + outerProd a ellStar +
        dc • outerProd (fun _ : m => (1 : ℚ)) (e0_row (k + 1)) := by abel
  rw [hid]
  have h := entrySum_add_le (D0 + outerProd a ellStar)
    (dc • outerProd (fun _ : m => (1 : ℚ)) (e0_row (k + 1)))
  rw [entrySum_smul] at h
  unfold deficitConstant
  refine le_trans h (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_right (gain_abs_le_constant T1 dc Kd hT1 hdc)
    (entrySum_nonneg (outerProd (fun _ : m => (1 : ℚ)) (e0_row (k + 1))))


/-- The explicit constant resulting from the interpolation formula. -/
def couplingConstant {m : Type*} [Fintype m] (k : ℕ) (lam KE Kd : ℚ)
    (a : m → ℚ) (X LX D0 : Matrix m (Fin (k + 1)) ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (L B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :=
  deficitConstant k Kd a D0 ellStar * inverseConstant k lam zeta0 + entrySum LX *
    (scoreConstant k lam KE Kd zeta0 ellStar L B +
      entrySum X * deficitConstant k Kd a D0 ellStar * inverseConstant k lam zeta0)


/-- A generic scalar specialization of the exact interpolation bound. -/
theorem interpolation_scaled_bound {m n w : Type*} [Fintype m] [Fintype n] [Fintype w]
    (X LX : Matrix m w ℚ) (M : Matrix n w ℚ) (RM : Matrix w n ℚ)
    (D : Matrix m w ℚ) (Q : Matrix n w ℚ) (P0 : Matrix m n ℚ)
    (T1 KD KW KQ : ℚ)
    (hD : entrySum (D - P0 * M) ≤ KD) (hR : entrySum RM ≤ KW / T1)
    (hQ : entrySum (Q - P0ᵀ * X) ≤ KQ / T1) :
    entrySum (P_interp X LX M RM D Q P0 - P0) ≤
      (KD * KW + entrySum LX * (KQ + entrySum X * KD * KW)) / T1 := by
  have hDR0 := entrySum_nonneg (D - P0 * M)
  have hKD : 0 ≤ KD := le_trans hDR0 hD
  have hpair : entrySum (D - P0 * M) * entrySum RM ≤ KD * (KW / T1) :=
    mul_le_mul hD hR (entrySum_nonneg RM) hKD
  have htriple : entrySum X * entrySum (D - P0 * M) * entrySum RM ≤
      entrySum X * KD * (KW / T1) := by
    have h := mul_le_mul_of_nonneg_left hpair (entrySum_nonneg X)
    simpa only [mul_assoc] using h
  have hinside := add_le_add hQ htriple
  have hLX := mul_le_mul_of_nonneg_left hinside (entrySum_nonneg LX)
  have hbase := interpolation_correction_bound X LX M RM D Q P0
  refine le_trans hbase (le_trans (add_le_add hpair hLX) ?_)
  exact le_of_eq (by ring)


/-- Actual P constructed by interpolation satisfies the uniform O(1/T1) bound.
No hypothesis assumes a final estimate on P or Q. -/
theorem coupling_error_bound {m : Type*} [Fintype m] (k : ℕ) (T1 T2 lam KE Kd dc : ℚ)
    (a : m → ℚ) (X LX D0 : Matrix m (Fin (k + 1)) ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E L B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (ha : Matrix.vecMul a X = zeta0 + Matrix.vecMul zeta0 B)
    (hT1 : 1 ≤ T1) (hT2 : T1 ≤ T2) (hlam : 0 < lam) (hzeta : 0 < zeta0 (lastIdx k))
    (hd : (1 / 2 : ℚ) < 1 + dotProduct ellStar
      (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (earlyUnit k)))
    (hlarge : 2 * inverseConstant k lam zeta0 * rowAbs ellStar ≤ T1)
    (hE : entrySum (E - T1 • paperE0 k lam zeta0) ≤ KE) (hdc : |dc| ≤ Kd / T1) :
    let WE := WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar
    let W := W_concrete k T1 T2 lam zeta0
    let M := Matrix.fromRows WE W
    let RM := Matrix.fromCols (0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
      (Winv_concrete k T1 T2 lam zeta0)
    let D := D0 + dc • outerProd (fun _ : m => (1 : ℚ)) (e0_row (k + 1))
    let Q := resetScoreTarget (Matrix.vecMul zeta0 B - zeta0 - dc • e0_row (k + 1))
      WE W L (paperCross k T1 T2 lam zeta0 ellStar E L) (1 / (T1 * T2 ^ 2)) B
    let P0 := referenceCoupling (r := Fin (k + 1)) a
    entrySum (P_interp X LX M RM D Q P0 - P0) ≤
      couplingConstant k lam KE Kd a X LX D0 zeta0 ellStar L B / T1 := by
  intro WE W M RM D Q P0
  have ht1 : 0 < T1 := lt_of_lt_of_le (by norm_num) hT1
  have hD : entrySum (D - P0 * M) ≤ deficitConstant k Kd a D0 ellStar :=
    deficit_error_bound k T1 T2 lam dc Kd a D0 zeta0 ellStar hT1 hdc
  have hR : entrySum RM ≤ inverseConstant k lam zeta0 / T1 := by
    dsimp only [RM]
    rw [entrySum_fromCols, entrySum_zero, zero_add]
    exact late_inverse_bound k T1 T2 lam zeta0 ht1 hT2
  have hQ : entrySum (Q - P0ᵀ * X) ≤ scoreConstant k lam KE Kd zeta0 ellStar L B / T1 := by
    change entrySum (Q - (referenceCoupling a)ᵀ * X) ≤ _
    rw [referenceCoupling_transpose_mul a X zeta0 B ha]
    exact score_error_bound k T1 T2 lam KE Kd dc zeta0 ellStar E L B
      hT1 hT2 hlam hzeta hd hlarge hE hdc
  exact interpolation_scaled_bound X LX M RM D Q P0 T1
    (deficitConstant k Kd a D0 ellStar) (inverseConstant k lam zeta0)
    (scoreConstant k lam KE Kd zeta0 ellStar L B) hD hR hQ


/-- The paper's first strict sign criterion, derived entrywise from the norm. -/
theorem cross_positive_of_error_bound (k : ℕ) (T1 lam K : ℚ)
    (C : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hT1 : 0 < T1) (hlam : 0 < lam)
    (hC : entrySum (C - paperKappa k T1 lam • outerProd (fun _ => 1) (fun _ => 1)) ≤ K / T1 ^ 2)
    (hlarge : (k + 1 : ℚ) * lam * K < T1) :
    ∀ i j, paperKappa k T1 lam / 2 < C i j ∧ 0 < C i j := by
  have hkp : 0 < paperKappa k T1 lam := by unfold paperKappa; positivity
  have hsmall : K / T1 ^ 2 < paperKappa k T1 lam / 2 := by
    have hr : (0 : ℚ) < k + 1 := by positivity
    have hprod := mul_lt_mul_of_pos_right hlarge hT1
    have hratio : K / T1 ^ 2 < 1 / ((k + 1 : ℚ) * lam * T1) := by
      apply (div_lt_div_iff₀ (sq_pos_of_pos hT1) (by positivity)).mpr
      nlinarith
    convert hratio using 1
    unfold paperKappa
    ring
  intro i j
  have hentry := le_trans (abs_entry_le_entrySum
    (C - paperKappa k T1 lam • outerProd (fun _ => 1) (fun _ => 1)) i j) hC
  simp only [Matrix.sub_apply, Matrix.smul_apply, outerProd, Matrix.of_apply, smul_eq_mul,
    mul_one] at hentry
  have hlo := (abs_le.mp hentry).1
  constructor <;> linarith


/-- Exact early/late signs and waiting margins follow from the paper's scalar
criterion on the actual interpolation error. -/
theorem coupling_margins_of_error_bound {m : Type*} [Fintype m]
    (k : ℕ) (a : m → ℚ) (g : m) (amin Ak c eps : ℚ)
    (P : Matrix m (Fin (k + 1) ⊕ Fin (k + 1)) ℚ)
    (hamin : 0 < amin) (ha : ∀ i, amin ≤ a i) (hag : Ak + 1 < a g) (hc : c < 1)
    (hP : entrySum (P - referenceCoupling a) ≤ eps)
    (heps : eps < amin / 4) (hepsg : eps < (a g - Ak - 1) / 2) :
    (∀ i j, P i (Sum.inl j) < -(amin / 4) ∧ amin / 4 < P i (Sum.inr j)) ∧
    (∀ j, Ak < -P g (Sum.inl j) - c) := by
  let P0 : Matrix m (Fin (k + 1) ⊕ Fin (k + 1)) ℚ := referenceCoupling a
  change entrySum (P - P0) ≤ eps at hP
  have hentry (i : m) (j : Fin (k + 1) ⊕ Fin (k + 1)) :
      |P i j - P0 i j| ≤ eps := by
    have hh := abs_entry_le_entrySum (P - P0) i j
    change |P i j - P0 i j| ≤ entrySum (P - P0) at hh
    exact hh.trans hP
  constructor
  · intro i j
    have he := (abs_le.mp (hentry i (Sum.inl j))).2
    have hl := (abs_le.mp (hentry i (Sum.inr j))).1
    simp only [P0, referenceCoupling, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
      Matrix.neg_apply, outerProd, Matrix.of_apply, mul_one] at he hl
    have hai := ha i
    constructor <;> linarith
  · intro j
    have he := (abs_le.mp (hentry g (Sum.inl j))).2
    simp only [P0, referenceCoupling, Matrix.fromCols_apply_inl, Matrix.neg_apply,
      outerProd, Matrix.of_apply, mul_one] at he
    linarith


/-- One fixed first-parameter threshold realizes all strict scalar sign
criteria simultaneously; it is chosen before the universal parameter values. -/
theorem exists_uniform_sign_threshold (k : ℕ) (lam Kcross KP amin ag Ak : ℚ)
    (hamin : 0 < amin) (hag : Ak + 1 < ag) :
    ∃ N : ℕ, 1 < (N : ℚ) ∧ ∀ T1 : ℚ, (N : ℚ) ≤ T1 →
      (k + 1 : ℚ) * lam * Kcross < T1 ∧ KP / T1 < amin / 4 ∧
      KP / T1 < (ag - Ak - 1) / 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max (max 1 ((k + 1 : ℚ) * lam * Kcross)) (max (4 * KP / amin) (2 * KP / (ag - Ak - 1))))
  have hone : (1 : ℚ) < (N : ℚ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  refine ⟨N, hone, ?_⟩
  intro T1 hT1
  have ht : 0 < T1 := lt_of_lt_of_le (lt_trans (by norm_num) hone) hT1
  have hx : (k + 1 : ℚ) * lam * Kcross < T1 :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN) hT1
  have ha : 4 * KP / amin < T1 :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN) hT1
  have hg : 2 * KP / (ag - Ak - 1) < T1 :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN) hT1
  have hagpos : 0 < ag - Ak - 1 := by linarith
  refine ⟨hx, (div_lt_iff₀ ht).mpr ?_, (div_lt_iff₀ ht).mpr ?_⟩
  · have h := (div_lt_iff₀ hamin).mp ha
    nlinarith
  · have h := (div_lt_iff₀ hagpos).mp hg
    nlinarith

/-- The literal coupling selected by the v15 interpolation formula. -/
def paperCoupling {m : Type*} [Fintype m] (k : ℕ) (T1 T2 lam dc : ℚ)
    (a : m → ℚ) (X LX D0 : Matrix m (Fin (k + 1)) ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E L B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :=
  let WE := WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar
  let W := W_concrete k T1 T2 lam zeta0
  let M := Matrix.fromRows WE W
  let RM := Matrix.fromCols (0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (Winv_concrete k T1 T2 lam zeta0)
  let D := D0 + dc • outerProd (fun _ : m => (1 : ℚ)) (e0_row (k + 1))
  let Q := resetScoreTarget (Matrix.vecMul zeta0 B - zeta0 - dc • e0_row (k + 1))
    WE W L (paperCross k T1 T2 lam zeta0 ellStar E L) (1 / (T1 * T2 ^ 2)) B
  P_interp X LX M RM D Q (referenceCoupling a)

open FaithfulAppendix (normStar)

/-- The literal sum-of-two-norms estimate feeds the unchanged fixed certificate
constant.  All norm comparisons go from `normStar` to `entrySum`; no reverse
comparison, and hence no unaccounted dimension factor, is used. -/
theorem internal_normStar_bound_with_entry_constants {r w : Type*}
    [Fintype r] [Fintype w] [Nonempty r] [Nonempty w]
    (Z : Matrix r w ℚ) (L : Matrix r r ℚ) (B : Matrix w w ℚ) (T1 T2 C : ℚ)
    (hT1 : 1 ≤ T1) (hT2 : T1 ≤ T2) (hZ : entrySum Z ≤ T2 * C) :
    normStar ((1 / (T1 * T2 ^ 2)) • (L * Z) -
      (1 / (T1 * T2 ^ 2)) • (Lᵀ * Z * B)) ≤
      entrySum L * C * (1 + entrySum B) / T1 := by
  have ht1 : 0 < T1 := by linarith
  have ht2 : 0 < T2 := ht1.trans_le hT2
  have hC : 0 ≤ C := by nlinarith [entrySum_nonneg Z]
  have hn : 0 ≤ entrySum L * C * (1 + entrySum B) :=
    mul_nonneg (mul_nonneg (entrySum_nonneg L) hC) (by linarith [entrySum_nonneg B])
  have hconstant : normStar L * C * (1 + normStar B) ≤
      entrySum L * C * (1 + entrySum B) :=
    mul_le_mul
      (mul_le_mul_of_nonneg_right (FaithfulAppendix.le_entrySum L) hC)
      (by linarith [FaithfulAppendix.le_entrySum B])
      (by linarith [FaithfulAppendix.nonneg B])
      (mul_nonneg (entrySum_nonneg L) hC)
  have hsum := FaithfulAppendix.internal_norm_sum_square_bound Z L B T1 T2 C ht1 hT2
    ((FaithfulAppendix.le_entrySum Z).trans hZ)
  exact (FaithfulAppendix.sub_le _ _).trans (hsum.trans
    ((div_le_div_of_nonneg_right hconstant (sq_nonneg T1)).trans
      (div_le_div_of_nonneg_left hn ht1 (by nlinarith))))

/-- The literal matrix norm now controls the actual score target. The selected
certificate constant is retained, using explicit forward norm comparisons. -/
theorem score_error_normStar_bound (k : ℕ) (T1 T2 lam KE Kd dc : ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E L B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hT1 : 1 ≤ T1) (hT2 : T1 ≤ T2) (hlam : 0 < lam) (hzeta : 0 < zeta0 (lastIdx k))
    (hd : (1 / 2 : ℚ) < 1 + dotProduct ellStar
      (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (earlyUnit k)))
    (hlarge : 2 * inverseConstant k lam zeta0 * rowAbs ellStar ≤ T1)
    (hE : entrySum (E - T1 • paperE0 k lam zeta0) ≤ KE) (hdc : |dc| ≤ Kd / T1) :
    let Z := outerProd (fun _ : Fin (k + 1) => (1 : ℚ)) zeta0
    normStar (resetScoreTarget (Matrix.vecMul zeta0 B - zeta0 - dc • e0_row (k + 1))
      (WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar) (W_concrete k T1 T2 lam zeta0)
      L (paperCross k T1 T2 lam zeta0 ellStar E L) (1 / (T1 * T2 ^ 2)) B -
      Matrix.fromRows (-(Z + Z * B)) (Z + Z * B)) ≤
      scoreConstant k lam KE Kd zeta0 ellStar L B / T1 := by
  intro Z
  let W := W_concrete k T1 T2 lam zeta0
  let WE := WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar
  let WI := Winv_concrete k T1 T2 lam zeta0
  let WEI := WE_inv_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar
  let F := paperResidual k T1 T2 lam zeta0 ellStar E L
  let H := (-dc) • outerProd (fun _ : Fin (k + 1) => (1 : ℚ)) (e0_row (k + 1))
  let EL := paperKappa k T1 lam • outerProd (fun _ : Fin (k + 1) => (1 : ℚ)) ellStar + WIᵀ * F
  let EE := WEIᵀ * Fᵀ * B
  let eta := 1 / (T1 * T2 ^ 2)
  let KW := inverseConstant k lam zeta0
  let KF := residualConstant k lam KE zeta0 ellStar L
  let KC := countConstant k lam zeta0 ellStar
  let KI := entrySum L * KC * (1 + entrySum B)
  have ht1 : 0 < T1 := lt_of_lt_of_le (by norm_num) hT1
  have ht2 : 0 < T2 := lt_of_lt_of_le ht1 hT2
  have hdn : 1 + dotProduct ellStar (Matrix.mulVec WI (earlyUnit k)) ≠ 0 := by
    have : 0 < 1 + dotProduct ellStar (Matrix.mulVec WI (earlyUnit k)) :=
      lt_trans (by norm_num) hd
    exact ne_of_gt this
  have hce : paperCross k T1 T2 lam zeta0 ellStar E L * WE = (2 : ℚ) • Z + EL := by
    have h := cross_mul_early k T1 T2 lam zeta0 ellStar E L
      (ne_of_gt ht1) (ne_of_gt ht2) (ne_of_gt hlam) (ne_of_gt hzeta) hdn
    change _ = (2 : ℚ) • Z + _ + _ at h
    rw [h]
    exact add_assoc _ _ _
  have hcl : (paperCross k T1 T2 lam zeta0 ellStar E L)ᵀ * W * B =
      (2 : ℚ) • (Z * B) + EE :=
    cross_transpose_mul_late k T1 T2 lam zeta0 ellStar E L B
      (ne_of_gt ht1) (ne_of_gt ht2) (ne_of_gt hlam) (ne_of_gt hzeta)
  rw [resetScoreTarget_error _ zeta0 WE W L _ eta B H EL EE
    (psi_table_identity k zeta0 B dc) hce hcl]
  apply (FaithfulAppendix.fromRows_le _ _).trans
  have hw : normStar WI ≤ KW / T1 :=
    (FaithfulAppendix.le_entrySum _).trans (late_inverse_bound k T1 T2 lam zeta0 ht1 hT2)
  have hwe : normStar WEI ≤ 2 * KW / T1 :=
    (FaithfulAppendix.le_entrySum _).trans
      (early_inverse_bound k T1 T2 lam zeta0 ellStar ht1 hT2 hd hlarge)
  have hf : normStar F ≤ KF :=
    (FaithfulAppendix.le_entrySum _).trans
      (residual_bound k T1 T2 lam KE zeta0 ellStar E L hT1 hT2 hE)
  have hwt : normStar WIᵀ ≤ KW / T1 := by rw [FaithfulAppendix.transpose]; exact hw
  have hwet : normStar WEIᵀ ≤ 2 * KW / T1 := by rw [FaithfulAppendix.transpose]; exact hwe
  have hft : normStar Fᵀ ≤ KF := by rw [FaithfulAppendix.transpose]; exact hf
  have hwf : normStar (WIᵀ * F) ≤ KW / T1 * KF := FaithfulAppendix.mul_bound _ _ _ _ hwt hf
  have hwef : normStar (WEIᵀ * Fᵀ) ≤ (2 * KW / T1) * KF :=
    FaithfulAppendix.mul_bound _ _ _ _ hwet hft
  have hee : normStar EE ≤ (2 * KW / T1) * KF * entrySum B :=
    FaithfulAppendix.mul_bound _ _ _ _ hwef (FaithfulAppendix.le_entrySum B)
  have hkappa : 0 < paperKappa k T1 lam := by unfold paperKappa; positivity
  have hlead : entrySum (paperKappa k T1 lam •
      outerProd (fun _ : Fin (k + 1) => (1 : ℚ)) ellStar) = 2 * rowAbs ellStar / (lam * T1) := by
    rw [entrySum_smul, abs_of_pos hkappa, entrySum_outer]
    have hones : rowAbs (fun _ : Fin (k + 1) => (1 : ℚ)) = (k + 1 : ℚ) := by simp [rowAbs]
    rw [hones]
    unfold paperKappa
    have hr : (k + 1 : ℚ) ≠ 0 := by positivity
    field_simp
  have hel : normStar EL ≤ 2 * rowAbs ellStar / (lam * T1) + KW / T1 * KF := by
    have h := FaithfulAppendix.add_le (paperKappa k T1 lam •
      outerProd (fun _ : Fin (k + 1) => (1 : ℚ)) ellStar) (WIᵀ * F)
    have hnorm : normStar (paperKappa k T1 lam •
        outerProd (fun _ : Fin (k + 1) => (1 : ℚ)) ellStar) ≤
        2 * rowAbs ellStar / (lam * T1) :=
      (FaithfulAppendix.le_entrySum _).trans_eq hlead
    exact h.trans (add_le_add hnorm hwf)
  obtain ⟨hW, hWE⟩ := count_table_bounds k T1 T2 lam zeta0 ellStar hT1 hT2
  have hiw : normStar (eta • (L * W) - eta • (Lᵀ * W * B)) ≤ KI / T1 :=
    internal_normStar_bound_with_entry_constants W L B T1 T2 KC hT1 hT2 hW
  have hiwe : normStar (eta • (L * WE) - eta • (Lᵀ * WE * B)) ≤ KI / T1 :=
    internal_normStar_bound_with_entry_constants WE L B T1 T2 KC hT1 hT2 hWE
  have hh : normStar H ≤ (k + 1 : ℚ) * Kd / T1 :=
    (FaithfulAppendix.le_entrySum _).trans (psi_error_bound k T1 dc Kd hdc)
  have hearly : normStar (H + eta • (L * WE) - eta • (Lᵀ * WE * B) - EE) ≤
      (k + 1 : ℚ) * Kd / T1 + KI / T1 + (2 * KW / T1) * KF * entrySum B := by
    have hform : H + eta • (L * WE) - eta • (Lᵀ * WE * B) - EE =
      (H + (eta • (L * WE) - eta • (Lᵀ * WE * B))) - EE := by abel
    rw [hform]
    have h := FaithfulAppendix.sub_le (H + (eta • (L * WE) - eta • (Lᵀ * WE * B))) EE
    have h' := FaithfulAppendix.add_le H (eta • (L * WE) - eta • (Lᵀ * WE * B))
    linarith
  have hlate : normStar (H + EL + eta • (L * W) - eta • (Lᵀ * W * B)) ≤
      (k + 1 : ℚ) * Kd / T1 + (2 * rowAbs ellStar / (lam * T1) + KW / T1 * KF) + KI / T1 := by
    have hform : H + EL + eta • (L * W) - eta • (Lᵀ * W * B) =
      H + EL + (eta • (L * W) - eta • (Lᵀ * W * B)) := by abel
    rw [hform]
    have h := FaithfulAppendix.add_le (H + EL) (eta • (L * W) - eta • (Lᵀ * W * B))
    have h' := FaithfulAppendix.add_le H EL
    linarith
  refine le_trans (add_le_add hearly hlate) ?_
  unfold scoreConstant
  dsimp only [KI, KC, KW, KF]
  exact le_of_eq (by ring)

/-- Interpolation propagates the literal score norm directly. The fixed input
norms are bounded above by the original entry-sum constants, preserving the
already selected rational cutoff. -/
theorem interpolation_normStar_scaled_bound {m n w : Type*}
    [Fintype m] [Fintype n] [Fintype w] [Nonempty m] [Nonempty n] [Nonempty w]
    (X LX : Matrix m w ℚ) (M : Matrix n w ℚ) (RM : Matrix w n ℚ)
    (D : Matrix m w ℚ) (Q : Matrix n w ℚ) (P0 : Matrix m n ℚ)
    (T1 KD KW KQ : ℚ)
    (hD : normStar (D - P0 * M) ≤ KD) (hR : normStar RM ≤ KW / T1)
    (hQ : normStar (Q - P0ᵀ * X) ≤ KQ / T1) :
    normStar (P_interp X LX M RM D Q P0 - P0) ≤
      (KD * KW + entrySum LX * (KQ + entrySum X * KD * KW)) / T1 := by
  let DR := D - P0 * M
  let QR := Q - P0ᵀ * X
  have hP : P_interp X LX M RM D Q P0 - P0 =
      DR * RM + LX * (QRᵀ - Xᵀ * DR * RM) := by
    change (P0 + DR * RM + LX * (QRᵀ - Xᵀ * DR * RM)) - P0 = _
    abel
  have hprod : normStar (DR * RM) ≤ KD * (KW / T1) :=
    FaithfulAppendix.mul_bound _ _ _ _ hD hR
  have hx : normStar (Xᵀ * DR) ≤ entrySum X * KD :=
    FaithfulAppendix.mul_bound _ _ _ _
      (by simpa only [FaithfulAppendix.transpose] using FaithfulAppendix.le_entrySum X) hD
  have hxdr : normStar (Xᵀ * DR * RM) ≤ entrySum X * KD * (KW / T1) :=
    FaithfulAppendix.mul_bound _ _ _ _ hx hR
  have hqr : normStar QRᵀ ≤ KQ / T1 := by
    rw [FaithfulAppendix.transpose]
    exact hQ
  have hinner : normStar (QRᵀ - Xᵀ * DR * RM) ≤
      KQ / T1 + entrySum X * KD * (KW / T1) :=
    (FaithfulAppendix.sub_le _ _).trans (add_le_add hqr hxdr)
  have hlx := FaithfulAppendix.mul_bound LX (QRᵀ - Xᵀ * DR * RM) _ _
    (FaithfulAppendix.le_entrySum LX) hinner
  rw [hP]
  exact (FaithfulAppendix.add_le _ _).trans ((add_le_add hprod hlx).trans_eq (by ring))

/-- The actual coupling error is now bounded in the paper's matrix norm,
using the same certificate constant as the original executable construction. -/
theorem coupling_error_normStar_bound {m : Type*} [Fintype m] [Nonempty m] (k : ℕ) (T1 T2 lam KE Kd dc : ℚ)
    (a : m → ℚ) (X LX D0 : Matrix m (Fin (k + 1)) ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E L B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (ha : Matrix.vecMul a X = zeta0 + Matrix.vecMul zeta0 B)
    (hT1 : 1 ≤ T1) (hT2 : T1 ≤ T2) (hlam : 0 < lam) (hzeta : 0 < zeta0 (lastIdx k))
    (hd : (1 / 2 : ℚ) < 1 + dotProduct ellStar
      (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (earlyUnit k)))
    (hlarge : 2 * inverseConstant k lam zeta0 * rowAbs ellStar ≤ T1)
    (hE : entrySum (E - T1 • paperE0 k lam zeta0) ≤ KE) (hdc : |dc| ≤ Kd / T1) :
    let WE := WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar
    let W := W_concrete k T1 T2 lam zeta0
    let M := Matrix.fromRows WE W
    let RM := Matrix.fromCols (0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
      (Winv_concrete k T1 T2 lam zeta0)
    let D := D0 + dc • outerProd (fun _ : m => (1 : ℚ)) (e0_row (k + 1))
    let Q := resetScoreTarget (Matrix.vecMul zeta0 B - zeta0 - dc • e0_row (k + 1))
      WE W L (paperCross k T1 T2 lam zeta0 ellStar E L) (1 / (T1 * T2 ^ 2)) B
    let P0 := referenceCoupling (r := Fin (k + 1)) a
    normStar (P_interp X LX M RM D Q P0 - P0) ≤
      couplingConstant k lam KE Kd a X LX D0 zeta0 ellStar L B / T1 := by
  intro WE W M RM D Q P0
  have ht1 : 0 < T1 := lt_of_lt_of_le (by norm_num) hT1
  have hD : normStar (D - P0 * M) ≤ deficitConstant k Kd a D0 ellStar :=
    (FaithfulAppendix.le_entrySum _).trans
      (deficit_error_bound k T1 T2 lam dc Kd a D0 zeta0 ellStar hT1 hdc)
  have hR : normStar RM ≤ inverseConstant k lam zeta0 / T1 := by
    dsimp only [RM]
    apply (FaithfulAppendix.le_entrySum _).trans
    rw [entrySum_fromCols, entrySum_zero, zero_add]
    exact late_inverse_bound k T1 T2 lam zeta0 ht1 hT2
  have hQ : normStar (Q - P0ᵀ * X) ≤ scoreConstant k lam KE Kd zeta0 ellStar L B / T1 := by
    change normStar (Q - (referenceCoupling a)ᵀ * X) ≤ _
    rw [referenceCoupling_transpose_mul a X zeta0 B ha]
    exact score_error_normStar_bound k T1 T2 lam KE Kd dc zeta0 ellStar E L B
      hT1 hT2 hlam hzeta hd hlarge hE hdc
  exact interpolation_normStar_scaled_bound X LX M RM D Q P0 T1
    (deficitConstant k Kd a D0 ellStar) (inverseConstant k lam zeta0)
    (scoreConstant k lam KE Kd zeta0 ellStar L B) hD hR hQ


theorem cross_positive_of_normStar_bound (k : ℕ) (T1 lam K : ℚ)
    (C : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hT1 : 0 < T1) (hlam : 0 < lam)
    (hC : normStar (C - paperKappa k T1 lam • outerProd (fun _ => 1) (fun _ => 1)) ≤ K / T1 ^ 2)
    (hlarge : (k + 1 : ℚ) * lam * K < T1) :
    ∀ i j, paperKappa k T1 lam / 2 < C i j ∧ 0 < C i j := by
  have hkp : 0 < paperKappa k T1 lam := by unfold paperKappa; positivity
  have hsmall : K / T1 ^ 2 < paperKappa k T1 lam / 2 := by
    have hr : (0 : ℚ) < k + 1 := by positivity
    have hprod := mul_lt_mul_of_pos_right hlarge hT1
    have hratio : K / T1 ^ 2 < 1 / ((k + 1 : ℚ) * lam * T1) := by
      apply (div_lt_div_iff₀ (sq_pos_of_pos hT1) (by positivity)).mpr
      nlinarith
    convert hratio using 1
    unfold paperKappa
    ring
  intro i j
  have hentry := le_trans (FaithfulAppendix.abs_entry_le
    (C - paperKappa k T1 lam • outerProd (fun _ => 1) (fun _ => 1)) i j) hC
  simp only [Matrix.sub_apply, Matrix.smul_apply, outerProd, Matrix.of_apply, smul_eq_mul,
    mul_one] at hentry
  have hlo := (abs_le.mp hentry).1
  constructor <;> linarith


theorem coupling_margins_of_normStar_bound {m : Type*} [Fintype m] [Nonempty m]
    (k : ℕ) (a : m → ℚ) (g : m) (amin Ak c eps : ℚ)
    (P : Matrix m (Fin (k + 1) ⊕ Fin (k + 1)) ℚ)
    (hamin : 0 < amin) (ha : ∀ i, amin ≤ a i) (hag : Ak + 1 < a g) (hc : c < 1)
    (hP : normStar (P - referenceCoupling a) ≤ eps)
    (heps : eps < amin / 4) (hepsg : eps < (a g - Ak - 1) / 2) :
    (∀ i j, P i (Sum.inl j) < -(amin / 4) ∧ amin / 4 < P i (Sum.inr j)) ∧
    (∀ j, Ak < -P g (Sum.inl j) - c) := by
  let P0 : Matrix m (Fin (k + 1) ⊕ Fin (k + 1)) ℚ := referenceCoupling a
  change normStar (P - P0) ≤ eps at hP
  have hentry (i : m) (j : Fin (k + 1) ⊕ Fin (k + 1)) :
      |P i j - P0 i j| ≤ eps := by
    have hh := FaithfulAppendix.abs_entry_le (P - P0) i j
    change |P i j - P0 i j| ≤ normStar (P - P0) at hh
    exact hh.trans hP
  constructor
  · intro i j
    have he := (abs_le.mp (hentry i (Sum.inl j))).2
    have hl := (abs_le.mp (hentry i (Sum.inr j))).1
    simp only [P0, referenceCoupling, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
      Matrix.neg_apply, outerProd, Matrix.of_apply, mul_one] at he hl
    have hai := ha i
    constructor <;> linarith
  · intro j
    have he := (abs_le.mp (hentry g (Sum.inl j))).2
    simp only [P0, referenceCoupling, Matrix.fromCols_apply_inl, Matrix.neg_apply,
      outerProd, Matrix.of_apply, mul_one] at he
    linarith


/-- The actual cross matrix and actual interpolated coupling have all strict
signs and waiting margins once the explicit first-parameter criteria hold.
The estimates above, not assumptions on the final C/P errors, prove the result. -/
theorem actual_reset_signs {m : Type*} [Fintype m] (k : ℕ) (T1 T2 lam KE Kd dc : ℚ)
    (a : m → ℚ) (X LX D0 : Matrix m (Fin (k + 1)) ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E L B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (g : m) (amin Ak c : ℚ)
    (ha : Matrix.vecMul a X = zeta0 + Matrix.vecMul zeta0 B)
    (hT1 : 1 ≤ T1) (hT2 : T1 ≤ T2) (hlam : 0 < lam) (hzeta : 0 < zeta0 (lastIdx k))
    (hd : (1 / 2 : ℚ) < 1 + dotProduct ellStar
      (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (earlyUnit k)))
    (hlarge : 2 * inverseConstant k lam zeta0 * rowAbs ellStar ≤ T1)
    (hE : entrySum (E - T1 • paperE0 k lam zeta0) ≤ KE) (hdc : |dc| ≤ Kd / T1)
    (hamin : 0 < amin) (halower : ∀ i, amin ≤ a i) (hag : Ak + 1 < a g) (hc : c < 1)
    (hcross : (k + 1 : ℚ) * lam * crossConstant k lam KE zeta0 ellStar L < T1)
    (hpmin : couplingConstant k lam KE Kd a X LX D0 zeta0 ellStar L B / T1 < amin / 4)
    (hpg : couplingConstant k lam KE Kd a X LX D0 zeta0 ellStar L B / T1 < (a g - Ak - 1) / 2) :
    (∀ i j, 0 < paperCross k T1 T2 lam zeta0 ellStar E L i j) ∧
    (∀ i j, paperCoupling k T1 T2 lam dc a X LX D0 zeta0 ellStar E L B i (Sum.inl j) < -(amin / 4) ∧
      amin / 4 < paperCoupling k T1 T2 lam dc a X LX D0 zeta0 ellStar E L B i (Sum.inr j)) ∧
    (∀ j, Ak < -paperCoupling k T1 T2 lam dc a X LX D0 zeta0 ellStar E L B g (Sum.inl j) - c) := by
  letI : Nonempty m := ⟨g⟩
  have ht1 : 0 < T1 := lt_of_lt_of_le (by norm_num) hT1
  have hC := (FaithfulAppendix.le_entrySum _).trans
    (cross_error_bound k T1 T2 lam KE zeta0 ellStar E L hT1 hT2 hd hlarge hE)
  have hpos := cross_positive_of_normStar_bound k T1 lam (crossConstant k lam KE zeta0 ellStar L)
    (paperCross k T1 T2 lam zeta0 ellStar E L) ht1 hlam hC hcross
  have hP : normStar (paperCoupling k T1 T2 lam dc a X LX D0 zeta0 ellStar E L B -
      referenceCoupling a) ≤ couplingConstant k lam KE Kd a X LX D0 zeta0 ellStar L B / T1 :=
    coupling_error_normStar_bound k T1 T2 lam KE Kd dc a X LX D0 zeta0 ellStar E L B
      ha hT1 hT2 hlam hzeta hd hlarge hE hdc
  have hmargins := coupling_margins_of_normStar_bound k a g amin Ak c
    (couplingConstant k lam KE Kd a X LX D0 zeta0 ellStar L B / T1)
    (paperCoupling k T1 T2 lam dc a X LX D0 zeta0 ellStar E L B)
    hamin halower hag hc hP hpmin hpg
  exact ⟨fun i j => (hpos i j).2, hmargins.1, hmargins.2⟩

/-- The first reset parameter can be selected before every value of the second
parameter and before the bounded moment/gain data are instantiated.  All
constants depend only on the fixed induction data.  In particular, no phase
or time index occurs among the inputs to this threshold. -/
theorem uniform_actual_reset_signs {m : Type*} [Fintype m]
    (k : ℕ) (lam KE Kd : ℚ) (a : m → ℚ)
    (X LX D0 : Matrix m (Fin (k + 1)) ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ)
    (L B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (g : m) (amin Ak : ℚ)
    (ha : Matrix.vecMul a X = zeta0 + Matrix.vecMul zeta0 B)
    (hlam : 0 < lam) (hzeta : 0 < zeta0 (lastIdx k))
    (hamin : 0 < amin) (halower : ∀ i, amin ≤ a i) (hag : Ak + 1 < a g) :
    ∃ N : ℕ, 0 < N ∧ ∀ T1 : ℚ, (N : ℚ) ≤ T1 → ∀ T2 : ℚ, T1 ≤ T2 →
      0 < T1 ∧ 0 < T2 ∧
      (∀ j, 0 < WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar j (lastIdx k) ∧
        0 < W_concrete k T1 T2 lam zeta0 j (lastIdx k)) ∧
      (1 / 2 : ℚ) < 1 + dotProduct ellStar
        (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (earlyUnit k)) ∧
      ∀ (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) (dc c : ℚ),
        entrySum (E - T1 • paperE0 k lam zeta0) ≤ KE → |dc| ≤ Kd / T1 → c < 1 →
        (∀ i j, 0 < paperCross k T1 T2 lam zeta0 ellStar E L i j) ∧
        (∀ i j, paperCoupling k T1 T2 lam dc a X LX D0 zeta0 ellStar E L B i (Sum.inl j) < -(amin / 4) ∧
          amin / 4 < paperCoupling k T1 T2 lam dc a X LX D0 zeta0 ellStar E L B i (Sum.inr j)) ∧
        (∀ j, Ak < -paperCoupling k T1 T2 lam dc a X LX D0 zeta0 ellStar E L B g (Sum.inl j) - c) := by
  obtain ⟨N0, hN0pos, hN0⟩ := uniform_reset_nondegenerate k lam zeta0 ellStar hlam hzeta
  obtain ⟨N1, hN1one, hN1⟩ := exists_uniform_sign_threshold k lam
    (crossConstant k lam KE zeta0 ellStar L)
    (couplingConstant k lam KE Kd a X LX D0 zeta0 ellStar L B) amin (a g) Ak hamin hag
  obtain ⟨N2, hN2⟩ := exists_nat_gt (2 * inverseConstant k lam zeta0 * rowAbs ellStar)
  refine ⟨max N0 (max N1 N2), lt_of_lt_of_le hN0pos (le_max_left _ _), ?_⟩
  intro T1 hT1 T2 hT2
  have hN0T : (N0 : ℚ) ≤ T1 := le_trans (by exact_mod_cast le_max_left N0 (max N1 N2)) hT1
  have hN1T : (N1 : ℚ) ≤ T1 :=
    le_trans (by exact_mod_cast (le_trans (le_max_left N1 N2) (le_max_right N0 (max N1 N2)))) hT1
  have hN2T : (N2 : ℚ) ≤ T1 :=
    le_trans (by exact_mod_cast (le_trans (le_max_right N1 N2) (le_max_right N0 (max N1 N2)))) hT1
  obtain ⟨ht1, ht2, hleading, hd⟩ := hN0 T1 hN0T T2 hT2
  obtain ⟨hcross, hpmin, hpg⟩ := hN1 T1 hN1T
  have hT1one : 1 ≤ T1 := le_of_lt (lt_of_lt_of_le hN1one hN1T)
  have hlarge : 2 * inverseConstant k lam zeta0 * rowAbs ellStar ≤ T1 :=
    le_trans (le_of_lt hN2) hN2T
  refine ⟨ht1, ht2, hleading, hd, ?_⟩
  intro E dc c hE hdc hc
  exact actual_reset_signs k T1 T2 lam KE Kd dc a X LX D0 zeta0 ellStar E L B g amin Ak c
    ha hT1one hT2 hlam hzeta hd hlarge hE hdc hamin halower hag hc hcross hpmin hpg

#print axioms uniform_actual_reset_signs
#print axioms actual_reset_signs
#print axioms cross_positive_of_error_bound
#print axioms coupling_margins_of_error_bound
#print axioms exists_uniform_sign_threshold
#print axioms deficit_error_bound
#print axioms coupling_error_bound
#print axioms internal_linear_bound
#print axioms score_error_bound
#print axioms resetScoreTarget_eq_blocks
#print axioms resetScoreTarget_error
#print axioms interpolation_correction_bound
#print axioms cross_mul_early
#print axioms cross_transpose_mul_late
#print axioms internal_quadratic_bound
#print axioms residual_bound
#print axioms cross_error_bound
#print axioms early_inverse_bound
#print axioms count_table_bounds
#print axioms entrySum_mul_le
#print axioms late_inverse_bound
end Karlin.Faithful
