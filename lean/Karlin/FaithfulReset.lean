import Karlin.PaperProof
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# v15 reset normalization and positive-cone parameter choice

Specification: `master_v15/master_v15.tex`, equations (J), (nextweights), (radius).
The results below use the manuscript's actual kappa, E0, and unscaled ellStar.
They do not establish the uniform-T1 sign estimates or produce the compatible
E/target; those are separate obligations. Every positivity premise is explicit.
-/

namespace Karlin.Faithful
open scoped BigOperators Matrix

/-- The first early reset row receives the unscaled paper correction ellStar. -/
def earlyUnit (k : ℕ) : Fin (k + 1) → ℚ :=
  fun i => if i.val = 0 then 1 else 0

/-- Equation (J), with r = k+1. -/
def paperKappa (k : ℕ) (T1 lam : ℚ) : ℚ :=
  2 / ((k + 1 : ℚ) * lam * T1)

/-- Equation (baseline), in the manuscript's normalization. -/
def paperE0 (k : ℕ) (lam : ℚ) (zeta0 : Fin (k + 1) → ℚ) :=
  (2 * (k + 1 : ℚ) * lam) • outerProd zeta0 zeta0

/-- Equation (J); ellStar is not rescaled. -/
def paperEbase (k : ℕ) (T1 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ) :=
  T1 • paperE0 k lam zeta0 + (2 : ℚ) • outerProd zeta0 ellStar

/-- The early table has row sum r T1 lambda zeta0 + ellStar exactly. -/
theorem early_row_sum (k : ℕ) (T1 T2 lam : ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ) :
    Matrix.vecMul (fun _ => 1)
      (WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar) =
      ((k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar := by
  unfold WE_concrete earlyUnit
  rw [Matrix.vecMul_add, vecMul_one_W_concrete, vecMul_one_outerProd_u]

/-- Exact leading cross-group contribution, using the literal v15 coefficients. -/
theorem exact_paper_base (k : ℕ) (T1 T2 lam : ℚ)
    (hT1 : T1 ≠ 0) (hlam : lam ≠ 0)
    (zeta0 ellStar : Fin (k + 1) → ℚ) :
    (W_concrete k T1 T2 lam zeta0)ᵀ *
      (paperKappa k T1 lam • outerProd (fun _ => 1) (fun _ => 1)) *
      (WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar) =
      paperEbase k T1 lam zeta0 ellStar := by
  rw [Matrix.mul_smul, mul_outerProd, Matrix.mulVec_transpose,
    Matrix.smul_mul, outerProd_mul, vecMul_one_W_concrete, early_row_sum]
  ext i j
  simp only [paperKappa, paperEbase, paperE0, Matrix.smul_apply, Matrix.add_apply,
    outerProd, Matrix.of_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have hr : (k + 1 : ℚ) ≠ 0 := by positivity
  field_simp

/-- Block expansion of the actual matrix product. -/
theorem reset_block_expansion {r w : Type*} [Fintype r] [Fintype w]
    (WE W : Matrix r w ℚ) (L C : Matrix r r ℚ) (eta : ℚ) :
    (Matrix.fromRows WE W)ᵀ *
      (Matrix.fromBlocks (eta • L) 0 C (eta • L)) *
      (Matrix.fromRows WE W) =
      eta • (WEᵀ * L * WE + Wᵀ * L * W) + Wᵀ * C * WE := by
  rw [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  simp only [Matrix.mul_zero, zero_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_add]
  abel

/-- Literal v15 equation M^T J M = E. Invertibility is proved from the concrete
inverse and the explicitly nonzero Sherman--Morrison denominator. -/
theorem exact_paper_moment (k : ℕ) (T1 T2 lam : ℚ)
    (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0) (hlam : lam ≠ 0)
    (zeta0 ellStar : Fin (k + 1) → ℚ) (hzeta : zeta0 (lastIdx k) ≠ 0)
    (hdenom : 1 + dotProduct ellStar
      (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (earlyUnit k)) ≠ 0)
    (E L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :
    let W := W_concrete k T1 T2 lam zeta0
    let WE := WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar
    let eta := 1 / (T1 * T2 ^ 2)
    let Fres := E - paperEbase k T1 lam zeta0 ellStar -
      eta • (WEᵀ * L * WE + Wᵀ * L * W)
    let C := paperKappa k T1 lam • outerProd (fun _ => 1) (fun _ => 1) +
      (Winv_concrete k T1 T2 lam zeta0)ᵀ * Fres *
      (WE_inv_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar)
    let M := Matrix.fromRows WE W
    let J := Matrix.fromBlocks (eta • L) 0 C (eta • L)
    Mᵀ * J * M = E := by
  intro W WE eta Fres C M J
  change (Matrix.fromRows WE W)ᵀ *
    (Matrix.fromBlocks (eta • L) 0 C (eta • L)) * Matrix.fromRows WE W = E
  rw [reset_block_expansion]
  exact M_transpose_mul_J_mul_M_concrete k T1 T2 lam hT1 hT2 hlam zeta0 hzeta
    (earlyUnit k) ellStar hdenom eta (paperKappa k T1 lam) L E
    (paperEbase k T1 lam zeta0 ellStar) Fres rfl C rfl
    (exact_paper_base k T1 T2 lam hT1 hlam zeta0 ellStar)

/-- The finite infinity norm appearing in equation (radius). -/
def rowMaxAbs (k : ℕ) (v : Fin (k + 1) → ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |v i|)

theorem abs_le_rowMaxAbs (k : ℕ) (v : Fin (k + 1) → ℚ) (j : Fin (k + 1)) :
    |v j| ≤ rowMaxAbs k v := by
  exact Finset.le_sup' (fun i => |v i|) (Finset.mem_univ j)

/-- The exact displayed bound in equation (radius). -/
def paperRadius (T1 upsilon alpha B : ℚ) : ℚ :=
  max (max T1 upsilon) (max 1 (2 * B / alpha))

/-- The least natural integer strictly above the paper bound; the bound is at
least one, so restricting the search to naturals loses no eligible integer. -/
def leastRadiusInteger (T1 upsilon alpha B : ℚ) : ℕ :=
  Nat.floor (paperRadius T1 upsilon alpha B) + 1

theorem leastRadiusInteger_spec (T1 upsilon alpha B : ℚ) :
    paperRadius T1 upsilon alpha B < (leastRadiusInteger T1 upsilon alpha B : ℚ) := by
  simpa only [leastRadiusInteger, Nat.cast_add, Nat.cast_one] using
    Nat.lt_floor_add_one (paperRadius T1 upsilon alpha B)

theorem leastRadiusInteger_minimal (T1 upsilon alpha B : ℚ) (N : ℕ)
    (hN : paperRadius T1 upsilon alpha B < (N : ℚ)) :
    leastRadiusInteger T1 upsilon alpha B ≤ N := by
  have hnonneg : 0 ≤ paperRadius T1 upsilon alpha B := by
    have h1 : (1 : ℚ) ≤ paperRadius T1 upsilon alpha B :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  exact Nat.succ_le_of_lt ((Nat.floor_lt hnonneg).mpr hN)

/-- A single integer parameter is chosen after all inputs in the radius are
fixed. The strict radius remains valid for every larger integer parameter. -/
theorem exists_integer_radius (T1 upsilon alpha B : ℚ) (halpha : 0 < alpha) :
    ∃ N : ℕ, T1 < (N : ℚ) ∧ upsilon < (N : ℚ) ∧ 1 < (N : ℚ) ∧
      ∀ T : ℕ, N ≤ T → 0 < (T : ℚ) ∧ 2 * B < alpha * (T : ℚ) := by
  let N := leastRadiusInteger T1 upsilon alpha B
  have hN := leastRadiusInteger_spec T1 upsilon alpha B
  change max (max T1 upsilon) (max 1 (2 * B / alpha)) < (N : ℚ) at hN
  have hT1 := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hu := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hone := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hrad := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  refine ⟨N, hT1, hu, hone, ?_⟩
  intro T hNT
  have hNTq : (N : ℚ) ≤ (T : ℚ) := by exact_mod_cast hNT
  refine ⟨lt_trans (by norm_num) (lt_of_lt_of_le hone hNTq), ?_⟩
  have := (div_lt_iff₀ halpha).mp (lt_of_lt_of_le hrad hNTq)
  simpa [mul_comm] using this

/-- The exact paper choice mu leaves three quarters of the leading target. -/
theorem residual_leading (k : ℕ) (target r0 : Fin (k + 1) → ℚ)
    (ht : 0 < target (lastIdx k)) (hr : 0 < r0 (lastIdx k)) :
    let mu := target (lastIdx k) / (4 * r0 (lastIdx k))
    0 < mu ∧ (target - mu • r0) (lastIdx k) = (3 / 4 : ℚ) * target (lastIdx k) ∧
      0 < (target - mu • r0) (lastIdx k) := by
  intro mu
  have hmu : 0 < mu := div_pos ht (by positivity)
  have heq : (target - mu • r0) (lastIdx k) = (3 / 4 : ℚ) * target (lastIdx k) := by
    dsimp [mu]
    field_simp
    ring
  refine ⟨hmu, heq, ?_⟩
  rw [heq]
  exact mul_pos (by norm_num) ht

/-- Combined old / early / late row table, in exactly the order of C_+. -/
def coneTable {o : Type*} (k : ℕ) (old : Matrix o (Fin (k + 1)) ℚ)
    (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ) :=
  Matrix.fromRows old
    (Matrix.fromRows (WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar)
      (W_concrete k T1 T2 lam zeta0))

/-- Constant row weights factor out of a matrix product. -/
theorem const_vecMul {ι κ : Type*} [Fintype ι] (mu : ℚ) (A : Matrix ι κ ℚ) :
    Matrix.vecMul (fun _ : ι => mu) A = mu • Matrix.vecMul (fun _ => 1) A := by
  ext j
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, one_mul]
  rw [Finset.mul_sum]

/-- A complete, quantified positive-cone construction. The target and r0 are
fixed before choosing T2. Positivity of their leading entries is explicit. -/
theorem positive_cone_exists {o : Type*} [Fintype o]
    (k : ℕ) (old : Matrix o (Fin (k + 1)) ℚ)
    (T1 lam : ℚ) (zeta0 ellStar target : Fin (k + 1) → ℚ)
    (hT1 : 0 < T1) (hlam : 0 < lam) (hzeta : 0 < zeta0 (lastIdx k))
    (htarget : 0 < target (lastIdx k))
    (hr0 : 0 < (Matrix.vecMul (fun _ => 1) old +
      ((k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar) (lastIdx k)) :
    let r0 := Matrix.vecMul (fun _ => 1) old +
      ((k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar
    let mu := target (lastIdx k) / (4 * r0 (lastIdx k))
    let rem := target - mu • r0
    let alpha := rem (lastIdx k) * (T1 * ((k + 1 : ℚ) * lam * zeta0 (lastIdx k)))⁻¹
    ∃ N : ℕ, T1 < (N : ℚ) ∧ T1 * lam * zeta0 (lastIdx k) < (N : ℚ) ∧
      1 < (N : ℚ) ∧ 0 < mu ∧ 0 < alpha ∧
      ∀ T : ℕ, N ≤ T →
      let aLate := Matrix.vecMul rem (Winv_concrete k T1 T lam zeta0)
      let weights := Sum.elim (fun _ : o => mu)
        (Sum.elim (fun _ : Fin (k + 1) => mu) aLate)
      (∀ j, alpha / 2 < aLate j) ∧
      (∀ i, 0 < weights i) ∧
      Matrix.vecMul weights (coneTable k old T1 T lam zeta0 ellStar) = target := by
  intro r0 mu rem alpha
  have hres := residual_leading k target r0 htarget hr0
  have hmu : 0 < mu := hres.1
  have hrem : 0 < rem (lastIdx k) := hres.2.2
  have halpha : 0 < alpha := mul_pos hrem (inv_pos.mpr (by positivity))
  let B := rowMaxAbs k (Matrix.vecMul rem (Phi1_concrete k zeta0))
  obtain ⟨N, hN1, hNu, hNone, hNrad⟩ := exists_integer_radius T1
    (T1 * lam * zeta0 (lastIdx k)) alpha B halpha
  refine ⟨N, hN1, hNu, hNone, hmu, halpha, ?_⟩
  intro T hNT aLate weights
  obtain ⟨hTpos, hTrad⟩ := hNrad T hNT
  have hlate := prop_8_1_late_weights_concrete rem T1 T lam zeta0
    (ne_of_gt hT1) (ne_of_gt hlam) (ne_of_gt hzeta) B halpha
    (abs_le_rowMaxAbs k (Matrix.vecMul rem (Phi1_concrete k zeta0)))
    hTpos hTrad target r0 mu rfl
  refine ⟨fun j => (hlate.1 j).1, ?_, ?_⟩
  · intro i
    rcases i with i | (i | i)
    · exact hmu
    · exact hmu
    · exact (hlate.1 i).2
  · change Matrix.vecMul (Sum.elim (fun _ : o => mu)
        (Sum.elim (fun _ : Fin (k + 1) => mu) aLate))
      (Matrix.fromRows old (Matrix.fromRows _ _)) = target
    rw [Matrix.sumElim_vecMul_fromRows, Matrix.sumElim_vecMul_fromRows]
    rw [const_vecMul mu old, const_vecMul mu _, early_row_sum]
    have hsum : mu • Matrix.vecMul (fun _ => 1) old +
        (mu • (((k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar) +
          Matrix.vecMul aLate (W_concrete k T1 T lam zeta0)) =
        mu • r0 + Matrix.vecMul aLate (W_concrete k T1 T lam zeta0) := by
      dsimp [r0]
      simp only [smul_add]
      abel
    rw [hsum]
    exact hlate.2

/-- The late reset count's leading coefficient is exactly upsilon_k. -/
theorem late_leading (k : ℕ) (T1 T2 lam : ℚ) (zeta0 : Fin (k + 1) → ℚ)
    (j : Fin (k + 1)) :
    W_concrete k T1 T2 lam zeta0 j (lastIdx k) = T1 * lam * zeta0 (lastIdx k) := by
  have hv : V0_paper k j (lastIdx k) = 0 := V0_last_col_zero k j
  simp [W_concrete, W_paper, outerProd, hv]

/-- The literal early correction changes only the first leading coefficient. -/
theorem early_leading (k : ℕ) (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ)
    (j : Fin (k + 1)) :
    WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar j (lastIdx k) =
      T1 * lam * zeta0 (lastIdx k) +
        (if j.val = 0 then ellStar (lastIdx k) else 0) := by
  simp only [WE_concrete, Matrix.add_apply, late_leading, outerProd, Matrix.of_apply]
  unfold earlyUnit
  split_ifs <;> simp

/-- Leading reset coefficients are positive under exactly the two scalar
conditions used after the uniform-T1 estimates. This holds for every T2. -/
theorem reset_leading_positive (k : ℕ) (T1 lam : ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (hu : 0 < T1 * lam * zeta0 (lastIdx k))
    (he : 0 < T1 * lam * zeta0 (lastIdx k) + ellStar (lastIdx k)) :
    ∀ T2 : ℚ, ∀ j : Fin (k + 1),
      0 < WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar j (lastIdx k) ∧
      0 < W_concrete k T1 T2 lam zeta0 j (lastIdx k) := by
  intro T2 j
  rw [early_leading, late_leading]
  constructor
  · split_ifs
    · exact he
    · simpa using hu
  · exact hu

/-- Positive r0_k follows from the old nonnegative leading counts and the
positive first early leading count. It is not a new induction premise. -/
theorem r0_leading_positive {o : Type*} [Fintype o] (k : ℕ)
    (old : Matrix o (Fin (k + 1)) ℚ) (T1 lam : ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (hold : ∀ i, 0 ≤ old i (lastIdx k))
    (hu : 0 < T1 * lam * zeta0 (lastIdx k))
    (he : 0 < T1 * lam * zeta0 (lastIdx k) + ellStar (lastIdx k)) :
    0 < (Matrix.vecMul (fun _ => 1) old +
      ((k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar) (lastIdx k) := by
  have hs : 0 ≤ Matrix.vecMul (fun _ => 1) old (lastIdx k) := by
    simp only [Matrix.vecMul, dotProduct, one_mul]
    exact Finset.sum_nonneg (fun i _ => hold i)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hku : 0 ≤ (k : ℚ) * (T1 * lam * zeta0 (lastIdx k)) :=
    mul_nonneg (by positivity) hu.le
  nlinarith

/-- The Sherman--Morrison correction has two fixed coefficients. -/
theorem denominator_two_scale (k : ℕ) (T1 T2 lam : ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ) :
    dotProduct ellStar (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (earlyUnit k)) =
      T1⁻¹ * dotProduct ellStar (Matrix.mulVec (Phi0_concrete k lam zeta0) (earlyUnit k)) +
      T2⁻¹ * dotProduct ellStar (Matrix.mulVec (Phi1_concrete k zeta0) (earlyUnit k)) := by
  simp only [Winv_concrete, W_inv_paper, Matrix.add_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul]

set_option maxHeartbeats 800000 in
/-- A scalar two-scale bound, uniform for every T2 >= T1. -/
theorem two_scale_abs_lt_half (a b T1 T2 : ℚ) (hT1 : 0 < T1) (hT2 : T1 ≤ T2)
    (hlarge : 2 * (|a| + |b|) < T1) :
    |T1⁻¹ * a + T2⁻¹ * b| < (1 / 2 : ℚ) := by
  have hT2pos : 0 < T2 := lt_of_lt_of_le hT1 hT2
  have hi1 : 0 < T1⁻¹ := inv_pos.mpr hT1
  have hi2 : 0 < T2⁻¹ := inv_pos.mpr hT2pos
  have hi21 : T2⁻¹ ≤ T1⁻¹ := (inv_le_inv₀ hT2pos hT1).mpr hT2
  have hbound : |T1⁻¹ * a + T2⁻¹ * b| ≤ T1⁻¹ * (|a| + |b|) := by
    calc
      _ ≤ |T1⁻¹ * a| + |T2⁻¹ * b| := abs_add_le _ _
      _ = T1⁻¹ * |a| + T2⁻¹ * |b| := by
        rw [abs_mul, abs_mul, abs_of_pos hi1, abs_of_pos hi2]
      _ ≤ T1⁻¹ * |a| + T1⁻¹ * |b| :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hi21 (abs_nonneg b))
      _ = T1⁻¹ * (|a| + |b|) := by ring
  have hsmall : (|a| + |b|) / T1 < (1 / 2 : ℚ) :=
    (div_lt_iff₀ hT1).mpr (by linarith)
  exact lt_of_le_of_lt hbound (by simpa only [div_eq_mul_inv, mul_comm] using hsmall)

/-- One fixed integer T0 secures the inverse denominator for all T1 >= T0 and
all T2 >= T1. No parameter is chosen after a phase or time index. -/
theorem uniform_denominator (k : ℕ) (lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ T1 : ℚ, (N : ℚ) ≤ T1 → ∀ T2 : ℚ, T1 ≤ T2 →
      (1 / 2 : ℚ) < 1 + dotProduct ellStar
        (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (earlyUnit k)) := by
  let a := dotProduct ellStar (Matrix.mulVec (Phi0_concrete k lam zeta0) (earlyUnit k))
  let b := dotProduct ellStar (Matrix.mulVec (Phi1_concrete k zeta0) (earlyUnit k))
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (2 * (|a| + |b|)))
  have hone : (1 : ℚ) < (N : ℚ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hNpos : 0 < N := by exact_mod_cast (lt_trans (by norm_num : (0 : ℚ) < 1) hone)
  refine ⟨N, hNpos, ?_⟩
  intro T1 hT1 T2 hT2
  have hT1pos : 0 < T1 := lt_of_lt_of_le (by exact_mod_cast hNpos) hT1
  have hlarge : 2 * (|a| + |b|) < T1 :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) hT1
  have hsmall := two_scale_abs_lt_half a b T1 T2 hT1pos hT2 hlarge
  rw [denominator_two_scale]
  have hlo := (abs_lt.mp hsmall).1
  change -(1 / 2 : ℚ) < T1⁻¹ * a + T2⁻¹ * b at hlo
  change (1 / 2 : ℚ) < 1 + (T1⁻¹ * a + T2⁻¹ * b)
  linarith

/-- A single first-parameter threshold supplies positive reset leading
coefficients and a positive inverse denominator uniformly in the second
parameter. The correction row is fixed before either parameter is selected. -/
theorem uniform_reset_nondegenerate (k : ℕ) (lam : ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (hlam : 0 < lam) (hzeta : 0 < zeta0 (lastIdx k)) :
    ∃ N : ℕ, 0 < N ∧ ∀ T1 : ℚ, (N : ℚ) ≤ T1 → ∀ T2 : ℚ, T1 ≤ T2 →
      0 < T1 ∧ 0 < T2 ∧
      (∀ j, 0 < WE_concrete k T1 T2 lam zeta0 (earlyUnit k) ellStar j (lastIdx k) ∧
        0 < W_concrete k T1 T2 lam zeta0 j (lastIdx k)) ∧
      (1 / 2 : ℚ) < 1 + dotProduct ellStar
        (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (earlyUnit k)) := by
  obtain ⟨N1, hN1pos, hN1⟩ := uniform_denominator k lam zeta0 ellStar
  obtain ⟨N2, hN2⟩ := exists_nat_gt
    (max 1 (-ellStar (lastIdx k) / (lam * zeta0 (lastIdx k))))
  refine ⟨max N1 N2, lt_of_lt_of_le hN1pos (le_max_left _ _), ?_⟩
  intro T1 hT1 T2 hT2
  have hN1T : (N1 : ℚ) ≤ T1 := le_trans (by exact_mod_cast le_max_left N1 N2) hT1
  have hN2T : (N2 : ℚ) ≤ T1 := le_trans (by exact_mod_cast le_max_right N1 N2) hT1
  have hT1pos : 0 < T1 := lt_of_lt_of_le (by exact_mod_cast hN1pos) hN1T
  have hu : 0 < T1 * lam * zeta0 (lastIdx k) := by positivity
  have he : 0 < T1 * lam * zeta0 (lastIdx k) + ellStar (lastIdx k) := by
    have hd := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN2) hN2T
    have hp := (div_lt_iff₀ (mul_pos hlam hzeta)).mp hd
    nlinarith
  exact ⟨hT1pos, lt_of_lt_of_le hT1pos hT2,
    reset_leading_positive k T1 lam zeta0 ellStar hu he T2,
    hN1 T1 hN1T T2 hT2⟩

#print axioms uniform_reset_nondegenerate
#print axioms leastRadiusInteger_minimal
#print axioms reset_leading_positive
#print axioms r0_leading_positive
#print axioms uniform_denominator
#print axioms exact_paper_base
#print axioms exact_paper_moment
#print axioms exists_integer_radius
#print axioms residual_leading
#print axioms positive_cone_exists
end Karlin.Faithful
