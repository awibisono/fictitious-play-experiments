import Karlin.FaithfulAppendixNorm

/-! Literal candidate-dependent bounds from v15 Appendix A. Every displayed
bound is independent of the later T2, and uses the paper's exact normStar. -/
namespace Karlin.FaithfulAppendix
open scoped BigOperators Matrix
open Faithful
set_option maxHeartbeats 1600000

def bW (k : ℕ) (T1 lam : ℚ) (z : Fin (k+1) → ℚ) : ℚ :=
  (normStar (Phi0_concrete k lam z) + normStar (Phi1_concrete k z)) / T1
def nu (k : ℕ) (T1 lam : ℚ) (z ell : Fin (k+1) → ℚ) : ℚ :=
  bW k T1 lam z * rowAbs ell
def bE (k : ℕ) (T1 lam : ℚ) (z ell : Fin (k+1) → ℚ) : ℚ :=
  bW k T1 lam z / (1 - nu k T1 lam z ell)
def bC (k : ℕ) (T1 lam : ℚ) (z ell : Fin (k+1) → ℚ) : ℚ :=
  normStar (outerProd (fun _ : Fin (k+1) => 1) (lam • z)) +
    normStar (V0_paper k) + rowAbs ell / T1
def bR (k : ℕ) (T1 lam : ℚ) (z ell : Fin (k+1) → ℚ)
    (E L : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) : ℚ :=
  normStar (E - paperEbase k T1 lam z ell) + 2 * normStar L * bC k T1 lam z ell ^ 2 / T1
def bCross (k : ℕ) (T1 lam : ℚ) (z ell : Fin (k+1) → ℚ)
    (E L : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) : ℚ :=
  bW k T1 lam z * bR k T1 lam z ell E L * bE k T1 lam z ell
def bQ (k : ℕ) (T1 lam : ℚ) (z ell psi : Fin (k+1) → ℚ)
    (E L B : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) : ℚ :=
  2 * (k+1 : ℚ) * rowAbs (psi - (Matrix.vecMul z B - z)) +
    paperKappa k T1 lam * (k+1 : ℚ) * rowAbs ell +
    4 * normStar L * bC k T1 lam z ell * (1 + normStar B) / T1 ^ 2 +
    bR k T1 lam z ell E L * (bE k T1 lam z ell * normStar B + bW k T1 lam z)
def bP {m : Type*} [Fintype m] [Nonempty m] (k : ℕ) (T1 lam : ℚ)
    (z ell psi : Fin (k+1) → ℚ) (E L B : Matrix (Fin (k+1)) (Fin (k+1)) ℚ)
    (a : m → ℚ) (X LX D : Matrix m (Fin (k+1)) ℚ) : ℚ :=
  normStar (D + outerProd a ell) * bW k T1 lam z + normStar LX *
    (bQ k T1 lam z ell psi E L B + normStar X * normStar (D + outerProd a ell) * bW k T1 lam z)

theorem inverse_bound (k : ℕ) (T1 T2 lam : ℚ) (z : Fin (k+1) → ℚ)
    (ht1 : 0 < T1) (ht2 : T1 ≤ T2) :
    normStar (Winv_concrete k T1 T2 lam z) ≤ bW k T1 lam z := by
  have ht2p : 0 < T2 := ht1.trans_le ht2
  have hi : T2⁻¹ ≤ T1⁻¹ := (inv_le_inv₀ ht2p ht1).mpr ht2
  have h0 := smul_le T1⁻¹ (Phi0_concrete k lam z)
  have h1 := smul_le T2⁻¹ (Phi1_concrete k z)
  rw [abs_of_pos (inv_pos.mpr ht1)] at h0
  rw [abs_of_pos (inv_pos.mpr ht2p)] at h1
  have hsum := (add_le (T1⁻¹ • Phi0_concrete k lam z) (T2⁻¹ • Phi1_concrete k z)).trans
    (add_le_add h0 h1)
  have hh := mul_le_mul_of_nonneg_right hi (nonneg (Phi1_concrete k z))
  unfold bW
  change normStar (T1⁻¹ • Phi0_concrete k lam z + T2⁻¹ • Phi1_concrete k z) ≤ _
  linarith [show (normStar (Phi0_concrete k lam z) + normStar (Phi1_concrete k z)) / T1 =
    T1⁻¹ * normStar (Phi0_concrete k lam z) + T1⁻¹ * normStar (Phi1_concrete k z) by ring]

theorem inverse_denominator (k : ℕ) (T1 T2 lam : ℚ) (z ell : Fin (k+1) → ℚ)
    (ht1 : 0 < T1) (ht2 : T1 ≤ T2) :
    1 - nu k T1 lam z ell ≤
      1 + dotProduct ell ((Winv_concrete k T1 T2 lam z).mulVec (earlyUnit k)) := by
  have h := (dot_inverse_le k (Winv_concrete k T1 T2 lam z) ell).trans
    (mul_le_mul_of_nonneg_right (inverse_bound k T1 T2 lam z ht1 ht2) (rowAbs_nonneg ell))
  have hh := (abs_le.mp h).1
  change -(nu k T1 lam z ell) ≤ _ at hh
  linarith

theorem sherman_bound (k : ℕ) (WI : Matrix (Fin (k+1)) (Fin (k+1)) ℚ)
    (ell : Fin (k+1) → ℚ) (b : ℚ) (hw : normStar WI ≤ b)
    (hn : b * rowAbs ell < 1) :
    normStar (WI - (1 + dotProduct ell (WI.mulVec (earlyUnit k)))⁻¹ •
      (WI * (outerProd (earlyUnit k) ell * WI))) ≤ b / (1 - b * rowAbs ell) := by
  let d := 1 + dotProduct ell (WI.mulVec (earlyUnit k))
  have hb : 0 ≤ b := (nonneg WI).trans hw
  have hden : 0 < 1 - b * rowAbs ell := by linarith
  have hd : 1 - b * rowAbs ell ≤ d := by
    have h := (abs_le.mp ((dot_inverse_le k WI ell).trans
      (mul_le_mul_of_nonneg_right hw (rowAbs_nonneg ell)))).1
    dsimp only [d]
    linarith
  have hdp : 0 < d := hden.trans_le hd
  have hi : d⁻¹ ≤ (1 - b * rowAbs ell)⁻¹ := (inv_le_inv₀ hdp hden).mpr hd
  have hprod : normStar (WI * (outerProd (earlyUnit k) ell * WI)) ≤ b * (rowAbs ell * b) :=
    mul_bound _ _ _ _ hw (mul_bound _ _ _ _ (outer_early_le k ell) hw)
  have hs := smul_le d⁻¹ (WI * (outerProd (earlyUnit k) ell * WI))
  rw [abs_of_pos (inv_pos.mpr hdp)] at hs
  have hs' : normStar (d⁻¹ • (WI * (outerProd (earlyUnit k) ell * WI))) ≤
      (1 - b * rowAbs ell)⁻¹ * (b * (rowAbs ell * b)) :=
    hs.trans (mul_le_mul hi hprod (nonneg _) (inv_nonneg.mpr hden.le))
  have h := (sub_le WI (d⁻¹ • (WI * (outerProd (earlyUnit k) ell * WI)))).trans
    (add_le_add hw hs')
  calc
    _ ≤ b + (1 - b * rowAbs ell)⁻¹ * (b * (rowAbs ell * b)) := h
    _ = _ := by field_simp; ring

theorem early_inverse_bound (k : ℕ) (T1 T2 lam : ℚ) (z ell : Fin (k+1) → ℚ)
    (ht1 : 0 < T1) (ht2 : T1 ≤ T2) (hnu : nu k T1 lam z ell < 1/2) :
    normStar (WE_inv_concrete k T1 T2 lam z (earlyUnit k) ell) ≤ bE k T1 lam z ell := by
  exact sherman_bound k (Winv_concrete k T1 T2 lam z) ell (bW k T1 lam z)
    (inverse_bound k T1 T2 lam z ht1 ht2) (by change nu k T1 lam z ell < 1; linarith)

theorem count_bounds (k : ℕ) (T1 T2 lam : ℚ) (z ell : Fin (k+1) → ℚ)
    (ht1 : 0 < T1) (ht2 : T1 ≤ T2) :
    normStar (W_concrete k T1 T2 lam z) ≤ T2 * bC k T1 lam z ell ∧
    normStar (WE_concrete k T1 T2 lam z (earlyUnit k) ell) ≤ T2 * bC k T1 lam z ell := by
  let Z := outerProd (fun _ : Fin (k+1) => (1 : ℚ)) (lam • z)
  let V := V0_paper k
  have ht2p : 0 < T2 := ht1.trans_le ht2
  have he : W_concrete k T1 T2 lam z = T1 • Z + T2 • V := by
    ext i j
    simp only [W_concrete, W_paper, Z, V, outerProd, Matrix.of_apply,
      Matrix.add_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hz := smul_le T1 Z
  have hv := smul_le T2 V
  rw [abs_of_pos ht1] at hz
  rw [abs_of_pos ht2p] at hv
  have hw : normStar (W_concrete k T1 T2 lam z) ≤ T2 * (normStar Z + normStar V) := by
    rw [he]
    have hh := (add_le (T1 • Z) (T2 • V)).trans (add_le_add hz hv)
    have hm := mul_le_mul_of_nonneg_right ht2 (nonneg Z)
    nlinarith
  have hell : rowAbs ell ≤ T2 * (rowAbs ell / T1) := by
    have h := mul_le_mul_of_nonneg_right ht2 (rowAbs_nonneg ell)
    have hh : rowAbs ell ≤ T2 * rowAbs ell / T1 := (le_div_iff₀ ht1).mpr (by nlinarith)
    convert hh using 1 <;> ring
  have hwe := (add_le (W_concrete k T1 T2 lam z) (outerProd (earlyUnit k) ell)).trans
    (add_le_add hw (outer_early_le k ell))
  have heln : 0 ≤ T2 * (rowAbs ell / T1) := mul_nonneg ht2p.le (div_nonneg (rowAbs_nonneg _) ht1.le)
  change normStar (W_concrete k T1 T2 lam z) ≤ T2 * (normStar Z + normStar V + rowAbs ell / T1) ∧ _
  constructor
  · nlinarith
  · change normStar (W_concrete k T1 T2 lam z + outerProd (earlyUnit k) ell) ≤
      T2 * (normStar Z + normStar V + rowAbs ell / T1)
    nlinarith

theorem quadratic_bound {r : Type*} [Fintype r] [Nonempty r]
    (W WE L : Matrix r r ℚ) (T1 T2 C : ℚ) (ht1 : 0 < T1) (ht2 : 0 < T2)
    (hw : normStar W ≤ T2*C) (hwe : normStar WE ≤ T2*C) :
    normStar ((1/(T1*T2^2)) • (WEᵀ*L*WE + Wᵀ*L*W)) ≤ 2*normStar L*C^2/T1 := by
  have h1 := mul_bound (WEᵀ*L) WE _ _
    (mul_bound WEᵀ L _ _ (by simpa only [transpose] using hwe) le_rfl) hwe
  have h2 := mul_bound (Wᵀ*L) W _ _
    (mul_bound Wᵀ L _ _ (by simpa only [transpose] using hw) le_rfl) hw
  have hh := (add_le (WEᵀ*L*WE) (Wᵀ*L*W)).trans (add_le_add h1 h2)
  have heta : 0 < 1/(T1*T2^2) := by positivity
  have hs := smul_le (1/(T1*T2^2)) (WEᵀ*L*WE + Wᵀ*L*W)
  rw [abs_of_pos heta] at hs
  refine hs.trans ((mul_le_mul_of_nonneg_left hh heta.le).trans_eq ?_)
  field_simp
  <;> ring

theorem residual_bound (k : ℕ) (T1 T2 lam : ℚ) (z ell : Fin (k+1) → ℚ)
    (E L : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (ht1 : 0 < T1) (ht2 : T1 ≤ T2) :
    normStar (paperResidual k T1 T2 lam z ell E L) ≤ bR k T1 lam z ell E L := by
  obtain ⟨hw,hwe⟩ := count_bounds k T1 T2 lam z ell ht1 ht2
  exact (sub_le _ _).trans (add_le_add le_rfl
    (quadratic_bound _ _ L T1 T2 (bC k T1 lam z ell) ht1 (ht1.trans_le ht2) hw hwe))

theorem cross_bound (k : ℕ) (T1 T2 lam : ℚ) (z ell : Fin (k+1) → ℚ)
    (E L : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (ht1 : 0 < T1) (ht2 : T1 ≤ T2)
    (hnu : nu k T1 lam z ell < 1/2) :
    normStar (paperCross k T1 T2 lam z ell E L -
      paperKappa k T1 lam • outerProd (fun _ => 1) (fun _ => 1)) ≤
      bCross k T1 lam z ell E L := by
  unfold paperCross
  rw [add_sub_cancel_left]
  exact mul_bound _ _ _ _
    (mul_bound _ _ _ _ (by rw [transpose]; exact inverse_bound k T1 T2 lam z ht1 ht2)
      (residual_bound k T1 T2 lam z ell E L ht1 ht2))
    (early_inverse_bound k T1 T2 lam z ell ht1 ht2 hnu)

theorem linear_internal_bound {r w : Type*} [Fintype r] [Fintype w]
    [Nonempty r] [Nonempty w] (Z : Matrix r w ℚ) (L : Matrix r r ℚ)
    (B : Matrix w w ℚ) (T1 T2 C : ℚ) (ht1 : 0 < T1) (ht2 : T1 ≤ T2)
    (hz : normStar Z ≤ T2*C) :
    normStar ((1/(T1*T2^2)) • (L*Z) - (1/(T1*T2^2)) • (Lᵀ*Z*B)) ≤
      normStar L * C * (1 + normStar B) / T1^2 := by
  have ht2p : 0 < T2 := ht1.trans_le ht2
  have hC : 0 ≤ C := by nlinarith [nonneg Z]
  have hn : 0 ≤ normStar L * C * (1 + normStar B) :=
    mul_nonneg (mul_nonneg (nonneg L) hC) (by linarith [nonneg B])
  have hlz := mul_bound L Z _ _ le_rfl hz
  have hltz := mul_bound Lᵀ Z _ _ (transpose L).le hz
  have hlb := mul_bound (Lᵀ*Z) B _ _ hltz le_rfl
  have heta : 0 < 1/(T1*T2^2) := by positivity
  have h1 := smul_le (1/(T1*T2^2)) (L*Z)
  have h2 := smul_le (1/(T1*T2^2)) (Lᵀ*Z*B)
  rw [abs_of_pos heta] at h1 h2
  have hs := (sub_le _ _).trans (add_le_add h1 h2)
  have hm := mul_le_mul_of_nonneg_left (add_le_add hlz hlb) heta.le
  have he : (1/(T1*T2^2)) *
      (normStar L * (T2*C) + (normStar L * (T2*C)) * normStar B) =
      (normStar L*C*(1+normStar B))/(T1*T2) := by field_simp <;> ring
  rw [he] at hm
  have hd : normStar L*C*(1+normStar B)/(T1*T2) ≤
      normStar L*C*(1+normStar B)/T1^2 :=
    div_le_div_of_nonneg_left hn (sq_pos_of_pos ht1) (by nlinarith)
  linarith

/-- Literal bQ after the count-table cancellations. The displayed factor four
in the internal term is conservative: the proof first obtains factor two. -/
theorem score_bound (k : ℕ) (T1 T2 lam : ℚ) (z ell psi : Fin (k+1) → ℚ)
    (E L B : Matrix (Fin (k+1)) (Fin (k+1)) ℚ)
    (ht1 : 0 < T1) (ht2 : T1 ≤ T2) (hlam : 0 < lam) (hz : 0 < z (lastIdx k))
    (hnu : nu k T1 lam z ell < 1/2) :
    let Z := outerProd (fun _ : Fin (k+1) => (1 : ℚ)) z
    normStar (resetScoreTarget psi
      (WE_concrete k T1 T2 lam z (earlyUnit k) ell) (W_concrete k T1 T2 lam z)
      L (paperCross k T1 T2 lam z ell E L) (1/(T1*T2^2)) B -
      Matrix.fromRows (-(Z+Z*B)) (Z+Z*B)) ≤ bQ k T1 lam z ell psi E L B := by
  intro Z
  let W := W_concrete k T1 T2 lam z
  let WE := WE_concrete k T1 T2 lam z (earlyUnit k) ell
  let WI := Winv_concrete k T1 T2 lam z
  let WEI := WE_inv_concrete k T1 T2 lam z (earlyUnit k) ell
  let F := paperResidual k T1 T2 lam z ell E L
  let H := outerProd (fun _ : Fin (k+1) => (1 : ℚ)) (psi - (Matrix.vecMul z B - z))
  let EL := paperKappa k T1 lam • outerProd (fun _ : Fin (k+1) => (1 : ℚ)) ell + WIᵀ*F
  let EE := WEIᵀ*Fᵀ*B
  let eta := 1/(T1*T2^2)
  let C := bC k T1 lam z ell
  let KI := normStar L*C*(1+normStar B)
  have ht2p : 0 < T2 := ht1.trans_le ht2
  have hdpos : 0 < 1 + dotProduct ell (WI.mulVec (earlyUnit k)) := by
    have hd := inverse_denominator k T1 T2 lam z ell ht1 ht2
    dsimp only [WI]
    linarith
  have hpsi : outerProd (fun _ : Fin (k+1) => (1 : ℚ)) psi = Z*B-Z+H := by
    rw [show Z*B = outerProd (fun _ : Fin (k+1) => (1 : ℚ)) (Matrix.vecMul z B) from outerProd_mul _ _ _]
    ext i j
    simp only [Z, H, outerProd, Matrix.of_apply, Pi.sub_apply, Matrix.sub_apply, Matrix.add_apply, one_mul]
    ring
  have hce : paperCross k T1 T2 lam z ell E L * WE = (2 : ℚ) • Z + EL := by
    rw [cross_mul_early k T1 T2 lam z ell E L ht1.ne' ht2p.ne' hlam.ne' hz.ne' hdpos.ne']
    exact add_assoc _ _ _
  have hcl : (paperCross k T1 T2 lam z ell E L)ᵀ * W * B = (2 : ℚ) • (Z*B) + EE :=
    cross_transpose_mul_late k T1 T2 lam z ell E L B ht1.ne' ht2p.ne' hlam.ne' hz.ne'
  rw [resetScoreTarget_error psi z WE W L _ eta B H EL EE hpsi hce hcl]
  have hw : normStar WI ≤ bW k T1 lam z := inverse_bound k T1 T2 lam z ht1 ht2
  have hwe : normStar WEI ≤ bE k T1 lam z ell := early_inverse_bound k T1 T2 lam z ell ht1 ht2 hnu
  have hf : normStar F ≤ bR k T1 lam z ell E L := residual_bound k T1 T2 lam z ell E L ht1 ht2
  have hwf := mul_bound WIᵀ F _ _ (by simpa only [transpose] using hw) hf
  have hwef := mul_bound WEIᵀ Fᵀ _ _ (by simpa only [transpose] using hwe)
    (by simpa only [transpose] using hf)
  have hee : normStar EE ≤ bE k T1 lam z ell * bR k T1 lam z ell E L * normStar B :=
    mul_bound _ _ _ _ hwef le_rfl
  have hk : 0 < paperKappa k T1 lam := by unfold paperKappa; positivity
  have hkell : normStar (paperKappa k T1 lam • outerProd (fun _ : Fin (k+1) => (1 : ℚ)) ell) ≤
      paperKappa k T1 lam * (k+1 : ℚ) * rowAbs ell := by
    have h := smul_le (paperKappa k T1 lam) (outerProd (fun _ : Fin (k+1) => (1 : ℚ)) ell)
    rw [abs_of_pos hk] at h
    have ho := outer_ones_le (m := Fin (k+1)) ell
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at ho
    exact h.trans ((mul_le_mul_of_nonneg_left ho hk.le).trans_eq (by ring))
  have hel : normStar EL ≤ paperKappa k T1 lam * (k+1 : ℚ) * rowAbs ell +
      bW k T1 lam z * bR k T1 lam z ell E L :=
    (add_le _ _).trans (add_le_add hkell hwf)
  obtain ⟨hW,hWE⟩ := count_bounds k T1 T2 lam z ell ht1 ht2
  have hiw : normStar (eta • (L*W) - eta • (Lᵀ*W*B)) ≤ KI/T1^2 :=
    linear_internal_bound W L B T1 T2 C ht1 ht2 hW
  have hiwe : normStar (eta • (L*WE) - eta • (Lᵀ*WE*B)) ≤ KI/T1^2 :=
    linear_internal_bound WE L B T1 T2 C ht1 ht2 hWE
  have hh : normStar H ≤ (k+1 : ℚ) * rowAbs (psi - (Matrix.vecMul z B - z)) := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
      outer_ones_le (m := Fin (k+1)) (psi - (Matrix.vecMul z B - z))
  have hearly : normStar (H + eta • (L*WE) - eta • (Lᵀ*WE*B) - EE) ≤
      (k+1 : ℚ) * rowAbs (psi - (Matrix.vecMul z B - z)) + KI/T1^2 +
        bE k T1 lam z ell * bR k T1 lam z ell E L * normStar B := by
    have he : H + eta • (L*WE) - eta • (Lᵀ*WE*B) - EE =
        (H + (eta • (L*WE) - eta • (Lᵀ*WE*B))) - EE := by abel
    rw [he]
    exact (sub_le _ _).trans (add_le_add ((add_le _ _).trans (add_le_add hh hiwe)) hee)
  have hlate : normStar (H + EL + eta • (L*W) - eta • (Lᵀ*W*B)) ≤
      (k+1 : ℚ) * rowAbs (psi - (Matrix.vecMul z B - z)) +
        (paperKappa k T1 lam * (k+1 : ℚ) * rowAbs ell + bW k T1 lam z * bR k T1 lam z ell E L) +
        KI/T1^2 := by
    have he : H + EL + eta • (L*W) - eta • (Lᵀ*W*B) =
        (H+EL) + (eta • (L*W) - eta • (Lᵀ*W*B)) := by abel
    rw [he]
    exact (add_le _ _).trans (add_le_add ((add_le _ _).trans (add_le_add hh hel)) hiw)
  have hC : 0 ≤ C := by
    dsimp [C, bC]
    exact add_nonneg (add_nonneg (nonneg _) (nonneg _)) (div_nonneg (rowAbs_nonneg ell) ht1.le)
  have hKI : 0 ≤ KI := mul_nonneg (mul_nonneg (nonneg L) hC) (by linarith [nonneg B])
  refine (fromRows_le _ _).trans ((add_le_add hearly hlate).trans ?_)
  calc
    _ = bQ k T1 lam z ell psi E L B - 2*KI/T1^2 := by
      unfold bQ
      dsimp only [KI, C]
      ring
    _ ≤ _ := sub_le_self _ (div_nonneg (mul_nonneg (by norm_num) hKI) (sq_nonneg T1))

theorem interpolation_bound {m n w : Type*} [Fintype m] [Fintype n] [Fintype w]
    [Nonempty m] [Nonempty n] [Nonempty w]
    (X LX : Matrix m w ℚ) (M : Matrix n w ℚ) (RM : Matrix w n ℚ)
    (D : Matrix m w ℚ) (Q : Matrix n w ℚ) (P0 : Matrix m n ℚ) :
    normStar (P_interp X LX M RM D Q P0 - P0) ≤
      normStar (D-P0*M)*normStar RM + normStar LX *
        (normStar (Q-P0ᵀ*X) + normStar X*normStar (D-P0*M)*normStar RM) := by
  let DR := D-P0*M
  let QR := Q-P0ᵀ*X
  have he : P_interp X LX M RM D Q P0 - P0 = DR*RM + LX*(QRᵀ-Xᵀ*DR*RM) := by
    change (P0 + DR*RM + LX*(QRᵀ-Xᵀ*DR*RM)) - P0 = _
    abel
  rw [he]
  have hx : normStar (Xᵀ*DR*RM) ≤ normStar X*normStar DR*normStar RM :=
    mul_bound _ _ _ _ (by simpa only [transpose] using mul_le Xᵀ DR) le_rfl
  have hinner : normStar (QRᵀ-Xᵀ*DR*RM) ≤ normStar QR + normStar X*normStar DR*normStar RM :=
    (sub_le _ _).trans (add_le_add (transpose QR).le hx)
  exact (add_le _ _).trans (add_le_add (mul_le DR RM) (mul_bound _ _ _ _ le_rfl hinner))

/-- Literal bP for the actual interpolation formula. No final estimate on P,
Q, or a right inverse is assumed; all are derived from the explicit tables. -/
theorem coupling_bound {m : Type*} [Fintype m] [Nonempty m] (k : ℕ)
    (T1 T2 lam : ℚ) (z ell psi : Fin (k+1) → ℚ)
    (E L B : Matrix (Fin (k+1)) (Fin (k+1)) ℚ)
    (a : m → ℚ) (X LX D : Matrix m (Fin (k+1)) ℚ)
    (ha : Matrix.vecMul a X = z + Matrix.vecMul z B)
    (ht1 : 0 < T1) (ht2 : T1 ≤ T2) (hlam : 0 < lam) (hz : 0 < z (lastIdx k))
    (hnu : nu k T1 lam z ell < 1/2) :
    let WE := WE_concrete k T1 T2 lam z (earlyUnit k) ell
    let W := W_concrete k T1 T2 lam z
    let M := Matrix.fromRows WE W
    let RM := Matrix.fromCols (0 : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (Winv_concrete k T1 T2 lam z)
    let Q := resetScoreTarget psi WE W L (paperCross k T1 T2 lam z ell E L) (1/(T1*T2^2)) B
    let P0 := referenceCoupling (r := Fin (k+1)) a
    normStar (P_interp X LX M RM D Q P0 - P0) ≤ bP k T1 lam z ell psi E L B a X LX D := by
  intro WE W M RM Q P0
  have hD : D-P0*M = D+outerProd a ell := by
    rw [referenceCoupling_mul_reset]
    simp only [sub_neg_eq_add]
  have hR : normStar RM ≤ bW k T1 lam z :=
    (fromCols_zero_le (Winv_concrete k T1 T2 lam z)).trans (inverse_bound k T1 T2 lam z ht1 ht2)
  have hQ : normStar (Q-P0ᵀ*X) ≤ bQ k T1 lam z ell psi E L B := by
    change normStar (Q-(referenceCoupling a)ᵀ*X) ≤ _
    rw [referenceCoupling_transpose_mul a X z B ha]
    exact score_bound k T1 T2 lam z ell psi E L B ht1 ht2 hlam hz hnu
  have hbase := interpolation_bound X LX M RM D Q P0
  rw [hD] at hbase
  have hpair := mul_le_mul_of_nonneg_left hR (nonneg (D+outerProd a ell))
  have htriple := mul_le_mul_of_nonneg_left hpair (nonneg X)
  have hsum := add_le_add hQ htriple
  have hscale := mul_le_mul_of_nonneg_left hsum (nonneg LX)
  exact hbase.trans (by simpa only [bP, mul_assoc] using add_le_add hpair hscale)

theorem coupling_signs_of_bound {m : Type*} [Fintype m] [Nonempty m] (k : ℕ)
    (C : Matrix m (Fin (k+1) ⊕ Fin (k+1)) ℚ) (a : m → ℚ) (g : m)
    (eps amin Ak c : ℚ) (hC : normStar (C-referenceCoupling a) ≤ eps)
    (hmin : 0 < amin) (ha : ∀ i, amin ≤ a i) (hag : Ak+1 < a g) (hc : c < 1)
    (heps : eps < amin/4) (hepsg : eps < (a g-Ak-1)/2) :
    (∀ i j, C i (Sum.inl j) < -(amin/4) ∧ amin/4 < C i (Sum.inr j)) ∧
    (∀ j, Ak < -C g (Sum.inl j)-c) := by
  let P0 : Matrix m (Fin (k+1) ⊕ Fin (k+1)) ℚ := referenceCoupling a
  change normStar (C-P0) ≤ eps at hC
  have hentry (i : m) (j : Fin (k+1) ⊕ Fin (k+1)) :
      |C i j-P0 i j| ≤ eps := by
    have hh := abs_entry_le (C-P0) i j
    change |C i j-P0 i j| ≤ normStar (C-P0) at hh
    exact hh.trans hC
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

#print axioms cross_bound
#print axioms score_bound
#print axioms coupling_bound
end Karlin.FaithfulAppendix
