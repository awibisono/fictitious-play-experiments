import Karlin.FaithfulTables
import Karlin.FaithfulReset
import Karlin.FaithfulGrowth
import Karlin.FaithfulProspectiveScale

/-! The literal target row and rotated-table summaries of v15.
The target is computed before the final reset-count parameter is chosen. -/

namespace Karlin.FaithfulNextTables
open scoped BigOperators Matrix
open FaithfulTables

theorem E_zero_column (k tau : ℕ) (i : Fin k) :
    E_tau_mat k tau i 0 = binomBasis k 0 i := by
  have h := congrFun (E_tau_mat_mulVec_binomBasis k tau 0) i
  simpa only [mulVec_binomBasis_zero, Nat.mul_zero] using h

theorem F_zero_column (k tau : ℕ) (i : Fin k) : F_tau_mat k tau i 0 = 0 := by
  have h := F_tau_mat_mulVec_binomBasis k tau 0 i
  simpa only [mulVec_binomBasis_zero, Nat.mul_zero, Finset.Ico_self,
    Finset.sum_empty] using h

theorem increment_zero {k : ℕ} (chi : Fin k → ℚ) (tau : ℕ) (c : ℚ) :
    increment chi tau c 0 = c := by
  simp [increment, Matrix.vecMul, dotProduct, Matrix.sub_apply, E_2tau_mat,
    E_zero_column, e0_row]

def targetRhs {k : ℕ} (chi : Fin k → ℚ) (tau : ℕ) (c H : ℚ) : Fin (k + 1) → ℚ :=
  zeta chi tau c H + Matrix.vecMul (zeta chi tau c H) (B_mat (k + 1)) -
    (2 * H - c) • e0_row (k + 1)

theorem targetRhs_zero {k : ℕ} (hk : 0 < k) (chi : Fin k → ℚ)
    (tau : ℕ) (c H : ℚ) : targetRhs chi tau c H 0 = 0 := by
  have h := congrFun (zeta_spec hk chi tau c H).1 0
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, Pi.sub_apply, increment_zero] at h
  have hz := (zeta_spec hk chi tau c H).2
  simp only [targetRhs, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    hz, e0_row, Fin.val_zero, ite_true, mul_one]
  linarith

/-- The unique row whose bundle equals the nonconstant part of two heights. -/
noncomputable def target {k : ℕ} (chi : Fin k → ℚ) (tau : ℕ) (c H : ℚ) : Fin k → ℚ :=
  Matrix.vecMul (fun i => targetRhs chi tau c H i.succ) (Fblock k tau)⁻¹

theorem F_vecMul_injective (k tau : ℕ) (htau : 0 < tau) :
    Function.Injective (fun u : Fin k → ℚ => Matrix.vecMul u (F_tau_mat k tau)) := by
  intro u v h
  have htail : Matrix.vecMul u (Fblock k tau) = Matrix.vecMul v (Fblock k tau) :=
    funext (fun j => congrFun h j.succ)
  exact (Matrix.vecMul_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr
      (Fblock_det_ne_zero k tau htau)))) htail

theorem target_spec {k : ℕ} (hk : 0 < k) (chi : Fin k → ℚ)
    (tau : ℕ) (htau : 0 < tau) (c H : ℚ) :
    Matrix.vecMul (target chi tau c H) (F_tau_mat k tau) = targetRhs chi tau c H := by
  have he := Matrix.nonsing_inv_mul (Fblock k tau)
    (isUnit_iff_ne_zero.mpr (Fblock_det_ne_zero k tau htau))
  have htail : Matrix.vecMul (target chi tau c H) (Fblock k tau) =
      (fun i => targetRhs chi tau c H i.succ) := by
    rw [target, Matrix.vecMul_vecMul, he, Matrix.vecMul_one]
  funext j
  induction j using Fin.cases with
  | zero => simp [Matrix.vecMul, dotProduct, F_zero_column, targetRhs_zero hk]
  | succ j => exact congrFun htail j

theorem target_unique {k : ℕ} (hk : 0 < k) (chi : Fin k → ℚ)
    (tau : ℕ) (htau : 0 < tau) (c H : ℚ) (t : Fin k → ℚ)
    (ht : Matrix.vecMul t (F_tau_mat k tau) = targetRhs chi tau c H) :
    t = target chi tau c H :=
  F_vecMul_injective k tau htau (ht.trans (target_spec hk chi tau htau c H).symm)

/-- The equivalence asserted in Definition (admissible)(ii), for the actual X. -/
theorem target_cone_iff {k : ℕ} (P : FaithfulClock.Clock k) (tau : ℕ)
    (htau : 0 < tau) (c H : ℚ) (aP : Fin P.m → ℚ) :
    Matrix.vecMul aP P.countTable = target (P.R P.b) tau c H ↔
    Matrix.vecMul (Sum.elim aP (fun _ : Fin 1 => 2 * H - c)) (X P tau) =
      zeta (P.R P.b) tau c H + Matrix.vecMul (zeta (P.R P.b) tau c H) (B_mat (k + 1)) := by
  have he : Matrix.vecMul (Sum.elim aP (fun _ : Fin 1 => 2 * H - c)) (X P tau) =
      Matrix.vecMul (Matrix.vecMul aP P.countTable) (F_tau_mat k tau) +
        (2 * H - c) • e0_row (k + 1) := by
    rw [X, Matrix.sumElim_vecMul_fromRows, Matrix.vecMul_vecMul]
    congr 1
    ext j
    simp [Matrix.vecMul, dotProduct]
  rw [he]
  constructor
  · intro h
    rw [h, target_spec (by have := P.order_ge_two; omega) _ _ htau]
    dsimp [targetRhs]
    abel
  · intro h
    apply target_unique (by have := P.order_ge_two; omega) _ _ htau
    dsimp [targetRhs]
    rw [← h]
    abel

theorem target_leading_times_diag {k : ℕ} (hk : 2 ≤ k) (chi : Fin k → ℚ)
    (tau : ℕ) (htau : 0 < tau) (c H : ℚ) :
    target chi tau c H ⟨k - 1, by omega⟩ *
      ((tau : ℚ) ^ k * ((2 : ℚ) ^ k - 1)) = 2 * zeta chi tau c H (Fin.last k) := by
  have h := congrFun (target_spec (by omega) chi tau htau c H) (Fin.last k)
  have hl : Matrix.vecMul (target chi tau c H) (F_tau_mat k tau) (Fin.last k) =
      target chi tau c H ⟨k - 1, by omega⟩ *
        ((tau : ℚ) ^ k * ((2 : ℚ) ^ k - 1)) := by
    rw [Matrix.vecMul, dotProduct, Finset.sum_eq_single ⟨k - 1, by omega⟩]
    · have he : Fin.last k = (⟨k - 1, by omega⟩ : Fin k).succ := Fin.ext (by simp; omega)
      rw [he]
      have hd := F_tau_mat_diag k tau (⟨k - 1, by omega⟩ : Fin k)
      change F_tau_mat k tau ⟨k - 1, by omega⟩ (⟨k - 1, by omega⟩ : Fin k).succ = _ at hd
      rw [hd]
      simp only [Fin.val_mk, show k - 1 + 1 = k by omega]
    · intro i _ hi
      have hi' : i.val ≠ k - 1 := fun h => hi (Fin.ext h)
      rw [F_tau_mat_eq_zero_of_gt k tau i (Fin.last k) (by have := i.isLt; simp; omega), mul_zero]
    · simp
  rw [hl] at h
  simpa [targetRhs, vecMul_B_last, e0_row, show k ≠ 0 by omega, two_mul] using h

theorem target_leading_pos {k : ℕ} (hk : 2 ≤ k) (chi : Fin k → ℚ)
    (hchi : 0 < chi ⟨k - 1, by omega⟩) (tau : ℕ) (htau : 0 < tau) (c H : ℚ) :
    0 < target chi tau c H ⟨k - 1, by omega⟩ := by
  have hd : 0 < (tau : ℚ) ^ k * ((2 : ℚ) ^ k - 1) := by
    have ht : (0 : ℚ) < tau := by exact_mod_cast htau
    have hpow : (1 : ℚ) < 2 ^ k := one_lt_pow₀ (by norm_num) (by omega)
    exact mul_pos (pow_pos ht _) (sub_pos.mpr hpow)
  have h := target_leading_times_diag hk chi tau htau c H
  have hz := zeta_leading_pos hk chi tau htau hchi c H
  exact (mul_pos_iff_of_pos_right hd).mp (by rw [h]; positivity)

/-- The exact leading coefficient displayed in equation (target). -/
theorem target_leading {k : ℕ} (hk : 2 ≤ k) (chi : Fin k → ℚ)
    (tau : ℕ) (htau : 0 < tau) (c H : ℚ) :
    target chi tau c H ⟨k - 1, by omega⟩ =
      (2 * chi ⟨k - 1, by omega⟩ * ((2 : ℚ) ^ (k - 1) - 1)) /
        ((tau : ℚ) * ((2 : ℚ) ^ k - 1)) := by
  have ht : (tau : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt htau
  have htwo : (2 : ℚ) ^ k - 1 ≠ 0 := ne_of_gt
    (sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega)))
  have hp : (tau : ℚ) ^ k = (tau : ℚ) ^ (k - 1) * tau := by
    rw [← pow_succ]
    congr 1
    omega
  apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero _ ht) htwo)
  rw [target_leading_times_diag hk chi tau htau c H, zeta_leading hk, hp]
  field_simp
  <;> ring

theorem zeta_change_constant {k : ℕ} (chi : Fin k → ℚ) (tau : ℕ) (c H H' : ℚ) :
    zeta chi tau c H = zeta chi tau c H' + (H - H') • e0_row (k + 1) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [zeta, antiderivative, e0_row]
  | succ j => simp [zeta, antiderivative, e0_row]

theorem e0_vecMul_B (k : ℕ) :
    Matrix.vecMul (e0_row (k + 1)) (B_mat (k + 1)) = e0_row (k + 1) := by
  have ht : Matrix.vecMul (e0_row (k + 1)) (T_mat (k + 1)) = e0_row (k + 1) := by
    rw [T_mat, Matrix.vecMul_add, Matrix.vecMul_one, e0_row_mul_N_mat, add_zero]
  have hh := congrArg (fun v => Matrix.vecMul v (B_mat (k + 1))) ht
  simpa only [Matrix.vecMul_vecMul, (B_mat_mul_T_mat (k + 1)).2,
    Matrix.vecMul_one] using hh.symm

/-- H cancels from the actual target, so the next suffix constant need not be
known when the next target and scale are selected. -/
theorem target_independent_H {k : ℕ} (chi : Fin k → ℚ) (tau : ℕ) (c H H' : ℚ) :
    target chi tau c H = target chi tau c H' := by
  have hh : targetRhs chi tau c H = targetRhs chi tau c H' := by
    unfold targetRhs
    rw [zeta_change_constant chi tau c H H', Matrix.add_vecMul, Matrix.smul_vecMul, e0_vecMul_B]
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [target, hh]

/-- Rotated score table, exactly equation (rotate), on old plus reset actions. -/
def nextScores {o r : Type*} [Fintype r] {w : ℕ}
    (Smid : Matrix o (Fin w) ℚ) (zeta : Fin w → ℚ)
    (J : Matrix r r ℚ) (M : Matrix r (Fin w) ℚ) : Matrix (o ⊕ r) (Fin w) ℚ :=
  Matrix.fromRows Smid (outerProd (fun _ : r => 1) zeta - J * M)

/-- The old word moves to q+1 while the reset word remains at q. -/
def nextCounts {o r : Type*} {w : ℕ}
    (X : Matrix o (Fin w) ℚ) (M : Matrix r (Fin w) ℚ) : Matrix (o ⊕ r) (Fin w) ℚ :=
  Matrix.fromRows (X * T_mat w) M

theorem nextScores_transpose_nextCounts {o r : Type*} [Fintype o] [Fintype r] {w : ℕ}
    (Smid X : Matrix o (Fin w) ℚ) (zeta ell : Fin w → ℚ)
    (J : Matrix r r ℚ) (M : Matrix r (Fin w) ℚ) (E : Matrix (Fin w) (Fin w) ℚ)
    (hsum : Matrix.vecMul (fun _ : r => 1) M = ell) (hmoment : Mᵀ * J * M = E) :
    (nextScores Smid zeta J M)ᵀ * nextCounts X M =
      Smidᵀ * X * T_mat w + outerProd zeta ell - Eᵀ := by
  rw [nextScores, nextCounts, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows,
    Matrix.transpose_sub, Matrix.sub_mul, outerProd_transpose, outerProd_mul, hsum]
  have hm : (J * M)ᵀ * M = Eᵀ := by
    rw [← hmoment]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [hm, ← Matrix.mul_assoc]
  abel

theorem nextCounts_sum {o r : Type*} [Fintype o] [Fintype r] {w : ℕ}
    (X : Matrix o (Fin w) ℚ) (M : Matrix r (Fin w) ℚ) (ell : Fin w → ℚ)
    (hsum : Matrix.vecMul (fun _ : r => 1) M = ell) :
    Matrix.vecMul (fun _ : o ⊕ r => 1) (nextCounts X M) =
      Matrix.vecMul (Matrix.vecMul (fun _ : o => 1) X) (T_mat w) + ell := by
  have ho : (fun _ : o ⊕ r => (1 : ℚ)) = Sum.elim (fun _ : o => 1) (fun _ : r => 1) := by
    funext i; cases i <;> rfl
  rw [ho, nextCounts]
  rw [Matrix.sumElim_vecMul_fromRows, hsum, Matrix.vecMul_vecMul]

theorem nextScores_first_reset {o r : Type*} [Fintype r] {w : ℕ}
    (Smid : Matrix o (Fin w) ℚ) (zeta : Fin w → ℚ)
    (J : Matrix r r ℚ) (M : Matrix r (Fin w) ℚ) (b : r)
    (hfirst : ∀ j, J b j = 0) : nextScores Smid zeta J M (Sum.inr b) = zeta := by
  ext j
  simp [nextScores, outerProd, Matrix.mul_apply, hfirst]

theorem nextCounts_gateway {k : ℕ} (P : FaithfulClock.Clock k) (tau : ℕ)
    {r : Type*} (M : Matrix r (Fin (k + 1)) ℚ) :
    nextCounts (X P tau) M (Sum.inl (Sum.inr 0)) = e0_row (k + 1) := by
  change Matrix.vecMul (e0_row (k + 1)) (T_mat (k + 1)) = _
  rw [T_mat, Matrix.vecMul_add, Matrix.vecMul_one, e0_row_mul_N_mat, add_zero]

theorem nextCounts_full_column_rank {o r : Type*} {w : ℕ}
    (X : Matrix o (Fin w) ℚ) (M : Matrix r (Fin w) ℚ)
    (hM : Function.Injective M.mulVec) : Function.Injective (nextCounts X M).mulVec := by
  intro x y h
  apply hM
  funext i
  exact congrFun h (Sum.inr i)

/-- Exact rotated clock equation from the two reset equations. -/
theorem next_clock_eq {o r : Type*} [Fintype o] [Fintype r] {w : ℕ}
    (G : Matrix o o ℚ) (P : Matrix o r ℚ) (J : Matrix r r ℚ)
    (S X : Matrix o (Fin w) ℚ) (M : Matrix r (Fin w) ℚ) (zeta : Fin w → ℚ)
    (hPM : P * M = S * N_mat w - G * X)
    (hPX : Pᵀ * X = Q_reset J M (B_mat w) zeta) :
    liftedGameMat G P J * nextCounts X M =
      nextScores (S + G * X) zeta J M * N_mat w := by
  have hVN := V_reset_mul_N J M (B_mat w) (N_mat w) zeta (B_mat_mul_T_mat w).1
  have hr : -Pᵀ * X + (J - Jᵀ) * M = V_reset J M (B_mat w) zeta * N_mat w := by
    rw [hVN, Matrix.neg_mul, hPX]
    abel
  have hreset := rotated_clock_reset_block P J X M (V_reset J M (B_mat w) zeta)
    (Q_reset J M (B_mat w) zeta) (N_mat w) hr hPX
  rw [rotated_reset_score_identity] at hreset
  have ho : one_zeta r zeta = outerProd (fun _ : r => 1) zeta := by
    ext i j; simp [one_zeta, outerProd]
  rw [ho] at hreset
  rw [liftedGameMat, nextCounts, nextScores, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
  exact congrArg₂ Matrix.fromRows (rotated_clock_old_block G P S X M (N_mat w) hPM) hreset

/-- The reset total is fixed before T2; its lower-degree redistribution cancels. -/
theorem concrete_reset_sum (k : ℕ) (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ) :
    Matrix.vecMul (fun _ => 1)
      (Matrix.fromRows (WE_concrete k T1 T2 lam zeta0 (Faithful.earlyUnit k) ellStar)
        (W_concrete k T1 T2 lam zeta0)) =
      (2 * (k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar := by
  have ho : (fun _ : Fin (k + 1) ⊕ Fin (k + 1) => (1 : ℚ)) =
      Sum.elim (fun _ : Fin (k + 1) => 1) (fun _ : Fin (k + 1) => 1) := by
    funext i; cases i <;> rfl
  rw [ho]
  rw [Matrix.sumElim_vecMul_fromRows, Faithful.early_row_sum, vecMul_one_W_concrete]
  ext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

def resetCounts (k : ℕ) (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ) :=
  Matrix.fromRows (WE_concrete k T1 T2 lam zeta0 (Faithful.earlyUnit k) ellStar)
    (W_concrete k T1 T2 lam zeta0)

/-- Literal equation (J), with the exact v15 normalization. -/
def resetInteractions (k : ℕ) (T1 T2 lam : ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E Lr : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :=
  let W := W_concrete k T1 T2 lam zeta0
  let WE := WE_concrete k T1 T2 lam zeta0 (Faithful.earlyUnit k) ellStar
  let eta := 1 / (T1 * T2 ^ 2)
  let Fres := E - Faithful.paperEbase k T1 lam zeta0 ellStar -
    eta • (WEᵀ * Lr * WE + Wᵀ * Lr * W)
  let Ccross := Faithful.paperKappa k T1 lam • outerProd (fun _ : Fin (k + 1) => 1) (fun _ => 1) +
    (Winv_concrete k T1 T2 lam zeta0)ᵀ * Fres *
      WE_inv_concrete k T1 T2 lam zeta0 (Faithful.earlyUnit k) ellStar
  Matrix.fromBlocks (eta • Lr) 0 Ccross (eta • Lr)

theorem resetInteractions_first_row (k : ℕ) (T1 T2 lam : ℚ)
    (zeta0 ellStar : Fin (k + 1) → ℚ)
    (E Lr : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) (hL : ∀ j, Lr 0 j = 0)
    (j : Fin (k + 1) ⊕ Fin (k + 1)) :
    resetInteractions k T1 T2 lam zeta0 ellStar E Lr (Sum.inl 0) j = 0 := by
  cases j <;> simp [resetInteractions, hL]

/-- The first next-order summary has a fixed right-hand side containing no T2.
The premise is only the explicitly checked inverse denominator, not a summary
or moment identity supplied as an assumption. -/
theorem concrete_next_summary {o : Type*} [Fintype o] (k : ℕ)
    (Smid X : Matrix o (Fin (k + 1)) ℚ) (zeta zeta0 ellStar : Fin (k + 1) → ℚ)
    (T1 T2 lam : ℚ) (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0) (hlam : lam ≠ 0)
    (hzeta : zeta0 (lastIdx k) ≠ 0)
    (hdenom : 1 + dotProduct ellStar
      (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (Faithful.earlyUnit k)) ≠ 0)
    (E Lr : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :
    (nextScores Smid zeta (resetInteractions k T1 T2 lam zeta0 ellStar E Lr)
      (resetCounts k T1 T2 lam zeta0 ellStar))ᵀ *
      nextCounts X (resetCounts k T1 T2 lam zeta0 ellStar) =
      Smidᵀ * X * T_mat (k + 1) +
        outerProd zeta ((2 * (k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar) - Eᵀ := by
  apply nextScores_transpose_nextCounts
  · exact concrete_reset_sum k T1 T2 lam zeta0 ellStar
  · exact Faithful.exact_paper_moment k T1 T2 lam hT1 hT2 hlam zeta0 ellStar hzeta hdenom E Lr

theorem concrete_next_count_sum {o : Type*} [Fintype o] (k : ℕ)
    (X : Matrix o (Fin (k + 1)) ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ) (T1 T2 lam : ℚ) :
    Matrix.vecMul (fun _ => 1) (nextCounts X (resetCounts k T1 T2 lam zeta0 ellStar)) =
      Matrix.vecMul (Matrix.vecMul (fun _ : o => 1) X) (T_mat (k + 1)) +
        ((2 * (k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar) :=
  nextCounts_sum X _ _ (concrete_reset_sum k T1 T2 lam zeta0 ellStar)

theorem vecMul_F_last {k : ℕ} (hk : 0 < k) (u : Fin k → ℚ) (tau : ℕ) :
    Matrix.vecMul u (F_tau_mat k tau) (Fin.last k) =
      u ⟨k - 1, by omega⟩ * ((tau : ℚ) ^ k * ((2 : ℚ) ^ k - 1)) := by
  rw [Matrix.vecMul, dotProduct, Finset.sum_eq_single ⟨k - 1, by omega⟩]
  · have he : Fin.last k = (⟨k - 1, by omega⟩ : Fin k).succ := Fin.ext (by simp; omega)
    rw [he]
    have hd := F_tau_mat_diag k tau (⟨k - 1, by omega⟩ : Fin k)
    change F_tau_mat k tau ⟨k - 1, by omega⟩ (⟨k - 1, by omega⟩ : Fin k).succ = _ at hd
    rw [hd]
    simp only [show k - 1 + 1 = k by omega]
  · intro i _ hi
    have hi' : i.val ≠ k - 1 := fun h => hi (Fin.ext h)
    rw [F_tau_mat_eq_zero_of_gt k tau i (Fin.last k) (by have := i.isLt; simp; omega), mul_zero]
  · simp

/-- Only the top count column is nonnegative; lower count coefficients may
have either sign. This derives the exact premise needed by the cone step. -/
theorem shifted_X_leading_nonneg {k : ℕ} (P : FaithfulClock.Clock k) (tau : ℕ)
    (i : OldAct P) : 0 ≤ (X P tau * T_mat (k + 1)) i (lastIdx k) := by
  have hk : 0 < k := by have := P.order_ge_two; omega
  have ht : (X P tau * T_mat (k + 1)) i (lastIdx k) = X P tau i (Fin.last k) := by
    rw [T_mat, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, mul_N_mat_apply]
    simp [lastIdx]
    congr 1
  rw [ht]
  rcases i with i | i
  · change 0 ≤ Matrix.vecMul (P.countTable i) (F_tau_mat k tau) (Fin.last k)
    rw [vecMul_F_last hk]
    apply mul_nonneg (FaithfulGrowth.Clock.leading_count_nonneg P i)
    apply mul_nonneg (pow_nonneg (by positivity) _)
    have hpow : (1 : ℚ) < 2 ^ k := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  · change 0 ≤ e0_row (k + 1) (Fin.last k)
    simp [e0_row, Nat.ne_of_gt hk]

/-- The actual next target and actual rotated count table admit positive
weights once T2 is chosen. Every input displayed before the existential is
fixed independently of T2. No positive target or old-leading premise remains. -/
theorem next_target_positive_weights {k : ℕ} (P : FaithfulClock.Clock k)
    (tau tauNext : ℕ) (htau : 0 < tau) (htauNext : 0 < tauNext)
    (c cref H Hnext : ℚ) (T1 lam : ℚ) (hT1 : 0 < T1) (hlam : 0 < lam)
    (ellStar : Fin (k + 1) → ℚ)
    (hearly : 0 < T1 * lam * zeta (P.R P.b) tau cref H (lastIdx k) + ellStar (lastIdx k)) :
    ∃ N : ℕ, T1 < (N : ℚ) ∧
      T1 * lam * zeta (P.R P.b) tau cref H (lastIdx k) < (N : ℚ) ∧
      ∀ T2 : ℕ, N ≤ T2 → ∃ a : OldAct P ⊕ (Fin (k + 1) ⊕ Fin (k + 1)) → ℚ,
        (∀ i, 0 < a i) ∧
        Matrix.vecMul a (nextCounts (X P tau)
          (resetCounts k T1 T2 lam (zeta (P.R P.b) tau cref H) ellStar)) =
          target (zeta (P.R P.b) tau c H) tauNext (1 / 2) Hnext := by
  have hz0 : 0 < zeta (P.R P.b) tau cref H (lastIdx k) :=
    zeta_leading_pos P.order_ge_two _ tau htau P.leading_height cref H
  have hz : 0 < zeta (P.R P.b) tau c H (Fin.last k) :=
    zeta_leading_pos P.order_ge_two _ tau htau P.leading_height c H
  have htarget : 0 < target (zeta (P.R P.b) tau c H) tauNext (1 / 2) Hnext (lastIdx k) := by
    exact target_leading_pos (by have := P.order_ge_two; omega) _ hz tauNext htauNext _ _
  have hr0 := Faithful.r0_leading_positive k (X P tau * T_mat (k + 1)) T1 lam
    (zeta (P.R P.b) tau cref H) ellStar (shifted_X_leading_nonneg P tau)
    (mul_pos (mul_pos hT1 hlam) hz0) hearly
  obtain ⟨N, hN1, hNu, _, _, _, hN⟩ := Faithful.positive_cone_exists k
    (X P tau * T_mat (k + 1)) T1 lam (zeta (P.R P.b) tau cref H) ellStar
    (target (zeta (P.R P.b) tau c H) tauNext (1 / 2) Hnext)
    hT1 hlam hz0 htarget hr0
  refine ⟨N, hN1, hNu, ?_⟩
  intro T2 hT2
  obtain ⟨_, hpos, heq⟩ := hN T2 hT2
  exact ⟨_, hpos, heq⟩

/-- The fixed first summary on the right of equation (nextsummary). -/
def fixedMoment {o : Type*} [Fintype o] (k : ℕ)
    (Smid X : Matrix o (Fin (k + 1)) ℚ) (zeta zeta0 ellStar : Fin (k + 1) → ℚ)
    (T1 lam : ℚ) (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :=
  Smidᵀ * X * T_mat (k + 1) +
    outerProd zeta ((2 * (k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar) - Eᵀ

def fixedLength {o : Type*} [Fintype o] (k : ℕ)
    (X : Matrix o (Fin (k + 1)) ℚ) (zeta0 ellStar : Fin (k + 1) → ℚ) (T1 lam : ℚ) :=
  Matrix.vecMul (Matrix.vecMul (fun _ : o => 1) X) (T_mat (k + 1)) +
    ((2 * (k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar)

/-- The prospective scale/correction family is computed before T2 or any
next trajectory exists. It uses precisely the fixed next-order summaries. -/
noncomputable def nextPolynomials {o : Type*} [Fintype o] (k : ℕ) (hk : 2 ≤ k + 1)
    (Smid X : Matrix o (Fin (k + 1)) ℚ) (zeta zeta0 ellStar : Fin (k + 1) → ℚ)
    (T1 lam : ℚ) (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :=
  FaithfulScale.referenceSolver (k + 1) hk
    (fixedMoment k Smid X zeta zeta0 ellStar T1 lam E)
    (fixedLength k X zeta0 ellStar T1 lam) zeta (1 / 2)

noncomputable def nextScale {o : Type*} [Fintype o] (k : ℕ) (hk : 2 ≤ k + 1)
    (Smid X : Matrix o (Fin (k + 1)) ℚ) (zeta zeta0 ellStar : Fin (k + 1) → ℚ)
    (T1 lam : ℚ) (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) : ℕ :=
  FaithfulScale.integerScale (k + 1) (nextPolynomials k hk Smid X zeta zeta0 ellStar T1 lam E)

noncomputable def nextCorrection {o : Type*} [Fintype o] (k : ℕ) (hk : 2 ≤ k + 1)
    (Smid X : Matrix o (Fin (k + 1)) ℚ) (zeta zeta0 ellStar : Fin (k + 1) → ℚ)
    (T1 lam : ℚ) (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) : Fin (k + 2) → ℤ :=
  FaithfulScale.referenceCorrectionInt (k + 1) hk
    (fixedMoment k Smid X zeta zeta0 ellStar T1 lam E)
    (fixedLength k X zeta0 ellStar T1 lam) zeta (1 / 2)

theorem nextScale_pos {o : Type*} [Fintype o] (k : ℕ) (hk : 2 ≤ k + 1)
    (Smid X : Matrix o (Fin (k + 1)) ℚ) (zeta zeta0 ellStar : Fin (k + 1) → ℚ)
    (T1 lam : ℚ) (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :
    0 < nextScale k hk Smid X zeta zeta0 ellStar T1 lam E :=
  FaithfulScale.integerScale_pos (k + 1) _

/-- The correction computed from the fixed next-order summaries already
satisfies every higher compatibility test in divided-power coordinates,
before selecting T2 or constructing the next valid Clock. -/
theorem nextCorrection_higher_tests {k : ℕ} (P : FaithfulClock.Clock k)
    (tau : ℕ) (htau : 0 < tau) (c cref H delta T1 lam : ℚ)
    (ellStar : Fin (k + 1) → ℚ) (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :
    let hk : 2 ≤ k + 1 := by have := P.order_ge_two; omega
    let z := zeta (P.R P.b) tau c H
    let z0 := zeta (P.R P.b) tau cref H
    let m := fixedMoment k (S_mid P tau c H delta) (X P tau) z z0 ellStar T1 lam E
    let l := fixedLength k (X P tau) z0 ellStar T1 lam
    let tauNext := nextScale k hk (S_mid P tau c H delta) (X P tau) z z0 ellStar T1 lam E
    let ellNext := nextCorrection k hk (S_mid P tau c H delta) (X P tau) z z0 ellStar T1 lam E
    ∀ h, k + 1 < h → h ≤ 2 * (k + 1) → Even h →
      matInnerProd (Z_DP (k + 2) h)
        ((Matrix.of fun i j => (FaithfulScale.referenceInterior (k + 1) m l z (1 / 2) i j).eval
          (tauNext : ℚ)) -
          outerProd (Matrix.vecMul (fun j => (ellNext j : ℚ)) (S_mat (k + 2)))
            (fun j => (FaithfulScale.referencePsi (k + 1) z (1 / 2) j).eval (tauNext : ℚ))) = 0 := by
  intro hk z z0 m l tauNext ellNext
  have hz : z ⟨k + 1 - 1, by omega⟩ ≠ 0 :=
    ne_of_gt (zeta_leading_pos P.order_ge_two _ tau htau P.leading_height c H)
  exact (FaithfulProspectiveScale.canonicalCorrection_DP_higher_tests (k + 1) hk
    m l z (1 / 2) hz).2

/-- Both deterministic outputs computed from the actual rotated tables equal
the fixed prospective outputs. Thus later changes in T2 cannot select a new
scale or correction row. -/
theorem actual_next_pair_eq_fixed {o : Type*} [Fintype o] (k : ℕ) (hk : 2 ≤ k + 1)
    (Smid X : Matrix o (Fin (k + 1)) ℚ) (zeta zeta0 ellStar : Fin (k + 1) → ℚ)
    (T1 T2 lam : ℚ) (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0) (hlam : lam ≠ 0)
    (hzeta : zeta0 (lastIdx k) ≠ 0)
    (hdenom : 1 + dotProduct ellStar
      (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) (Faithful.earlyUnit k)) ≠ 0)
    (E Lr : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :
    let Rplus := nextScores Smid zeta (resetInteractions k T1 T2 lam zeta0 ellStar E Lr)
      (resetCounts k T1 T2 lam zeta0 ellStar)
    let Cplus := nextCounts X (resetCounts k T1 T2 lam zeta0 ellStar)
    FaithfulScale.integerScale (k + 1)
      (FaithfulScale.referenceSolver (k + 1) hk (Rplusᵀ * Cplus)
        (Matrix.vecMul (fun _ => 1) Cplus) zeta (1 / 2)) =
      nextScale k hk Smid X zeta zeta0 ellStar T1 lam E ∧
    FaithfulScale.referenceCorrectionInt (k + 1) hk (Rplusᵀ * Cplus)
      (Matrix.vecMul (fun _ => 1) Cplus) zeta (1 / 2) =
      nextCorrection k hk Smid X zeta zeta0 ellStar T1 lam E := by
  dsimp only
  rw [concrete_next_summary k Smid X zeta zeta0 ellStar T1 T2 lam hT1 hT2 hlam hzeta hdenom E Lr,
    concrete_next_count_sum]
  exact ⟨rfl, rfl⟩

/-- The permitted final parameter is chosen only after the deterministic
prospective scale has been fixed from the literal, T2-independent summaries. -/
theorem next_chosen_positive_weights {k : ℕ} (P : FaithfulClock.Clock k)
    (tau : ℕ) (htau : 0 < tau) (c cref H Hnext delta : ℚ)
    (T1 lam : ℚ) (hT1 : 0 < T1) (hlam : 0 < lam)
    (ellStar : Fin (k + 1) → ℚ) (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hearly : 0 < T1 * lam * zeta (P.R P.b) tau cref H (lastIdx k) + ellStar (lastIdx k)) :
    let tauNext := nextScale k (by have := P.order_ge_two; omega)
      (S_mid P tau c H delta) (X P tau) (zeta (P.R P.b) tau c H)
      (zeta (P.R P.b) tau cref H) ellStar T1 lam E
    ∃ N : ℕ, T1 < (N : ℚ) ∧
      T1 * lam * zeta (P.R P.b) tau cref H (lastIdx k) < (N : ℚ) ∧
      ∀ T2 : ℕ, N ≤ T2 → ∃ a : OldAct P ⊕ (Fin (k + 1) ⊕ Fin (k + 1)) → ℚ,
        (∀ i, 0 < a i) ∧
        Matrix.vecMul a (nextCounts (X P tau)
          (resetCounts k T1 T2 lam (zeta (P.R P.b) tau cref H) ellStar)) =
          target (zeta (P.R P.b) tau c H) tauNext (1 / 2) Hnext := by
  intro tauNext
  exact next_target_positive_weights P tau tauNext htau (nextScale_pos _ _ _ _ _ _ _ _ _ _)
    c cref H Hnext T1 lam hT1 hlam ellStar hearly

/-- Strong parameter order: the final suffix baseline may be computed after
T2 and may depend on T2. The already selected positive weights work for every
baseline because the actual target is independent of its constant height. -/
theorem next_chosen_positive_weights_all_baselines {k : ℕ} (P : FaithfulClock.Clock k)
    (tau : ℕ) (htau : 0 < tau) (c cref H delta : ℚ)
    (T1 lam : ℚ) (hT1 : 0 < T1) (hlam : 0 < lam)
    (ellStar : Fin (k + 1) → ℚ) (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hearly : 0 < T1 * lam * zeta (P.R P.b) tau cref H (lastIdx k) + ellStar (lastIdx k)) :
    let tauNext := nextScale k (by have := P.order_ge_two; omega)
      (S_mid P tau c H delta) (X P tau) (zeta (P.R P.b) tau c H)
      (zeta (P.R P.b) tau cref H) ellStar T1 lam E
    ∃ N : ℕ, T1 < (N : ℚ) ∧
      T1 * lam * zeta (P.R P.b) tau cref H (lastIdx k) < (N : ℚ) ∧
      ∀ T2 : ℕ, N ≤ T2 → ∃ a : OldAct P ⊕ (Fin (k + 1) ⊕ Fin (k + 1)) → ℚ,
        (∀ i, 0 < a i) ∧ ∀ Hnext : ℚ,
        Matrix.vecMul a (nextCounts (X P tau)
          (resetCounts k T1 T2 lam (zeta (P.R P.b) tau cref H) ellStar)) =
          target (zeta (P.R P.b) tau c H) tauNext (1 / 2) Hnext := by
  intro tauNext
  obtain ⟨N, hN1, hNu, hN⟩ := next_chosen_positive_weights P tau htau c cref H 0 delta
    T1 lam hT1 hlam ellStar E hearly
  refine ⟨N, hN1, hNu, ?_⟩
  intro T2 hT2
  obtain ⟨a, hpos, heq⟩ := hN T2 hT2
  refine ⟨a, hpos, ?_⟩
  intro Hnext
  rw [target_independent_H _ _ _ Hnext 0]
  exact heq

/-- The manuscript's prescribed least integer, with its literal radius. -/
def radiusT2 {o : Type*} [Fintype o] (k : ℕ) (old : Matrix o (Fin (k + 1)) ℚ)
    (T1 lam : ℚ) (zeta0 ellStar targetRow : Fin (k + 1) → ℚ) : ℕ :=
  let r0 := Matrix.vecMul (fun _ : o => 1) old +
    ((k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar
  let mu := targetRow (lastIdx k) / (4 * r0 (lastIdx k))
  let rem := targetRow - mu • r0
  let alpha := rem (lastIdx k) * (T1 * ((k + 1 : ℚ) * lam * zeta0 (lastIdx k)))⁻¹
  Faithful.leastRadiusInteger T1 (T1 * lam * zeta0 (lastIdx k)) alpha
    (Faithful.rowMaxAbs k (Matrix.vecMul rem (Phi1_concrete k zeta0)))

/-- Literal old/early common weight and late inverse weights at that integer. -/
def radiusWeights {o : Type*} [Fintype o] (k : ℕ) (old : Matrix o (Fin (k + 1)) ℚ)
    (T1 lam : ℚ) (zeta0 ellStar targetRow : Fin (k + 1) → ℚ) :
    o ⊕ (Fin (k + 1) ⊕ Fin (k + 1)) → ℚ :=
  let r0 := Matrix.vecMul (fun _ : o => 1) old +
    ((k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar
  let mu := targetRow (lastIdx k) / (4 * r0 (lastIdx k))
  let rem := targetRow - mu • r0
  Sum.elim (fun _ : o => mu) (Sum.elim (fun _ : Fin (k + 1) => mu)
    (Matrix.vecMul rem (Winv_concrete k T1 (radiusT2 k old T1 lam zeta0 ellStar targetRow) lam zeta0)))

theorem radiusT2_weights_spec {o : Type*} [Fintype o]
    (k : ℕ) (old : Matrix o (Fin (k + 1)) ℚ)
    (T1 lam : ℚ) (zeta0 ellStar targetRow : Fin (k + 1) → ℚ)
    (hT1 : 0 < T1) (hlam : 0 < lam) (hzeta : 0 < zeta0 (lastIdx k))
    (htarget : 0 < targetRow (lastIdx k))
    (hr0 : 0 < (Matrix.vecMul (fun _ => 1) old +
      ((k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar) (lastIdx k)) :
    let T2 := radiusT2 k old T1 lam zeta0 ellStar targetRow
    let a := radiusWeights k old T1 lam zeta0 ellStar targetRow
    T1 < (T2 : ℚ) ∧ T1 * lam * zeta0 (lastIdx k) < (T2 : ℚ) ∧ 1 < (T2 : ℚ) ∧
      (∀ i, 0 < a i) ∧
      Matrix.vecMul a (Faithful.coneTable k old T1 T2 lam zeta0 ellStar) = targetRow := by
  let r0 := Matrix.vecMul (fun _ : o => 1) old +
    ((k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar
  let mu := targetRow (lastIdx k) / (4 * r0 (lastIdx k))
  let rem := targetRow - mu • r0
  let alpha := rem (lastIdx k) * (T1 * ((k + 1 : ℚ) * lam * zeta0 (lastIdx k)))⁻¹
  let B := Faithful.rowMaxAbs k (Matrix.vecMul rem (Phi1_concrete k zeta0))
  let T2 := radiusT2 k old T1 lam zeta0 ellStar targetRow
  have hres := Faithful.residual_leading k targetRow r0 htarget hr0
  have hmu : 0 < mu := hres.1
  have hrem : 0 < rem (lastIdx k) := hres.2.2
  have halpha : 0 < alpha := mul_pos hrem (inv_pos.mpr (by positivity))
  have hN : Faithful.paperRadius T1 (T1 * lam * zeta0 (lastIdx k)) alpha B < (T2 : ℚ) :=
    Faithful.leastRadiusInteger_spec _ _ _ _
  change max (max T1 (T1 * lam * zeta0 (lastIdx k))) (max 1 (2 * B / alpha)) < (T2 : ℚ) at hN
  have hN1 := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNu := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNone := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hrad := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hT2 : (0 : ℚ) < T2 := lt_trans (by norm_num) hNone
  have hTrad : 2 * B < alpha * (T2 : ℚ) := by
    simpa [mul_comm] using (div_lt_iff₀ halpha).mp hrad
  have hlate := prop_8_1_late_weights_concrete rem T1 T2 lam zeta0
    (ne_of_gt hT1) (ne_of_gt hlam) (ne_of_gt hzeta) B halpha
    (Faithful.abs_le_rowMaxAbs k (Matrix.vecMul rem (Phi1_concrete k zeta0)))
    hT2 hTrad targetRow r0 mu rfl
  refine ⟨hN1, hNu, hNone, ?_, ?_⟩
  · intro i
    rcases i with i | (i | i)
    · exact hmu
    · exact hmu
    · exact (hlate.1 i).2
  · change Matrix.vecMul (Sum.elim (fun _ : o => mu)
        (Sum.elim (fun _ : Fin (k + 1) => mu)
          (Matrix.vecMul rem (Winv_concrete k T1 T2 lam zeta0))))
        (Matrix.fromRows old (Matrix.fromRows _ _)) = targetRow
    rw [Matrix.sumElim_vecMul_fromRows, Matrix.sumElim_vecMul_fromRows,
      Faithful.const_vecMul mu old, Faithful.const_vecMul mu _, Faithful.early_row_sum]
    have he : mu • Matrix.vecMul (fun _ => 1) old +
        (mu • (((k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar) +
          Matrix.vecMul (Matrix.vecMul rem (Winv_concrete k T1 T2 lam zeta0))
            (W_concrete k T1 T2 lam zeta0)) =
        mu • r0 + Matrix.vecMul (Matrix.vecMul rem (Winv_concrete k T1 T2 lam zeta0))
            (W_concrete k T1 T2 lam zeta0) := by
      dsimp [r0]
      simp only [smul_add]
      abel
    rw [he]
    exact hlate.2

/-- The value is the least natural integer strictly above the exact displayed
radius, not merely an unspecified sufficiently large choice. -/
theorem radiusT2_minimal {o : Type*} [Fintype o] (k : ℕ)
    (old : Matrix o (Fin (k + 1)) ℚ) (T1 lam : ℚ) (zeta0 ellStar targetRow : Fin (k + 1) → ℚ) :
    let r0 := Matrix.vecMul (fun _ : o => 1) old +
      ((k + 1 : ℚ) * T1 * lam) • zeta0 + ellStar
    let mu := targetRow (lastIdx k) / (4 * r0 (lastIdx k))
    let rem := targetRow - mu • r0
    let alpha := rem (lastIdx k) * (T1 * ((k + 1 : ℚ) * lam * zeta0 (lastIdx k)))⁻¹
    ∀ n : ℕ, Faithful.paperRadius T1 (T1 * lam * zeta0 (lastIdx k)) alpha
      (Faithful.rowMaxAbs k (Matrix.vecMul rem (Phi1_concrete k zeta0))) < (n : ℚ) →
      radiusT2 k old T1 lam zeta0 ellStar targetRow ≤ n := by
  exact Faithful.leastRadiusInteger_minimal _ _ _ _

noncomputable def nextTarget {k : ℕ} (P : FaithfulClock.Clock k)
    (tau : ℕ) (c cref H delta T1 lam : ℚ) (ellStar : Fin (k + 1) → ℚ)
    (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) : Fin (k + 1) → ℚ :=
  target (zeta (P.R P.b) tau c H)
    (nextScale k (by have := P.order_ge_two; omega) (S_mid P tau c H delta)
      (X P tau) (zeta (P.R P.b) tau c H) (zeta (P.R P.b) tau cref H) ellStar T1 lam E)
    (1 / 2) 0

/-- The fully specified T2 of v15, computed after T1 and before Q. -/
noncomputable def prescribedT2 {k : ℕ} (P : FaithfulClock.Clock k)
    (tau : ℕ) (c cref H delta T1 lam : ℚ) (ellStar : Fin (k + 1) → ℚ)
    (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) : ℕ :=
  radiusT2 k (X P tau * T_mat (k + 1)) T1 lam (zeta (P.R P.b) tau cref H) ellStar
    (nextTarget P tau c cref H delta T1 lam ellStar E)

noncomputable def prescribedWeights {k : ℕ} (P : FaithfulClock.Clock k)
    (tau : ℕ) (c cref H delta T1 lam : ℚ) (ellStar : Fin (k + 1) → ℚ)
    (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :
    OldAct P ⊕ (Fin (k + 1) ⊕ Fin (k + 1)) → ℚ :=
  radiusWeights k (X P tau * T_mat (k + 1)) T1 lam (zeta (P.R P.b) tau cref H) ellStar
    (nextTarget P tau c cref H delta T1 lam ellStar E)

/-- The prescribed least T2 and prescribed weights work for the actual next
target, simultaneously for every later height baseline. -/
theorem prescribedT2_weights_spec {k : ℕ} (P : FaithfulClock.Clock k)
    (tau : ℕ) (htau : 0 < tau) (c cref H delta T1 lam : ℚ)
    (hT1 : 0 < T1) (hlam : 0 < lam) (ellStar : Fin (k + 1) → ℚ)
    (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hearly : 0 < T1 * lam * zeta (P.R P.b) tau cref H (lastIdx k) + ellStar (lastIdx k)) :
    let tauNext := nextScale k (by have := P.order_ge_two; omega)
      (S_mid P tau c H delta) (X P tau) (zeta (P.R P.b) tau c H)
      (zeta (P.R P.b) tau cref H) ellStar T1 lam E
    let T2 := prescribedT2 P tau c cref H delta T1 lam ellStar E
    let a := prescribedWeights P tau c cref H delta T1 lam ellStar E
    T1 < (T2 : ℚ) ∧ T1 * lam * zeta (P.R P.b) tau cref H (lastIdx k) < (T2 : ℚ) ∧
      1 < (T2 : ℚ) ∧ (∀ i, 0 < a i) ∧ ∀ Hnext : ℚ,
        Matrix.vecMul a (nextCounts (X P tau)
          (resetCounts k T1 T2 lam (zeta (P.R P.b) tau cref H) ellStar)) =
          target (zeta (P.R P.b) tau c H) tauNext (1 / 2) Hnext := by
  intro tauNext T2 a
  have hz0 : 0 < zeta (P.R P.b) tau cref H (lastIdx k) :=
    zeta_leading_pos P.order_ge_two _ tau htau P.leading_height cref H
  have hz : 0 < zeta (P.R P.b) tau c H (Fin.last k) :=
    zeta_leading_pos P.order_ge_two _ tau htau P.leading_height c H
  have htarget : 0 < nextTarget P tau c cref H delta T1 lam ellStar E (lastIdx k) :=
    target_leading_pos (by have := P.order_ge_two; omega) _ hz tauNext
      (nextScale_pos _ _ _ _ _ _ _ _ _ _) _ _
  have hr0 := Faithful.r0_leading_positive k (X P tau * T_mat (k + 1)) T1 lam
    (zeta (P.R P.b) tau cref H) ellStar (shifted_X_leading_nonneg P tau)
    (mul_pos (mul_pos hT1 hlam) hz0) hearly
  obtain ⟨hT, hu, h1, ha, heq⟩ := radiusT2_weights_spec k (X P tau * T_mat (k + 1))
    T1 lam (zeta (P.R P.b) tau cref H) ellStar
    (nextTarget P tau c cref H delta T1 lam ellStar E) hT1 hlam hz0 htarget hr0
  refine ⟨hT, hu, h1, ha, ?_⟩
  intro Hnext
  rw [target_independent_H _ _ _ Hnext 0]
  exact heq

#print axioms target_cone_iff
#print axioms target_leading_pos
#print axioms nextScores_transpose_nextCounts
#print axioms concrete_reset_sum
#print axioms next_clock_eq
#print axioms concrete_next_summary
#print axioms next_target_positive_weights
#print axioms actual_next_pair_eq_fixed
#print axioms next_chosen_positive_weights
#print axioms next_chosen_positive_weights_all_baselines
#print axioms nextCorrection_higher_tests
#print axioms radiusT2_weights_spec
#print axioms radiusT2_minimal
#print axioms prescribedT2_weights_spec

end Karlin.FaithfulNextTables
