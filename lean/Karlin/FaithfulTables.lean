import Karlin.FaithfulClock
import Karlin.FaithfulScale
import Karlin.FaithfulPolynomialRoutes
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Literal v15 height and old-action coefficient tables

These definitions use the dyadic transfer matrices, the prescribed backward
antiderivative, and the gateway block of equations (y) and (old).
-/

namespace Karlin.FaithfulTables
open scoped BigOperators Matrix
open FaithfulClock

theorem vecMul_N_apply {w : ℕ} (v : Fin w → ℚ) (j : Fin w) :
    Matrix.vecMul v (N_mat w) j =
      if h : j.val + 1 < w then v ⟨j.val + 1, h⟩ else 0 := by
  exact mul_N_mat_apply (fun _ : Unit => v) () j

theorem vecMul_T_apply {w : ℕ} (v : Fin w → ℚ) (j : Fin w) :
    Matrix.vecMul v (T_mat w) j = v j +
      if h : j.val + 1 < w then v ⟨j.val + 1, h⟩ else 0 := by
  rw [T_mat, Matrix.vecMul_add, Matrix.vecMul_one]
  exact congrArg (v j + ·) (vecMul_N_apply v j)

/-- The unique backward antiderivative with prescribed constant coefficient.
The input must have zero last coefficient for the specification below. -/
def antiderivative {k : ℕ} (g : Fin (k + 1) → ℚ) (H : ℚ) : Fin (k + 1) → ℚ :=
  Fin.cases H (fun i => Matrix.vecMul g (T_mat (k + 1)) i.castSucc)

@[simp] theorem antiderivative_zero {k : ℕ} (g : Fin (k + 1) → ℚ) (H : ℚ) :
    antiderivative g H 0 = H := rfl

@[simp] theorem antiderivative_succ {k : ℕ} (g : Fin (k + 1) → ℚ) (H : ℚ)
    (i : Fin k) :
    antiderivative g H i.succ = Matrix.vecMul g (T_mat (k + 1)) i.castSucc := rfl

theorem antiderivative_forward {k : ℕ} (g : Fin (k + 1) → ℚ) (H : ℚ)
    (hg : g (Fin.last k) = 0) :
    Matrix.vecMul (antiderivative g H) (N_mat (k + 1)) =
      Matrix.vecMul g (T_mat (k + 1)) := by
  ext j
  rw [vecMul_N_apply]
  by_cases hj : j.val + 1 < k + 1
  · rw [dif_pos hj]
    let i : Fin k := ⟨j.val, by omega⟩
    change antiderivative g H i.succ = Matrix.vecMul g (T_mat (k + 1)) i.castSucc
    rfl
  · rw [dif_neg hj, vecMul_T_apply, dif_neg hj, add_zero]
    have heq : j = Fin.last k := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [heq, hg]

theorem difference_mul_shift (k : ℕ) :
    (1 - B_mat (k + 1)) * T_mat (k + 1) = N_mat (k + 1) := by
  rw [Matrix.sub_mul, Matrix.one_mul, (B_mat_mul_T_mat (k + 1)).1, T_mat]
  abel

theorem antiderivative_spec {k : ℕ} (g : Fin (k + 1) → ℚ) (H : ℚ)
    (hg : g (Fin.last k) = 0) :
    Matrix.vecMul (antiderivative g H) (1 - B_mat (k + 1)) = g := by
  have h := antiderivative_forward g H hg
  have hd : Matrix.vecMul
      (Matrix.vecMul (antiderivative g H) (1 - B_mat (k + 1)))
      (T_mat (k + 1)) = Matrix.vecMul g (T_mat (k + 1)) := by
    rw [Matrix.vecMul_vecMul, difference_mul_shift]
    exact h
  have hm := congrArg (fun v => Matrix.vecMul v (B_mat (k + 1))) hd
  simpa only [Matrix.vecMul_vecMul, Matrix.mul_assoc, (B_mat_mul_T_mat (k + 1)).2,
    Matrix.mul_one, Matrix.vecMul_one] using hm

theorem antiderivative_unique {k : ℕ} (g f : Fin (k + 1) → ℚ) (H : ℚ)
    (hzero : f 0 = H)
    (hdiff : Matrix.vecMul f (1 - B_mat (k + 1)) = g) :
    f = antiderivative g H := by
  have hf : Matrix.vecMul f (N_mat (k + 1)) = Matrix.vecMul g (T_mat (k + 1)) := by
    rw [← hdiff, Matrix.vecMul_vecMul, difference_mul_shift]
  funext j
  induction j using Fin.cases with
  | zero => exact hzero
  | succ i =>
      have hh := congrFun hf i.castSucc
      rw [vecMul_N_apply, dif_pos (by simpa using i.isLt)] at hh
      exact hh

/-- The right hand side of the backward-height equation (y). -/
def increment {k : ℕ} (chi : Fin k → ℚ) (tau : ℕ) (c : ℚ) : Fin (k + 1) → ℚ :=
  Matrix.vecMul chi (E_2tau_mat k tau - E_tau_mat k tau) + c • e0_row (k + 1)

theorem increment_last {k : ℕ} (hk : 0 < k) (chi : Fin k → ℚ) (tau : ℕ) (c : ℚ) :
    increment chi tau c (Fin.last k) = 0 := by
  simp only [increment, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.vecMul, dotProduct, Matrix.sub_apply]
  simp [Fin.last, E_tau_mat_last_col_zero, E_2tau_mat_last_col_zero, e0_row, Nat.ne_of_gt hk]

def zeta {k : ℕ} (chi : Fin k → ℚ) (tau : ℕ) (c H : ℚ) : Fin (k + 1) → ℚ :=
  antiderivative (increment chi tau c) H

theorem zeta_spec {k : ℕ} (hk : 0 < k) (chi : Fin k → ℚ) (tau : ℕ) (c H : ℚ) :
    Matrix.vecMul (zeta chi tau c H) (1 - B_mat (k + 1)) = increment chi tau c ∧
      zeta chi tau c H 0 = H :=
  ⟨antiderivative_spec _ H (increment_last hk chi tau c), rfl⟩

theorem zeta_unique {k : ℕ} (chi : Fin k → ℚ) (tau : ℕ) (c H : ℚ)
    (f : Fin (k + 1) → ℚ) (hzero : f 0 = H)
    (hdiff : Matrix.vecMul f (1 - B_mat (k + 1)) = increment chi tau c) :
    f = zeta chi tau c H := antiderivative_unique _ f H hzero hdiff

def translation {k : ℕ} (chi : Fin k → ℚ) (tau : ℕ) (c H : ℚ) : Fin (k + 1) → ℚ :=
  Matrix.vecMul (zeta chi tau c H) (B_mat (k + 1)) - Matrix.vecMul chi (E_tau_mat k tau)

theorem antiderivative_last {k : ℕ} (hk : 0 < k) (g : Fin (k + 1) → ℚ)
    (H : ℚ) (hg : g (Fin.last k) = 0) :
    antiderivative g H (Fin.last k) = g ⟨k - 1, by omega⟩ := by
  let i : Fin k := ⟨k - 1, by omega⟩
  have he : Fin.last k = i.succ := Fin.ext (by simp [i]; omega)
  rw [he, antiderivative_succ, vecMul_T_apply, dif_pos (by simp [i]; omega)]
  have ht : (⟨i.castSucc.val + 1, by simp [i]; omega⟩ : Fin (k + 1)) = Fin.last k :=
    Fin.ext (by simp [i]; omega)
  rw [ht, hg, add_zero]
  rfl

theorem vecMul_E_penultimate {k : ℕ} (hk : 0 < k) (chi : Fin k → ℚ) (tau : ℕ) :
    Matrix.vecMul chi (E_tau_mat k tau) ⟨k - 1, by omega⟩ =
      chi ⟨k - 1, by omega⟩ * (tau : ℚ) ^ (k - 1) := by
  rw [Matrix.vecMul, dotProduct, Finset.sum_eq_single ⟨k - 1, by omega⟩]
  · rw [E_tau_mat, Matrix.of_apply, E_tilde_diag]
  · intro i _ hi
    have hlt : i.val < k - 1 := by
      have hn : i.val ≠ k - 1 := fun h => hi (Fin.ext h)
      have := i.isLt
      omega
    have hz : E_tau_mat k tau i ⟨k - 1, by omega⟩ = 0 :=
      E_tilde_eq_zero_of_lt tau hlt
    rw [hz, mul_zero]
  · simp

theorem zeta_leading {k : ℕ} (hk : 2 ≤ k) (chi : Fin k → ℚ) (tau : ℕ) (c H : ℚ) :
    zeta chi tau c H (Fin.last k) =
      chi ⟨k - 1, by omega⟩ * (tau : ℚ) ^ (k - 1) * ((2 : ℚ) ^ (k - 1) - 1) := by
  -- Apply the actual backward equation to the ordinary polynomial.  Exact
  -- degree drop supplies its top coefficient, including the degenerate cases.
  have he := FaithfulPolynomialRoutes.rowPoly_backwardDifference (zeta chi tau c H)
  rw [(zeta_spec (by omega) chi tau c H).1] at he
  rw [increment, FaithfulPolynomialRoutes.rowPoly_increment_eq] at he
  have hc := congrArg (fun p : Polynomial ℚ => p.coeff (k-1)) he
  dsimp only at hc
  rw [FaithfulPolynomialRoutes.backwardDifference_top_coefficient (k := k) _ (by omega)
    (by simpa using FaithfulGrowth.rowPoly_natDegree_le (zeta chi tau c H))] at hc
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_C,
    if_neg (by omega : k-1 ≠ 0), add_zero] at hc
  have hz := FaithfulGrowth.rowPoly_top_coeff (Nat.succ_pos k) (zeta chi tau c H)
  have hh := FaithfulGrowth.rowPoly_top_coeff (by omega : 0<k) chi
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at hz
  rw [hz, hh, mul_pow] at hc
  have hfac : (k.factorial : ℚ) = (k : ℚ)*((k-1).factorial : ℚ) := by
    conv_lhs => rw [show k=k-1+1 by omega, Nat.factorial_succ]
    push_cast
    congr 1
    exact_mod_cast (by omega : k-1+1=k)
  rw [hfac] at hc
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hf0 : ((k-1).factorial : ℚ) ≠ 0 := by positivity
  field_simp at hc
  exact hc

theorem zeta_leading_pos {k : ℕ} (hk : 2 ≤ k) (chi : Fin k → ℚ) (tau : ℕ)
    (htau : 0 < tau) (hchi : 0 < chi ⟨k - 1, by omega⟩) (c H : ℚ) :
    0 < zeta chi tau c H (Fin.last k) := by
  rw [zeta_leading hk]
  have hpow : (1 : ℚ) < 2 ^ (k - 1) := one_lt_pow₀ (by norm_num) (by omega)
  have ht : (0 : ℚ) < tau := by exact_mod_cast htau
  exact mul_pos (mul_pos hchi (pow_pos ht _)) (sub_pos.mpr hpow)

def L (k tau : ℕ) : Matrix (Fin k) (Fin (k + 1)) ℚ :=
  E_tau_mat k tau * T_mat (k + 1) - E_2tau_mat k tau

def f {k : ℕ} (chi : Fin k → ℚ) (tau : ℕ) (c : ℚ) : Fin (k + 1) → ℚ :=
  c • e0_row (k + 1) - Matrix.vecMul chi (L k tau)

theorem translation_forward {k : ℕ} (hk : 0 < k) (chi : Fin k → ℚ)
    (tau : ℕ) (c H : ℚ) :
    Matrix.vecMul (translation chi tau c H) (N_mat (k + 1)) = f chi tau c := by
  rw [translation, Matrix.sub_vecMul, Matrix.vecMul_vecMul,
    (B_mat_mul_N_mat (k + 1)).1, (zeta_spec hk chi tau c H).1]
  simp only [f, L, increment, Matrix.vecMul_sub, Matrix.vecMul_vecMul, T_mat,
    Matrix.mul_add, Matrix.mul_one, Matrix.vecMul_add]
  abel

theorem antiderivative_add_e0 {k : ℕ} (g : Fin (k + 1) → ℚ) (H d : ℚ) :
    antiderivative (g + d • e0_row (k + 1)) H =
      antiderivative g H + d • e1_row (k + 1) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [antiderivative, e1_row]
  | succ i =>
      simp only [antiderivative_succ, Matrix.add_vecMul, Matrix.smul_vecMul,
        T_mat, Matrix.vecMul_add, Matrix.vecMul_one, e0_row_mul_N_mat, add_zero,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simp [antiderivative, T_mat, Matrix.vecMul_add, Matrix.vecMul_one,
        e0_row, e1_row]
      ring

theorem zeta_add_gain {k : ℕ} (chi : Fin k → ℚ) (tau : ℕ) (c c0 H : ℚ) :
    zeta chi tau c H = zeta chi tau c0 H + (c - c0) • e1_row (k + 1) := by
  have hi : increment chi tau c = increment chi tau c0 + (c - c0) • e0_row (k + 1) := by
    ext j
    simp only [increment, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  change antiderivative (increment chi tau c) H = _
  rw [hi, antiderivative_add_e0]
  rfl

theorem zeta_sub_gain {k : ℕ} (chi : Fin k → ℚ) (tau : ℕ) (c c0 H : ℚ) :
    zeta chi tau c H - zeta chi tau c0 H = (c - c0) • e1_row (k + 1) := by
  rw [zeta_add_gain chi tau c c0 H]
  abel

def psi {k : ℕ} (chi : Fin k → ℚ) (tau : ℕ) (c H : ℚ) : Fin (k + 1) → ℚ :=
  Matrix.vecMul (zeta chi tau c H) (B_mat (k + 1)) - zeta chi tau c H

theorem psi_eq_neg_increment {k : ℕ} (hk : 0 < k) (chi : Fin k → ℚ)
    (tau : ℕ) (c H : ℚ) : psi chi tau c H = -increment chi tau c := by
  have hh := (zeta_spec hk chi tau c H).1
  rw [Matrix.vecMul_sub, Matrix.vecMul_one] at hh
  rw [psi, ← hh]
  abel

theorem psi_sub_gain {k : ℕ} (hk : 0 < k) (chi : Fin k → ℚ)
    (tau : ℕ) (c c0 H : ℚ) :
    psi chi tau c H - psi chi tau c0 H = -(c - c0) • e0_row (k + 1) := by
  rw [psi_eq_neg_increment hk, psi_eq_neg_increment hk]
  ext j
  simp only [increment, Pi.sub_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

variable {k : ℕ} (P : Clock k)

abbrev OldAct := Fin P.m ⊕ Fin 1

def oldGame : Matrix (OldAct P) (OldAct P) ℚ :=
  Matrix.fromBlocks P.A (fun i _ => -(P.A P.b i + P.v i))
    (fun _ j => P.A P.b j + P.v j) 0

def X (tau : ℕ) : Matrix (OldAct P) (Fin (k + 1)) ℚ :=
  Matrix.fromRows (P.countTable * F_tau_mat k tau) (fun _ : Fin 1 => e0_row (k + 1))

def S (tau : ℕ) (c H delta : ℚ) : Matrix (OldAct P) (Fin (k + 1)) ℚ :=
  Matrix.fromRows
    (P.R * E_tau_mat k tau + outerProd (fun _ => 1) (translation (P.R P.b) tau c H))
    (fun _ : Fin 1 => Matrix.vecMul (zeta (P.R P.b) tau c H) (B_mat (k + 1)) -
      Matrix.vecMul P.v (P.countTable * F_tau_mat k tau) + delta • e0_row (k + 1))

def S_mid (tau : ℕ) (c H delta : ℚ) := S P tau c H delta + oldGame P * X P tau

def D (tau : ℕ) (c H delta : ℚ) := S P tau c H delta * N_mat (k + 1) - oldGame P * X P tau

theorem D_eq_shift_difference (tau : ℕ) (c H delta : ℚ) :
    D P tau c H delta = S P tau c H delta * T_mat (k + 1) - S_mid P tau c H delta := by
  simp only [D, S_mid, T_mat, Matrix.mul_add, Matrix.mul_one]
  abel

theorem oldGame_skew : IsSkewSymmetric (oldGame P) := by
  intro x y
  cases x <;> cases y <;> simp [oldGame, Matrix.fromBlocks]
  exact P.skew _ _

theorem oldGame_X_parent (tau : ℕ) (i : Fin P.m) :
    (oldGame P * X P tau) (Sum.inl i) =
      (P.A * (P.countTable * F_tau_mat k tau)) i -
        (P.A P.b i + P.v i) • e0_row (k + 1) := by
  ext j
  simp [oldGame, X, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromRows,
    Matrix.fromBlocks, sub_eq_add_neg]
  ring

theorem counter_bundle (tau : ℕ) :
    Matrix.vecMul P.v (P.countTable * F_tau_mat k tau) =
      Matrix.vecMul (e0_row k) (F_tau_mat k tau) := by
  have hv : Matrix.vecMul P.v P.countTable = e0_row k := P.counter_table
  rw [← Matrix.vecMul_vecMul, hv]

theorem oldGame_X_gateway (tau : ℕ) :
    (oldGame P * X P tau) (Sum.inr 0) =
      Matrix.vecMul (P.R P.b) (E_2tau_mat k tau - E_tau_mat k tau) +
        Matrix.vecMul (e0_row k) (F_tau_mat k tau) := by
  have hbase := bundled_parent_transfer P.A P.R P.countTable tau P.clock_eq
  ext j
  change (oldGame P * X P tau) (Sum.inr 0) j = _
  simp only [oldGame, X, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, add_mul, Finset.sum_add_distrib]
  change (P.A * (P.countTable * F_tau_mat k tau)) P.b j +
    Matrix.vecMul P.v (P.countTable * F_tau_mat k tau) j = _
  rw [hbase, counter_bundle]
  rfl

theorem S_parent (tau : ℕ) (c H delta : ℚ) (i : Fin P.m) :
    S P tau c H delta (Sum.inl i) =
      (P.R * E_tau_mat k tau) i + translation (P.R P.b) tau c H := by
  ext j
  simp [S, outerProd]

theorem S_gateway (tau : ℕ) (c H delta : ℚ) :
    S P tau c H delta (Sum.inr 0) =
      Matrix.vecMul (zeta (P.R P.b) tau c H) (B_mat (k + 1)) -
      Matrix.vecMul (e0_row k) (F_tau_mat k tau) + delta • e0_row (k + 1) := by
  change Matrix.vecMul (zeta (P.R P.b) tau c H) (B_mat (k + 1)) -
      Matrix.vecMul P.v (P.countTable * F_tau_mat k tau) + delta • e0_row (k + 1) = _
  rw [counter_bundle]

theorem D_parent (tau : ℕ) (c H delta : ℚ) (i : Fin P.m) :
    D P tau c H delta (Sum.inl i) =
      (P.R * L k tau) i + f (P.R P.b) tau c +
        (P.A P.b i + P.v i) • e0_row (k + 1) := by
  change Matrix.vecMul (S P tau c H delta (Sum.inl i)) (N_mat (k + 1)) -
    (oldGame P * X P tau) (Sum.inl i) = _
  rw [S_parent, oldGame_X_parent, Matrix.add_vecMul,
    translation_forward (by have := P.order_ge_two; omega)]
  have hbase := bundled_parent_transfer P.A P.R P.countTable tau P.clock_eq
  rw [hbase]
  simp only [L, T_mat, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one]
  ext j
  change ((P.R * E_tau_mat k tau) * N_mat (k + 1)) i j +
    f (P.R P.b) tau c j -
    ((P.R * E_2tau_mat k tau - P.R * E_tau_mat k tau) i j -
      ((P.A P.b i + P.v i) • e0_row (k + 1)) j) = _
  simp only [Matrix.mul_assoc, Matrix.add_apply, Matrix.sub_apply, Pi.add_apply,
    Pi.sub_apply]
  ring

theorem D_gateway (tau : ℕ) (c H delta : ℚ) :
    D P tau c H delta (Sum.inr 0) = c • e0_row (k + 1) -
      Matrix.vecMul (Matrix.vecMul (e0_row k) (F_tau_mat k tau)) (T_mat (k + 1)) := by
  change Matrix.vecMul (S P tau c H delta (Sum.inr 0)) (N_mat (k + 1)) -
    (oldGame P * X P tau) (Sum.inr 0) = _
  rw [S_gateway, oldGame_X_gateway, Matrix.add_vecMul, Matrix.sub_vecMul,
    Matrix.smul_vecMul, e0_row_mul_N_mat, smul_zero, add_zero,
    Matrix.vecMul_vecMul, (B_mat_mul_N_mat (k + 1)).1,
    (zeta_spec (by have := P.order_ge_two; omega) (P.R P.b) tau c H).1]
  simp only [increment, T_mat, Matrix.vecMul_add, Matrix.vecMul_one]
  abel

theorem D_independent_delta (tau : ℕ) (c H delta delta' : ℚ) :
    D P tau c H delta = D P tau c H delta' := by
  ext i j
  rcases i with i | i
  · rw [show D P tau c H delta (Sum.inl i) j = _ from congrFun (D_parent P tau c H delta i) j,
      show D P tau c H delta' (Sum.inl i) j = _ from congrFun (D_parent P tau c H delta' i) j]
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact congrFun ((D_gateway P tau c H delta).trans (D_gateway P tau c H delta').symm) j

theorem D_sub_gain (tau : ℕ) (c c0 H delta : ℚ) :
    D P tau c H delta - D P tau c0 H delta =
      (c - c0) • outerProd (fun _ : OldAct P => 1) (e0_row (k + 1)) := by
  ext i j
  rcases i with i | i
  · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, outerProd,
      Matrix.of_apply, one_mul]
    rw [congrFun (D_parent P tau c H delta i) j, congrFun (D_parent P tau c0 H delta i) j]
    simp only [f, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, outerProd,
      Matrix.of_apply, one_mul]
    rw [congrFun (D_gateway P tau c H delta) j, congrFun (D_gateway P tau c0 H delta) j]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem D_eq_fromRows (tau : ℕ) (c H delta : ℚ) :
    D P tau c H delta = Matrix.fromRows
      (P.R * L k tau + outerProd (fun _ => 1) (f (P.R P.b) tau c) +
        outerProd (fun i => P.A P.b i + P.v i) (e0_row (k + 1)))
      (fun _ : Fin 1 => c • e0_row (k + 1) -
        Matrix.vecMul (Matrix.vecMul (e0_row k) (F_tau_mat k tau)) (T_mat (k + 1))) := by
  ext i j
  rcases i with i | i
  · rw [congrFun (D_parent P tau c H delta i) j]
    simp [outerProd]
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact congrFun (D_gateway P tau c H delta) j

theorem gateway_counter_bundle (tau : ℕ) :
    Matrix.vecMul (fun i => P.A P.b i + P.v i) (P.countTable * F_tau_mat k tau) =
      Matrix.vecMul (P.R P.b) (E_2tau_mat k tau - E_tau_mat k tau) +
        Matrix.vecMul (e0_row k) (F_tau_mat k tau) := by
  have hbase := bundled_parent_transfer P.A P.R P.countTable tau P.clock_eq
  change Matrix.vecMul (P.A P.b + P.v) _ = _
  rw [Matrix.add_vecMul, counter_bundle]
  ext j
  change (P.A * (P.countTable * F_tau_mat k tau)) P.b j + _ = _
  rw [hbase]
  rfl

theorem singleton_rows_product {w : Type*} [Fintype w] (u v : w → ℚ) :
    (Matrix.of (fun (_ : Fin 1) (j : w) => u j))ᵀ *
      Matrix.of (fun (_ : Fin 1) (j : w) => v j) = outerProd u v := by
  ext i j
  simp [Matrix.mul_apply, outerProd]

/-- Equation (summary), for the actual deficit and actual dyadic counts. -/
theorem DX_summary (tau : ℕ) (c H delta : ℚ) :
    (D P tau c H delta)ᵀ * X P tau =
      (L k tau)ᵀ * (P.Rᵀ * P.countTable) * F_tau_mat k tau +
      outerProd (f (P.R P.b) tau c)
        (Matrix.vecMul (Matrix.vecMul (fun _ => 1) P.countTable) (F_tau_mat k tau)) +
      outerProd (e0_row (k + 1))
        (Matrix.vecMul (P.R P.b) (E_2tau_mat k tau - E_tau_mat k tau) +
          Matrix.vecMul (e0_row k) (F_tau_mat k tau)) +
      outerProd (c • e0_row (k + 1) -
        Matrix.vecMul (Matrix.vecMul (e0_row k) (F_tau_mat k tau)) (T_mat (k + 1)))
        (e0_row (k + 1)) := by
  rw [D_eq_fromRows, X, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows]
  simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.transpose_mul,
    outerProd_transpose, outerProd_mul]
  rw [gateway_counter_bundle]
  simp only [Matrix.mul_assoc, Matrix.vecMul_vecMul]
  congr 1
  ext i j
  simp [Matrix.mul_apply, outerProd]

/-- The nonconstant square block of the actual dyadic bundle transfer. -/
def Fblock (k tau : ℕ) : Matrix (Fin k) (Fin k) ℚ :=
  Matrix.of fun i j => F_tau_mat k tau i j.succ

theorem Fblock_det_ne_zero (k tau : ℕ) (htau : 0 < tau) : (Fblock k tau).det ≠ 0 := by
  have htri : (Fblock k tau).BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact F_tau_mat_eq_zero_of_gt k tau i j.succ (Nat.add_lt_add_right hij 1)
  rw [Matrix.det_of_lowerTriangular _ htri]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  change F_tau_mat k tau i ⟨i.val + 1, by omega⟩ ≠ 0
  rw [F_tau_mat_diag]
  apply mul_ne_zero
  · exact pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt htau)
  · exact ne_of_gt (sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega)))

theorem X_full_column_rank (tau : ℕ) (htau : 0 < tau) :
    Function.Injective (fun x => (X P tau).mulVec x) := by
  intro x y hxy
  have hF : (F_tau_mat k tau).mulVec x = (F_tau_mat k tau).mulVec y := by
    apply P.full_column_rank
    ext i
    have h := congrFun hxy (Sum.inl i)
    simpa only [X, Matrix.fromRows_mulVec, Sum.elim_inl,
      Matrix.mulVec_mulVec] using h
  have h0 : x 0 = y 0 := by
    have h := congrFun hxy (Sum.inr 0)
    change dotProduct (e0_row (k + 1)) x = dotProduct (e0_row (k + 1)) y at h
    simpa [dotProduct, Fin.sum_univ_succ, e0_row] using h
  have htail : (Fblock k tau).mulVec (fun i => x i.succ) =
      (Fblock k tau).mulVec (fun i => y i.succ) := by
    ext i
    have h := congrFun hF i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h
    rw [h0] at h
    exact add_left_cancel h
  have hinj : Function.Injective (Fblock k tau).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (Fblock_det_ne_zero k tau htau)))
  have hs := hinj htail
  funext i
  induction i using Fin.cases with
  | zero => exact h0
  | succ i => exact congrFun hs i

theorem E_integer (k tau : ℕ) (i : Fin k) (j : Fin (k + 1)) :
    FaithfulScale.IntegerMultiple 1 (E_tau_mat k tau i j) := by
  apply FaithfulScale.binomial_row_integral_of_values (k + 1) (E_tau_mat k tau i)
  intro q _
  change FaithfulScale.IntegerMultiple 1 ((E_tau_mat k tau).mulVec (binomBasis (k + 1) q) i)
  rw [E_tau_mat_mulVec_binomBasis]
  exact ⟨(Nat.choose (tau * q) i.val : ℤ), by simp [binomBasis]⟩

theorem F_integer (k tau : ℕ) (i : Fin k) (j : Fin (k + 1)) :
    FaithfulScale.IntegerMultiple 1 (F_tau_mat k tau i j) := by
  apply FaithfulScale.binomial_row_integral_of_values (k + 1) (F_tau_mat k tau i)
  intro q _
  change FaithfulScale.IntegerMultiple 1 ((F_tau_mat k tau).mulVec (binomBasis (k + 1) q) i)
  rw [F_tau_mat_mulVec_binomBasis]
  apply FaithfulScale.integerMultiple_sum
  intro s _
  exact ⟨(Nat.choose s i.val : ℤ), by simp [binomBasis]⟩

theorem X_integer (tau : ℕ) (i : OldAct P) (j : Fin (k + 1)) :
    FaithfulScale.IntegerMultiple 1 (X P tau i j) := by
  rcases i with i | i
  · change FaithfulScale.IntegerMultiple 1 (∑ a, P.countTable i a * F_tau_mat k tau a j)
    apply FaithfulScale.integerMultiple_sum
    intro a _
    obtain ⟨z, hz⟩ := F_integer k tau a j
    refine ⟨P.C i a * z, ?_⟩
    simpa [FaithfulClock.Clock.countTable, hz] using congrArg (fun x : ℚ => (P.C i a : ℚ) * x) hz
  · change FaithfulScale.IntegerMultiple 1 (e0_row (k + 1) j)
    by_cases hj : j.val = 0
    · exact ⟨1, by simp [e0_row, hj]⟩
    · exact ⟨0, by simp [e0_row, hj]⟩

theorem vecMul_B_last {k : ℕ} (v : Fin (k + 1) → ℚ) :
    Matrix.vecMul v (B_mat (k + 1)) (Fin.last k) = v (Fin.last k) := by
  rw [Matrix.vecMul, dotProduct, Finset.sum_eq_single (Fin.last k)]
  · simp [B_mat]
  · intro i _ hi
    have hlt : i.val < k := by
      have hn : i.val ≠ k := fun h => hi (Fin.ext h)
      have := i.isLt
      omega
    simp [B_mat, not_le.mpr hlt, hi]
  · simp

theorem vecMul_E_last {k : ℕ} (chi : Fin k → ℚ) (tau : ℕ) :
    Matrix.vecMul chi (E_tau_mat k tau) (Fin.last k) = 0 := by
  simp [Matrix.vecMul, dotProduct, Fin.last, E_tau_mat_last_col_zero]

theorem counter_bundle_last (hk : 2 ≤ k) (tau : ℕ) :
    Matrix.vecMul (e0_row k) (F_tau_mat k tau) (Fin.last k) = 0 := by
  let z : Fin k := ⟨0, by omega⟩
  rw [Matrix.vecMul, dotProduct, Finset.sum_eq_single z]
  · simp [z, e0_row, Fin.last, F_tau_mat_row_zero_last_col_zero k hk tau]
  · intro i _ hi
    have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp [e0_row, hi0]
  · simp

theorem S_entry_row (tau : ℕ) (c H delta : ℚ) :
    S P tau c H delta (Sum.inl P.b) =
      Matrix.vecMul (zeta (P.R P.b) tau c H) (B_mat (k + 1)) := by
  rw [S_parent, translation]
  change Matrix.vecMul (P.R P.b) (E_tau_mat k tau) + _ = _
  abel

theorem S_mid_entry_row (tau : ℕ) (c H delta : ℚ) :
    S_mid P tau c H delta (Sum.inl P.b) =
      zeta (P.R P.b) tau c H - c • e0_row (k + 1) := by
  have hb : P.A P.b P.b = 0 := by have h := P.skew P.b P.b; linarith
  have hz := (zeta_spec (by have := P.order_ge_two; omega) (P.R P.b) tau c H).1
  rw [Matrix.vecMul_sub, Matrix.vecMul_one] at hz
  change S P tau c H delta (Sum.inl P.b) + (oldGame P * X P tau) (Sum.inl P.b) = _
  rw [S_entry_row, oldGame_X_parent, hb, P.counter_entry, zero_add, zero_smul, sub_zero,
    bundled_parent_transfer P.A P.R P.countTable tau P.clock_eq]
  change Matrix.vecMul (zeta (P.R P.b) tau c H) (B_mat (k + 1)) +
    Matrix.vecMul (P.R P.b) (E_2tau_mat k tau - E_tau_mat k tau) = _
  rw [increment] at hz
  ext j
  have hj := congrFun hz j
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
  linarith

theorem S_mid_gateway_row (tau : ℕ) (c H delta : ℚ) :
    S_mid P tau c H delta (Sum.inr 0) =
      zeta (P.R P.b) tau c H - (c - delta) • e0_row (k + 1) := by
  have hz := (zeta_spec (by have := P.order_ge_two; omega) (P.R P.b) tau c H).1
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, increment] at hz
  change S P tau c H delta (Sum.inr 0) + (oldGame P * X P tau) (Sum.inr 0) = _
  rw [S_gateway, oldGame_X_gateway]
  ext j
  have hj := congrFun hz j
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
  linear_combination -hj

theorem oldGame_X_last (tau : ℕ) (i : OldAct P) :
    (oldGame P * X P tau) i (Fin.last k) = 0 := by
  have hk : k ≠ 0 := by have := P.order_ge_two; omega
  rcases i with i | i
  · rw [congrFun (oldGame_X_parent P tau i) (Fin.last k)]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (P.A * (P.countTable * F_tau_mat k tau)) i (Fin.last k) = 0 from
      bundled_parent_transfer_last_col_zero P.A P.R P.countTable tau P.clock_eq i]
    simp [e0_row, hk]
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [congrFun (oldGame_X_gateway P tau) (Fin.last k)]
    simp only [Pi.add_apply, Matrix.vecMul_sub, Pi.sub_apply, E_2tau_mat,
      vecMul_E_last, counter_bundle_last P.order_ge_two, sub_self, zero_add]

theorem S_last (tau : ℕ) (c H delta : ℚ) (i : OldAct P) :
    S P tau c H delta i (Fin.last k) = zeta (P.R P.b) tau c H (Fin.last k) := by
  have hk : k ≠ 0 := by have := P.order_ge_two; omega
  rcases i with i | i
  · rw [congrFun (S_parent P tau c H delta i) (Fin.last k)]
    change Matrix.vecMul (P.R i) (E_tau_mat k tau) (Fin.last k) + _ = _
    simp [translation, vecMul_E_last, vecMul_B_last]
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [congrFun (S_gateway P tau c H delta) (Fin.last k)]
    simp [vecMul_B_last, counter_bundle_last P.order_ge_two, e0_row, hk]

theorem S_mid_last (tau : ℕ) (c H delta : ℚ) (i : OldAct P) :
    S_mid P tau c H delta i (Fin.last k) = zeta (P.R P.b) tau c H (Fin.last k) := by
  simp only [S_mid, Matrix.add_apply, S_last, oldGame_X_last, add_zero]

theorem D_last (tau : ℕ) (c H delta : ℚ) (i : OldAct P) :
    D P tau c H delta i (Fin.last k) = 0 := by
  simp only [D, Matrix.sub_apply, oldGame_X_last, sub_zero]
  rw [mul_N_mat_apply, dif_neg (by simp)]

/-- The scalar height and common parent-score translation in equation (y). -/
def heightValue (tau : ℕ) (c H : ℚ) (q : ℕ) : ℚ :=
  dotProduct (zeta (P.R P.b) tau c H) (binomBasis (k + 1) q)

def parentTranslation (tau : ℕ) (c H : ℚ) (q : ℕ) : ℚ :=
  dotProduct (translation (P.R P.b) tau c H) (binomBasis (k + 1) q)

theorem heightValue_zero (tau : ℕ) (c H : ℚ) : heightValue P tau c H 0 = H := by
  change (Matrix.of (fun _ : Unit => zeta (P.R P.b) tau c H)).mulVec
    (binomBasis (k + 1) 0) () = H
  rw [mulVec_binomBasis_zero]
  rfl

theorem parentTranslation_step (tau q : ℕ) (c H : ℚ) :
    parentTranslation P tau c H (q + 1) =
      heightValue P tau c H q - P.entry (tau * (q + 1)) P.b := by
  rw [parentTranslation, translation, sub_dotProduct, ← Matrix.dotProduct_mulVec,
    B_mat_mulVec_binomBasis, ← Matrix.dotProduct_mulVec, E_tau_mat_mulVec_binomBasis]
  rfl

theorem X_eval_parent (tau q : ℕ) (i : Fin P.m) :
    (X P tau).mulVec (binomBasis (k + 1) q) (Sum.inl i) =
      ∑ s ∈ Finset.Ico (tau * q) (2 * tau * q), (P.countTable.mulVec (binomBasis k s)) i := by
  change (P.countTable * F_tau_mat k tau).mulVec (binomBasis (k + 1) q) i = _
  rw [← Matrix.mulVec_mulVec]
  change (∑ j, P.countTable i j * (F_tau_mat k tau).mulVec (binomBasis (k + 1) q) j) = _
  simp_rw [F_tau_mat_mulVec_binomBasis]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem X_eval_gateway (tau q : ℕ) :
    (X P tau).mulVec (binomBasis (k + 1) q) (Sum.inr 0) = 1 := by
  change dotProduct (e0_row (k + 1)) (binomBasis (k + 1) q) = 1
  simp [dotProduct, e0_row, binomBasis]

theorem counter_bundle_eval (hk : 0 < k) (tau q : ℕ) :
    dotProduct (Matrix.vecMul (e0_row k) (F_tau_mat k tau)) (binomBasis (k + 1) q) =
      (tau * q : ℕ) := by
  rw [← Matrix.dotProduct_mulVec]
  let z : Fin k := ⟨0, hk⟩
  rw [dotProduct, Finset.sum_eq_single z]
  · change e0_row k z * (F_tau_mat k tau).mulVec (binomBasis (k + 1) q) z = _
    rw [F_tau_mat_mulVec_binomBasis]
    simp [z, e0_row, binomBasis, show 2 * tau * q = tau * q + tau * q by ring]
  · intro i _ hi
    have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp [e0_row, hi0]
  · simp

theorem heightValue_step (tau q : ℕ) (c H : ℚ) :
    heightValue P tau c H (q + 1) - heightValue P tau c H q =
      P.entry (2 * tau * (q + 1)) P.b - P.entry (tau * (q + 1)) P.b + c := by
  have hz := congrArg (fun v => dotProduct v (binomBasis (k + 1) (q + 1)))
    (zeta_spec (by have := P.order_ge_two; omega) (P.R P.b) tau c H).1
  dsimp only at hz
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, sub_dotProduct, ← Matrix.dotProduct_mulVec,
    B_mat_mulVec_binomBasis] at hz
  change _ = dotProduct (increment (P.R P.b) tau c) _ at hz
  rw [increment, add_dotProduct, Matrix.vecMul_sub, sub_dotProduct,
    ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, E_2tau_mat,
    E_tau_mat_mulVec_binomBasis, E_tau_mat_mulVec_binomBasis, smul_dotProduct] at hz
  have he : dotProduct (e0_row (k + 1)) (binomBasis (k + 1) (q + 1)) = 1 := by
    simp [dotProduct, e0_row, binomBasis]
  rw [he, smul_eq_mul, mul_one] at hz
  exact hz

theorem S_eval (tau q : ℕ) (c H delta : ℚ) :
    (S P tau c H delta).mulVec (binomBasis (k + 1) q) =
      Sum.elim (fun i => P.entry (tau * q) i + parentTranslation P tau c H q)
        (fun _ : Fin 1 => P.entry (tau * q) P.b + parentTranslation P tau c H q -
          (tau * q : ℕ) + delta) := by
  funext i
  cases i with
  | inl i =>
      change dotProduct (S P tau c H delta (Sum.inl i)) _ = _
      rw [S_parent, add_dotProduct]
      change dotProduct (Matrix.vecMul (P.R i) (E_tau_mat k tau)) _ + _ = _
      rw [← Matrix.dotProduct_mulVec, E_tau_mat_mulVec_binomBasis]
      rfl
  | inr i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      change dotProduct (S P tau c H delta (Sum.inr 0)) _ = _
      rw [S_gateway, add_dotProduct, sub_dotProduct,
        counter_bundle_eval (by have := P.order_ge_two; omega)]
      have he : dotProduct (e0_row (k + 1)) (binomBasis (k + 1) q) = 1 := by
        simp [dotProduct, Fin.sum_univ_succ, e0_row, binomBasis]
      rw [smul_dotProduct, he, smul_eq_mul, mul_one]
      simp only [parentTranslation, translation, sub_dotProduct,
        ← Matrix.dotProduct_mulVec, E_tau_mat_mulVec_binomBasis, Sum.elim_inr,
        Clock.entry, Matrix.mulVec]
      ring

#print axioms zeta_unique
#print axioms DX_summary
#print axioms X_full_column_rank
#print axioms X_integer
#print axioms S_eval

end Karlin.FaithfulTables
