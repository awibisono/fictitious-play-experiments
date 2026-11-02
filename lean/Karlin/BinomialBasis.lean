import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Binomial Basis and Bundle Transfer Matrices (`sec:preliminaries` & `sec:bundle`)

This module formalizes Sections 3.1 and 5.1 of *On Karlin's Conjecture for Fictitious Play*:

1. **General Width-`w` Difference and Shift Matrices (`N_mat w`, `T_mat w`, `B_mat w`)**:
   - `e0_row_mul_N_mat`: $e_0^\top N_{w-1} = 0$ (Equation `eq:e0N`).
   - `N_mat_mulVec_elast_col`: $N_{w-1} e_{w-1} = 0$ (Equation `eq:e0N`).
   - `mul_N_of_mul_T_eq_one` & `N_mul_of_T_mul_eq_one`: $B T = I \implies B N = I - B$ and
     $T B = I \implies N B = I - B$.
2. **Binomial Basis `p_{w-1}(q)` and Pascal's Shift Identity (`eq:binomialshift`)**:
   - `binomBasis_succ_sub`: $p_{w-1}(q + 1) - p_{w-1}(q) = N_{w-1} p_{w-1}(q)$ for all $w, q \in \mathbb{N}$.
   - `binomBasis_succ`: $p_{w-1}(q + 1) = T_{w-1} p_{w-1}(q)$ for all $w, q \in \mathbb{N}$.
3. **Telescoping Bundle Sum and Scaled Parent Bundle Transfer Identity (`sec:bundle`)**:
   - `N_mat_F_transfer_sum`: $\sum_{\sigma=a}^{b-1} N_{w-1} p_{w-1}(\sigma) = p_{w-1}(b) - p_{w-1}(a)$
     for all $a \le b$.
   - `parent_bundle_transfer`: If $G_O C = R N_{k-1}$ and $N_{k-1} F_\tau = E_{2\tau} - E_\tau$,
     then with $S_{\mathrm{beg}} = R E_\tau$, $S_{\mathrm{end}} = R E_{2\tau}$, and $Z = C F_\tau$,
     we have $G_O Z = S_{\mathrm{end}} - S_{\mathrm{beg}}$.
-/

namespace Karlin

open scoped BigOperators

/-- Width-`w` lower-shift difference matrix `N_{w-1}` with ones on the first subdiagonal. -/
def N_mat (w : ℕ) : Matrix (Fin w) (Fin w) ℚ :=
  Matrix.of fun i j => if i.val = j.val + 1 then 1 else 0

/-- Width-`w` Pascal shift matrix `T_{w-1} = I_w + N_{w-1}`. -/
def T_mat (w : ℕ) : Matrix (Fin w) (Fin w) ℚ :=
  1 + N_mat w

/-- Explicit lower-triangular inverse matrix `B_{w-1} = T_{w-1}⁻¹` with alternating signs
    `B_{i,j} = (-1)^{i-j}` for `j ≤ i`. -/
def B_mat (w : ℕ) : Matrix (Fin w) (Fin w) ℚ :=
  Matrix.of fun i j => if j.val ≤ i.val then (-1 : ℚ) ^ (i.val - j.val) else 0

/-- First standard basis row `e_0^\top = (1, 0, …, 0) ∈ ℚ^w`. -/
def e0_row (w : ℕ) : Fin w → ℚ :=
  fun j => if j.val = 0 then 1 else 0

/-- Top-degree standard basis column `e_{w-1} = (0, …, 0, 1)^\top ∈ ℚ^w`. -/
def elast_col (w : ℕ) : Fin w → ℚ :=
  fun i => if i.val + 1 = w then 1 else 0

/-- **Annihilation of First Row (`eq:e0N`)**:
    `e_0^\top N_{w-1} = 0` for every width `w`. -/
theorem e0_row_mul_N_mat (w : ℕ) :
    Matrix.vecMul (e0_row w) (N_mat w) = 0 := by
  ext j
  simp only [Matrix.vecMul, dotProduct, e0_row, N_mat, Matrix.of_apply, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.val = 0 <;> simp [hi]

/-- **Annihilation of Top Column (`eq:e0N`)**:
    `N_{w-1} e_{w-1} = 0` for every width `w`. -/
theorem N_mat_mulVec_elast_col (w : ℕ) :
    (N_mat w).mulVec (elast_col w) = 0 := by
  ext i
  simp only [Matrix.mulVec, dotProduct, N_mat, elast_col, Matrix.of_apply, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j.val + 1 = w
  · simp [hj, ne_of_lt i.isLt]
  · simp [hj]

/-- **Orthogonality of `e_0^\top` and `e_{w-1}` (`w ≥ 2`)**:
    For `w ≥ 2`, `e_0^\top e_{w-1} = 0`. -/
theorem e0_row_dot_elast_col {w : ℕ} (hw : 2 ≤ w) :
    (∑ i : Fin w, e0_row w i * elast_col w i) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  simp only [e0_row, elast_col]
  by_cases hi : i.val = 0
  · have h1 : (1 : ℕ) ≠ w := by omega
    simp [hi, h1]
  · simp [hi]

/-- **Right Shift-Inverse Identity**:
    If `B * (1 + N) = 1`, then `B * N = 1 - B`. -/
theorem mul_N_of_mul_T_eq_one {w : ℕ} {B N : Matrix (Fin w) (Fin w) ℚ}
    (hBT : B * (1 + N) = 1) :
    B * N = 1 - B := by
  have h1 : B + B * N = 1 := by
    simpa [mul_add] using hBT
  exact eq_sub_of_add_eq' h1

/-- **Left Shift-Inverse Identity**:
    If `(1 + N) * B = 1`, then `N * B = 1 - B`. -/
theorem N_mul_of_T_mul_eq_one {w : ℕ} {B N : Matrix (Fin w) (Fin w) ℚ}
    (hTB : (1 + N) * B = 1) :
    N * B = 1 - B := by
  have h1 : B + N * B = 1 := by
    simpa [add_mul] using hTB
  exact eq_sub_of_add_eq' h1

/-- Binomial basis vector `p_{w-1}(q) = (1, q, \binom{q}{2}, …, \binom{q}{w-1})^\top ∈ ℚ^w`. -/
def binomBasis (w : ℕ) (q : ℕ) : Fin w → ℚ :=
  fun i => (Nat.choose q i.val : ℚ)

/-- **Binomial Forward-Difference Identity (`eq:binomialshift`)**:
    For every width `w` and phase index `q ∈ ℕ`,
    `p_{w-1}(q + 1) - p_{w-1}(q) = N_{w-1} p_{w-1}(q)`. -/
theorem binomBasis_succ_sub (w q : ℕ) :
    binomBasis w (q + 1) - binomBasis w q = (N_mat w).mulVec (binomBasis w q) := by
  ext ⟨i, hi⟩
  rcases i with _ | k
  · simp [binomBasis, Matrix.mulVec, dotProduct, N_mat]
  · simp only [Pi.sub_apply, binomBasis, Matrix.mulVec, dotProduct, N_mat, Matrix.of_apply]
    let j0 : Fin w := ⟨k, Nat.lt_of_succ_lt hi⟩
    have hsum :
        (∑ j : Fin w, (if k + 1 = j.val + 1 then (1 : ℚ) else 0) * (Nat.choose q j.val : ℚ)) =
          ∑ j : Fin w, if j = j0 then (Nat.choose q j.val : ℚ) else 0 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j = j0
      · subst hj
        simp [j0]
      · have hne : k ≠ j.val := by
          intro h
          apply hj
          ext
          exact h.symm
        simp [hj, hne]
    rw [hsum, Finset.sum_ite_eq' Finset.univ j0]
    simp only [Finset.mem_univ, ↓reduceIte, j0]
    have hchoose : (Nat.choose (q + 1) (k + 1) : ℚ) = (Nat.choose q k : ℚ) + (Nat.choose q (k + 1) : ℚ) := by
      exact_mod_cast Nat.choose_succ_succ q k
    linarith

/-- **Pascal's Shift Matrix Identity (`eq:binomialshift`)**:
    For every width `w` and phase index `q ∈ ℕ`,
    `p_{w-1}(q + 1) = T_{w-1} p_{w-1}(q)`. -/
theorem binomBasis_succ (w q : ℕ) :
    binomBasis w (q + 1) = (T_mat w).mulVec (binomBasis w q) := by
  have hsub := binomBasis_succ_sub w q
  ext i
  have hi := congr_fun hsub i
  simp only [Pi.sub_apply] at hi
  simp only [T_mat, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  linarith

/-- **Telescoping Bundle Sum Identity (`sec:bundle`)**:
    Summing `N_{w-1} p_{w-1}(\sigma)` over `\sigma ∈ [a, b)` telescopes to
    `p_{w-1}(b) - p_{w-1}(a)` for all `a ≤ b`. -/
theorem binomBasis_bundle_sum (w : ℕ) {a b : ℕ} (hab : a ≤ b) (i : Fin w) :
    (∑ σ ∈ Finset.Ico a b, (N_mat w).mulVec (binomBasis w σ) i) =
      binomBasis w b i - binomBasis w a i := by
  have hcongr :
      (∑ σ ∈ Finset.Ico a b, (N_mat w).mulVec (binomBasis w σ) i) =
        ∑ σ ∈ Finset.Ico a b, (binomBasis w (σ + 1) i - binomBasis w σ i) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    have h := congr_fun (binomBasis_succ_sub w σ) i
    simp only [Pi.sub_apply] at h
    exact h.symm
  rw [hcongr]
  exact Finset.sum_Ico_sub (fun σ => binomBasis w σ i) hab

/-- **Scaled Parent Bundle Transfer Identity (`sec:bundle`, Equation (27))**:
    If a parent game `G_O` has score/count tables `R, C` satisfying `G_O * C = R * N`,
    and the bundle transfer matrices `E_beg, E_end, F` satisfy `N * F = E_end - E_beg`,
    then the bundled count matrix `Z = C * F` and bundled score tables
    `S_beg = R * E_beg`, `S_end = R * E_end` satisfy
    `G_O * Z = S_end - S_beg`. -/
theorem parent_bundle_transfer {m k w : Type*} [Fintype m] [Fintype k] [Fintype w]
    [DecidableEq m] [DecidableEq k] [DecidableEq w]
    (G_O : Matrix m m ℚ) (R C : Matrix m k ℚ) (N : Matrix k k ℚ)
    (E_beg E_end F : Matrix k w ℚ)
    (hclock : G_O * C = R * N)
    (htransfer : N * F = E_end - E_beg) :
    G_O * (C * F) = R * E_end - R * E_beg := by
  calc
    G_O * (C * F) = (G_O * C) * F := (Matrix.mul_assoc G_O C F).symm
    _ = (R * N) * F := by rw [hclock]
    _ = R * (N * F) := Matrix.mul_assoc R N F
    _ = R * (E_end - E_beg) := by rw [htransfer]
    _ = R * E_end - R * E_beg := Matrix.mul_sub R E_end E_beg

end Karlin

#print axioms Karlin.e0_row_mul_N_mat
#print axioms Karlin.N_mat_mulVec_elast_col
#print axioms Karlin.e0_row_dot_elast_col
#print axioms Karlin.mul_N_of_mul_T_eq_one
#print axioms Karlin.N_mul_of_T_mul_eq_one
#print axioms Karlin.binomBasis_succ_sub
#print axioms Karlin.binomBasis_succ
#print axioms Karlin.binomBasis_bundle_sum
#print axioms Karlin.parent_bundle_transfer
