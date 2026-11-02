import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Karlin.BinomialBasis

/-!
# The All-Orders Inductive Lift: Algebraic & Coupling Core (`sec:gateway`–`sec:next`)

This module formalizes the complete algebraic engine of the one-step inductive lift
(Sections 5, 6, 7, and 8 of *On Karlin's Conjecture for Fictitious Play*):

1. **Lemma 5.3 (`lem:gateway` — Endpoint Action & Deficit Matrix `D`)**:
   - `gateway_deficit_invariance`: $(u_g - u_b) + v z^{\mathrm{rem}} = \delta$ is invariant
     throughout the parent bundle.
   - `gateway_waits_on_proper_prefix`: $H_{\mathrm{parent}} - u_g \ge \delta_0 - \delta$ at every
     proper prefix of the parent bundle.
   - `gateway_takeover_at_completion`: When $z^{\mathrm{rem}} = 0$, $u_g - u_b = \delta$.
   - `gateway_D_independent_of_delta`: Because $e_0^\top N_{w-1} = 0$, the deficit matrix
     $D = S N_{w-1} - G_O X$ is independent of the endpoint margin $\delta$.

2. **Lemma 5.4 (`lem:resetidentity` — Two-Sided Reset Identity)**:
   - `V_reset_mul_N`: If $B (I + N) = I$, then $V N = (J - J^\top) M - Q$.
   - `reset_identity_iff`: If $B (I + N) = I$, the full-phase return identity
     $G \binom{X}{M} = \binom{S}{V} N$ holds if and only if both coupling equations
     $P M = D$ and $P^\top X = Q$ hold.

3. **Lemma 5.5 (`lem:interpolate` — Simultaneous Matrix Equation Interpolation Solver)**:
   - `interpolate_necessary`: $(\exists P,\; P M = D \land P^\top X = Q) \implies D^\top X = M^\top Q$.
   - `interpolate_residual_compat`: $D^\top X = M^\top Q \iff D_R^\top X = M^\top Q_R$.
   - `interpolate_PtX` & `interpolate_PM`: If $X^\top L_X = I$ and $R_M M = I$, then the explicit
     interpolation formula $P = P_0 + D_R R_M + L_X (Q_R^\top - X^\top D_R R_M)$ satisfies
     $P^\top X = Q$ unconditionally and $P M = D$ whenever $D^\top X = M^\top Q$.
   - `interpolate_iff`: Under full column rank ($X^\top L_X = I$, $R_M M = I$),
     $(\exists P,\; P M = D \land P^\top X = Q) \iff D^\top X = M^\top Q$.

4. **Equation (37) & Lemma 6.1 (`eq:moment`, `lem:cokernel` — Moment Equation & Adjoint Cokernel)**:
   - `M_transpose_mul_Q_reset`: $M^\top Q = \ell^\top \psi + (E - E^\top B)$.
   - `moment_equation_iff`: $D^\top X = M^\top Q \iff E - E^\top B = D^\top X - \ell^\top \psi$.
   - `cokernel_trace_adjoint` & `cokernel_trace_orthogonality`:
     $\operatorname{tr}(Z^\top (E - E^\top B)) = \operatorname{tr}((Z - B Z^\top)^\top E)$, so any
     adjoint-kernel test matrix $Z = B Z^\top$ is orthogonal to $\operatorname{im}(\mathcal{L})$.

5. **Section 7 (`sec:synthesis` — Closed-Form Inverses, Sherman–Morrison, Interaction Realization)**:
   - `L_op_E0`: $\mathcal{L}(E_0) = -\ell_0^\top \psi^\circ$.
   - `W_closed_form_inverse`: $W^{-1} = T_*^{-1} \Phi_0 + A_\circ^{-1} \Phi_1$ is the exact inverse of
     $W = U_0 + A_\circ V_0$.
   - `sherman_morrison_right` & `sherman_morrison_left`: The Sherman–Morrison formula gives the
     exact two-sided inverse of the rank-1 update $W_E = W + e_0 \ell_*$.
   - `interaction_realization_MJM`: The block interaction matrix $J$ with cross-block
     $C_\times = C_{\mathrm{lead}} + W^{-\top} F_{\mathrm{res}} W_E^{-1}$ satisfies $M^\top J M = E$.
   - `C_times_mul_W_E` & `P0_mul_M_cancellation`: Exact count-table cancellations that make the
     coupling error $P - P_0 = O(T_*^{-1})$ uniform in $A_\circ$.

6. **Section 8 (`prop:nextweights` — Rotated Next-Order Tables & Positive Weights)**:
   - `rotated_reset_score_identity`: $V - Q = \mathbf{1}_n \zeta - J M$.
   - `rotated_clock_old_block` & `rotated_clock_reset_block`: The rotated tables
     $R_+ = \binom{S_{\mathrm{mid}}}{\mathbf{1}_n \zeta - J M}$ and $C_+ = \binom{X T}{M}$ satisfy
     $G C_+ = R_+ N$.
   - `next_weights_identity`: The positive weight construction satisfies
     $\mu r_0 + (t_{\mathrm{rem}} W^{-1}) W = t_+$.
-/

namespace Karlin

open scoped BigOperators

/-!
## 1. Lemma 5.3 (`lem:gateway`): Endpoint Action and Deficit Matrix `D`
-/

/-- **Endpoint Counter Deficit Invariance (`lem:gateway`, Equation (30))**:
    Suppose the endpoint action `g` has parent-action payoff row `G_O b + v`, starts the bundle at
    score `u_g_beg = s_b - (∑ i, v i * z_bundle i) + δ`, and `z_bundle = z_play + z_rem`.
    Then after any prefix `z_play`, the current scores `u_b` and `u_g` satisfy
    `(u_g - u_b) + ∑ i, v i * z_rem i = δ`. -/
theorem gateway_deficit_invariance {m : Type*} [Fintype m]
    (row_b v z_play z_rem : m → ℚ) (s_b δ : ℚ) :
    let z_bundle := fun i => z_play i + z_rem i
    let u_g_beg := s_b - (∑ i : m, v i * z_bundle i) + δ
    let u_b := s_b + ∑ i : m, row_b i * z_play i
    let u_g := u_g_beg + ∑ i : m, (row_b i + v i) * z_play i
    (u_g - u_b) + (∑ i : m, v i * z_rem i) = δ := by
  intro z_bundle u_g_beg u_b u_g
  have hsum :
      (∑ i : m, (row_b i + v i) * z_play i) -
        (∑ i : m, row_b i * z_play i) +
        (∑ i : m, v i * z_rem i) -
        (∑ i : m, v i * (z_play i + z_rem i)) = 0 := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    ring
  dsimp only [u_g, u_b, u_g_beg, z_bundle]
  linarith

/-- **Endpoint Waiting Bound on Proper Prefixes (`lem:gateway`, Equation (31))**:
    If `(u_g - u_b) + v ⋅ z_rem = δ` and the parent clock satisfies the remaining-counter bound
    `(H_parent - u_b) + v ⋅ z_rem ≥ δ0`, then `H_parent - u_g ≥ δ0 - δ`. -/
theorem gateway_waits_on_proper_prefix {u_g u_b vz_rem H_parent δ δ0 : ℚ}
    (hinv : (u_g - u_b) + vz_rem = δ)
    (hclock : δ0 ≤ (H_parent - u_b) + vz_rem) :
    δ0 - δ ≤ H_parent - u_g := by
  linarith

/-- **Endpoint Takeover at Bundle Completion (`lem:gateway`)**:
    At bundle completion (`vz_rem = 0`), if `(u_g - u_b) + vz_rem = δ` and every parent action
    has score `u_i ≤ u_b`, then `u_g - u_i ≥ δ`. -/
theorem gateway_takeover_at_completion {u_g u_b u_i δ : ℚ}
    (hinv : (u_g - u_b) + 0 = δ) (hparent : u_i ≤ u_b) :
    δ ≤ u_g - u_i := by
  linarith

/-- **Deficit Matrix `D` is Independent of `\delta` (`lem:gateway`)**:
    Perturbing any rows of `S` by multiples of `e_0^\top` leaves `S * N_mat w - G_O * X`
    unchanged because `e_0^\top N_{w-1} = 0`. -/
theorem gateway_D_independent_of_delta {m : Type*} [Fintype m] [DecidableEq m] (w : ℕ)
    (G_O : Matrix m m ℚ) (S0 X : Matrix m (Fin w) ℚ) (c_row : m → ℚ) :
    let dS : Matrix m (Fin w) ℚ := Matrix.of fun i j => c_row i * e0_row w j
    (S0 + dS) * N_mat w - G_O * X = S0 * N_mat w - G_O * X := by
  intro dS
  have hdS : dS * N_mat w = 0 := by
    ext i j
    simp only [dS, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    have hmul :
        (∑ k : Fin w, c_row i * e0_row w k * N_mat w k j) =
          c_row i * (∑ k : Fin w, e0_row w k * N_mat w k j) := by
      simp only [mul_assoc, ← Finset.mul_sum]
    rw [hmul]
    have he0 := congr_fun (e0_row_mul_N_mat w) j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at he0
    rw [he0, mul_zero]
  rw [Matrix.add_mul, hdS, add_zero]

/-!
## 2. Lemma 5.4 (`lem:resetidentity`): Two-Sided Reset Identity
-/

/-- Rank-1 matrix `1_n ζ` whose every row equals `zeta`. -/
def one_zeta (n : Type*) {w : Type*} (zeta : w → ℚ) : Matrix n w ℚ :=
  Matrix.of fun _ j => zeta j

/-- Reset entrance score table `V = 1_n ζ B - Jᵀ M B` (`eq:controllerdata`). -/
def V_reset {n w : Type*} [Fintype n] [Fintype w]
    (J : Matrix n n ℚ) (M : Matrix n w ℚ) (B : Matrix w w ℚ) (zeta : w → ℚ) : Matrix n w ℚ :=
  one_zeta n zeta * B - J.transpose * M * B

/-- Reset coupling target table `Q = 1_n (ζ B - ζ) + J M - Jᵀ M B` (`eq:controllerdata`). -/
def Q_reset {n w : Type*} [Fintype n] [Fintype w]
    (J : Matrix n n ℚ) (M : Matrix n w ℚ) (B : Matrix w w ℚ) (zeta : w → ℚ) : Matrix n w ℚ :=
  one_zeta n zeta * B - one_zeta n zeta + J * M - J.transpose * M * B

/-- Old-action score deficit table `D = S N - G_O X` (`eq:old`). -/
def D_deficit {m w : Type*} [Fintype m] [Fintype w]
    (G_O : Matrix m m ℚ) (S X : Matrix m w ℚ) (N : Matrix w w ℚ) : Matrix m w ℚ :=
  S * N - G_O * X

/-- **Key Shift Relation for `V_reset` (`lem:resetidentity`)**:
    If `B * (1 + N) = 1`, then `V_reset J M B zeta * N = (J - J.transpose) * M - Q_reset J M B zeta`. -/
theorem V_reset_mul_N {n w : Type*} [Fintype n] [Fintype w] [DecidableEq w]
    (J : Matrix n n ℚ) (M : Matrix n w ℚ) (B N : Matrix w w ℚ) (zeta : w → ℚ)
    (hBT : B * (1 + N) = 1) :
    V_reset J M B zeta * N = (J - J.transpose) * M - Q_reset J M B zeta := by
  have hBN : B * N = 1 - B := by
    have h1 : B + B * N = 1 := by simpa [mul_add] using hBT
    exact eq_sub_of_add_eq' h1
  calc
    V_reset J M B zeta * N
      = (one_zeta n zeta * B - J.transpose * M * B) * N := rfl
    _ = one_zeta n zeta * (B * N) - (J.transpose * M) * (B * N) := by
        rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = one_zeta n zeta * (1 - B) - (J.transpose * M) * (1 - B) := by rw [hBN]
    _ = (J - J.transpose) * M - Q_reset J M B zeta := by
        unfold Q_reset
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
        abel

/-- **Two-Sided Reset Identity (`lem:resetidentity`, Equation (35))**:
    If `B * (1 + N) = 1`, the full phase return equations
    `G_O * X + P * M = S * N` and `-Pᵀ * X + (J - Jᵀ) * M = V * N`
    hold if and only if both coupling equations `P * M = D` and `Pᵀ * X = Q` hold. -/
theorem reset_identity_iff {m n w : Type*} [Fintype m] [Fintype n] [Fintype w] [DecidableEq w]
    (G_O : Matrix m m ℚ) (P : Matrix m n ℚ) (J : Matrix n n ℚ)
    (S X : Matrix m w ℚ) (M : Matrix n w ℚ) (B N : Matrix w w ℚ) (zeta : w → ℚ)
    (hBT : B * (1 + N) = 1) :
    (G_O * X + P * M = S * N ∧
      -P.transpose * X + (J - J.transpose) * M = V_reset J M B zeta * N) ↔
    (P * M = D_deficit G_O S X N ∧ P.transpose * X = Q_reset J M B zeta) := by
  rw [V_reset_mul_N J M B N zeta hBT]
  unfold D_deficit
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨eq_sub_of_add_eq' h1, ?_⟩
    have h2' : -P.transpose * X = -Q_reset J M B zeta := by
      calc
        -P.transpose * X = (-P.transpose * X + (J - J.transpose) * M) - (J - J.transpose) * M := by abel
        _ = ((J - J.transpose) * M - Q_reset J M B zeta) - (J - J.transpose) * M := by rw [h2]
        _ = -Q_reset J M B zeta := by abel
    rw [Matrix.neg_mul] at h2'
    exact neg_inj.mp h2'
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [h1, add_sub_cancel]
    · rw [Matrix.neg_mul, h2]
      abel

/-!
## 3. Lemma 5.5 (`lem:interpolate`): Simultaneous Matrix Equation Interpolation Solver
-/

/-- Residual old-score deficit `D_R = D - P_0 * M` (`eq:interpolate`). -/
def D_res {m n w : Type*} [Fintype n]
    (D : Matrix m w ℚ) (P0 : Matrix m n ℚ) (M : Matrix n w ℚ) : Matrix m w ℚ :=
  D - P0 * M

/-- Residual reset-score target `Q_R = Q - P_0ᵀ * X` (`eq:interpolate`). -/
def Q_res {m n w : Type*} [Fintype m]
    (Q : Matrix n w ℚ) (P0 : Matrix m n ℚ) (X : Matrix m w ℚ) : Matrix n w ℚ :=
  Q - P0.transpose * X

/-- Explicit interpolation solution `P = P_0 + D_R R_M + L_X (Q_Rᵀ - Xᵀ D_R R_M)` (`eq:interpolate`). -/
def P_interp {m n w : Type*} [Fintype m] [Fintype n] [Fintype w]
    (X L_X : Matrix m w ℚ) (M : Matrix n w ℚ) (R_M : Matrix w n ℚ)
    (D : Matrix m w ℚ) (Q : Matrix n w ℚ) (P0 : Matrix m n ℚ) : Matrix m n ℚ :=
  let DR := D_res D P0 M
  let QR := Q_res Q P0 X
  P0 + DR * R_M + L_X * (QR.transpose - X.transpose * DR * R_M)

/-- **Necessity of Compatibility (`lem:interpolate`, Equation (36))**:
    If there exists `P` such that `P * M = D` and `Pᵀ * X = Q`, then `Dᵀ * X = Mᵀ * Q`. -/
theorem interpolate_necessary {m n w : Type*} [Fintype m] [Fintype n]
    {X : Matrix m w ℚ} {M : Matrix n w ℚ} {D : Matrix m w ℚ} {Q : Matrix n w ℚ}
    (h : ∃ P : Matrix m n ℚ, P * M = D ∧ P.transpose * X = Q) :
    D.transpose * X = M.transpose * Q := by
  rcases h with ⟨P, hPM, hPtX⟩
  calc
    D.transpose * X = (P * M).transpose * X := by rw [hPM]
    _ = (M.transpose * P.transpose) * X := by rw [Matrix.transpose_mul]
    _ = M.transpose * (P.transpose * X) := Matrix.mul_assoc M.transpose P.transpose X
    _ = M.transpose * Q := by rw [hPtX]

/-- **Residual Compatibility Equivalence (`lem:interpolate`)**:
    `Dᵀ * X = Mᵀ * Q` if and only if `D_Rᵀ * X = Mᵀ * Q_R`. -/
theorem interpolate_residual_compat {m n w : Type*} [Fintype m] [Fintype n]
    (X : Matrix m w ℚ) (M : Matrix n w ℚ) (D : Matrix m w ℚ) (Q : Matrix n w ℚ)
    (P0 : Matrix m n ℚ) :
    (D_res D P0 M).transpose * X - M.transpose * Q_res Q P0 X =
      D.transpose * X - M.transpose * Q := by
  unfold D_res Q_res
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc]
  abel

/-- **Left Interpolation Identity (`Pᵀ * X = Q`, `lem:interpolate`)**:
    Whenever `Xᵀ * L_X = 1`, the explicit formula `P_interp` satisfies `P_interpᵀ * X = Q`. -/
theorem interpolate_PtX {m n w : Type*} [Fintype m] [Fintype n] [Fintype w] [DecidableEq w]
    (X L_X : Matrix m w ℚ) (M : Matrix n w ℚ) (R_M : Matrix w n ℚ)
    (D : Matrix m w ℚ) (Q : Matrix n w ℚ) (P0 : Matrix m n ℚ)
    (hX : X.transpose * L_X = 1) :
    (P_interp X L_X M R_M D Q P0).transpose * X = Q := by
  have hLXtX : L_X.transpose * X = 1 := by
    have ht := congr_arg Matrix.transpose hX
    simpa [Matrix.transpose_mul] using ht
  unfold P_interp D_res Q_res
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc,
    hLXtX, Matrix.mul_one]
  abel

/-- **Right Interpolation Identity (`P * M = D`, `lem:interpolate`)**:
    Whenever `R_M * M = 1` and `Dᵀ * X = Mᵀ * Q`, the explicit formula `P_interp`
    satisfies `P_interp * M = D`. -/
theorem interpolate_PM {m n w : Type*} [Fintype m] [Fintype n] [Fintype w] [DecidableEq w]
    (X L_X : Matrix m w ℚ) (M : Matrix n w ℚ) (R_M : Matrix w n ℚ)
    (D : Matrix m w ℚ) (Q : Matrix n w ℚ) (P0 : Matrix m n ℚ)
    (hM : R_M * M = 1) (hcompat : D.transpose * X = M.transpose * Q) :
    P_interp X L_X M R_M D Q P0 * M = D := by
  have hres : (D_res D P0 M).transpose * X = M.transpose * Q_res Q P0 X := by
    have hdiff := interpolate_residual_compat X M D Q P0
    rw [sub_eq_zero.mpr hcompat] at hdiff
    exact sub_eq_zero.mp hdiff
  have hres_t : (Q_res Q P0 X).transpose * M = X.transpose * D_res D P0 M := by
    have ht := congr_arg Matrix.transpose hres
    simpa [Matrix.transpose_mul] using ht.symm
  unfold P_interp
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hM, Matrix.mul_one]
  rw [hres_t, sub_self, add_zero]
  unfold D_res
  abel

/-- **Complete Characterization of Simultaneous Solvability (`lem:interpolate`)**:
    If `Xᵀ * L_X = 1` and `R_M * M = 1`, then there exists `P` solving
    `P * M = D` and `Pᵀ * X = Q` if and only if `Dᵀ * X = Mᵀ * Q`. -/
theorem interpolate_iff {m n w : Type*} [Fintype m] [Fintype n] [Fintype w] [DecidableEq w]
    (X L_X : Matrix m w ℚ) (M : Matrix n w ℚ) (R_M : Matrix w n ℚ)
    (D : Matrix m w ℚ) (Q : Matrix n w ℚ) (P0 : Matrix m n ℚ)
    (hX : X.transpose * L_X = 1) (hM : R_M * M = 1) :
    (∃ P : Matrix m n ℚ, P * M = D ∧ P.transpose * X = Q) ↔
      D.transpose * X = M.transpose * Q := by
  constructor
  · exact interpolate_necessary
  · intro hcompat
    exact ⟨P_interp X L_X M R_M D Q P0,
      interpolate_PM X L_X M R_M D Q P0 hM hcompat,
      interpolate_PtX X L_X M R_M D Q P0 hX⟩

/-!
## 4. Moment Equation (`eq:moment`) and Adjoint Cokernel (`lem:cokernel`)
-/

/-- Row vector of ones `1_nᵀ ∈ ℚ^{1×n}`. -/
def one_row (n : Type*) : Matrix Unit n ℚ :=
  Matrix.of fun _ _ => 1

/-- Row matrix representation of `zeta : w → ℚ` (`ζ ∈ ℚ^{1×w}`). -/
def zeta_row {w : Type*} (zeta : w → ℚ) : Matrix Unit w ℚ :=
  Matrix.of fun _ j => zeta j

/-- Total reset count row `ℓ = 1_nᵀ M ∈ ℚ^{1×w}`. -/
def ell_row {n w : Type*} [Fintype n] (M : Matrix n w ℚ) : Matrix Unit w ℚ :=
  one_row n * M

/-- Backward height-difference row `ψ = ζ B - ζ ∈ ℚ^{1×w}`. -/
def psi_row {w : Type*} [Fintype w] (zeta : w → ℚ) (B : Matrix w w ℚ) : Matrix Unit w ℚ :=
  zeta_row zeta * B - zeta_row zeta

/-- Factoring `one_zeta n zeta = (one_row n)ᵀ * zeta_row zeta`. -/
theorem one_zeta_eq_mul (n : Type*) {w : Type*} (zeta : w → ℚ) :
    one_zeta n zeta = (one_row n).transpose * zeta_row zeta := by
  ext i j
  simp [one_zeta, one_row, zeta_row, Matrix.mul_apply]

/-- **Expansion of `Mᵀ * Q_reset` (`eq:moment` derivation)**:
    With `E = Mᵀ J M`, `ℓ = 1_nᵀ M`, and `ψ = ζ B - ζ`,
    `Mᵀ Q_reset = ℓᵀ ψ + (E - Eᵀ B)`. -/
theorem M_transpose_mul_Q_reset {n w : Type*} [Fintype n] [Fintype w]
    (J : Matrix n n ℚ) (M : Matrix n w ℚ) (B : Matrix w w ℚ) (zeta : w → ℚ) :
    M.transpose * Q_reset J M B zeta =
      (ell_row M).transpose * psi_row zeta B +
        (M.transpose * J * M - (M.transpose * J * M).transpose * B) := by
  unfold Q_reset ell_row psi_row
  rw [one_zeta_eq_mul]
  simp only [Matrix.transpose_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_assoc]
  abel

/-- **Matrix Compatibility Equation Equivalence (`eq:moment`)**:
    `Dᵀ X = Mᵀ Q_reset` holds if and only if
    `E - Eᵀ B = Dᵀ X - ℓᵀ ψ` (where `E = Mᵀ J M`). -/
theorem moment_equation_iff {m n w : Type*} [Fintype m] [Fintype n] [Fintype w]
    (D X : Matrix m w ℚ) (J : Matrix n n ℚ) (M : Matrix n w ℚ)
    (B : Matrix w w ℚ) (zeta : w → ℚ) :
    D.transpose * X = M.transpose * Q_reset J M B zeta ↔
      M.transpose * J * M - (M.transpose * J * M).transpose * B =
        D.transpose * X - (ell_row M).transpose * psi_row zeta B := by
  rw [M_transpose_mul_Q_reset]
  constructor <;> intro h
  · rw [h]; abel
  · calc
      D.transpose * X
        = (D.transpose * X - (ell_row M).transpose * psi_row zeta B) +
            (ell_row M).transpose * psi_row zeta B := by abel
      _ = (M.transpose * J * M - (M.transpose * J * M).transpose * B) +
            (ell_row M).transpose * psi_row zeta B := by rw [← h]
      _ = (ell_row M).transpose * psi_row zeta B +
            (M.transpose * J * M - (M.transpose * J * M).transpose * B) := by abel

/-- **Adjoint Operator Identity for the Trace Inner Product (`lem:cokernel`)**:
    For any `w × w` matrices `Z, E, B`,
    `tr(Zᵀ (E - Eᵀ B)) = tr((Z - B Zᵀ)ᵀ E)`. -/
theorem cokernel_trace_adjoint {w : Type*} [Fintype w]
    (Z E B : Matrix w w ℚ) :
    Matrix.trace (Z.transpose * (E - E.transpose * B)) =
      Matrix.trace ((Z - B * Z.transpose).transpose * E) := by
  rw [mul_sub, Matrix.trace_sub, Matrix.transpose_sub, sub_mul, Matrix.trace_sub]
  congr 1
  have htr : Matrix.trace (Z.transpose * (E.transpose * B)) =
      Matrix.trace ((Z.transpose * (E.transpose * B)).transpose) :=
    (Matrix.trace_transpose _).symm
  rw [htr]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.trace_mul_comm (B.transpose * E) Z, ← Matrix.mul_assoc]

/-- **Adjoint Cokernel Orthogonality (`lem:cokernel`, Section 6.1)**:
    Every matrix `Z` in the adjoint kernel (`Z = B * Zᵀ`) is orthogonal to `E - Eᵀ * B`
    under the Frobenius/trace inner product `⟨Z, F⟩ = tr(Zᵀ F)`. -/
theorem cokernel_trace_orthogonality {w : Type*} [Fintype w]
    (Z E B : Matrix w w ℚ) (hZ : Z = B * Z.transpose) :
    Matrix.trace (Z.transpose * (E - E.transpose * B)) = 0 := by
  rw [cokernel_trace_adjoint, sub_eq_zero.mpr hZ, Matrix.transpose_zero, zero_mul,
    Matrix.trace_zero]

/-!
## 5. Section 7 (`sec:synthesis`): Closed-Form Inverses, Sherman–Morrison, and Interaction Realization
-/

/-- **Leading Term Compatibility Cancellation (`prop:momentchoice`, Equation (54))**:
    For `E_0 = c • (ζ₀ᵀ * ζ₀)`, `ℓ_0 = c • ζ₀`, and `ψ₀ = ζ₀ * B - ζ₀`,
    `E_0 - E_0ᵀ * B = -ℓ_0ᵀ * ψ₀`. -/
theorem L_op_E0 {w : Type*} [Fintype w]
    (zeta0 : Matrix Unit w ℚ) (B : Matrix w w ℚ) (c : ℚ) :
    let E0 := c • (zeta0.transpose * zeta0)
    let ell0 := c • zeta0
    let psi0 := zeta0 * B - zeta0
    E0 - E0.transpose * B = -ell0.transpose * psi0 := by
  intro E0 ell0 psi0
  dsimp only [E0, ell0, psi0]
  simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.smul_mul, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc]
  abel

/-- **Closed-Form Right Inverse of `W = U_0 + A_∘ V_0` (`eq:inverse`)**:
    Suppose the projectors `Φ_0, Φ_1` satisfy `U_0 * Φ_0 = T_* • Φ_0`, `U_0 * Φ_1 = 0`,
    `V_0 * Φ_0 = 0`, `V_0 * Φ_1 = Φ_1`, and `Φ_0 + Φ_1 = 1`.
    Then for any non-zero scalars `T_*, A_∘ ≠ 0`,
    `(U_0 + A_∘ • V_0) * (T_*⁻¹ • Φ_0 + A_∘⁻¹ • Φ_1) = 1`. -/
theorem W_closed_form_inverse {w : Type*} [Fintype w] [DecidableEq w]
    (U0 V0 Phi0 Phi1 : Matrix w w ℚ) (T_star A_circ : ℚ)
    (hT : T_star ≠ 0) (hA : A_circ ≠ 0)
    (hU0Phi0 : U0 * Phi0 = T_star • Phi0)
    (hU0Phi1 : U0 * Phi1 = 0)
    (hV0Phi0 : V0 * Phi0 = 0)
    (hV0Phi1 : V0 * Phi1 = Phi1)
    (hsum : Phi0 + Phi1 = 1) :
    (U0 + A_circ • V0) * (T_star⁻¹ • Phi0 + A_circ⁻¹ • Phi1) = 1 := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [hU0Phi0, hU0Phi1, hV0Phi0, hV0Phi1]
  simp only [smul_smul, inv_mul_cancel₀ hT, inv_mul_cancel₀ hA, one_smul, smul_zero,
    add_zero, zero_add]
  exact hsum

/-- A `1 × 1` matrix (`Matrix Unit Unit ℚ`) sandwiched between a column `u : Matrix w Unit ℚ`
    and a row `v : Matrix Unit w ℚ` acts by scalar multiplication by its unique entry `S () ()`. -/
theorem unit_mat_sandwich {w : Type*}
    (u : Matrix w Unit ℚ) (S : Matrix Unit Unit ℚ) (v : Matrix Unit w ℚ) :
    u * S * v = (S () ()) • (u * v) := by
  ext i j
  simp [Matrix.mul_apply, mul_assoc, mul_left_comm]

/-- **Sherman–Morrison Formula — Right Inverse (`eq:inverse`)**:
    If `W * W_inv = 1`, `u : Matrix w Unit ℚ`, `v : Matrix Unit w ℚ`, and
    `1 + (v * W_inv * u) () () ≠ 0`, then
    `W_E_inv = W_inv - (1 + σ)⁻¹ • (W_inv * u * v * W_inv)`
    satisfies `(W + u * v) * W_E_inv = 1`. -/
theorem sherman_morrison_right {w : Type*} [Fintype w] [DecidableEq w]
    (W W_inv : Matrix w w ℚ) (u : Matrix w Unit ℚ) (v : Matrix Unit w ℚ)
    (hW : W * W_inv = 1)
    (hden : 1 + (v * W_inv * u) () () ≠ 0) :
    let σ := (v * W_inv * u) () ()
    let WE_inv := W_inv - (1 + σ)⁻¹ • (W_inv * u * v * W_inv)
    (W + u * v) * WE_inv = 1 := by
  intro σ WE_inv
  dsimp only [WE_inv]
  have h1 : (W + u * v) * W_inv = 1 + u * v * W_inv := by
    rw [add_mul, hW, Matrix.mul_assoc]
  have h2 :
      (W + u * v) * (W_inv * u * v * W_inv) =
        (1 + σ) • (u * v * W_inv) := by
    calc
      (W + u * v) * (W_inv * u * v * W_inv)
        = (W * W_inv) * u * v * W_inv + (u * (v * W_inv * u) * v) * W_inv := by
            simp only [add_mul, Matrix.mul_assoc]
      _ = u * v * W_inv + (σ • (u * v)) * W_inv := by
            rw [hW, Matrix.one_mul, unit_mat_sandwich u (v * W_inv * u) v]
      _ = (1 : ℚ) • (u * v * W_inv) + σ • (u * v * W_inv) := by
            rw [one_smul, smul_mul_assoc]
      _ = (1 + σ) • (u * v * W_inv) := (add_smul 1 σ (u * v * W_inv)).symm
  rw [mul_sub, h1, mul_smul_comm, h2, smul_smul, inv_mul_cancel₀ hden, one_smul,
    add_sub_cancel_right]

/-- **Sherman–Morrison Formula — Left Inverse (`eq:inverse`)**:
    If `W_inv * W = 1`, `u : Matrix w Unit ℚ`, `v : Matrix Unit w ℚ`, and
    `1 + (v * W_inv * u) () () ≠ 0`, then
    `W_E_inv = W_inv - (1 + σ)⁻¹ • (W_inv * u * v * W_inv)`
    satisfies `W_E_inv * (W + u * v) = 1`. -/
theorem sherman_morrison_left {w : Type*} [Fintype w] [DecidableEq w]
    (W W_inv : Matrix w w ℚ) (u : Matrix w Unit ℚ) (v : Matrix Unit w ℚ)
    (hW : W_inv * W = 1)
    (hden : 1 + (v * W_inv * u) () () ≠ 0) :
    let σ := (v * W_inv * u) () ()
    let WE_inv := W_inv - (1 + σ)⁻¹ • (W_inv * u * v * W_inv)
    WE_inv * (W + u * v) = 1 := by
  intro σ WE_inv
  dsimp only [WE_inv]
  have h1 : W_inv * (W + u * v) = 1 + W_inv * u * v := by
    rw [mul_add, hW, Matrix.mul_assoc]
  have h2 :
      (W_inv * u * v * W_inv) * (W + u * v) =
        (1 + σ) • (W_inv * u * v) := by
    calc
      (W_inv * u * v * W_inv) * (W + u * v)
        = W_inv * u * v * (W_inv * W) + W_inv * (u * (v * W_inv * u) * v) := by
            simp only [mul_add, Matrix.mul_assoc]
      _ = W_inv * u * v + W_inv * (σ • (u * v)) := by
            rw [hW, Matrix.mul_one, unit_mat_sandwich u (v * W_inv * u) v]
      _ = (1 : ℚ) • (W_inv * u * v) + σ • (W_inv * u * v) := by
            rw [one_smul, Matrix.mul_smul, ← Matrix.mul_assoc]
      _ = (1 + σ) • (W_inv * u * v) := (add_smul 1 σ (W_inv * u * v)).symm
  rw [sub_mul, h1, smul_mul_assoc, h2, smul_smul, inv_mul_cancel₀ hden, one_smul,
    add_sub_cancel_right]

/-- **Block Interaction Realization Identity (`eq:J`, Section 7.2)**:
    If `C_times = C_lead + W_invᵀ * F_res * WE_inv` where `Wᵀ * C_lead * W_E = E_base`,
    `F_res = E - E_base - J_diag`, `W_inv * W = 1`, and `WE_inv * W_E = 1`, then
    `J_diag + Wᵀ * C_times * W_E = E`. -/
theorem interaction_realization_MJM {w : Type*} [Fintype w] [DecidableEq w]
    (W W_inv W_E WE_inv C_lead E E_base J_diag : Matrix w w ℚ)
    (hW : W_inv * W = 1) (hWE : WE_inv * W_E = 1)
    (hlead : W.transpose * C_lead * W_E = E_base) :
    let F_res := E - E_base - J_diag
    let C_times := C_lead + W_inv.transpose * F_res * WE_inv
    J_diag + W.transpose * C_times * W_E = E := by
  intro F_res C_times
  have hWt : W.transpose * W_inv.transpose = 1 := by
    have ht := congr_arg Matrix.transpose hW
    simpa [Matrix.transpose_mul] using ht
  calc
    J_diag + W.transpose * C_times * W_E
      = J_diag + (W.transpose * C_lead * W_E +
          (W.transpose * W_inv.transpose) * F_res * (WE_inv * W_E)) := by
        dsimp only [C_times]
        simp only [mul_add, add_mul, Matrix.mul_assoc]
    _ = J_diag + (E_base + F_res) := by
        rw [hlead, hWt, hWE, Matrix.one_mul, Matrix.mul_one]
    _ = E := by
        dsimp only [F_res]
        abel

/-- **Count-Table Cancellation in `C_times * W_E` (Step 3 of Lemma 7.2 `lem:uniform`)**:
    Right-multiplying `C_times = C_lead + W_invᵀ * F_res * WE_inv` by `W_E` cancels `W_E`
    from the residual term, leaving `C_lead * W_E + W_invᵀ * F_res`. -/
theorem C_times_mul_W_E {w : Type*} [Fintype w] [DecidableEq w]
    (W_inv W_E WE_inv C_lead F_res : Matrix w w ℚ)
    (hWE : WE_inv * W_E = 1) :
    (C_lead + W_inv.transpose * F_res * WE_inv) * W_E =
      C_lead * W_E + W_inv.transpose * F_res := by
  rw [add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hWE, Matrix.mul_one]

/-- **Baseline Coupling Cancellation in `P_0 * M` (Step 4 of Lemma 7.2 `lem:uniform`)**:
    For the sign-definite reference blocks `P0_E = -a * 1_rᵀ` and `P0_L = a * 1_rᵀ` and
    `W_E = W + e_0 * ℓ_*`, the large baseline table `W` cancels between early and late groups:
    `P0_E * W_E + P0_L * W = -(a * 1_rᵀ) * (e_0 * ℓ_*)`. -/
theorem P0_mul_M_cancellation {m r w : Type*} [Fintype r]
    (a_one : Matrix m r ℚ) (W dW : Matrix r w ℚ) :
    (-a_one) * (W + dW) + a_one * W = -(a_one * dW) := by
  simp only [Matrix.neg_mul, Matrix.mul_add]
  abel

/-!
## 6. Section 8 (`prop:nextweights`): Next-Order Rotated Tables & Positive Weights
-/

/-- **Intermediate Reset Score Table Identity (`eq:rotate`, Section 8.1)**:
    After the old-action block `\mathcal{A}(q)`, the reset-action score table is
    `V_reset - Q_reset = 1_n ζ - J * M`. -/
theorem rotated_reset_score_identity {n w : Type*} [Fintype n] [Fintype w]
    (J : Matrix n n ℚ) (M : Matrix n w ℚ) (B : Matrix w w ℚ) (zeta : w → ℚ) :
    V_reset J M B zeta - Q_reset J M B zeta = one_zeta n zeta - J * M := by
  unfold V_reset Q_reset
  abel

/-- **Rotated Clock Identity — Old-Action Block (`prop:nextweights`, Equation (68))**:
    If `P * M = S * N - G_O * X`, then with `S_mid = S + G_O * X` and `T = 1 + N`,
    `G_O * (X * T) + P * M = S_mid * N`. -/
theorem rotated_clock_old_block {m n w : Type*} [Fintype m] [Fintype n] [Fintype w] [DecidableEq w]
    (G_O : Matrix m m ℚ) (P : Matrix m n ℚ) (S X : Matrix m w ℚ) (M : Matrix n w ℚ)
    (N : Matrix w w ℚ) (hPM : P * M = S * N - G_O * X) :
    G_O * (X * (1 + N)) + P * M = (S + G_O * X) * N := by
  rw [hPM, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, ← Matrix.mul_assoc]
  abel

/-- **Rotated Clock Identity — Reset-Action Block (`prop:nextweights`, Equation (68))**:
    If `-Pᵀ * X + (J - Jᵀ) * M = V * N` and `Pᵀ * X = Q`, then with `T = 1 + N`,
    `-Pᵀ * (X * T) + (J - Jᵀ) * M = (V - Q) * N`. -/
theorem rotated_clock_reset_block {m n w : Type*} [Fintype m] [Fintype n] [Fintype w] [DecidableEq w]
    (P : Matrix m n ℚ) (J : Matrix n n ℚ) (X : Matrix m w ℚ) (M V Q : Matrix n w ℚ)
    (N : Matrix w w ℚ)
    (hreset : -P.transpose * X + (J - J.transpose) * M = V * N)
    (hPtX : P.transpose * X = Q) :
    -P.transpose * (X * (1 + N)) + (J - J.transpose) * M = (V - Q) * N := by
  calc
    -P.transpose * (X * (1 + N)) + (J - J.transpose) * M
      = (-P.transpose * X + (J - J.transpose) * M) - (P.transpose * X) * N := by
        simp only [Matrix.mul_add, Matrix.mul_one, Matrix.neg_mul, ← Matrix.mul_assoc]
        abel
    _ = V * N - Q * N := by rw [hreset, hPtX]
    _ = (V - Q) * N := (Matrix.sub_mul V Q N).symm

/-- **Rotated Summary `R_+ᵀ * C_+` Independence Identity (`eq:nextsummary`, Section 8.1)**:
    For the reset block `R_reset_+ = 1_n ζ - J * M` and `C_reset_+ = M`,
    `R_reset_+ᵀ * M = (ζ_row)ᵀ * ℓ_row - (Mᵀ * J * M)ᵀ`. -/
theorem rotated_reset_summary_identity {n w : Type*} [Fintype n] [Fintype w]
    (J : Matrix n n ℚ) (M : Matrix n w ℚ) (zeta : w → ℚ) :
    (one_zeta n zeta - J * M).transpose * M =
      (zeta_row zeta).transpose * ell_row M - (M.transpose * J * M).transpose := by
  unfold ell_row
  rw [one_zeta_eq_mul]
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.sub_mul, Matrix.mul_assoc]

/-- **Next-Order Positive Weights Identity (`prop:nextweights`, Equation (72))**:
    For `t_rem = t_+ - μ • r_0` and `W_inv * W = 1`, assigning weight `μ` to the old/early
    sum `r_0` and weights `t_rem * W_inv` to the late block `W` reconstructs `t_+`:
    `μ • r_0 + (t_rem * W_inv) * W = t_+`. -/
theorem next_weights_identity {w : Type*} [Fintype w] [DecidableEq w]
    (t_plus r0 : Matrix Unit w ℚ) (W W_inv : Matrix w w ℚ) (μ : ℚ)
    (hW : W_inv * W = 1) :
    let t_rem := t_plus - μ • r0
    μ • r0 + (t_rem * W_inv) * W = t_plus := by
  intro t_rem
  dsimp only [t_rem]
  rw [Matrix.mul_assoc, hW, Matrix.mul_one, add_sub_cancel]

/-!
## 7. Concrete General-Width Coupled-Moment Matrices (`V0_coupled`, `W_coupled`, `W_coupled_inv`, `J_coupled`)
-/

/-- The `r × r` all-ones matrix `1_r 1_rᵀ`. -/
def J_ones (r : ℕ) : Matrix (Fin r) (Fin r) ℚ :=
  Matrix.of fun _ _ => 1

/-- The `(w + 1) × (w + 1)` matrix `e_w 1_{w+1}ᵀ` with `1` in the last row `i = ⟨w, _⟩`
    and `0` in all earlier rows. -/
def E_last (w : ℕ) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ :=
  Matrix.of fun i _ => if i = ⟨w, Nat.lt_succ_self w⟩ then 1 else 0

/-- The cokernel basis matrix `V_0 = \begin{pmatrix} I_w & 0 \\ -\mathbf{1}_w^\top & 0 \end{pmatrix} = 1 - E_{\text{last}}(w)`
    from Equation `eq:V0` (Section 7.1) for `ζ_0 = 1_{w+1}ᵀ`. -/
def V0_coupled (w : ℕ) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ :=
  1 - E_last w

/-- The non-singular positive reset count block `W = 2 J_{\text{ones}}(w + 1) + V_0(w)`
    from Equation `eq:W` (Section 7.1) with `T_* = 2` and `A_∘ = 1`. -/
def W_coupled (w : ℕ) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ :=
  (2 : ℚ) • J_ones (w + 1) + V0_coupled w

/-- The closed-form inverse `W⁻¹ = (2(w+1))⁻¹ E_{\text{last}}(w) + (I - (w+1)⁻¹ J_{\text{ones}}(w+1))`
    from Equation `eq:inverse` (Lemma 7.1). -/
def W_coupled_inv (w : ℕ) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ :=
  (2 * (w + 1 : ℚ))⁻¹ • E_last w + (1 - (w + 1 : ℚ)⁻¹ • J_ones (w + 1))

/-- The strictly lower-triangular all-ones matrix `L_{\text{strict}}(r)` with `1` for `j < i`
    and `0` for `i ≤ j`. -/
def L_strict (r : ℕ) : Matrix (Fin r) (Fin r) ℚ :=
  Matrix.of fun i j => if j.val < i.val then 1 else 0

/-- `J_ones r * J_ones r = r • J_ones r`. -/
theorem J_ones_mul_J_ones (r : ℕ) :
    J_ones r * J_ones r = (r : ℚ) • J_ones r := by
  ext i j
  simp [J_ones, Matrix.mul_apply, Matrix.smul_apply]

/-- `J_ones (w + 1) * E_last w = J_ones (w + 1)`. -/
theorem J_ones_mul_E_last (w : ℕ) :
    J_ones (w + 1) * E_last w = J_ones (w + 1) := by
  ext i j
  simp [J_ones, E_last, Matrix.mul_apply]

/-- `E_last w * J_ones (w + 1) = (w + 1) • E_last w`. -/
theorem E_last_mul_J_ones (w : ℕ) :
    E_last w * J_ones (w + 1) = (w + 1 : ℚ) • E_last w := by
  ext i j
  simp only [E_last, J_ones, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, mul_one]
  split_ifs <;> simp

/-- `E_last w * E_last w = E_last w`. -/
theorem E_last_mul_E_last (w : ℕ) :
    E_last w * E_last w = E_last w := by
  ext i j
  simp only [E_last, Matrix.mul_apply, Matrix.of_apply]
  split_ifs <;> simp

/-- **Every Entry of `W_coupled w` Is at Least `1` (`W_coupled_entry_ge_one`)**:
    For all `i, j : Fin (w + 1)`, `W_coupled w i j ∈ {1, 2, 3}`, hence `1 ≤ W_coupled w i j`. -/
theorem W_coupled_entry_ge_one (w : ℕ) (i j : Fin (w + 1)) :
    1 ≤ W_coupled w i j := by
  simp only [W_coupled, V0_coupled, J_ones, E_last, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul, mul_one]
  split_ifs <;> norm_num

/-- **Right Inverse Identity for `W_coupled w` (`W_coupled_mul_inv`, Lemma 7.1)**:
    For every `w ∈ ℕ`, `W_coupled w * W_coupled_inv w = 1`. -/
theorem W_coupled_mul_inv (w : ℕ) :
    W_coupled w * W_coupled_inv w = 1 := by
  have hw : (w : ℚ) + 1 ≠ 0 := by positivity
  unfold W_coupled W_coupled_inv V0_coupled
  simp only [add_mul, mul_add, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one,
    smul_mul_assoc, mul_smul_comm, smul_smul, J_ones_mul_E_last, J_ones_mul_J_ones,
    E_last_mul_E_last, E_last_mul_J_ones]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp [hw]
  ring

/-- **Left Inverse Identity for `W_coupled w` (`W_coupled_inv_mul`, Lemma 7.1)**:
    For every `w ∈ ℕ`, `W_coupled_inv w * W_coupled w = 1`. -/
theorem W_coupled_inv_mul (w : ℕ) :
    W_coupled_inv w * W_coupled w = 1 := by
  have hw : (w : ℚ) + 1 ≠ 0 := by positivity
  unfold W_coupled W_coupled_inv V0_coupled
  simp only [add_mul, mul_add, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one,
    smul_mul_assoc, mul_smul_comm, smul_smul, J_ones_mul_E_last, J_ones_mul_J_ones,
    E_last_mul_E_last, E_last_mul_J_ones]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp [hw]
  ring

/-- **Column Sum Identity for `W_coupled w` (`one_row_mul_W_coupled`)**:
    Every column of `W_coupled w` sums to `2 * (w + 1)` (`1_{w+1}ᵀ W_coupled w = 2(w+1) 1_{w+1}ᵀ`). -/
theorem one_row_mul_W_coupled (w : ℕ) :
    one_row (Fin (w + 1)) * W_coupled w = (2 * (w + 1 : ℚ)) • one_row (Fin (w + 1)) := by
  ext i j
  simp only [one_row, W_coupled, V0_coupled, J_ones, E_last, Matrix.mul_apply, Matrix.of_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, one_mul, smul_eq_mul,
    mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [Finset.sum_const]
  ring

/-- **Quadratic All-Ones Sandwich for `W_coupled w`**:
    `(W_coupled w)ᵀ * J_ones (w + 1) * W_coupled w = (4 * (w + 1) ^ 2) • J_ones (w + 1)`. -/
theorem W_coupled_transpose_mul_J_ones_mul_W_coupled (w : ℕ) :
    (W_coupled w).transpose * J_ones (w + 1) * W_coupled w =
      (4 * (w + 1 : ℚ) ^ 2) • J_ones (w + 1) := by
  have hJ : J_ones (w + 1) = (one_row (Fin (w + 1))).transpose * one_row (Fin (w + 1)) := by
    ext i j
    simp [J_ones, one_row, Matrix.mul_apply]
  have h1 := one_row_mul_W_coupled w
  have h1t :
      (W_coupled w).transpose * (one_row (Fin (w + 1))).transpose =
        (2 * (w + 1 : ℚ)) • (one_row (Fin (w + 1))).transpose := by
    have ht := congr_arg Matrix.transpose h1
    simpa [Matrix.transpose_mul] using ht
  calc
    (W_coupled w).transpose * J_ones (w + 1) * W_coupled w
      = ((W_coupled w).transpose * (one_row (Fin (w + 1))).transpose) *
          (one_row (Fin (w + 1)) * W_coupled w) := by
        rw [hJ]
        simp only [Matrix.mul_assoc]
    _ = ((2 * (w + 1 : ℚ)) • (one_row (Fin (w + 1))).transpose) *
          ((2 * (w + 1 : ℚ)) • one_row (Fin (w + 1))) := by
        rw [h1t, h1]
    _ = (4 * (w + 1 : ℚ) ^ 2) • J_ones (w + 1) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hJ]
        congr 1
        ring

end Karlin

#print axioms Karlin.gateway_deficit_invariance
#print axioms Karlin.gateway_waits_on_proper_prefix
#print axioms Karlin.gateway_takeover_at_completion
#print axioms Karlin.gateway_D_independent_of_delta
#print axioms Karlin.V_reset_mul_N
#print axioms Karlin.reset_identity_iff
#print axioms Karlin.interpolate_necessary
#print axioms Karlin.interpolate_residual_compat
#print axioms Karlin.interpolate_PtX
#print axioms Karlin.interpolate_PM
#print axioms Karlin.interpolate_iff
#print axioms Karlin.M_transpose_mul_Q_reset
#print axioms Karlin.one_zeta_eq_mul
#print axioms Karlin.moment_equation_iff
#print axioms Karlin.cokernel_trace_adjoint
#print axioms Karlin.cokernel_trace_orthogonality
#print axioms Karlin.L_op_E0
#print axioms Karlin.W_closed_form_inverse
#print axioms Karlin.unit_mat_sandwich
#print axioms Karlin.sherman_morrison_right
#print axioms Karlin.sherman_morrison_left
#print axioms Karlin.interaction_realization_MJM
#print axioms Karlin.C_times_mul_W_E
#print axioms Karlin.P0_mul_M_cancellation
#print axioms Karlin.rotated_reset_score_identity
#print axioms Karlin.rotated_clock_old_block
#print axioms Karlin.rotated_clock_reset_block
#print axioms Karlin.rotated_reset_summary_identity
#print axioms Karlin.next_weights_identity
#print axioms Karlin.J_ones_mul_J_ones
#print axioms Karlin.J_ones_mul_E_last
#print axioms Karlin.E_last_mul_J_ones
#print axioms Karlin.E_last_mul_E_last
#print axioms Karlin.W_coupled_entry_ge_one
#print axioms Karlin.W_coupled_mul_inv
#print axioms Karlin.W_coupled_inv_mul
#print axioms Karlin.one_row_mul_W_coupled
#print axioms Karlin.W_coupled_transpose_mul_J_ones_mul_W_coupled

