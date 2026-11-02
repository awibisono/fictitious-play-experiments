import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Karlin.FictitiousPlay
import Karlin.RPSClock
import Karlin.CubicSevenAction
import Karlin.BinomialBasis
import Karlin.InductiveLift
import Karlin.GatewayLift
import Karlin.AllOrdersComplete
import Karlin.AdmissibleLift
import Karlin.AllTimeGap

namespace Karlin

open scoped BigOperators
open scoped Matrix

/-!
# Paper-Faithful Formalization of Sections 5, 6, 7, and 8 (`PaperProof.lean`)

This module provides the complete, mathematically faithful formalization of the exact algebraic
pipeline from Sections 5, 6, 7, and 8 of the paper (`master_v15.tex`, aligning with `v12_annotated.tex`).

## Six Core Formalizations

1. **Sections 6.1 & 6.3: Adjoint Operator, Compatibility Duality, and RPS Lowest-Test Obstruction Cancellation**:
   - Matrix inner product $\langle U, V \rangle = \sum_{i,j} U_{ij} V_{ij}$ and its adjunction relations.
   - Moment operator $\mathcal{L}(E) = E - E^\top B$ and adjoint operator $\mathcal{L}^*(Z) = Z - B Z^\top$.
   - Adjoint duality $\langle Z, \mathcal{L}(E) \rangle = \langle \mathcal{L}^*(Z), E \rangle$ and exact image-cokernel orthogonality.
   - Explicit $k=2, w=3$ lowest-test matrix $Z^{(2)}$ for Rock-Paper-Scissors:
     $$Z^{(2)} = \begin{pmatrix} 0 & 0 & 1 \\ 0 & -1 & 0 \\ 1 & 1 & -1/8 \end{pmatrix}$$
   - Proof that $Z^{(2)} \in \ker(\mathcal{L}^*)$ (i.e. $\mathcal{L}^*(Z^{(2)}) = 0$).
   - Evaluation of the compatibility obstruction $\langle Z^{(2)}, (D^\circ)^\top X \rangle = -81/2$.
   - Exact cancellation of the $-81/2$ obstruction via the paper's gain adjustment:
     $$c(T_1) = \frac{2(T_1 + 9)}{4 T_1 + 9} = \frac{1}{2} + \frac{27}{8 T_1 + 18}, \quad \Delta c(27 + 12 T_1) = 81/2.$$

2. **Section 7.1: Baseline Moment Cancellation & Gain Shift Expansion**:
   - Baseline moment equation $\mathcal{L}(E_0) = -\ell_0^\top \psi^\circ$ for $E_0 = 2 r \lambda (\zeta^\circ)^\top \zeta^\circ$.
   - Explicit gain-shift perturbation of the moment equation under reset scale $T_1$.

3. **Sections 7.1 & 7.2: Inverse Reset Blocks, Sherman-Morrison Inversion, & Exact Realization**:
   - Normalization projector $\Pi = [I_k \mid 0] - \frac{1}{r} \mathbf{1}_k \mathbf{1}_r^\top$ and coordinate projector $V_0$.
   - Reset inverse basis matrices $\Phi_0$ and $\Phi_1$.
   - Two-sided inversion of the late reset block $W = \mathbf{1}_r \upsilon + T_2 V_0$:
     $$W^{-1} = T_1^{-1} \Phi_0 + T_2^{-1} \Phi_1, \quad W W^{-1} = I, \quad W^{-1} W = I.$$
   - Sherman-Morrison rank-one inversion formula for $W_E = W + e_0 \ell_*$:
     $$W_E^{-1} = W^{-1} - \frac{W^{-1} e_0 \ell_* W^{-1}}{1 + \ell_* W^{-1} e_0}.$$
   - Exact quadratic realization $M^\top J M = E$.

4. **Sections 7.3 & 8.1: Parameter Cancellation, Score Invariance, & Late Weight Decomposition**:
   - Auxiliary scale $T_2$ (or $A_\circ$) cancellation in $P_0 M = -a \ell_*$.
   - Reset action contribution to $R_+^\top C_+$: $(\mathbf{1}_{2r} \zeta - J M)^\top M = \zeta^\top \ell - E^\top$, independent of $T_2$.
   - Late weight vector decomposition $t_{\mathrm{rem}} W^{-1} = \alpha \mathbf{1}_r^\top + T_2^{-1} t_{\mathrm{rem}} \Phi_1$.
   - Cone weight reconstruction: $\mu r_0 + (t_{\mathrm{rem}} W^{-1}) W = t_+$.

5. **Section 6.1: Divided-Power Cokernel Basis $Z_{\mathrm{DP}}^{(h)}, Z^{(h)}$ & Kernel Completeness (Lemma 6.1 `lem:cokernel`)**:
   - Subdiagonal shift matrix $N_0$ and coordinate nilpotent matrix exponential $e^{t N_0}$.
   - Group homomorphism $e^{s N_0} e^{t N_0} = e^{(s+t) N_0}$ via binomial theorem $\sum \binom{d}{m} s^{d-m} t^m$.
   - Alternating anti-diagonal basis $V^{(h)}$ and Lie algebra derivation identity $N_0 V^{(h)} + V^{(h)} N_0^\top = 0$.
   - Matrix exponential intertwining $e^{t N_0} V^{(h)} = V^{(h)} (e^{-t N_0})^\top$.
   - Divided-power cokernel matrices $Z_{\mathrm{DP}}^{(h)} = e^{-N_0/2} V^{(h)}$ and adjoint kernel membership $L^*_{\mathrm{DP}}(Z_{\mathrm{DP}}^{(h)}) = 0$.
   - Cokernel completeness: any symmetric solution to $N_0 V + V N_0^\top = 0$ vanishes strictly below the first anti-diagonal.
   - Binomial-coordinate cokernel basis $Z^{(h)} = S_w Z_{\mathrm{DP}}^{(h)} S_w^\top$ and adjoint kernel membership $L^*(Z^{(h)}) = 0$.
   - Inner product basis change $\langle S Z S^\top, F \rangle = \langle Z, S^\top F S \rangle$.
   - Support and boundary properties of $Z_{\mathrm{DP}}^{(h)}$ (vanishing for $i + j < h$, boundary values $(-1)^i$, zero first row/column for $h \ge w$, top test vanishing for $F_{kk} = 0$, lowest test corners for $h = k$).

6. **Section 6.2: Triangular Pivot System & Higher Compatibility Test Solver (Lemma 6.2 `lem:scale`)**:
   - Triangular decomposition $\langle Z_{\mathrm{DP}}^{(h)}, \widehat{\ell}^\top \widehat{\psi} \rangle = (-1)^i \widehat{\psi}_{k-1} \widehat{\ell}_i + \text{tail}$ for $i = h - k + 1$.
   - Single-step pivot cancellation theorem: solving for $\widehat{\ell}_i$ cancels $\langle Z_{\mathrm{DP}}^{(h)}, \widehat{F} - \widehat{\ell}^\top \widehat{\psi} \rangle = 0$.
   - Triangular back-substitution invariance: modifying lower indices $a < i$ preserves the higher-test inner product.
   - Top test invariant cancellation: $\langle Z_{\mathrm{DP}}^{(2k)}, \widehat{F} - \widehat{\ell}^\top \widehat{\psi} \rangle = 0$ is automatically satisfied whenever $\widehat{\psi}_k = 0$ and $\widehat{F}_{kk} = 0$.
-/

/-!
## Part 1: Sections 6.1 & 6.3 (Adjoint Operator, Compatibility Duality, and RPS Lowest-Test Cancellation)
-/

/-- Matrix entrywise / Frobenius inner product `⟨U, V⟩ = ∑ i, ∑ j, U i j * V i j`. -/
def matInnerProd {n m : Type*} [Fintype n] [Fintype m] (U V : Matrix n m ℚ) : ℚ :=
  ∑ i, ∑ j, U i j * V i j

theorem matInnerProd_comm {n m : Type*} [Fintype n] [Fintype m] (U V : Matrix n m ℚ) :
    matInnerProd U V = matInnerProd V U := by
  dsimp [matInnerProd]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm (U i j) (V i j)

#print axioms Karlin.matInnerProd_comm

theorem matInnerProd_add_left {n m : Type*} [Fintype n] [Fintype m] (U1 U2 V : Matrix n m ℚ) :
    matInnerProd (U1 + U2) V = matInnerProd U1 V + matInnerProd U2 V := by
  dsimp [matInnerProd]
  simp_rw [add_mul, Finset.sum_add_distrib]

#print axioms Karlin.matInnerProd_add_left

theorem matInnerProd_add_right {n m : Type*} [Fintype n] [Fintype m] (U V1 V2 : Matrix n m ℚ) :
    matInnerProd U (V1 + V2) = matInnerProd U V1 + matInnerProd U V2 := by
  dsimp [matInnerProd]
  simp_rw [mul_add, Finset.sum_add_distrib]

#print axioms Karlin.matInnerProd_add_right

theorem matInnerProd_smul_left {n m : Type*} [Fintype n] [Fintype m] (c : ℚ) (U V : Matrix n m ℚ) :
    matInnerProd (c • U) V = c * matInnerProd U V := by
  dsimp [matInnerProd]
  simp_rw [mul_assoc, ← Finset.mul_sum]

#print axioms Karlin.matInnerProd_smul_left

theorem matInnerProd_smul_right {n m : Type*} [Fintype n] [Fintype m] (c : ℚ) (U V : Matrix n m ℚ) :
    matInnerProd U (c • V) = c * matInnerProd U V := by
  dsimp [matInnerProd]
  have hcomm : (∑ i, ∑ j, U i j * (c * V i j)) = (∑ i, ∑ j, c * (U i j * V i j)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcomm]
  simp_rw [← Finset.mul_sum]

#print axioms Karlin.matInnerProd_smul_right

theorem matInnerProd_sub_left {n m : Type*} [Fintype n] [Fintype m] (U1 U2 V : Matrix n m ℚ) :
    matInnerProd (U1 - U2) V = matInnerProd U1 V - matInnerProd U2 V := by
  dsimp [matInnerProd]
  simp_rw [sub_mul, Finset.sum_sub_distrib]

#print axioms Karlin.matInnerProd_sub_left

theorem matInnerProd_sub_right {n m : Type*} [Fintype n] [Fintype m] (U V1 V2 : Matrix n m ℚ) :
    matInnerProd U (V1 - V2) = matInnerProd U V1 - matInnerProd U V2 := by
  dsimp [matInnerProd]
  simp_rw [mul_sub, Finset.sum_sub_distrib]

#print axioms Karlin.matInnerProd_sub_right

theorem matInnerProd_transpose_mul {w : Type*} [Fintype w] (Z B E : Matrix w w ℚ) :
    matInnerProd Z (E.transpose * B) = matInnerProd (B * Z.transpose) E := by
  dsimp [matInnerProd, Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  have h1 : (∑ i, ∑ j, ∑ k, Z i j * (E k i * B k j)) =
      ∑ i, ∑ k, ∑ j, Z i j * (E k i * B k j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  have h2 : (∑ i, ∑ k, ∑ j, Z i j * (E k i * B k j)) =
      ∑ k, ∑ i, ∑ j, B k j * Z i j * E k i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h1, h2]

#print axioms Karlin.matInnerProd_transpose_mul

/-- The moment operator `L(E) = E - Eᵀ * B` from Section 6.1. -/
def L_moment {w : Type*} [Fintype w] (B : Matrix w w ℚ) (E : Matrix w w ℚ) : Matrix w w ℚ :=
  E - E.transpose * B

/-- The adjoint operator `L*(Z) = Z - B * Zᵀ` from Section 6.1. -/
def L_adjoint {w : Type*} [Fintype w] (B : Matrix w w ℚ) (Z : Matrix w w ℚ) : Matrix w w ℚ :=
  Z - B * Z.transpose

/-- Adjoint duality identity `⟨Z, L(E)⟩ = ⟨L*(Z), E⟩` (Section 6.1). -/
theorem matInnerProd_L_adjoint {w : Type*} [Fintype w] (B E Z : Matrix w w ℚ) :
    matInnerProd Z (L_moment B E) = matInnerProd (L_adjoint B Z) E := by
  dsimp [L_moment, L_adjoint]
  rw [matInnerProd_sub_right, matInnerProd_sub_left]
  congr 1
  exact matInnerProd_transpose_mul Z B E

#print axioms Karlin.matInnerProd_L_adjoint

/-- Orthogonality of adjoint kernel to image of `L`:
    if `L*(Z) = 0`, then `⟨Z, L(E)⟩ = 0` for every `E` (Section 6.1). -/
theorem L_orthogonality {w : Type*} [Fintype w] (B E Z : Matrix w w ℚ)
    (hZ : L_adjoint B Z = 0) :
    matInnerProd Z (L_moment B E) = 0 := by
  rw [matInnerProd_L_adjoint, hZ]
  dsimp [matInnerProd]
  simp

#print axioms Karlin.L_orthogonality

/-- Solvability condition: if `F = L(E)`, then `⟨Z, F⟩ = 0` for every `Z ∈ ker(L*)` (Section 6.1). -/
theorem L_moment_solvability_ortho {w : Type*} [Fintype w] (B F Z : Matrix w w ℚ)
    (E : Matrix w w ℚ) (hE : L_moment B E = F) (hZ : L_adjoint B Z = 0) :
    matInnerProd Z F = 0 := by
  rw [← hE]
  exact L_orthogonality B E Z hZ

#print axioms Karlin.L_moment_solvability_ortho

/-- The lowest compatibility test matrix $Z^{(2)}$ for RPS ($k=2, w=3$) from Equation (eq:cokernel) / (eq:seed). -/
def Z2_rps : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, 0, 1;
     0, -1, 0;
     1, 1, -1/8]

/-- The old-action matrix product $(D^\circ)^\top X$ for RPS from Section 6.3. -/
def D0tX_rps : Matrix (Fin 3) (Fin 3) ℚ :=
  !![-1/2, -23/2, -27/2;
     -1, 27, 27;
     0, 0, 0]

/-- Proof that $Z^{(2)}$ belongs to the adjoint kernel $\ker(\mathcal{L}^*)$ for the RPS backward shift $B = B_{\mathrm{mat}} 3$. -/
theorem Z2_rps_in_adjoint_kernel : L_adjoint (B_mat 3) Z2_rps = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals (
    simp [L_adjoint, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, B_mat, Z2_rps]
  )

#print axioms Karlin.Z2_rps_in_adjoint_kernel

/-- The exact compatibility obstruction evaluated on the RPS base: $\langle Z^{(2)}, (D^\circ)^\top X \rangle = -81/2$. -/
theorem Z2_rps_inner_D0tX : matInnerProd Z2_rps D0tX_rps = -81/2 := by
  dsimp [matInnerProd]
  simp [Fin.sum_univ_three, Z2_rps, D0tX_rps]
  norm_num

#print axioms Karlin.Z2_rps_inner_D0tX

/-- The paper's gain adjustment formula for RPS (Section 6.3, Eq. 1702 in v15 / Eq. 1668 in v12):
    $c(T_1) = \frac{2(T_1 + 9)}{4 T_1 + 9} = \frac{1}{2} + \frac{27}{8 T_1 + 18}$. -/
def c_gain_rps (T1 : ℚ) : ℚ :=
  2 * (T1 + 9) / (4 * T1 + 9)

/-- The gain shift $\Delta c(T_1) = c(T_1) - 1/2 = \frac{27}{8 T_1 + 18}$. -/
theorem rps_gain_correction_shift (T1 : ℚ) (h : 4 * T1 + 9 ≠ 0) :
    c_gain_rps T1 - 1/2 = 27 / (8 * T1 + 18) := by
  dsimp [c_gain_rps]
  have hdenom : 8 * T1 + 18 = 2 * (4 * T1 + 9) := by ring
  rw [hdenom]
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  rw [div_sub_div _ _ h h2]
  have htop : 2 * (T1 + 9) * 2 - (4 * T1 + 9) * 1 = 27 := by ring
  have hbot : (4 * T1 + 9) * 2 = 2 * (4 * T1 + 9) := by ring
  rw [htop, hbot]

#print axioms Karlin.rps_gain_correction_shift

/-- Exact obstruction cancellation:
    $\langle Z^{(2)}, (D^\circ)^\top X \rangle + \Delta c \cdot (27 + 12 T_1) = -81/2 + 81/2 = 0$. -/
theorem rps_gain_correction_cancels (T1 : ℚ) (h : 4 * T1 + 9 ≠ 0) :
    -81/2 + (c_gain_rps T1 - 1/2) * (27 + 12 * T1) = 0 := by
  rw [rps_gain_correction_shift T1 h]
  have hdenom : 8 * T1 + 18 = 2 * (4 * T1 + 9) := by ring
  have hfactor : 27 + 12 * T1 = 3 * (4 * T1 + 9) := by ring
  rw [hdenom, hfactor]
  have hmul : 27 / (2 * (4 * T1 + 9)) * (3 * (4 * T1 + 9)) = 81 / 2 := by
    rw [div_mul_eq_mul_div]
    have htop : 27 * (3 * (4 * T1 + 9)) = 81 * (4 * T1 + 9) := by ring
    rw [htop, mul_div_mul_right 81 2 h]
  rw [hmul]
  ring

#print axioms Karlin.rps_gain_correction_cancels

/-!
## Part 2: Section 7.1 (Baseline Moment Cancellation & Gain Shift Expansion)
-/

/-- Outer product / rank-one matrix `(u ⊗ v)_{i,j} = u i * v j`. -/
def outerProd {n m : Type*} (u : n → ℚ) (v : m → ℚ) : Matrix n m ℚ :=
  Matrix.of fun i j => u i * v j

theorem outerProd_transpose {n m : Type*} (u : n → ℚ) (v : m → ℚ) :
    (outerProd u v).transpose = outerProd v u := by
  ext i j
  dsimp [outerProd]
  exact mul_comm (u j) (v i)

#print axioms Karlin.outerProd_transpose

theorem outerProd_mul {n m k : Type*} [Fintype m] (u : n → ℚ) (v : m → ℚ) (M : Matrix m k ℚ) :
    outerProd u v * M = outerProd u (Matrix.vecMul v M) := by
  ext i j
  dsimp [outerProd, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  simp_rw [mul_assoc, ← Finset.mul_sum]

#print axioms Karlin.outerProd_mul

theorem mul_outerProd {n m k : Type*} [Fintype m] (M : Matrix n m ℚ) (u : m → ℚ) (v : k → ℚ) :
    M * outerProd u v = outerProd (Matrix.mulVec M u) v := by
  ext i j
  dsimp [outerProd, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have : (∑ x : m, M i x * (u x * v j)) = (∑ x : m, M i x * u x) * v j := by
    simp_rw [← mul_assoc, ← Finset.sum_mul]
  rw [this]

#print axioms Karlin.mul_outerProd

theorem outerProd_mul_outerProd {n m k : Type*} [Fintype m]
    (u : n → ℚ) (v : m → ℚ) (w : m → ℚ) (z : k → ℚ) :
    outerProd u v * outerProd w z = (dotProduct v w) • outerProd u z := by
  ext i j
  dsimp [outerProd, Matrix.mul_apply, dotProduct]
  have : (∑ x : m, u i * v x * (w x * z j)) = (∑ x : m, v x * w x) * (u i * z j) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    have : (∑ x : m, v x * (w x * z j)) = (∑ x : m, v x * w x) * z j := by
      simp_rw [← mul_assoc, ← Finset.sum_mul]
    rw [this]
    ring
  rw [this]

#print axioms Karlin.outerProd_mul_outerProd

theorem L_moment_rank1_symmetric {w : Type*} [Fintype w]
    (B : Matrix w w ℚ) (u : w → ℚ) (c : ℚ) :
    L_moment B (outerProd (c • u) u) = - outerProd (c • u) (Matrix.vecMul u B - u) := by
  dsimp [L_moment]
  have hsymm : (outerProd (c • u) u)ᵀ = outerProd (c • u) u := by
    ext i j
    dsimp [outerProd]
    ring
  rw [hsymm, outerProd_mul]
  ext i j
  dsimp [outerProd]
  ring

#print axioms Karlin.L_moment_rank1_symmetric

/-- **Baseline Moment Cancellation (`prop:momentchoice`, Section 7.1)**:
    For $E_0 = 2 r \lambda (\zeta^\circ)^\top \zeta^\circ$, $\ell_0 = 2 r \lambda \zeta^\circ$,
    and $\psi^\circ = \zeta^\circ B - \zeta^\circ$, we have:
    $$\mathcal{L}(E_0) = -\ell_0^\top \psi^\circ.$$ -/
theorem baseline_moment_cancellation {w : Type*} [Fintype w]
    (B : Matrix w w ℚ) (zeta0 : w → ℚ) (r lambda : ℚ) :
    let ell0 := (2 * r * lambda) • zeta0
    let psi0 := Matrix.vecMul zeta0 B - zeta0
    let E0 := outerProd ell0 zeta0
    L_moment B E0 = - outerProd ell0 psi0 := by
  intro ell0 psi0 E0
  dsimp [E0, ell0, psi0]
  exact L_moment_rank1_symmetric B zeta0 (2 * r * lambda)

#print axioms Karlin.baseline_moment_cancellation

/-- Gain shift scaling of the baseline moment cancellation under the reset scale factor $T_1$:
    $\mathcal{L}(T_1 E_0) = - (T_1 \ell_0)^\top \psi^\circ$. -/
theorem L_moment_scaled_E0 {w : Type*} [Fintype w]
    (B : Matrix w w ℚ) (zeta0 : w → ℚ) (r lambda T1 : ℚ) :
    let ell0 := (2 * r * lambda) • zeta0
    let psi0 := Matrix.vecMul zeta0 B - zeta0
    let E0 := outerProd ell0 zeta0
    L_moment B (T1 • E0) = - outerProd (T1 • ell0) psi0 := by
  intro ell0 psi0 E0
  dsimp [E0, ell0, psi0]
  have hsmul : T1 • outerProd ((2 * r * lambda) • zeta0) zeta0 =
      outerProd ((T1 * (2 * r * lambda)) • zeta0) zeta0 := by
    ext i j
    dsimp [outerProd]
    ring
  rw [hsmul]
  have hsymm := L_moment_rank1_symmetric B zeta0 (T1 * (2 * r * lambda))
  rw [hsymm]
  congr 1
  ext i j
  dsimp [outerProd]
  ring

#print axioms Karlin.L_moment_scaled_E0

/-!
## Part 3: Sections 7.1 & 7.2 (Reset Inverses, Sherman-Morrison, & Quadratic Realization)
-/

/-- The coordinate adjustment matrix $V_0 \in \mathbb{Z}^{(k+1) \times (k+1)}$
    from Section 7.1 (`eq:W`), with $V_0 = \begin{pmatrix} I_k & 0 \\ -\mathbf{1}_k^\top & 0 \end{pmatrix}$. -/
def V0_paper (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  Matrix.of fun x y =>
    match finSumFinEquiv.symm x, finSumFinEquiv.symm y with
    | Sum.inl i, Sum.inl j => if i = j then 1 else 0
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr _, Sum.inl _ => -1
    | Sum.inr _, Sum.inr _ => 0

/-- Row sum of $V_0$ vanishes: $\mathbf{1}_{k+1}^\top V_0 = 0$ (Section 7.1). -/
theorem vecMul_one_V0 (k : ℕ) :
    Matrix.vecMul (fun _ : Fin (k + 1) => (1 : ℚ)) (V0_paper k) = 0 := by
  ext y
  dsimp [Matrix.vecMul, dotProduct]
  have hcomp := (Equiv.sum_comp finSumFinEquiv fun x => (1 : ℚ) * V0_paper k x y).symm
  rw [hcomp, Fintype.sum_sum_type]
  simp only [one_mul]
  cases hy : finSumFinEquiv.symm y with
  | inl j =>
    have hinl : (∑ i : Fin k, V0_paper k (finSumFinEquiv (Sum.inl i)) y) = 1 := by
      simp only [V0_paper, Matrix.of_apply, hy, Equiv.symm_apply_apply]
      rw [Finset.sum_ite_eq' Finset.univ j]
      simp
    have hinr : (∑ i : Fin 1, V0_paper k (finSumFinEquiv (Sum.inr i)) y) = -1 := by
      have : (Finset.univ : Finset (Fin 1)) = {0} := rfl
      rw [this, Finset.sum_singleton]
      simp [V0_paper, Matrix.of_apply, hy]
    rw [hinl, hinr]
    ring
  | inr j =>
    have hinl : (∑ i : Fin k, V0_paper k (finSumFinEquiv (Sum.inl i)) y) = 0 := by
      simp [V0_paper, Matrix.of_apply, hy]
    have hinr : (∑ i : Fin 1, V0_paper k (finSumFinEquiv (Sum.inr i)) y) = 0 := by
      simp [V0_paper, Matrix.of_apply, hy]
    rw [hinl, hinr, add_zero]

#print axioms Karlin.vecMul_one_V0

/-- Last column of $V_0$ is identically zero (Section 7.1). -/
theorem V0_last_col_zero (k : ℕ) (x : Fin (k + 1)) :
    V0_paper k x (finSumFinEquiv (Sum.inr 0)) = 0 := by
  simp [V0_paper]
  cases finSumFinEquiv.symm x <;> rfl

#print axioms Karlin.V0_last_col_zero

/-- Projector $\Pi = [I_k \mid 0] - \frac{1}{r} \mathbf{1}_k \mathbf{1}_r^\top \in \mathbb{Q}^{k \times (k+1)}$ (Section 7.2, Eq. (1721)). -/
def Pi_mat (k : ℕ) : Matrix (Fin k) (Fin (k + 1)) ℚ :=
  Matrix.of fun i y =>
    match finSumFinEquiv.symm y with
    | Sum.inl j => (if i = j then 1 else 0) - (1 / (k + 1 : ℚ))
    | Sum.inr _ => - (1 / (k + 1 : ℚ))

/-- $\Pi \mathbf{1}_{k+1} = 0$ (Section 7.2). -/
theorem mulVec_Pi_one (k : ℕ) :
    Matrix.mulVec (Pi_mat k) (fun _ : Fin (k + 1) => (1 : ℚ)) = 0 := by
  ext i
  dsimp [Matrix.mulVec, dotProduct]
  have hcomp := (Equiv.sum_comp finSumFinEquiv fun y => Pi_mat k i y * 1).symm
  rw [hcomp, Fintype.sum_sum_type]
  simp only [mul_one]
  have hinl : (∑ j : Fin k, Pi_mat k i (finSumFinEquiv (Sum.inl j))) =
      1 - (k : ℚ) * (1 / (k + 1 : ℚ)) := by
    simp only [Pi_mat, Matrix.of_apply, Equiv.symm_apply_apply]
    rw [Finset.sum_sub_distrib]
    have : (∑ j : Fin k, if i = j then (1:ℚ) else 0) = 1 := by
      rw [Finset.sum_ite_eq]
      simp
    rw [this]
    simp [Finset.card_univ]
  have hinr : (∑ j : Fin 1, Pi_mat k i (finSumFinEquiv (Sum.inr j))) =
      - (1 / (k + 1 : ℚ)) := by
    have : (Finset.univ : Finset (Fin 1)) = {0} := rfl
    rw [this, Finset.sum_singleton]
    simp [Pi_mat, Matrix.of_apply]
  rw [hinl, hinr]
  have hr : (k + 1 : ℚ) ≠ 0 := by positivity
  calc
    1 - (k : ℚ) * (1 / (k + 1 : ℚ)) + - (1 / (k + 1 : ℚ))
      = 1 - ((k : ℚ) + 1) * (k + 1 : ℚ)⁻¹ := by ring
    _ = 1 - 1 := by rw [mul_inv_cancel₀ hr]
    _ = 0 := sub_self 1

#print axioms Karlin.mulVec_Pi_one

/-- $\Pi V_0 = [I_k \mid 0]$ (Section 7.2). -/
theorem Pi_mul_V0 (k : ℕ) :
    Pi_mat k * V0_paper k =
      Matrix.of fun i y =>
        match finSumFinEquiv.symm y with
        | Sum.inl j => if i = j then 1 else 0
        | Sum.inr _ => 0 := by
  ext i y
  simp only [Matrix.mul_apply, Matrix.of_apply]
  have hcomp := (Equiv.sum_comp finSumFinEquiv fun z => Pi_mat k i z * V0_paper k z y).symm
  rw [hcomp, Fintype.sum_sum_type]
  cases hy : finSumFinEquiv.symm y with
  | inl j =>
    have hinl : (∑ l : Fin k, Pi_mat k i (finSumFinEquiv (Sum.inl l)) *
        V0_paper k (finSumFinEquiv (Sum.inl l)) y) =
        Pi_mat k i (finSumFinEquiv (Sum.inl j)) := by
      simp only [V0_paper, Matrix.of_apply, hy, Equiv.symm_apply_apply]
      rw [← Finset.sum_subset (Finset.subset_univ {j})]
      · rw [Finset.sum_singleton]
        simp
      · intro l _ hlj
        simp only [Finset.mem_singleton] at hlj
        simp [hlj]
    have hinr : (∑ l : Fin 1, Pi_mat k i (finSumFinEquiv (Sum.inr l)) *
        V0_paper k (finSumFinEquiv (Sum.inr l)) y) =
        1 / (k + 1 : ℚ) := by
      have : (Finset.univ : Finset (Fin 1)) = {0} := rfl
      rw [this, Finset.sum_singleton]
      simp [Pi_mat, V0_paper, Matrix.of_apply, hy]
    rw [hinl, hinr]
    simp [Pi_mat, Matrix.of_apply]
  | inr j =>
    have hinl : (∑ l : Fin k, Pi_mat k i (finSumFinEquiv (Sum.inl l)) *
        V0_paper k (finSumFinEquiv (Sum.inl l)) y) = 0 := by
      simp [V0_paper, Matrix.of_apply, hy]
    have hinr : (∑ l : Fin 1, Pi_mat k i (finSumFinEquiv (Sum.inr l)) *
        V0_paper k (finSumFinEquiv (Sum.inr l)) y) = 0 := by
      simp [V0_paper, Matrix.of_apply, hy]
    rw [hinl, hinr, add_zero]

#print axioms Karlin.Pi_mul_V0

/-- The late reset count block $W = \mathbf{1}_r \upsilon + T_2 V_0$ from Section 7.1 (`eq:W`). -/
def W_paper {r : Type*} [Fintype r] (upsilon : r → ℚ) (T2 : ℚ) (V0 : Matrix r r ℚ) : Matrix r r ℚ :=
  outerProd (fun _ => 1) upsilon + T2 • V0

/-- Row sum of $W$: $\mathbf{1}_r^\top W = r \upsilon$ when $\mathbf{1}_r^\top V_0 = 0$ (Section 7.1). -/
theorem vecMul_one_W_paper {r : Type*} [Fintype r] (upsilon : r → ℚ) (T2 : ℚ) (V0 : Matrix r r ℚ)
    (hV0 : Matrix.vecMul (fun _ => 1) V0 = 0) :
    Matrix.vecMul (fun _ => 1) (W_paper upsilon T2 V0) = (Fintype.card r : ℚ) • upsilon := by
  dsimp [W_paper]
  rw [Matrix.vecMul_add, Matrix.vecMul_smul, hV0, smul_zero, add_zero]
  ext j
  dsimp [outerProd, Matrix.vecMul, dotProduct]
  simp only [one_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

#print axioms Karlin.vecMul_one_W_paper

/-- Inverse $W^{-1} = T_1^{-1} \Phi_0 + T_2^{-1} \Phi_1$ from Section 7.2 (`eq:inverse`). -/
def W_inv_paper {r : Type*} (T1 T2 : ℚ) (Phi0 Phi1 : Matrix r r ℚ) : Matrix r r ℚ :=
  T1⁻¹ • Phi0 + T2⁻¹ • Phi1

/-- **Two-Sided Inverse of $W$ (Right Inverse, Section 7.2, Eq. (1721))**:
    If $\Phi_0, \Phi_1$ satisfy the block identities
    $\mathbf{1}_r \upsilon \Phi_0 = T_1 \frac{1}{r} \mathbf{1}_r \mathbf{1}_r^\top$,
    $V_0 \Phi_0 = 0$,
    $\upsilon \Phi_1 = 0$,
    and $V_0 \Phi_1 = I_r - \frac{1}{r} \mathbf{1}_r \mathbf{1}_r^\top$,
    with $T_1 \ne 0$ and $T_2 \ne 0$, then $W W^{-1} = I_r$. -/
theorem W_mul_Winv_paper {r : Type*} [Fintype r] [DecidableEq r]
    (upsilon : r → ℚ) (T1 T2 : ℚ) (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0)
    (V0 Phi0 Phi1 : Matrix r r ℚ)
    (hW0 : outerProd (fun _ : r => (1:ℚ)) upsilon * Phi0 = T1 • ((Fintype.card r : ℚ)⁻¹ • outerProd (fun _ : r => (1:ℚ)) (fun _ : r => (1:ℚ))))
    (hV0Phi0 : V0 * Phi0 = 0)
    (hupsiPhi1 : outerProd (fun _ : r => (1:ℚ)) upsilon * Phi1 = 0)
    (hV0Phi1 : V0 * Phi1 = 1 - (Fintype.card r : ℚ)⁻¹ • outerProd (fun _ : r => (1:ℚ)) (fun _ : r => (1:ℚ))) :
    W_paper upsilon T2 V0 * W_inv_paper T1 T2 Phi0 Phi1 = 1 := by
  dsimp [W_paper, W_inv_paper]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hV0Phi0, smul_zero, add_zero]
  rw [hupsiPhi1, zero_add]
  rw [hW0, hV0Phi1]
  rw [smul_smul, inv_mul_cancel₀ hT1, one_smul]
  rw [smul_smul, inv_mul_cancel₀ hT2, one_smul]
  abel

#print axioms Karlin.W_mul_Winv_paper

/-- **Two-Sided Inverse of $W$ (Left Inverse, Section 7.2, Eq. (1721))**:
    If $\Phi_0, \Phi_1$ satisfy the left block identities
    $\Phi_0 \mathbf{1}_r \upsilon = T_1 \Pi_{\mathrm{proj}}$,
    $\Phi_0 V_0 = 0$,
    $\Phi_1 \mathbf{1}_r \upsilon = 0$,
    and $\Phi_1 V_0 = I_r - \Pi_{\mathrm{proj}}$,
    with $T_1 \ne 0$ and $T_2 \ne 0$, then $W^{-1} W = I_r$. -/
theorem Winv_mul_W_paper {r : Type*} [Fintype r] [DecidableEq r]
    (upsilon : r → ℚ) (T1 T2 : ℚ) (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0)
    (V0 Phi0 Phi1 Proj : Matrix r r ℚ)
    (hPhi0W : Phi0 * outerProd (fun _ : r => (1:ℚ)) upsilon = T1 • Proj)
    (hPhi0V0 : Phi0 * V0 = 0)
    (hPhi1W : Phi1 * outerProd (fun _ : r => (1:ℚ)) upsilon = 0)
    (hPhi1V0 : Phi1 * V0 = 1 - Proj) :
    W_inv_paper T1 T2 Phi0 Phi1 * W_paper upsilon T2 V0 = 1 := by
  dsimp [W_paper, W_inv_paper]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hPhi0V0, smul_zero, zero_add]
  rw [hPhi1W, smul_zero, add_zero]
  rw [hPhi0W, hPhi1V0]
  rw [smul_smul, inv_mul_cancel₀ hT1, one_smul]
  rw [smul_smul, mul_inv_cancel₀ hT2, one_smul]
  abel

#print axioms Karlin.Winv_mul_W_paper

/-- **Sherman-Morrison Inversion Formula for $W_E = W + e_0 \ell_*$ (Section 7.2, Eq. (1721))**:
    For invertible $W$ with $W W^{-1} = 1$, rank-one update $W_E = W + u \otimes v$,
    and scalar denominator $\delta = 1 + v^\top W^{-1} u \ne 0$,
    the matrix $W_E^{-1} = W^{-1} - \frac{1}{\delta} W^{-1} (u \otimes v) W^{-1}$ satisfies $W_E W_E^{-1} = I$. -/
theorem sherman_morrison_rank1_inv {r : Type*} [Fintype r] [DecidableEq r]
    (W Winv : Matrix r r ℚ) (hW : W * Winv = 1)
    (u v : r → ℚ)
    (hdenom : 1 + dotProduct v (Matrix.mulVec Winv u) ≠ 0) :
    let d := 1 + dotProduct v (Matrix.mulVec Winv u)
    let WE := W + outerProd u v
    let WE_inv := Winv - d⁻¹ • (Winv * (outerProd u v * Winv))
    WE * WE_inv = 1 := by
  intro d WE WE_inv
  dsimp [WE, WE_inv]
  simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.mul_smul]
  rw [hW]
  have h1 : W * (Winv * (outerProd u v * Winv)) = outerProd u v * Winv := by
    rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
  rw [h1]
  have h2 : outerProd u v * (Winv * (outerProd u v * Winv)) =
      (dotProduct v (Matrix.mulVec Winv u)) • (outerProd u v * Winv) := by
    rw [← Matrix.mul_assoc Winv, mul_outerProd, ← Matrix.mul_assoc (outerProd u v),
        outerProd_mul_outerProd, Matrix.smul_mul]
  rw [h2]
  have hd_inv : d⁻¹ * d = 1 := inv_mul_cancel₀ hdenom
  have h_scalar : (1 : ℚ) - d⁻¹ - d⁻¹ * dotProduct v (Matrix.mulVec Winv u) = 0 := by
    dsimp [d]
    calc
      (1 : ℚ) - d⁻¹ - d⁻¹ * dotProduct v (Matrix.mulVec Winv u)
        = 1 - d⁻¹ * (1 + dotProduct v (Matrix.mulVec Winv u)) := by ring
      _ = 1 - 1 := by rw [hd_inv]
      _ = 0 := sub_self 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  set A := (outerProd u v * Winv) i j
  linear_combination A * h_scalar

#print axioms Karlin.sherman_morrison_rank1_inv

/-- **Exact Quadratic Realization $M^\top J M = E$ (Section 7.2, Eq. (1723))**:
    For $M = \begin{pmatrix} W_E \\ W \end{pmatrix}$ and $J = \begin{pmatrix} \eta L_r & 0 \\ C_\times & \eta L_r \end{pmatrix}$,
    we have $M^\top J M = \eta (W_E^\top L_r W_E + W^\top L_r W) + W^\top C_\times W_E$.
    With $C_\times = \kappa \mathbf{1}_r \mathbf{1}_r^\top + W^{-\top} F_{\mathrm{res}} W_E^{-1}$,
    $W^\top C_\times W_E = E_{\mathrm{base}} + F_{\mathrm{res}}$, realizing $M^\top J M = E$. -/
theorem M_transpose_mul_J_mul_M {r w : Type*} [Fintype r] [Fintype w] [DecidableEq r] [DecidableEq w]
    (WE W : Matrix r w ℚ) (WE_inv Winv : Matrix w r ℚ)
    (hWE : WE_inv * WE = 1) (hW : Wᵀ * Winvᵀ = 1)
    (eta kappa : ℚ) (Lr : Matrix r r ℚ)
    (E E_base : Matrix w w ℚ)
    (Fres : Matrix w w ℚ)
    (hFres : Fres = E - E_base - eta • (WEᵀ * Lr * WE + Wᵀ * Lr * W))
    (C_cross : Matrix r r ℚ)
    (hC_cross : C_cross = kappa • (outerProd (fun _ : r => (1:ℚ)) (fun _ : r => (1:ℚ))) + Winvᵀ * Fres * WE_inv)
    (hEbase : Wᵀ * (kappa • (outerProd (fun _ : r => (1:ℚ)) (fun _ : r => (1:ℚ)))) * WE = E_base) :
    eta • (WEᵀ * Lr * WE + Wᵀ * Lr * W) + Wᵀ * C_cross * WE = E := by
  rw [hC_cross]
  simp only [Matrix.mul_add, Matrix.add_mul]
  rw [hEbase]
  have hmid : Wᵀ * (Winvᵀ * Fres * WE_inv) * WE = Fres := by
    calc
      Wᵀ * (Winvᵀ * Fres * WE_inv) * WE
        = (Wᵀ * Winvᵀ) * Fres * (WE_inv * WE) := by
          simp only [Matrix.mul_assoc]
      _ = 1 * Fres * 1 := by rw [hW, hWE]
      _ = Fres := by simp only [Matrix.one_mul, Matrix.mul_one]
  rw [hmid, hFres]
  abel

#print axioms Karlin.M_transpose_mul_J_mul_M

/-!
## Part 4: Sections 7.3 & 8.1 (Parameter Cancellation, Score Invariance, & Late Weight Decomposition)
-/

/-- **Auxiliary Parameter Cancellation in $P_0 M = -a \ell_*$ (Section 7.3 & 8.1)**:
    For $P_0 = [-a \mathbf{1}_r^\top \mid a \mathbf{1}_r^\top]$ and $M = \begin{pmatrix} W_E \\ W \end{pmatrix}$
    with $W_E = W + e_0 \ell_*$ and $\mathbf{1}_r^\top e_0 = 1$,
    the auxiliary scale $T_2$ cancels identically, giving:
    $$P_0 M = -a \mathbf{1}_r^\top W_E + a \mathbf{1}_r^\top W = -a \ell_*.$$ -/
theorem P0_mul_M_eq_neg_a_ell_star {m r w : Type*} [Fintype r]
    (a : m → ℚ) (W : Matrix r w ℚ) (ell_star : w → ℚ) (e0 : r → ℚ)
    (he0 : dotProduct (fun _ : r => (1 : ℚ)) e0 = 1) :
    let WE := W + outerProd e0 ell_star
    (- outerProd a (fun _ : r => (1:ℚ))) * WE + outerProd a (fun _ : r => (1:ℚ)) * W = - outerProd a ell_star := by
  intro WE
  dsimp [WE]
  rw [Matrix.neg_mul, Matrix.mul_add, outerProd_mul_outerProd, he0, one_smul]
  abel

#print axioms Karlin.P0_mul_M_eq_neg_a_ell_star

/-- **Reset Contribution to Rotated Table Product $R_+^\top C_+$ (Section 8.1, Eq. (1734))**:
    The reset block rows contribute $(\mathbf{1}_{2r} \zeta - J M)^\top M = \zeta^\top \ell - E^\top$,
    independent of the auxiliary parameter $T_2$:
    $$(\mathbf{1}_{2r} \zeta - J M)^\top M = \zeta^\top (\mathbf{1}_{2r}^\top M) - (M^\top J M)^\top = \zeta^\top \ell - E^\top.$$ -/
theorem reset_contribution_to_RtC {r2 w : Type*} [Fintype r2] [Fintype w]
    (zeta : w → ℚ) (ell : w → ℚ) (M : Matrix r2 w ℚ) (J : Matrix r2 r2 ℚ)
    (E : Matrix w w ℚ)
    (h_row_sum : Matrix.vecMul (fun _ : r2 => (1:ℚ)) M = ell)
    (h_realize : Mᵀ * J * M = E) :
    (outerProd (fun _ : r2 => (1:ℚ)) zeta - J * M)ᵀ * M =
      outerProd zeta ell - Eᵀ := by
  rw [Matrix.transpose_sub, Matrix.sub_mul]
  rw [outerProd_transpose, outerProd_mul]
  rw [h_row_sum]
  have hJM : (J * M)ᵀ * M = Eᵀ := by
    calc
      (J * M)ᵀ * M = Mᵀ * Jᵀ * M := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (Mᵀ * J * M)ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = Eᵀ := by rw [h_realize]
  rw [hJM]

#print axioms Karlin.reset_contribution_to_RtC

/-- **Late Weight Decomposition (Section 8.1, Eq. (1736))**:
    Multiplying the residual target $t_{\mathrm{rem}}$ by $W^{-1} = T_1^{-1} \Phi_0 + T_2^{-1} \Phi_1$ gives:
    $$t_{\mathrm{rem}} W^{-1} = \alpha \mathbf{1}_r^\top + T_2^{-1} t_{\mathrm{rem}} \Phi_1,$$
    where $\alpha = (t_{\mathrm{rem}})_k / (r \upsilon_k) > 0$. -/
theorem late_weight_decomposition {r w : Type*} [Fintype w]
    (trem : w → ℚ) (T1 T2 alpha : ℚ)
    (Phi0 Phi1 : Matrix w r ℚ)
    (hPhi0 : Matrix.vecMul trem (T1⁻¹ • Phi0) = alpha • (fun _ : r => (1 : ℚ))) :
    Matrix.vecMul trem (T1⁻¹ • Phi0 + T2⁻¹ • Phi1) =
      alpha • (fun _ : r => (1:ℚ)) + T2⁻¹ • Matrix.vecMul trem Phi1 := by
  rw [Matrix.vecMul_add, hPhi0, Matrix.vecMul_smul]

#print axioms Karlin.late_weight_decomposition

/-- **Cone Reconstruction Identity (Section 8.1, Eq. (1738))**:
    $$\mu r_0 + (t_{\mathrm{rem}} W^{-1}) W = \mu r_0 + t_{\mathrm{rem}} = t_+.$$ -/
theorem cone_weight_reconstruction {r w : Type*} [Fintype r]
    (t_plus r0 trem : w → ℚ) (mu : ℚ)
    (W : Matrix r w ℚ) (W_weights : r → ℚ)
    (htrem : trem = t_plus - mu • r0)
    (hW_inv : Matrix.vecMul W_weights W = trem) :
    mu • r0 + Matrix.vecMul W_weights W = t_plus := by
  rw [hW_inv, htrem]
  abel

#print axioms Karlin.cone_weight_reconstruction

/-!
## Part 5: Section 6.1 — Divided-Power Cokernel Basis Z_DP^{(h)}, Z^{(h)} & Kernel Completeness (Lemma 6.1)
-/

theorem neg_one_pow_eq_of_add_even {a b : ℕ} (h : Even (a + b)) : (-1 : ℚ) ^ a = (-1 : ℚ) ^ b := by
  obtain ⟨m, hm⟩ := h
  have h1 : (-1 : ℚ) ^ (a + b) = 1 := by
    have : a + b = 2 * m := by omega
    rw [this, pow_mul]
    norm_num
  have h2 : (-1 : ℚ) ^ (a + b) = (-1 : ℚ) ^ a * (-1 : ℚ) ^ b := by rw [pow_add]
  have h3 : (-1 : ℚ) ^ a * (-1 : ℚ) ^ b = 1 := by rw [← h2, h1]
  have h_sq : (-1 : ℚ) ^ b * (-1 : ℚ) ^ b = 1 := by
    rw [← pow_add]
    have : b + b = 2 * b := by omega
    rw [this, pow_mul]
    norm_num
  calc (-1 : ℚ) ^ a = (-1 : ℚ) ^ a * 1 := by ring
  _ = (-1 : ℚ) ^ a * ((-1 : ℚ) ^ b * (-1 : ℚ) ^ b) := by rw [h_sq]
  _ = ((-1 : ℚ) ^ a * (-1 : ℚ) ^ b) * (-1 : ℚ) ^ b := by ring
  _ = 1 * (-1 : ℚ) ^ b := by rw [h3]
  _ = (-1 : ℚ) ^ b := by ring

#print axioms Karlin.neg_one_pow_eq_of_add_even

/-- Subdiagonal shift matrix `N0_mat w` (Eq. (1294)). -/
def N0_mat (w : ℕ) : Matrix (Fin w) (Fin w) ℚ :=
  Matrix.of fun i j => if i.val = j.val + 1 then 1 else 0

/-- Coordinate form of the nilpotent matrix exponential `exp(t * N0)` (Eq. (1538)). -/
def expN0 (w : ℕ) (t : ℚ) : Matrix (Fin w) (Fin w) ℚ :=
  Matrix.of fun i j =>
    if j.val ≤ i.val then
      t ^ (i.val - j.val) / (Nat.factorial (i.val - j.val) : ℚ)
    else 0

/-- Lower-triangular vanishing of `expN0`. -/
theorem expN0_apply_of_lt {w : ℕ} (t : ℚ) {i j : Fin w} (h : i.val < j.val) :
    expN0 w t i j = 0 := by
  dsimp [expN0]
  rw [if_neg (not_le.mpr h)]

#print axioms Karlin.expN0_apply_of_lt

/-- Diagonal unit entries of `expN0`. -/
theorem expN0_apply_self {w : ℕ} (t : ℚ) (i : Fin w) :
    expN0 w t i i = 1 := by
  dsimp [expN0]
  simp

#print axioms Karlin.expN0_apply_self

theorem exp_binomial_sum (s t : ℚ) (d : ℕ) :
    (s + t) ^ d / (Nat.factorial d : ℚ) =
      ∑ m ∈ Finset.range (d + 1),
        (s ^ (d - m) / (Nat.factorial (d - m) : ℚ)) * (t ^ m / (Nat.factorial m : ℚ)) := by
  have hbin : (s + t) ^ d = ∑ m ∈ Finset.range (d + 1), (d.choose m : ℚ) * (s ^ (d - m) * t ^ m) := by
    rw [add_comm s t, add_pow t s d]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hbin, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  have hle : m ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  have hfac : (d.choose m : ℚ) = (Nat.factorial d : ℚ) / ((Nat.factorial (d - m) : ℚ) * (Nat.factorial m : ℚ)) := by
    have h1 := Nat.choose_mul_factorial_mul_factorial hle
    have h2 : ((d.choose m : ℚ) * (Nat.factorial m : ℚ)) * (Nat.factorial (d - m) : ℚ) = (Nat.factorial d : ℚ) := by
      exact_mod_cast h1
    have hm_pos : (Nat.factorial m : ℚ) ≠ 0 := by positivity
    have hdm_pos : (Nat.factorial (d - m) : ℚ) ≠ 0 := by positivity
    rw [← h2]
    field_simp
  rw [hfac]
  have hm_pos : (Nat.factorial m : ℚ) ≠ 0 := by positivity
  have hdm_pos : (Nat.factorial (d - m) : ℚ) ≠ 0 := by positivity
  have hd_pos : (Nat.factorial d : ℚ) ≠ 0 := by positivity
  field_simp

#print axioms Karlin.exp_binomial_sum

theorem sum_filter_d {w : ℕ} {j i : Fin w} (hle : j.val ≤ i.val) (g : ℕ → ℚ) :
    (∑ k : Fin w, (if k.val ≤ i.val ∧ j.val ≤ k.val then g (k.val - j.val) else 0)) =
      ∑ m ∈ Finset.range (i.val - j.val + 1), g m := by
  set d := i.val - j.val
  have hsum_filter : (∑ k : Fin w, (if k.val ≤ i.val ∧ j.val ≤ k.val then g (k.val - j.val) else 0)) =
      ∑ k ∈ Finset.univ.filter (fun k : Fin w => k.val ≤ i.val ∧ j.val ≤ k.val), g (k.val - j.val) := by
    rw [← Finset.sum_filter]
  rw [hsum_filter]
  symm
  apply Finset.sum_bij (fun m _ => (⟨j.val + m, by
    have hm_le : m ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp ‹_›)
    have : j.val + m < w := by omega
    exact this⟩ : Fin w))
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hm_le : m ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    omega
  · intro m1 hm1 m2 hm2 heq
    simp only [Fin.mk.injEq, add_right_inj] at heq
    exact heq
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    refine ⟨k.val - j.val, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · ext
      dsimp
      omega
  · intro m hm
    dsimp
    simp only [add_tsub_cancel_left]

#print axioms Karlin.sum_filter_d

/-- Matrix exponential addition homomorphism: `exp(s * N0) * exp(t * N0) = exp((s + t) * N0)`. -/
theorem expN0_mul_expN0 (w : ℕ) (s t : ℚ) : expN0 w s * expN0 w t = expN0 w (s + t) := by
  ext i j
  dsimp [Matrix.mul_apply, expN0]
  by_cases hle : j.val ≤ i.val
  · rw [if_pos hle]
    set d := i.val - j.val
    have hterm : ∀ k : Fin w,
        (if k.val ≤ i.val then s ^ (i.val - k.val) / (Nat.factorial (i.val - k.val) : ℚ) else 0) *
        (if j.val ≤ k.val then t ^ (k.val - j.val) / (Nat.factorial (k.val - j.val) : ℚ) else 0) =
        if k.val ≤ i.val ∧ j.val ≤ k.val then
          (s ^ (d - (k.val - j.val)) / (Nat.factorial (d - (k.val - j.val)) : ℚ)) *
          (t ^ (k.val - j.val) / (Nat.factorial (k.val - j.val) : ℚ))
        else 0 := by
      intro k
      by_cases h : k.val ≤ i.val ∧ j.val ≤ k.val
      · rw [if_pos h.1, if_pos h.2, if_pos h]
        have : i.val - k.val = d - (k.val - j.val) := by omega
        rw [this]
      · rw [if_neg h]
        push_neg at h
        by_cases h1 : k.val ≤ i.val
        · have h2 := h h1
          rw [if_neg (not_le.mpr h2), mul_zero]
        · rw [if_neg h1, zero_mul]
    simp_rw [hterm]
    have hsum := sum_filter_d hle (fun m =>
      (s ^ (d - m) / (Nat.factorial (d - m) : ℚ)) *
      (t ^ m / (Nat.factorial m : ℚ)))
    rw [hsum, ← exp_binomial_sum s t d]
  · rw [if_neg hle]
    apply Finset.sum_eq_zero
    intro k _
    by_cases h1 : k.val ≤ i.val
    · have h2 : ¬ j.val ≤ k.val := by omega
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

#print axioms Karlin.expN0_mul_expN0

/-- Identity property at `t = 0`: `exp(0 * N0) = 1`. -/
theorem expN0_zero (w : ℕ) : expN0 w 0 = 1 := by
  ext i j
  dsimp [expN0, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · by_cases hle : j.val ≤ i.val
    · have hpos : i.val - j.val ≠ 0 := by
        intro h; apply hij; ext; omega
      rw [if_pos hle, if_neg hij, zero_pow hpos, zero_div]
    · rw [if_neg hle, if_neg hij]

#print axioms Karlin.expN0_zero

/-- Inverse property: `exp(-t * N0) * exp(t * N0) = 1`. -/
theorem expN0_neg_mul_cancel (w : ℕ) (t : ℚ) : expN0 w (-t) * expN0 w t = 1 := by
  rw [expN0_mul_expN0, neg_add_cancel, expN0_zero]

#print axioms Karlin.expN0_neg_mul_cancel

/-- Inverse property: `exp(t * N0) * exp(-t * N0) = 1`. -/
theorem expN0_mul_neg_cancel (w : ℕ) (t : ℚ) : expN0 w t * expN0 w (-t) = 1 := by
  rw [expN0_mul_expN0, add_neg_cancel, expN0_zero]

#print axioms Karlin.expN0_mul_neg_cancel

/-- Composition identity: `exp(-N0) * exp(N0 / 2) = exp(-N0 / 2)`. -/
theorem expN0_neg_one_mul_half (w : ℕ) :
    expN0 w (-1) * expN0 w (1/2) = expN0 w (-1/2) := by
  rw [expN0_mul_expN0]
  norm_num

#print axioms Karlin.expN0_neg_one_mul_half

/-- Anti-diagonal alternating sign matrix `V_antidiag w h` (Eq. (1296)). -/
def V_antidiag (w h : ℕ) : Matrix (Fin w) (Fin w) ℚ :=
  Matrix.of fun i j => if i.val + j.val = h then (-1 : ℚ) ^ i.val else 0

/-- Symmetry of `V_antidiag` for even anti-diagonal sum `h` (Eq. (1560)). -/
theorem V_antidiag_transpose_of_even {w h : ℕ} (hh : Even h) :
    (V_antidiag w h).transpose = V_antidiag w h := by
  ext i j
  dsimp [Matrix.transpose_apply, V_antidiag]
  have hcomm : j.val + i.val = i.val + j.val := by omega
  rw [hcomm]
  by_cases hij : i.val + j.val = h
  · rw [if_pos hij, if_pos hij]
    have heven : Even (j.val + i.val) := by
      rw [hcomm, hij]
      exact hh
    exact neg_one_pow_eq_of_add_even heven
  · rw [if_neg hij, if_neg hij]

#print axioms Karlin.V_antidiag_transpose_of_even

theorem sum_single_pred {w : ℕ} (i : Fin w) (hi : i.val > 0) (f : Fin w → ℚ) :
    (∑ k : Fin w, (if i.val = k.val + 1 then (1 : ℚ) else 0) * f k) = f ⟨i.val - 1, by omega⟩ := by
  have hk0 : (⟨i.val - 1, by omega⟩ : Fin w) ∈ Finset.univ := Finset.mem_univ _
  have hneq : ∀ k ∈ Finset.univ, k ≠ ⟨i.val - 1, by omega⟩ → (if i.val = k.val + 1 then (1 : ℚ) else 0) * f k = 0 := by
    intro k _ hk
    have : ¬ i.val = k.val + 1 := by
      intro heq
      apply hk
      ext
      dsimp
      omega
    rw [if_neg this, zero_mul]
  have h := Finset.sum_eq_single_of_mem (⟨i.val - 1, by omega⟩ : Fin w) hk0 hneq
  rw [h]
  have heq : i.val = (⟨i.val - 1, by omega⟩ : Fin w).val + 1 := by dsimp; omega
  rw [if_pos heq, one_mul]

#print axioms Karlin.sum_single_pred

theorem sum_single_pred_right {w : ℕ} (j : Fin w) (hj : j.val > 0) (f : Fin w → ℚ) :
    (∑ k : Fin w, f k * (if j.val = k.val + 1 then (1 : ℚ) else 0)) = f ⟨j.val - 1, by omega⟩ := by
  have hk0 : (⟨j.val - 1, by omega⟩ : Fin w) ∈ Finset.univ := Finset.mem_univ _
  have hneq : ∀ k ∈ Finset.univ, k ≠ ⟨j.val - 1, by omega⟩ → f k * (if j.val = k.val + 1 then (1 : ℚ) else 0) = 0 := by
    intro k _ hk
    have : ¬ j.val = k.val + 1 := by
      intro heq
      apply hk
      ext
      dsimp
      omega
    rw [if_neg this, mul_zero]
  have h := Finset.sum_eq_single_of_mem (⟨j.val - 1, by omega⟩ : Fin w) hk0 hneq
  rw [h]
  have heq : j.val = (⟨j.val - 1, by omega⟩ : Fin w).val + 1 := by dsimp; omega
  rw [if_pos heq, mul_one]

#print axioms Karlin.sum_single_pred_right

/-- Lie algebra derivation kernel property: `N0 * V^{(h)} + V^{(h)} * N0ᵀ = 0` (Eq. (1560)). -/
theorem N0_mul_V_antidiag_add_V_antidiag_mul_N0_transpose {w h : ℕ} (hh : w ≤ h + 1) :
    N0_mat w * V_antidiag w h + V_antidiag w h * (N0_mat w).transpose = 0 := by
  ext i j
  dsimp [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, N0_mat, V_antidiag]
  have hsum1 : (∑ k : Fin w, (if i.val = k.val + 1 then (1 : ℚ) else 0) *
      (if k.val + j.val = h then (-1 : ℚ) ^ k.val else 0)) =
      if i.val > 0 ∧ i.val - 1 + j.val = h then (-1 : ℚ) ^ (i.val - 1) else 0 := by
    by_cases hi : i.val > 0
    · rw [sum_single_pred i hi]
      dsimp
      by_cases h2 : i.val - 1 + j.val = h
      · rw [if_pos h2, if_pos ⟨hi, h2⟩]
      · rw [if_neg h2, if_neg (fun h => h2 h.2)]
    · rw [if_neg (fun h => hi h.1)]
      apply Finset.sum_eq_zero
      intro k _
      have : ¬ i.val = k.val + 1 := by omega
      rw [if_neg this, zero_mul]
  have hsum2 : (∑ k : Fin w, (if i.val + k.val = h then (-1 : ℚ) ^ i.val else 0) *
      (if j.val = k.val + 1 then (1 : ℚ) else 0)) =
      if j.val > 0 ∧ i.val + (j.val - 1) = h then (-1 : ℚ) ^ i.val else 0 := by
    by_cases hj : j.val > 0
    · rw [sum_single_pred_right j hj]
      dsimp
      by_cases h2 : i.val + (j.val - 1) = h
      · rw [if_pos h2, if_pos ⟨hj, h2⟩]
      · rw [if_neg h2, if_neg (fun h => h2 h.2)]
    · rw [if_neg (fun h => hj h.1)]
      apply Finset.sum_eq_zero
      intro k _
      have : ¬ j.val = k.val + 1 := by omega
      rw [if_neg this, mul_zero]
  rw [hsum1, hsum2]
  by_cases hsum_eq : i.val + j.val = h + 1
  · have hi : i.val > 0 := by
      by_contra hc
      have : i.val = 0 := by omega
      have : j.val = h + 1 := by omega
      have : j.val < w := j.isLt
      omega
    have hj : j.val > 0 := by
      by_contra hc
      have : j.val = 0 := by omega
      have : i.val = h + 1 := by omega
      have : i.val < w := i.isLt
      omega
    have hcond1 : i.val > 0 ∧ i.val - 1 + j.val = h := ⟨hi, by omega⟩
    have hcond2 : j.val > 0 ∧ i.val + (j.val - 1) = h := ⟨hj, by omega⟩
    rw [if_pos hcond1, if_pos hcond2]
    have : (-1 : ℚ) ^ i.val = - ((-1 : ℚ) ^ (i.val - 1)) := by
      have : i.val = (i.val - 1) + 1 := by omega
      nth_rw 1 [this]
      rw [pow_succ]
      ring
    rw [this, add_neg_cancel]
  · have hcond1 : ¬(i.val > 0 ∧ i.val - 1 + j.val = h) := by
      rintro ⟨_, h2⟩; apply hsum_eq; omega
    have hcond2 : ¬(j.val > 0 ∧ i.val + (j.val - 1) = h) := by
      rintro ⟨_, h2⟩; apply hsum_eq; omega
    rw [if_neg hcond1, if_neg hcond2, add_zero]

#print axioms Karlin.N0_mul_V_antidiag_add_V_antidiag_mul_N0_transpose

/-- Intertwining relation: `exp(t * N0) * V^{(h)} = V^{(h)} * (exp(-t * N0))ᵀ`. -/
theorem expN0_mul_V_antidiag {w h : ℕ} (hh : w ≤ h + 1) (t : ℚ) :
    expN0 w t * V_antidiag w h = V_antidiag w h * (expN0 w (-t)).transpose := by
  ext i j
  dsimp [Matrix.mul_apply, Matrix.transpose_apply, expN0, V_antidiag]
  by_cases hge : i.val + j.val ≥ h
  · have hl_lt : h - j.val < w := by omega
    let l0 : Fin w := ⟨h - j.val, hl_lt⟩
    have hsum1 : (∑ l : Fin w, (if l.val ≤ i.val then t ^ (i.val - l.val) / (Nat.factorial (i.val - l.val) : ℚ) else 0) *
        (if l.val + j.val = h then (-1 : ℚ) ^ l.val else 0)) =
        (t ^ (i.val + j.val - h) / (Nat.factorial (i.val + j.val - h) : ℚ)) * (-1 : ℚ) ^ (h - j.val) := by
      have hl0_mem : l0 ∈ Finset.univ := Finset.mem_univ _
      have hneq : ∀ l ∈ Finset.univ, l ≠ l0 →
          (if l.val ≤ i.val then t ^ (i.val - l.val) / (Nat.factorial (i.val - l.val) : ℚ) else 0) *
          (if l.val + j.val = h then (-1 : ℚ) ^ l.val else 0) = 0 := by
        intro l _ hl
        have : ¬ l.val + j.val = h := by
          intro heq
          apply hl
          ext
          dsimp [l0]
          omega
        rw [if_neg this, mul_zero]
      have hsingle := Finset.sum_eq_single_of_mem l0 hl0_mem hneq
      rw [hsingle]
      dsimp [l0]
      have hle1 : h - j.val ≤ i.val := by omega
      have heq1 : h - j.val + j.val = h := by omega
      have hsub1 : i.val - (h - j.val) = i.val + j.val - h := by omega
      rw [if_pos hle1, if_pos heq1, hsub1]
    have hl_lt' : h - i.val < w := by omega
    let l0' : Fin w := ⟨h - i.val, hl_lt'⟩
    have hsum2 : (∑ l : Fin w, (if i.val + l.val = h then (-1 : ℚ) ^ i.val else 0) *
        (if l.val ≤ j.val then (-t) ^ (j.val - l.val) / (Nat.factorial (j.val - l.val) : ℚ) else 0)) =
        (-1 : ℚ) ^ i.val * ((-t) ^ (i.val + j.val - h) / (Nat.factorial (i.val + j.val - h) : ℚ)) := by
      have hl0'_mem : l0' ∈ Finset.univ := Finset.mem_univ _
      have hneq : ∀ l ∈ Finset.univ, l ≠ l0' →
          (if i.val + l.val = h then (-1 : ℚ) ^ i.val else 0) *
          (if l.val ≤ j.val then (-t) ^ (j.val - l.val) / (Nat.factorial (j.val - l.val) : ℚ) else 0) = 0 := by
        intro l _ hl
        have : ¬ i.val + l.val = h := by
          intro heq
          apply hl
          ext
          dsimp [l0']
          omega
        rw [if_neg this, zero_mul]
      have hsingle := Finset.sum_eq_single_of_mem l0' hl0'_mem hneq
      rw [hsingle]
      dsimp [l0']
      have heq2 : i.val + (h - i.val) = h := by omega
      have hle2 : h - i.val ≤ j.val := by omega
      have hsub2 : j.val - (h - i.val) = i.val + j.val - h := by omega
      rw [if_pos heq2, if_pos hle2, hsub2]
    rw [hsum1, hsum2]
    set d := i.val + j.val - h
    have hneg : (-t) ^ d = (-1 : ℚ) ^ d * t ^ d := by
      have : -t = (-1 : ℚ) * t := by ring
      rw [this, mul_pow]
    rw [hneg]
    have hsign : (-1 : ℚ) ^ (h - j.val) = (-1 : ℚ) ^ i.val * (-1 : ℚ) ^ d := by
      rw [← pow_add]
      have heven : Even ((h - j.val) + (i.val + d)) := by
        refine ⟨i.val, by omega⟩
      exact neg_one_pow_eq_of_add_even heven
    rw [hsign]
    ring
  · rw [not_le] at hge
    have hsum1 : (∑ l : Fin w, (if l.val ≤ i.val then t ^ (i.val - l.val) / (Nat.factorial (i.val - l.val) : ℚ) else 0) *
        (if l.val + j.val = h then (-1 : ℚ) ^ l.val else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro l _
      by_cases hle : l.val ≤ i.val
      · have : ¬ l.val + j.val = h := by omega
        rw [if_neg this, mul_zero]
      · rw [if_neg hle, zero_mul]
    have hsum2 : (∑ l : Fin w, (if i.val + l.val = h then (-1 : ℚ) ^ i.val else 0) *
        (if l.val ≤ j.val then (-t) ^ (j.val - l.val) / (Nat.factorial (j.val - l.val) : ℚ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro l _
      by_cases hle : l.val ≤ j.val
      · have : ¬ i.val + l.val = h := by omega
        rw [if_neg this, zero_mul]
      · rw [if_neg hle, mul_zero]
    rw [hsum1, hsum2]

#print axioms Karlin.expN0_mul_V_antidiag

/-- Divided-power cokernel basis matrix `Z_DP w h = exp(-N0/2) * V^{(h)}` (Eq. (1298)). -/
def Z_DP (w h : ℕ) : Matrix (Fin w) (Fin w) ℚ :=
  expN0 w (-1/2) * V_antidiag w h

/-- Divided-power adjoint operator `L*_DP(Z) = Z - exp(-N0) * Zᵀ`. -/
def L_adjoint_DP (w : ℕ) (Z : Matrix (Fin w) (Fin w) ℚ) : Matrix (Fin w) (Fin w) ℚ :=
  Z - expN0 w (-1) * Z.transpose

/-- **Lemma 6.1 (Divided-Power Adjoint Kernel Membership)**:
    `L*_DP(Z_DP^{(h)}) = 0` for all even `h ≥ w - 1`. -/
theorem Z_DP_in_adjoint_kernel {w h : ℕ} (hh_ge : w ≤ h + 1) (hh_even : Even h) :
    L_adjoint_DP w (Z_DP w h) = 0 := by
  dsimp [L_adjoint_DP, Z_DP]
  rw [Matrix.transpose_mul, V_antidiag_transpose_of_even hh_even]
  have h_half := expN0_mul_V_antidiag hh_ge (1/2)
  have h_neg_half : -(1/2 : ℚ) = -1/2 := by ring
  rw [h_neg_half] at h_half
  rw [← h_half]
  rw [← Matrix.mul_assoc, expN0_neg_one_mul_half]
  exact sub_self _

#print axioms Karlin.Z_DP_in_adjoint_kernel

theorem N0_step {w : ℕ} (V : Matrix (Fin w) (Fin w) ℚ)
    (hD : N0_mat w * V + V * (N0_mat w).transpose = 0)
    (i : Fin w) (hi : i.val + 1 < w) (j : Fin w) :
    V i j + (if hj : j.val > 0 then V ⟨i.val + 1, hi⟩ ⟨j.val - 1, by omega⟩ else 0) = 0 := by
  have h0 : (N0_mat w * V + V * (N0_mat w).transpose) ⟨i.val + 1, hi⟩ j = 0 := by
    rw [hD]; rfl
  dsimp [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, N0_mat] at h0
  have h1 : (∑ k : Fin w, (if i.val + 1 = k.val + 1 then (1 : ℚ) else 0) * V k j) = V i j := by
    have h_single : (⟨i.val, by omega⟩ : Fin w) ∈ Finset.univ := Finset.mem_univ _
    have hneq : ∀ k ∈ Finset.univ, k ≠ ⟨i.val, by omega⟩ → (if i.val + 1 = k.val + 1 then (1 : ℚ) else 0) * V k j = 0 := by
      intro k _ hk
      have : ¬ i.val + 1 = k.val + 1 := by
        intro heq; apply hk; ext; dsimp; omega
      rw [if_neg this, zero_mul]
    have h := Finset.sum_eq_single_of_mem (⟨i.val, by omega⟩ : Fin w) h_single hneq
    rw [h]
    have : i.val + 1 = (⟨i.val, by omega⟩ : Fin w).val + 1 := by dsimp
    rw [if_pos this, one_mul]
  have h2 : (∑ k : Fin w, V ⟨i.val + 1, hi⟩ k * (if j.val = k.val + 1 then (1 : ℚ) else 0)) =
      if hj : j.val > 0 then V ⟨i.val + 1, hi⟩ ⟨j.val - 1, by omega⟩ else 0 := by
    by_cases hj : j.val > 0
    · rw [sum_single_pred_right j hj]
      rw [dif_pos hj]
    · rw [dif_neg hj]
      apply Finset.sum_eq_zero
      intro k _
      have : ¬ j.val = k.val + 1 := by omega
      rw [if_neg this, mul_zero]
  rw [h1, h2] at h0
  exact h0

#print axioms Karlin.N0_step

/-- **Lemma 6.1 (Cokernel Completeness & Vanishing Below Anti-Diagonal)**:
    Any solution to `N0 * V + V * N0ᵀ = 0` vanishes strictly below the first anti-diagonal `i + j + 1 < w`. -/
theorem V_eq_zero_of_add_lt {w : ℕ} (V : Matrix (Fin w) (Fin w) ℚ)
    (hD : N0_mat w * V + V * (N0_mat w).transpose = 0)
    {i j : Fin w} (hij : i.val + j.val + 1 < w) : V i j = 0 := by
  generalize hj_eq : j.val = m
  revert i j
  induction' m with m ih
  · intro i j hj_eq hij
    have hj0 : ¬ j.val > 0 := by omega
    have hstep := N0_step V hD i (by omega) j
    rw [dif_neg hj0, add_zero] at hstep
    exact hstep
  · intro i j hj_eq hij
    have hj_pos : j.val > 0 := by omega
    have hstep := N0_step V hD i (by omega) j
    rw [dif_pos hj_pos] at hstep
    have hnext : V ⟨i.val + 1, by omega⟩ ⟨j.val - 1, by omega⟩ = 0 := by
      apply ih
      · dsimp; omega
      · dsimp; omega
    rw [hnext, add_zero] at hstep
    exact hstep

#print axioms Karlin.V_eq_zero_of_add_lt

/-- Binomial-coordinate cokernel matrix `Z^{(h)} = S_w * Z_DP^{(h)} * S_wᵀ` (Eq. (1299)). -/
def Z_binom {w : ℕ} (S_w : Matrix (Fin w) (Fin w) ℚ) (h : ℕ) : Matrix (Fin w) (Fin w) ℚ :=
  S_w * Z_DP w h * S_w.transpose

/-- **Lemma 6.1 (Binomial Cokernel Adjoint Kernel Membership)**:
    Under intertwining `B * S_w = S_w * exp(-N0)`, `Z^{(h)} ∈ ker(L*)`. -/
theorem Z_binom_in_adjoint_kernel {w h : ℕ}
    (hh_ge : w ≤ h + 1) (hh_even : Even h)
    (B S_w : Matrix (Fin w) (Fin w) ℚ)
    (hB : B * S_w = S_w * expN0 w (-1)) :
    L_adjoint B (Z_binom S_w h) = 0 := by
  dsimp [L_adjoint, Z_binom]
  have h_trans : (S_w * Z_DP w h * S_w.transpose).transpose = S_w * (Z_DP w h).transpose * S_w.transpose := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [h_trans]
  have h_assoc1 : B * (S_w * (Z_DP w h).transpose * S_w.transpose) =
      (B * S_w) * ((Z_DP w h).transpose * S_w.transpose) := by
    simp only [Matrix.mul_assoc]
  rw [h_assoc1, hB]
  have h_left : S_w * Z_DP w h * S_w.transpose = S_w * (Z_DP w h * S_w.transpose) := by
    simp only [Matrix.mul_assoc]
  have h_right : S_w * expN0 w (-1) * ((Z_DP w h).transpose * S_w.transpose) =
      S_w * (expN0 w (-1) * (Z_DP w h).transpose * S_w.transpose) := by
    simp only [Matrix.mul_assoc]
  rw [h_left, h_right, ← Matrix.mul_sub]
  have h_sub : Z_DP w h * S_w.transpose - expN0 w (-1) * (Z_DP w h).transpose * S_w.transpose =
      (Z_DP w h - expN0 w (-1) * (Z_DP w h).transpose) * S_w.transpose := by
    rw [Matrix.sub_mul]
  have h_DP : Z_DP w h - expN0 w (-1) * (Z_DP w h).transpose = 0 := Z_DP_in_adjoint_kernel hh_ge hh_even
  rw [h_sub, h_DP, Matrix.zero_mul, Matrix.mul_zero]

#print axioms Karlin.Z_binom_in_adjoint_kernel

theorem matInnerProd_mul_left {l m n : Type*} [Fintype l] [Fintype m] [Fintype n] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    (A : Matrix l m ℚ) (M : Matrix m n ℚ) (N : Matrix l n ℚ) :
    matInnerProd (A * M) N = matInnerProd M (A.transpose * N) := by
  dsimp [matInnerProd, Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h_swap : (∑ j, ∑ i, ∑ k, A i k * M k j * N i j) =
      ∑ j, ∑ k, ∑ i, A i k * M k j * N i j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  rw [h_swap, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

#print axioms Karlin.matInnerProd_mul_left

theorem matInnerProd_mul_right {l m n : Type*} [Fintype l] [Fintype m] [Fintype n] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    (M : Matrix l m ℚ) (B : Matrix m n ℚ) (N : Matrix l n ℚ) :
    matInnerProd (M * B) N = matInnerProd M (N * B.transpose) := by
  dsimp [matInnerProd, Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

#print axioms Karlin.matInnerProd_mul_right

/-- Two-sided change of basis for matrix inner product: `⟨S * Z * Sᵀ, F⟩ = ⟨Z, Sᵀ * F * S⟩` (Eq. (1572)). -/
theorem matInnerProd_Z_binom_eq_Z_DP {w : ℕ}
    (S_w : Matrix (Fin w) (Fin w) ℚ) (h : ℕ) (F : Matrix (Fin w) (Fin w) ℚ) :
    matInnerProd (Z_binom S_w h) F = matInnerProd (Z_DP w h) (S_w.transpose * F * S_w) := by
  dsimp [Z_binom]
  rw [matInnerProd_mul_right, Matrix.transpose_transpose]
  rw [matInnerProd_mul_left, Matrix.mul_assoc]

#print axioms Karlin.matInnerProd_Z_binom_eq_Z_DP

/-- Vanishing strictly below anti-diagonal: `(Z_DP^{(h)})_{ij} = 0` when `i + j < h`. -/
theorem Z_DP_apply_of_add_lt {w h : ℕ} {i j : Fin w} (hij : i.val + j.val < h) :
    Z_DP w h i j = 0 := by
  dsimp [Z_DP, Matrix.mul_apply, expN0, V_antidiag]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hle : l.val ≤ i.val
  · have : ¬ l.val + j.val = h := by omega
    rw [if_neg this, mul_zero]
  · rw [if_neg hle, zero_mul]

#print axioms Karlin.Z_DP_apply_of_add_lt

/-- Boundary value on anti-diagonal: `(Z_DP^{(h)})_{ij} = (-1)^i` when `i + j = h`. -/
theorem Z_DP_apply_antidiag {w h : ℕ} {i j : Fin w} (hij : i.val + j.val = h) :
    Z_DP w h i j = (-1 : ℚ) ^ i.val := by
  dsimp [Z_DP, Matrix.mul_apply, expN0, V_antidiag]
  have hi_mem : i ∈ Finset.univ := Finset.mem_univ _
  have hneq : ∀ l ∈ Finset.univ, l ≠ i →
      (if l.val ≤ i.val then (-1/2 : ℚ) ^ (i.val - l.val) / (Nat.factorial (i.val - l.val) : ℚ) else 0) *
      (if l.val + j.val = h then (-1 : ℚ) ^ l.val else 0) = 0 := by
    intro l _ hl
    have : ¬ l.val + j.val = h := by
      intro heq
      apply hl
      ext
      omega
    rw [if_neg this, mul_zero]
  have hsum := Finset.sum_eq_single_of_mem i hi_mem hneq
  rw [hsum]
  have h1 : i.val ≤ i.val := le_refl _
  have h2 : i.val + j.val = h := hij
  rw [if_pos h1, if_pos h2]
  have : i.val - i.val = 0 := by omega
  rw [this]
  simp

#print axioms Karlin.Z_DP_apply_antidiag

/-- For higher tests `h ≥ w`, row 0 of `Z_DP` is identically zero. -/
theorem Z_DP_first_row_zero_of_gt {w h : ℕ} (hh : w ≤ h) (j : Fin w) (h0 : 0 < w) :
    Z_DP w h ⟨0, h0⟩ j = 0 := by
  apply Z_DP_apply_of_add_lt
  have : j.val < w := j.isLt
  dsimp
  omega

#print axioms Karlin.Z_DP_first_row_zero_of_gt

/-- For higher tests `h ≥ w`, column 0 of `Z_DP` is identically zero. -/
theorem Z_DP_first_col_zero_of_gt {w h : ℕ} (hh : w ≤ h) (i : Fin w) (h0 : 0 < w) :
    Z_DP w h i ⟨0, h0⟩ = 0 := by
  apply Z_DP_apply_of_add_lt
  have : i.val < w := i.isLt
  dsimp
  omega

#print axioms Karlin.Z_DP_first_col_zero_of_gt

/-- Top test evaluation: `⟨Z_DP^{(2k)}, F⟩ = (-1)^k * F_{kk}`. -/
theorem Z_DP_top_test_inner {k : ℕ} (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :
    matInnerProd (Z_DP (k + 1) (2 * k)) F =
      (-1 : ℚ) ^ k * F ⟨k, by omega⟩ ⟨k, by omega⟩ := by
  have hk : (⟨k, by omega⟩ : Fin (k + 1)) ∈ Finset.univ := Finset.mem_univ _
  have hinner : ∀ i : Fin (k + 1),
      (∑ j : Fin (k + 1), Z_DP (k + 1) (2 * k) i j * F i j) =
        if i = ⟨k, by omega⟩ then (-1 : ℚ) ^ k * F ⟨k, by omega⟩ ⟨k, by omega⟩ else 0 := by
    intro i
    by_cases hi : i = ⟨k, by omega⟩
    · subst hi
      have hsingle : ∀ j ∈ Finset.univ, j ≠ ⟨k, by omega⟩ →
          Z_DP (k + 1) (2 * k) ⟨k, by omega⟩ j * F ⟨k, by omega⟩ j = 0 := by
        intro j _ hj
        have hlt : (⟨k, by omega⟩ : Fin (k + 1)).val + j.val < 2 * k := by
          have : j.val < k := by
            have : j.val < k + 1 := j.isLt
            have : j.val ≠ k := fun h => hj (Fin.ext h)
            omega
          dsimp; omega
        rw [Z_DP_apply_of_add_lt hlt, zero_mul]
      have h := Finset.sum_eq_single_of_mem (⟨k, by omega⟩ : Fin (k + 1)) hk hsingle
      rw [h, if_pos rfl]
      have h_antidiag := Z_DP_apply_antidiag (w := k + 1) (h := 2 * k) (i := ⟨k, by omega⟩) (j := ⟨k, by omega⟩) (by dsimp; omega)
      rw [h_antidiag]
    · rw [if_neg hi]
      apply Finset.sum_eq_zero
      intro j _
      have hlt : i.val + j.val < 2 * k := by
        have : i.val < k := by
          have : i.val < k + 1 := i.isLt
          have : i.val ≠ k := fun h => hi (Fin.ext h)
          omega
        have : j.val ≤ k := by
          have : j.val < k + 1 := j.isLt
          omega
        omega
      rw [Z_DP_apply_of_add_lt hlt, zero_mul]
  have hsum : (∑ i : Fin (k + 1), ∑ j : Fin (k + 1), Z_DP (k + 1) (2 * k) i j * F i j) =
      ∑ i : Fin (k + 1), if i = ⟨k, by omega⟩ then (-1 : ℚ) ^ k * F ⟨k, by omega⟩ ⟨k, by omega⟩ else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    exact hinner i
  dsimp [matInnerProd]
  rw [hsum]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

#print axioms Karlin.Z_DP_top_test_inner

/-- Automatic top test cancellation when `F_{kk} = 0`. -/
theorem top_test_zero_of_F_zero {k : ℕ} (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hF : F ⟨k, by omega⟩ ⟨k, by omega⟩ = 0) :
    matInnerProd (Z_DP (k + 1) (2 * k)) F = 0 := by
  rw [Z_DP_top_test_inner, hF, mul_zero]

#print axioms Karlin.top_test_zero_of_F_zero

/-- Lowest test corner (0, k) is 1. -/
theorem Z_DP_lowest_test_corner_top_right {k : ℕ} :
    Z_DP (k + 1) k ⟨0, by omega⟩ ⟨k, by omega⟩ = 1 := by
  have h_anti := Z_DP_apply_antidiag (w := k + 1) (h := k) (i := ⟨0, by omega⟩) (j := ⟨k, by omega⟩) (by dsimp; omega)
  rw [h_anti]
  simp

#print axioms Karlin.Z_DP_lowest_test_corner_top_right

/-- Lowest test corner (k, 0) is 1 for even `k`. -/
theorem Z_DP_lowest_test_corner_bottom_left {k : ℕ} (hk : Even k) :
    Z_DP (k + 1) k ⟨k, by omega⟩ ⟨0, by omega⟩ = 1 := by
  have h_anti := Z_DP_apply_antidiag (w := k + 1) (h := k) (i := ⟨k, by omega⟩) (j := ⟨0, by omega⟩) (by dsimp)
  rw [h_anti]
  dsimp
  obtain ⟨m, hm⟩ := hk
  have : k = 2 * m := by omega
  rw [this, pow_mul]
  norm_num

#print axioms Karlin.Z_DP_lowest_test_corner_bottom_left

/-- Lowest test row 0 vanishes for `j < k`. -/
theorem Z_DP_lowest_test_row_zero {k : ℕ} (j : Fin (k + 1)) (hj : j.val < k) :
    Z_DP (k + 1) k ⟨0, by omega⟩ j = 0 := by
  apply Z_DP_apply_of_add_lt
  dsimp
  omega

#print axioms Karlin.Z_DP_lowest_test_row_zero

/-- Lowest test column 0 vanishes for `i < k`. -/
theorem Z_DP_lowest_test_col_zero {k : ℕ} (i : Fin (k + 1)) (hi : i.val < k) :
    Z_DP (k + 1) k i ⟨0, by omega⟩ = 0 := by
  apply Z_DP_apply_of_add_lt
  dsimp
  omega

#print axioms Karlin.Z_DP_lowest_test_col_zero


/-!
## Part 6: Section 6.2 — Triangular Pivot System & Higher Compatibility Test Solver (Lemma 6.2)
-/

/-- **Lemma 6.2 (Triangular Pivot Decomposition, Eq. (1637))**:
    For `k < h < 2k` and `ψ_k = 0`, the inner product `⟨Z_DP^{(h)}, ℓᵀ * ψ⟩` decomposes as
    a leading pivot term `(-1)^i * ℓ_i * ψ_{k-1}` with `i = h - k + 1` plus a strictly higher-index tail. -/
theorem inner_Z_DP_outerProd_triangular_decomp {k h : ℕ}
    (hk_pos : 0 < k) (hk_h : k < h) (hh_top : h < 2 * k)
    (psi_hat : Fin (k + 1) → ℚ) (hpsi_k : psi_hat ⟨k, by omega⟩ = 0)
    (ell_hat : Fin (k + 1) → ℚ) :
    let i_piv : Fin (k + 1) := ⟨h - k + 1, by omega⟩
    let k_minus_1 : Fin (k + 1) := ⟨k - 1, by omega⟩
    matInnerProd (Z_DP (k + 1) h) (outerProd ell_hat psi_hat) =
      (-1 : ℚ) ^ (h - k + 1) * ell_hat i_piv * psi_hat k_minus_1 +
      ∑ a ∈ Finset.univ.filter (fun a : Fin (k + 1) => a.val > h - k + 1),
        ∑ b ∈ Finset.univ.filter (fun b : Fin (k + 1) => b.val < k),
          Z_DP (k + 1) h a b * ell_hat a * psi_hat b := by
  intro i_piv k_minus_1
  dsimp [matInnerProd, outerProd]
  have hterm : ∀ a b : Fin (k + 1),
      Z_DP (k + 1) h a b * (ell_hat a * psi_hat b) =
        (if a = i_piv ∧ b = k_minus_1 then (-1 : ℚ) ^ (h - k + 1) * ell_hat i_piv * psi_hat k_minus_1 else 0) +
        (if a.val > h - k + 1 ∧ b.val < k then Z_DP (k + 1) h a b * ell_hat a * psi_hat b else 0) := by
    intro a b
    by_cases hb_k : b.val = k
    · have hb_eq : b = ⟨k, by omega⟩ := Fin.ext hb_k
      rw [hb_eq]
      have : psi_hat ⟨k, by omega⟩ = 0 := hpsi_k
      rw [this, mul_zero, mul_zero]
      have h1 : ¬(a = i_piv ∧ (⟨k, by omega⟩ : Fin (k + 1)) = k_minus_1) := by
        rintro ⟨_, h2⟩
        have : (⟨k, by omega⟩ : Fin (k + 1)).val = k_minus_1.val := by rw [h2]
        dsimp [k_minus_1] at this
        omega
      have h2 : ¬(a.val > h - k + 1 ∧ (⟨k, by omega⟩ : Fin (k + 1)).val < k) := by
        rintro ⟨_, hlt⟩; dsimp at hlt; omega
      rw [if_neg h1, if_neg h2, add_zero]
    · have hb_lt : b.val < k := by
        have : b.val < k + 1 := b.isLt
        omega
      by_cases ha_lt : a.val < h - k + 1
      · have hab_lt : a.val + b.val < h := by omega
        rw [Z_DP_apply_of_add_lt hab_lt, zero_mul]
        have h1 : ¬(a = i_piv ∧ b = k_minus_1) := by
          rintro ⟨rfl, _⟩; dsimp [i_piv] at ha_lt; omega
        have h2 : ¬(a.val > h - k + 1 ∧ b.val < k) := by
          rintro ⟨hgt, _⟩; omega
        rw [if_neg h1, if_neg h2, add_zero]
      · by_cases ha_eq : a.val = h - k + 1
        · have ha : a = i_piv := Fin.ext ha_eq
          subst ha
          by_cases hb_prev : b.val = k - 1
          · have hb : b = k_minus_1 := Fin.ext hb_prev
            subst hb
            have h_antidiag := Z_DP_apply_antidiag (w := k + 1) (h := h) (i := i_piv) (j := k_minus_1) (by
              dsimp [i_piv, k_minus_1]; omega)
            rw [h_antidiag]
            have h1 : i_piv = i_piv ∧ k_minus_1 = k_minus_1 := ⟨rfl, rfl⟩
            have h2 : ¬(i_piv.val > h - k + 1 ∧ k_minus_1.val < k) := by
              rintro ⟨hgt, _⟩; dsimp [i_piv] at hgt; omega
            rw [if_pos h1, if_neg h2, add_zero]
            ring
          · have hab_lt : (i_piv : Fin (k + 1)).val + b.val < h := by
              dsimp [i_piv]; omega
            rw [Z_DP_apply_of_add_lt hab_lt, zero_mul]
            have h1 : ¬(i_piv = i_piv ∧ b = k_minus_1) := by
              rintro ⟨_, rfl⟩; dsimp [k_minus_1] at hb_prev; omega
            have h2 : ¬(i_piv.val > h - k + 1 ∧ b.val < k) := by
              rintro ⟨hgt, _⟩; dsimp [i_piv] at hgt; omega
            rw [if_neg h1, if_neg h2, add_zero]
        · have ha_gt : a.val > h - k + 1 := by omega
          have h1 : ¬(a = i_piv ∧ b = k_minus_1) := by
            rintro ⟨rfl, _⟩; dsimp [i_piv] at ha_gt; omega
          have h2 : a.val > h - k + 1 ∧ b.val < k := ⟨ha_gt, hb_lt⟩
          rw [if_neg h1, if_pos h2, zero_add]
          ring
  simp_rw [hterm, Finset.sum_add_distrib]
  have hsum_piv : (∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
      if i = i_piv ∧ j = k_minus_1 then (-1 : ℚ) ^ (h - k + 1) * ell_hat i_piv * psi_hat k_minus_1 else 0) =
      (-1 : ℚ) ^ (h - k + 1) * ell_hat i_piv * psi_hat k_minus_1 := by
    have h_inner : ∀ i : Fin (k + 1),
        (∑ j : Fin (k + 1), if i = i_piv ∧ j = k_minus_1 then (-1 : ℚ) ^ (h - k + 1) * ell_hat i_piv * psi_hat k_minus_1 else 0) =
        if i = i_piv then (-1 : ℚ) ^ (h - k + 1) * ell_hat i_piv * psi_hat k_minus_1 else 0 := by
      intro i
      by_cases hi : i = i_piv
      · subst hi
        rw [if_pos rfl]
        have h_congr : (∑ j : Fin (k + 1), if i_piv = i_piv ∧ j = k_minus_1 then (-1 : ℚ) ^ (h - k + 1) * ell_hat i_piv * psi_hat k_minus_1 else 0) =
            ∑ j : Fin (k + 1), if j = k_minus_1 then (-1 : ℚ) ^ (h - k + 1) * ell_hat i_piv * psi_hat k_minus_1 else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          have hiff : (i_piv = i_piv ∧ j = k_minus_1) ↔ j = k_minus_1 := ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
          rw [if_congr hiff rfl rfl]
        rw [h_congr, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      · rw [if_neg hi]
        apply Finset.sum_eq_zero
        intro j _
        have : ¬(i = i_piv ∧ j = k_minus_1) := by rintro ⟨rfl, _⟩; exact hi rfl
        rw [if_neg this]
    have h_outer : (∑ i : Fin (k + 1), ∑ j : Fin (k + 1), if i = i_piv ∧ j = k_minus_1 then (-1 : ℚ) ^ (h - k + 1) * ell_hat i_piv * psi_hat k_minus_1 else 0) =
        ∑ i : Fin (k + 1), if i = i_piv then (-1 : ℚ) ^ (h - k + 1) * ell_hat i_piv * psi_hat k_minus_1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact h_inner i
    rw [h_outer, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  have hsum_tail : (∑ a ∈ Finset.univ.filter (fun a : Fin (k + 1) => a.val > h - k + 1),
      ∑ b ∈ Finset.univ.filter (fun b : Fin (k + 1) => b.val < k),
        Z_DP (k + 1) h a b * ell_hat a * psi_hat b) =
      ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
        if i.val > h - k + 1 ∧ j.val < k then Z_DP (k + 1) h i j * ell_hat i * psi_hat j else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a.val > h - k + 1
      · rw [if_pos ha, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro b _
        by_cases hb : b.val < k
        · rw [if_pos hb, if_pos ⟨ha, hb⟩]
        · rw [if_neg hb, if_neg (fun h => hb h.2)]
      · rw [if_neg ha]
        symm
        apply Finset.sum_eq_zero
        intro b _
        rw [if_neg (fun h => ha h.1)]
  rw [hsum_piv, ← hsum_tail]

#print axioms Karlin.inner_Z_DP_outerProd_triangular_decomp

/-- **Lemma 6.2 (Single-Step Higher Test Pivot Cancellation Theorem, Eq. (1637))**:
    If `ℓ_i` is set to cancel the pivot equation, then `⟨Z_DP^{(h)}, F - ℓᵀ * ψ⟩ = 0`. -/
theorem higher_test_solved_of_pivot_eq {k h : ℕ}
    (hk_pos : 0 < k) (hk_h : k < h) (hh_top : h < 2 * k)
    (psi_hat : Fin (k + 1) → ℚ) (hpsi_k : psi_hat ⟨k, by omega⟩ = 0)
    (hpsi_prev : psi_hat ⟨k - 1, by omega⟩ ≠ 0)
    (F_hat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (ell_hat : Fin (k + 1) → ℚ)
    (h_pivot : ell_hat ⟨h - k + 1, by omega⟩ =
      ((-1 : ℚ) ^ (h - k + 1) / psi_hat ⟨k - 1, by omega⟩) *
        (matInnerProd (Z_DP (k + 1) h) F_hat -
          ∑ a ∈ Finset.univ.filter (fun a : Fin (k + 1) => a.val > h - k + 1),
            ∑ b ∈ Finset.univ.filter (fun b : Fin (k + 1) => b.val < k),
              Z_DP (k + 1) h a b * ell_hat a * psi_hat b)) :
    matInnerProd (Z_DP (k + 1) h) (F_hat - outerProd ell_hat psi_hat) = 0 := by
  rw [matInnerProd_sub_right]
  rw [inner_Z_DP_outerProd_triangular_decomp hk_pos hk_h hh_top psi_hat hpsi_k ell_hat]
  rw [h_pivot]
  have h_sq : (-1 : ℚ) ^ (h - k + 1) * (-1 : ℚ) ^ (h - k + 1) = 1 := by
    rw [← pow_add]
    have : (h - k + 1) + (h - k + 1) = 2 * (h - k + 1) := by omega
    rw [this, pow_mul]
    norm_num
  set tail := ∑ a ∈ Finset.univ.filter (fun a : Fin (k + 1) => a.val > h - k + 1),
                ∑ b ∈ Finset.univ.filter (fun b : Fin (k + 1) => b.val < k),
                  Z_DP (k + 1) h a b * ell_hat a * psi_hat b
  set F_val := matInnerProd (Z_DP (k + 1) h) F_hat
  have : (-1 : ℚ) ^ (h - k + 1) *
      (((-1 : ℚ) ^ (h - k + 1) / psi_hat ⟨k - 1, by omega⟩) * (F_val - tail)) *
      psi_hat ⟨k - 1, by omega⟩ = F_val - tail := by
    calc (-1 : ℚ) ^ (h - k + 1) * (((-1 : ℚ) ^ (h - k + 1) / psi_hat ⟨k - 1, by omega⟩) * (F_val - tail)) * psi_hat ⟨k - 1, by omega⟩
      _ = ((-1 : ℚ) ^ (h - k + 1) * (-1 : ℚ) ^ (h - k + 1)) * ((F_val - tail) / psi_hat ⟨k - 1, by omega⟩ * psi_hat ⟨k - 1, by omega⟩) := by ring
      _ = 1 * (F_val - tail) := by
        rw [h_sq, div_mul_cancel₀ (F_val - tail) hpsi_prev]
      _ = F_val - tail := by ring
  rw [this]
  ring

#print axioms Karlin.higher_test_solved_of_pivot_eq

/-- **Lemma 6.2 (Triangular Back-Substitution Invariance)**:
    Modifying `ℓ` at any lower index `a < h - k + 1` leaves the higher-test inner product invariant. -/
theorem triangular_back_substitution_invariance {k h : ℕ}
    (hk_pos : 0 < k) (hk_h : k < h) (hh_top : h < 2 * k)
    (psi_hat : Fin (k + 1) → ℚ) (hpsi_k : psi_hat ⟨k, by omega⟩ = 0)
    (ell1 ell2 : Fin (k + 1) → ℚ)
    (h_eq : ∀ a : Fin (k + 1), a.val ≥ h - k + 1 → ell1 a = ell2 a) :
    matInnerProd (Z_DP (k + 1) h) (outerProd ell1 psi_hat) =
      matInnerProd (Z_DP (k + 1) h) (outerProd ell2 psi_hat) := by
  rw [inner_Z_DP_outerProd_triangular_decomp hk_pos hk_h hh_top psi_hat hpsi_k ell1]
  rw [inner_Z_DP_outerProd_triangular_decomp hk_pos hk_h hh_top psi_hat hpsi_k ell2]
  have h_piv : ell1 ⟨h - k + 1, by omega⟩ = ell2 ⟨h - k + 1, by omega⟩ := by
    apply h_eq; dsimp; omega
  rw [h_piv]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  have ha_eq : ell1 a = ell2 a := h_eq a (by omega)
  rw [ha_eq]

#print axioms Karlin.triangular_back_substitution_invariance

/-- **Lemma 6.2 (Top Test Invariant Cancellation)**:
    When `ψ_k = 0` and `F_{kk} = 0`, the top test `h = 2k` is automatically satisfied for ANY `ℓ`. -/
theorem higher_top_test_solved {k : ℕ}
    (psi_hat : Fin (k + 1) → ℚ) (hpsi_k : psi_hat ⟨k, by omega⟩ = 0)
    (F_hat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hF_kk : F_hat ⟨k, by omega⟩ ⟨k, by omega⟩ = 0)
    (ell_hat : Fin (k + 1) → ℚ) :
    matInnerProd (Z_DP (k + 1) (2 * k)) (F_hat - outerProd ell_hat psi_hat) = 0 := by
  apply top_test_zero_of_F_zero
  dsimp [Matrix.sub_apply, outerProd]
  rw [hF_kk, hpsi_k, mul_zero, sub_zero]

#print axioms Karlin.higher_top_test_solved


/-!
## Part 7: Section 6.2 Global Higher-Test Solver (`solveHigherTestsDP`) & Section 7.1 General Even-$k$ Lowest-Test Cancellation (Proposition 7.1 `prop:momentchoice`)
-/

/-- The pivot tail sum $\sum_{a' > a, b < k} Z_{\mathrm{DP}}^{(a + k - 1)}_{a', b} \widehat{\ell}_{a'} \widehat{\psi}_b$. -/
def pivotTail (k : ℕ) (psi_hat : Fin (k + 1) → ℚ) (ell_hat : Fin (k + 1) → ℚ) (a : ℕ) : ℚ :=
  ∑ x ∈ Finset.univ.filter (fun x : Fin (k + 1) => x.val > a),
    ∑ y ∈ Finset.univ.filter (fun y : Fin (k + 1) => y.val < k),
      Z_DP (k + 1) (a + k - 1) x y * ell_hat x * psi_hat y

/-- The pivot term for coordinate $a$:
    $\frac{(-1)^a}{\widehat{\psi}_{k-1}} (\langle Z_{\mathrm{DP}}^{(a + k - 1)}, \widehat{F} \rangle - \text{pivotTail})$. -/
def pivotTerm (k : ℕ) (psi_hat : Fin (k + 1) → ℚ) (F_hat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (ell_hat : Fin (k + 1) → ℚ) (a : ℕ) : ℚ :=
  let h := a + k - 1
  let F_val := matInnerProd (Z_DP (k + 1) h) F_hat
  let tail := pivotTail k psi_hat ell_hat a
  ((-1 : ℚ) ^ a / psi_hat ⟨k - 1, by omega⟩) * (F_val - tail)

/-- Step-by-step downward back-substitution accumulator.
    Step `s` processes index `a = k - 1 - s`. -/
def solveHelper (k : ℕ) (psi_hat : Fin (k + 1) → ℚ) (F_hat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :
    ℕ → (Fin (k + 1) → ℚ)
  | 0 => fun _ => 0
  | s + 1 =>
    let prev := solveHelper k psi_hat F_hat s
    let a := k - 1 - s
    if 1 < a ∧ a < k ∧ (a + k - 1) % 2 = 0 then
      fun x => if x.val = a then pivotTerm k psi_hat F_hat prev a else prev x
    else
      prev

/-- The global higher-test back-substitution solver vector $\widehat{\ell}$ (Lemma 6.2). -/
def solveHigherTestsDP (k : ℕ) (psi_hat : Fin (k + 1) → ℚ) (F_hat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :
    Fin (k + 1) → ℚ :=
  solveHelper k psi_hat F_hat (k - 1)

/-- $\widehat{\ell}_0 = 0$ for `solveHigherTestsDP`. -/
theorem solveHigherTestsDP_zero_at_zero (k : ℕ) (psi_hat : Fin (k + 1) → ℚ)
    (F_hat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) (h0 : 0 < k + 1) :
    solveHigherTestsDP k psi_hat F_hat ⟨0, h0⟩ = 0 := by
  dsimp [solveHigherTestsDP]
  have h_ind : ∀ s : ℕ, solveHelper k psi_hat F_hat s ⟨0, h0⟩ = 0 := by
    intro s
    induction' s with s ih
    · rfl
    · dsimp [solveHelper]
      split_ifs with h
      · dsimp
        have h_neq : ¬ (⟨0, h0⟩ : Fin (k + 1)).val = k - 1 - s := by
          dsimp; omega
        rw [if_neg h_neq]
        exact ih
      · exact ih
  exact h_ind (k - 1)

#print axioms Karlin.solveHigherTestsDP_zero_at_zero

/-- $\widehat{\ell}_k = 0$ for `solveHigherTestsDP`. -/
theorem solveHigherTestsDP_zero_at_last (k : ℕ) (psi_hat : Fin (k + 1) → ℚ)
    (F_hat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) (hk : k < k + 1) :
    solveHigherTestsDP k psi_hat F_hat ⟨k, hk⟩ = 0 := by
  dsimp [solveHigherTestsDP]
  have h_ind : ∀ s : ℕ, solveHelper k psi_hat F_hat s ⟨k, hk⟩ = 0 := by
    intro s
    induction' s with s ih
    · rfl
    · dsimp [solveHelper]
      split_ifs with h
      · dsimp
        have h_neq : ¬ (⟨k, hk⟩ : Fin (k + 1)).val = k - 1 - s := by
          dsimp; omega
        rw [if_neg h_neq]
        exact ih
      · exact ih
  exact h_ind (k - 1)

#print axioms Karlin.solveHigherTestsDP_zero_at_last

/-- Coordinates with $s \le k - 1 - x$ remain 0 in `solveHelper`. -/
theorem solveHelper_apply_of_le (k : ℕ) (psi_hat : Fin (k + 1) → ℚ)
    (F_hat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (s : ℕ) (x : Fin (k + 1)) (hx : s ≤ k - 1 - x.val) :
    solveHelper k psi_hat F_hat s x = 0 := by
  induction' s with s ih
  · rfl
  · dsimp [solveHelper]
    split_ifs with h
    · dsimp
      have hneq : ¬ x.val = k - 1 - s := by omega
      rw [if_neg hneq]
      exact ih (by omega)
    · exact ih (by omega)

#print axioms Karlin.solveHelper_apply_of_le

/-- Coordinates with $k - x \le s$ are invariant at step $s + 1$. -/
theorem solveHelper_apply_eq_of_ge (k : ℕ) (psi_hat : Fin (k + 1) → ℚ)
    (F_hat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (s : ℕ) (x : Fin (k + 1)) (hx : k - x.val ≤ s) :
    solveHelper k psi_hat F_hat (s + 1) x = solveHelper k psi_hat F_hat s x := by
  dsimp [solveHelper]
  split_ifs with h
  · dsimp
    have hneq : ¬ x.val = k - 1 - s := by omega
    rw [if_neg hneq]
  · rfl

#print axioms Karlin.solveHelper_apply_eq_of_ge

/-- Once step $s \ge k - x$ is reached, coordinate $x$ equals its final value `solveHigherTestsDP`. -/
theorem solveHelper_apply_eq_solveHigherTestsDP (k : ℕ) (psi_hat : Fin (k + 1) → ℚ)
    (F_hat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (s : ℕ) (x : Fin (k + 1)) (hs : k - x.val ≤ s) (hsk : s ≤ k - 1) :
    solveHelper k psi_hat F_hat s x = solveHigherTestsDP k psi_hat F_hat x := by
  dsimp [solveHigherTestsDP]
  obtain ⟨d, hd⟩ := Nat.le.dest hsk
  rw [← hd]
  clear hd hsk
  induction' d with d ih
  · rfl
  · rw [← add_assoc, solveHelper_apply_eq_of_ge k psi_hat F_hat (s + d) x (by omega)]
    exact ih

#print axioms Karlin.solveHelper_apply_eq_solveHigherTestsDP

/-- At any active pivot index $a$, `solveHigherTestsDP` satisfies the pivot equation. -/
theorem solveHigherTestsDP_eq_pivotTerm {k : ℕ}
    (psi_hat : Fin (k + 1) → ℚ) (F_hat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (a : ℕ) (ha1 : 1 < a) (hak : a < k) (heven : (a + k - 1) % 2 = 0) :
    solveHigherTestsDP k psi_hat F_hat ⟨a, by omega⟩ =
      pivotTerm k psi_hat F_hat (solveHigherTestsDP k psi_hat F_hat) a := by
  set s := k - 1 - a
  have hs_lt : s ≤ k - 1 := by omega
  have hs1_le : s + 1 ≤ k - 1 := by omega
  have h_eq1 : solveHigherTestsDP k psi_hat F_hat ⟨a, by omega⟩ =
      solveHelper k psi_hat F_hat (s + 1) ⟨a, by omega⟩ := by
    symm
    apply solveHelper_apply_eq_solveHigherTestsDP k psi_hat F_hat (s + 1) ⟨a, by omega⟩ (by dsimp; omega) hs1_le
  rw [h_eq1]
  dsimp [solveHelper]
  have hcond : 1 < k - 1 - s ∧ k - 1 - s < k ∧ (k - 1 - s + k - 1) % 2 = 0 := by
    have : k - 1 - s = a := by omega
    rw [this]
    exact ⟨ha1, hak, heven⟩
  rw [if_pos hcond]
  dsimp
  have ha_eq : (⟨a, by omega⟩ : Fin (k + 1)).val = k - 1 - s := by dsimp; omega
  rw [if_pos ha_eq]
  have hka : k - 1 - s = a := by omega
  rw [hka]
  dsimp [pivotTerm, pivotTail]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  apply Finset.sum_congr rfl
  intro y _
  have hx_eq : solveHelper k psi_hat F_hat s x = solveHigherTestsDP k psi_hat F_hat x := by
    apply solveHelper_apply_eq_solveHigherTestsDP k psi_hat F_hat s x (by omega) hs_lt
  rw [hx_eq]

#print axioms Karlin.solveHigherTestsDP_eq_pivotTerm

/-- **Master Lemma 6.2 (Global Higher-Test Solvability Theorem)**:
    For any even $h \in (k, 2k]$, `solveHigherTestsDP` solves test $h$ simultaneously! -/
theorem solveHigherTestsDP_solves_all_higher_tests {k h : ℕ}
    (hk_pos : 0 < k) (hk_h : k < h) (hh_top : h ≤ 2 * k) (hh_even : Even h)
    (psi_hat : Fin (k + 1) → ℚ) (hpsi_k : psi_hat ⟨k, by omega⟩ = 0)
    (hpsi_prev : psi_hat ⟨k - 1, by omega⟩ ≠ 0)
    (F_hat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hF_kk : F_hat ⟨k, by omega⟩ ⟨k, by omega⟩ = 0) :
    matInnerProd (Z_DP (k + 1) h) (F_hat - outerProd (solveHigherTestsDP k psi_hat F_hat) psi_hat) = 0 := by
  by_cases hh_eq : h = 2 * k
  · subst hh_eq
    exact higher_top_test_solved psi_hat hpsi_k F_hat hF_kk (solveHigherTestsDP k psi_hat F_hat)
  · have hh_lt : h < 2 * k := by omega
    set a := h - k + 1
    have ha1 : 1 < a := by dsimp [a]; omega
    have hak : a < k := by
      dsimp [a]
      obtain ⟨m, hm⟩ := hh_even
      have : h ≤ 2 * k - 2 := by omega
      omega
    have heven : (a + k - 1) % 2 = 0 := by
      have : a + k - 1 = h := by dsimp [a]; omega
      rw [this]
      obtain ⟨m, hm⟩ := hh_even
      rw [hm]
      omega
    have h_piv := solveHigherTestsDP_eq_pivotTerm psi_hat F_hat a ha1 hak heven
    dsimp [pivotTerm, pivotTail] at h_piv
    have ha_k : a + k - 1 = h := by dsimp [a]; omega
    rw [ha_k] at h_piv
    apply higher_test_solved_of_pivot_eq hk_pos hk_h hh_lt psi_hat hpsi_k hpsi_prev F_hat (solveHigherTestsDP k psi_hat F_hat)
    exact h_piv

#print axioms Karlin.solveHigherTestsDP_solves_all_higher_tests

/-- Higher test vanishing for row-0 / column-0 rank-one perturbations (Eq. (48)). -/
theorem Z_DP_higher_test_row0_col0_perturbation_zero {k h : ℕ}
    (hk_pos : 0 < k) (hh : k + 1 ≤ h) (u v : Fin (k + 1) → ℚ) :
    matInnerProd (Z_DP (k + 1) h)
      (outerProd (fun i => if i.val = 0 then 1 else 0) u +
       outerProd v (fun j => if j.val = 0 then 1 else 0)) = 0 := by
  have h0 : 0 < k + 1 := by omega
  rw [matInnerProd_add_right]
  have h1 : matInnerProd (Z_DP (k + 1) h) (outerProd (fun i => if i.val = 0 then 1 else 0) u) = 0 := by
    dsimp [matInnerProd, outerProd]
    have h_inner : ∀ i : Fin (k + 1), (∑ j : Fin (k + 1), Z_DP (k + 1) h i j * ((if i.val = 0 then (1:ℚ) else 0) * u j)) = 0 := by
      intro i
      by_cases hi : i.val = 0
      · have hi_eq : i = ⟨0, h0⟩ := Fin.ext hi
        subst hi_eq
        rw [if_pos rfl]
        have h_all : ∀ j : Fin (k + 1), Z_DP (k + 1) h ⟨0, h0⟩ j * (1 * u j) = 0 := by
          intro j
          rw [Z_DP_first_row_zero_of_gt hh j h0, zero_mul]
        have h_sum : (∑ j : Fin (k + 1), Z_DP (k + 1) h ⟨0, h0⟩ j * (1 * u j)) = ∑ j : Fin (k + 1), 0 := by
          apply Finset.sum_congr rfl
          intro j _
          exact h_all j
        rw [h_sum, Finset.sum_const_zero]
      · rw [if_neg hi]
        have h_all : ∀ j : Fin (k + 1), Z_DP (k + 1) h i j * ((0 : ℚ) * u j) = 0 := by
          intro j
          rw [zero_mul, mul_zero]
        have h_sum : (∑ j : Fin (k + 1), Z_DP (k + 1) h i j * ((0 : ℚ) * u j)) = ∑ j : Fin (k + 1), 0 := by
          apply Finset.sum_congr rfl
          intro j _
          exact h_all j
        rw [h_sum, Finset.sum_const_zero]
    have h_sum : (∑ i : Fin (k + 1), ∑ j : Fin (k + 1), Z_DP (k + 1) h i j * ((if i.val = 0 then (1:ℚ) else 0) * u j)) =
        ∑ i : Fin (k + 1), 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact h_inner i
    rw [h_sum, Finset.sum_const_zero]
  have h2 : matInnerProd (Z_DP (k + 1) h) (outerProd v (fun j => if j.val = 0 then 1 else 0)) = 0 := by
    dsimp [matInnerProd, outerProd]
    have h_inner : ∀ i : Fin (k + 1), (∑ j : Fin (k + 1), Z_DP (k + 1) h i j * (v i * if j.val = 0 then (1:ℚ) else 0)) = 0 := by
      intro i
      have h_zero : ∀ j : Fin (k + 1), Z_DP (k + 1) h i j * (v i * if j.val = 0 then (1:ℚ) else 0) =
          if j = ⟨0, h0⟩ then Z_DP (k + 1) h i ⟨0, h0⟩ * v i else 0 := by
        intro j
        by_cases hj : j.val = 0
        · have hj_eq : j = ⟨0, h0⟩ := Fin.ext hj
          subst hj_eq
          rw [if_pos rfl, if_pos rfl, mul_one]
        · have hj_neq : j ≠ ⟨0, h0⟩ := fun h => hj (congr_arg Fin.val h)
          rw [if_neg hj, if_neg hj_neq, mul_zero, mul_zero]
      have h_sum : (∑ j : Fin (k + 1), Z_DP (k + 1) h i j * (v i * if j.val = 0 then (1:ℚ) else 0)) =
          ∑ j : Fin (k + 1), if j = ⟨0, h0⟩ then Z_DP (k + 1) h i ⟨0, h0⟩ * v i else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        exact h_zero j
      rw [h_sum, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), Z_DP_first_col_zero_of_gt hh i h0, zero_mul]
    have h_sum : (∑ i : Fin (k + 1), ∑ j : Fin (k + 1), Z_DP (k + 1) h i j * (v i * if j.val = 0 then (1:ℚ) else 0)) =
        ∑ i : Fin (k + 1), 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact h_inner i
    rw [h_sum, Finset.sum_const_zero]
  rw [h1, h2, add_zero]

#print axioms Karlin.Z_DP_higher_test_row0_col0_perturbation_zero

/-- Lowest test non-zero corner evaluation for row-0 / column-0 perturbations (Eq. (48)). -/
theorem Z_DP_lowest_test_row0_col0_perturbation {k : ℕ}
    (hk_pos : 0 < k) (hk_even : Even k) (u v : Fin (k + 1) → ℚ) :
    matInnerProd (Z_DP (k + 1) k)
      (outerProd (fun i => if i.val = 0 then 1 else 0) u +
       outerProd v (fun j => if j.val = 0 then 1 else 0)) =
      u ⟨k, by omega⟩ + v ⟨k, by omega⟩ := by
  have h0 : 0 < k + 1 := by omega
  rw [matInnerProd_add_right]
  have h1 : matInnerProd (Z_DP (k + 1) k) (outerProd (fun i => if i.val = 0 then 1 else 0) u) = u ⟨k, by omega⟩ := by
    dsimp [matInnerProd, outerProd]
    have h_inner : ∀ i : Fin (k + 1), (∑ j : Fin (k + 1), Z_DP (k + 1) k i j * ((if i.val = 0 then (1:ℚ) else 0) * u j)) =
        if i = ⟨0, h0⟩ then u ⟨k, by omega⟩ else 0 := by
      intro i
      by_cases hi : i.val = 0
      · have hi_eq : i = ⟨0, h0⟩ := Fin.ext hi
        rw [hi_eq]
        rw [if_pos rfl, if_pos rfl]
        have h_all : ∀ j : Fin (k + 1), Z_DP (k + 1) k ⟨0, h0⟩ j * (1 * u j) =
            if j = ⟨k, by omega⟩ then u ⟨k, by omega⟩ else 0 := by
          intro j
          by_cases hj : j.val = k
          · have hj_eq : j = ⟨k, by omega⟩ := Fin.ext hj
            rw [hj_eq]
            rw [if_pos rfl, one_mul]
            have h_top := @Z_DP_lowest_test_corner_top_right k
            rw [h_top, one_mul]
          · have hj_lt : j.val < k := by
              have : j.val < k + 1 := j.isLt
              omega
            have hj_neq : j ≠ ⟨k, by omega⟩ := fun h => hj (congr_arg Fin.val h)
            rw [if_neg hj_neq]
            rw [Z_DP_lowest_test_row_zero j hj_lt, zero_mul]
        have h_sum : (∑ j : Fin (k + 1), Z_DP (k + 1) k ⟨0, h0⟩ j * (1 * u j)) =
            ∑ j : Fin (k + 1), if j = ⟨k, by omega⟩ then u ⟨k, by omega⟩ else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          exact h_all j
        rw [h_sum, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      · rw [if_neg hi]
        have hi_neq : i ≠ ⟨0, h0⟩ := fun h => hi (congr_arg Fin.val h)
        rw [if_neg hi_neq]
        have h_all : ∀ j : Fin (k + 1), Z_DP (k + 1) k i j * ((0 : ℚ) * u j) = 0 := by
          intro j
          rw [zero_mul, mul_zero]
        have h_sum : (∑ j : Fin (k + 1), Z_DP (k + 1) k i j * ((0 : ℚ) * u j)) = ∑ j : Fin (k + 1), 0 := by
          apply Finset.sum_congr rfl
          intro j _
          exact h_all j
        rw [h_sum, Finset.sum_const_zero]
    have h_sum : (∑ i : Fin (k + 1), ∑ j : Fin (k + 1), Z_DP (k + 1) k i j * ((if i.val = 0 then (1:ℚ) else 0) * u j)) =
        ∑ i : Fin (k + 1), if i = ⟨0, h0⟩ then u ⟨k, by omega⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact h_inner i
    rw [h_sum, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  have h2 : matInnerProd (Z_DP (k + 1) k) (outerProd v (fun j => if j.val = 0 then 1 else 0)) = v ⟨k, by omega⟩ := by
    dsimp [matInnerProd, outerProd]
    have h_inner : ∀ i : Fin (k + 1), (∑ j : Fin (k + 1), Z_DP (k + 1) k i j * (v i * if j.val = 0 then (1:ℚ) else 0)) =
        if i = ⟨k, by omega⟩ then v ⟨k, by omega⟩ else 0 := by
      intro i
      have h_zero : ∀ j : Fin (k + 1), Z_DP (k + 1) k i j * (v i * if j.val = 0 then (1:ℚ) else 0) =
          if j = ⟨0, h0⟩ then Z_DP (k + 1) k i ⟨0, h0⟩ * v i else 0 := by
        intro j
        by_cases hj : j.val = 0
        · have hj_eq : j = ⟨0, h0⟩ := Fin.ext hj
          rw [hj_eq]
          rw [if_pos rfl, if_pos rfl, mul_one]
        · have hj_neq : j ≠ ⟨0, h0⟩ := fun h => hj (congr_arg Fin.val h)
          rw [if_neg hj, if_neg hj_neq, mul_zero, mul_zero]
      have h_sum : (∑ j : Fin (k + 1), Z_DP (k + 1) k i j * (v i * if j.val = 0 then (1:ℚ) else 0)) =
          ∑ j : Fin (k + 1), if j = ⟨0, h0⟩ then Z_DP (k + 1) k i ⟨0, h0⟩ * v i else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        exact h_zero j
      rw [h_sum, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      by_cases hi : i.val = k
      · have hi_eq : i = ⟨k, by omega⟩ := Fin.ext hi
        rw [hi_eq]
        rw [if_pos rfl]
        have h_corner := @Z_DP_lowest_test_corner_bottom_left k hk_even
        rw [h_corner, one_mul]
      · have hi_lt : i.val < k := by
          have : i.val < k + 1 := i.isLt
          omega
        have hi_neq : i ≠ ⟨k, by omega⟩ := fun h => hi (congr_arg Fin.val h)
        rw [if_neg hi_neq]
        rw [Z_DP_lowest_test_col_zero i hi_lt, zero_mul]
    have h_sum : (∑ i : Fin (k + 1), ∑ j : Fin (k + 1), Z_DP (k + 1) k i j * (v i * if j.val = 0 then (1:ℚ) else 0)) =
        ∑ i : Fin (k + 1), if i = ⟨k, by omega⟩ then v ⟨k, by omega⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact h_inner i
    rw [h_sum, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  rw [h1, h2]

#print axioms Karlin.Z_DP_lowest_test_row0_col0_perturbation

/-- The exact scalar gain calibration $d_c$ for even $k$ (Eq. (46) / `eq:parity`). -/
def dc_even_paper (k : ℕ) (F0_hat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) (uk vk : ℚ) : ℚ :=
  - (matInnerProd (Z_DP (k + 1) k) F0_hat) / (uk + vk)

/-- **Proposition 7.1 (General Even-$k$ Lowest-Test Cancellation & Preservation of Higher Tests)**:
    Setting $d_c = \operatorname{dc\_even\_paper}$ cancels the lowest test obstruction at $h = k$
    while leaving all higher tests $h \ge k + 1$ completely unchanged! -/
theorem prop_7_1_all_tests_solved_even_k {k : ℕ}
    (hk_pos : 0 < k) (hk_even : Even k)
    (F0_hat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (u v : Fin (k + 1) → ℚ)
    (hdenom : u ⟨k, by omega⟩ + v ⟨k, by omega⟩ ≠ 0) :
    let dc := dc_even_paper k F0_hat (u ⟨k, by omega⟩) (v ⟨k, by omega⟩)
    let F_hat := F0_hat + dc • (outerProd (fun i => if i.val = 0 then 1 else 0) u +
                                outerProd v (fun j => if j.val = 0 then 1 else 0))
    matInnerProd (Z_DP (k + 1) k) F_hat = 0 ∧
    ∀ h, k + 1 ≤ h → matInnerProd (Z_DP (k + 1) h) F_hat = matInnerProd (Z_DP (k + 1) h) F0_hat := by
  intro dc F_hat
  constructor
  · dsimp [F_hat]
    rw [matInnerProd_add_right, matInnerProd_smul_right]
    rw [Z_DP_lowest_test_row0_col0_perturbation hk_pos hk_even u v]
    dsimp [dc, dc_even_paper]
    rw [div_mul_cancel₀ _ hdenom]
    ring
  · intro h hh
    dsimp [F_hat]
    rw [matInnerProd_add_right, matInnerProd_smul_right]
    rw [Z_DP_higher_test_row0_col0_perturbation_zero hk_pos hh u v]
    rw [mul_zero, add_zero]

#print axioms Karlin.prop_7_1_all_tests_solved_even_k


/-!
## Part 8: Section 7.2 Concrete $\Phi_0, \Phi_1$ Instantiation (Eliminating All Premise Shortcuts)
-/

/-- The final boundary coordinate index in $\mathrm{Fin}\ (k + 1)$ corresponding to $\mathrm{Sum.inr}\ 0$. -/
def lastIdx (k : ℕ) : Fin (k + 1) := finSumFinEquiv (Sum.inr 0)

/-- The concrete rank-one inverse projector matrix $\Phi_0$ from Section 7.2 (Eq. (50)). -/
def Phi0_concrete (k : ℕ) (lam : ℚ) (zeta0 : Fin (k + 1) → ℚ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  Matrix.of fun x _ => if x = lastIdx k then ((k + 1 : ℚ) * lam * zeta0 (lastIdx k))⁻¹ else 0

/-- Coordinate lift matrix $U_\zeta \in \mathbb{Q}^{(k+1) \times k}$ from Section 7.2. -/
def U_zeta_concrete (k : ℕ) (zeta0 : Fin (k + 1) → ℚ) : Matrix (Fin (k + 1)) (Fin k) ℚ :=
  Matrix.of fun x j =>
    match finSumFinEquiv.symm x with
    | Sum.inl i => if i = j then 1 else 0
    | Sum.inr _ => - zeta0 (finSumFinEquiv (Sum.inl j)) / zeta0 (lastIdx k)

/-- The concrete complementary projector matrix $\Phi_1 = U_\zeta \Pi$ from Section 7.2 (Eq. (50)). -/
def Phi1_concrete (k : ℕ) (zeta0 : Fin (k + 1) → ℚ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  U_zeta_concrete k zeta0 * Pi_mat k

/-- Concrete reset block $W = \mathbf{1}_{k+1} \upsilon + T_2 V_0$ with $\upsilon = (T_1 \lambda) \bullet \zeta^\circ$. -/
def W_concrete (k : ℕ) (T1 T2 lam : ℚ) (zeta0 : Fin (k + 1) → ℚ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  W_paper ((T1 * lam) • zeta0) T2 (V0_paper k)

/-- Concrete two-sided inverse $W^{-1} = T_1^{-1} \Phi_0 + T_2^{-1} \Phi_1$. -/
def Winv_concrete (k : ℕ) (T1 T2 lam : ℚ) (zeta0 : Fin (k + 1) → ℚ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  W_inv_paper T1 T2 (Phi0_concrete k lam zeta0) (Phi1_concrete k zeta0)

/-- Block identity 1: $V_0 \Phi_0 = 0$. -/
theorem V0_mul_Phi0_concrete (k : ℕ) (lam : ℚ) (zeta0 : Fin (k + 1) → ℚ) :
    V0_paper k * Phi0_concrete k lam zeta0 = 0 := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.zero_apply, Phi0_concrete, Matrix.of_apply]
  have h_single : ∀ z : Fin (k + 1), V0_paper k x z * (if z = lastIdx k then ((k + 1 : ℚ) * lam * zeta0 (lastIdx k))⁻¹ else 0) =
      if z = lastIdx k then V0_paper k x (lastIdx k) * ((k + 1 : ℚ) * lam * zeta0 (lastIdx k))⁻¹ else 0 := by
    intro z
    by_cases hz : z = lastIdx k
    · subst hz; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hz, if_neg hz, mul_zero]
  have h_sum : (∑ z : Fin (k + 1), V0_paper k x z * (if z = lastIdx k then ((k + 1 : ℚ) * lam * zeta0 (lastIdx k))⁻¹ else 0)) =
      ∑ z : Fin (k + 1), if z = lastIdx k then V0_paper k x (lastIdx k) * ((k + 1 : ℚ) * lam * zeta0 (lastIdx k))⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro z _
    exact h_single z
  rw [h_sum, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  have h_last : lastIdx k = finSumFinEquiv (Sum.inr 0) := rfl
  rw [h_last, V0_last_col_zero, zero_mul]

#print axioms Karlin.V0_mul_Phi0_concrete

/-- Block identity 2: $\mathbf{1} \upsilon \Phi_0 = T_1 \frac{1}{r} \mathbf{1} \mathbf{1}^\top$. -/
theorem outerProd_one_mul_Phi0_concrete (k : ℕ) (T1 lam : ℚ) (hlam : lam ≠ 0)
    (zeta0 : Fin (k + 1) → ℚ) (hzeta : zeta0 (lastIdx k) ≠ 0) :
    outerProd (fun _ : Fin (k + 1) => (1:ℚ)) ((T1 * lam) • zeta0) * Phi0_concrete k lam zeta0 =
      T1 • ((k + 1 : ℚ)⁻¹ • outerProd (fun _ : Fin (k + 1) => (1:ℚ)) (fun _ : Fin (k + 1) => (1:ℚ))) := by
  ext i j
  simp only [Matrix.mul_apply, outerProd, Phi0_concrete, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply,
             smul_eq_mul, mul_one, one_mul]
  have h_single : ∀ z : Fin (k + 1), (T1 * lam * zeta0 z) * (if z = lastIdx k then ((k + 1 : ℚ) * lam * zeta0 (lastIdx k))⁻¹ else 0) =
      if z = lastIdx k then (T1 * lam * zeta0 (lastIdx k)) * ((k + 1 : ℚ) * lam * zeta0 (lastIdx k))⁻¹ else 0 := by
    intro z
    by_cases hz : z = lastIdx k
    · subst hz; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hz, if_neg hz, mul_zero]
  have h_sum : (∑ z : Fin (k + 1), (T1 * lam * zeta0 z) * (if z = lastIdx k then ((k + 1 : ℚ) * lam * zeta0 (lastIdx k))⁻¹ else 0)) =
      ∑ z : Fin (k + 1), if z = lastIdx k then (T1 * lam * zeta0 (lastIdx k)) * ((k + 1 : ℚ) * lam * zeta0 (lastIdx k))⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro z _
    exact h_single z
  rw [h_sum, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  have hk : (k + 1 : ℚ) ≠ 0 := by positivity
  have hlz : lam * zeta0 (lastIdx k) ≠ 0 := mul_ne_zero hlam hzeta
  have h_assoc : (k + 1 : ℚ) * lam * zeta0 (lastIdx k) = (k + 1 : ℚ) * (lam * zeta0 (lastIdx k)) := by ring
  rw [h_assoc, mul_inv (k + 1 : ℚ) (lam * zeta0 (lastIdx k))]
  calc T1 * lam * zeta0 (lastIdx k) * ((k + 1 : ℚ)⁻¹ * (lam * zeta0 (lastIdx k))⁻¹)
    _ = T1 * (k + 1 : ℚ)⁻¹ * (lam * zeta0 (lastIdx k) * (lam * zeta0 (lastIdx k))⁻¹) := by ring
    _ = T1 * (k + 1 : ℚ)⁻¹ * 1 := by rw [mul_inv_cancel₀ hlz]
    _ = T1 * (k + 1 : ℚ)⁻¹ := by ring

#print axioms Karlin.outerProd_one_mul_Phi0_concrete

/-- Lift orthogonality: $\mathbf{1} \upsilon U_\zeta = 0$. -/
theorem outerProd_one_mul_U_zeta_concrete (k : ℕ) (T1 lam : ℚ) (zeta0 : Fin (k + 1) → ℚ)
    (hzeta : zeta0 (lastIdx k) ≠ 0) :
    outerProd (fun _ : Fin (k + 1) => (1:ℚ)) ((T1 * lam) • zeta0) * U_zeta_concrete k zeta0 = 0 := by
  ext i j
  simp only [Matrix.mul_apply, outerProd, Matrix.zero_apply, U_zeta_concrete, Matrix.of_apply,
             one_mul, Pi.smul_apply, smul_eq_mul]
  have hcomp := (Equiv.sum_comp (finSumFinEquiv (m := k) (n := 1)) (fun z =>
      (T1 * lam * zeta0 z) * match finSumFinEquiv.symm z with
      | Sum.inl i => if i = j then (1:ℚ) else 0
      | Sum.inr _ => - zeta0 (finSumFinEquiv (Sum.inl j)) / zeta0 (lastIdx k))).symm
  rw [hcomp, Fintype.sum_sum_type]
  have hinl : (∑ l : Fin k, (T1 * lam * zeta0 (finSumFinEquiv (Sum.inl l))) *
      match (finSumFinEquiv (m := k) (n := 1)).symm (finSumFinEquiv (Sum.inl l)) with
      | Sum.inl i => if i = j then (1:ℚ) else 0
      | Sum.inr _ => - zeta0 (finSumFinEquiv (Sum.inl j)) / zeta0 (lastIdx k)) =
      T1 * lam * zeta0 (finSumFinEquiv (Sum.inl j)) := by
    simp only [Equiv.symm_apply_apply]
    have h_single : (∑ l : Fin k, (T1 * lam * zeta0 (finSumFinEquiv (Sum.inl l))) * (if l = j then (1:ℚ) else 0)) =
        T1 * lam * zeta0 (finSumFinEquiv (Sum.inl j)) * 1 := by
      have h_term : ∀ l : Fin k, (T1 * lam * zeta0 (finSumFinEquiv (Sum.inl l))) * (if l = j then (1:ℚ) else 0) =
          if l = j then (T1 * lam * zeta0 (finSumFinEquiv (Sum.inl l))) * 1 else 0 := by
        intro l
        by_cases hlj : l = j
        · subst hlj; rw [if_pos rfl, if_pos rfl]
        · rw [if_neg hlj, if_neg hlj, mul_zero]
      rw [Finset.sum_congr rfl (fun l _ => h_term l), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    rw [h_single, mul_one]
  have hinr : (∑ l : Fin 1, (T1 * lam * zeta0 (finSumFinEquiv (Sum.inr l))) *
      match (finSumFinEquiv (m := k) (n := 1)).symm (finSumFinEquiv (Sum.inr l)) with
      | Sum.inl i => if i = j then (1:ℚ) else 0
      | Sum.inr _ => - zeta0 (finSumFinEquiv (Sum.inl j)) / zeta0 (lastIdx k)) =
      - (T1 * lam * zeta0 (finSumFinEquiv (Sum.inl j))) := by
    have : (Finset.univ : Finset (Fin 1)) = {0} := rfl
    rw [this, Finset.sum_singleton]
    simp only [Equiv.symm_apply_apply]
    have h_last : finSumFinEquiv (Sum.inr 0) = lastIdx k := rfl
    rw [h_last]
    calc T1 * lam * zeta0 (lastIdx k) * (- zeta0 (finSumFinEquiv (Sum.inl j)) / zeta0 (lastIdx k))
      _ = (T1 * lam) * (zeta0 (lastIdx k) * (- zeta0 (finSumFinEquiv (Sum.inl j)) / zeta0 (lastIdx k))) := by ring
      _ = (T1 * lam) * (- zeta0 (finSumFinEquiv (Sum.inl j))) := by
        rw [mul_div_cancel₀ _ hzeta]
      _ = - (T1 * lam * zeta0 (finSumFinEquiv (Sum.inl j))) := by ring
  rw [hinl, hinr, add_neg_cancel]

#print axioms Karlin.outerProd_one_mul_U_zeta_concrete

/-- Block identity 3: $\mathbf{1} \upsilon \Phi_1 = 0$. -/
theorem outerProd_one_mul_Phi1_concrete (k : ℕ) (T1 lam : ℚ) (zeta0 : Fin (k + 1) → ℚ)
    (hzeta : zeta0 (lastIdx k) ≠ 0) :
    outerProd (fun _ : Fin (k + 1) => (1:ℚ)) ((T1 * lam) • zeta0) * Phi1_concrete k zeta0 = 0 := by
  dsimp [Phi1_concrete]
  rw [← Matrix.mul_assoc]
  rw [outerProd_one_mul_U_zeta_concrete k T1 lam zeta0 hzeta]
  rw [Matrix.zero_mul]

#print axioms Karlin.outerProd_one_mul_Phi1_concrete

/-- $V_0 U_\zeta = [I_k \mid -\mathbf{1}_k]^\top$. -/
theorem V0_mul_U_zeta_concrete (k : ℕ) (zeta0 : Fin (k + 1) → ℚ) :
    V0_paper k * U_zeta_concrete k zeta0 =
      Matrix.of fun x j =>
        match finSumFinEquiv.symm x with
        | Sum.inl i => if i = j then 1 else 0
        | Sum.inr _ => -1 := by
  ext x j
  simp only [Matrix.mul_apply, U_zeta_concrete, Matrix.of_apply]
  have hcomp := (Equiv.sum_comp (finSumFinEquiv (m := k) (n := 1)) (fun z =>
      V0_paper k x z * match finSumFinEquiv.symm z with
      | Sum.inl i => if i = j then (1:ℚ) else 0
      | Sum.inr _ => - zeta0 (finSumFinEquiv (Sum.inl j)) / zeta0 (lastIdx k))).symm
  rw [hcomp, Fintype.sum_sum_type]
  have hinl : (∑ l : Fin k, V0_paper k x (finSumFinEquiv (Sum.inl l)) *
      match (finSumFinEquiv (m := k) (n := 1)).symm (finSumFinEquiv (Sum.inl l)) with
      | Sum.inl i => if i = j then (1:ℚ) else 0
      | Sum.inr _ => - zeta0 (finSumFinEquiv (Sum.inl j)) / zeta0 (lastIdx k)) =
      V0_paper k x (finSumFinEquiv (Sum.inl j)) := by
    simp only [Equiv.symm_apply_apply]
    have h_single : (∑ l : Fin k, V0_paper k x (finSumFinEquiv (Sum.inl l)) * (if l = j then (1:ℚ) else 0)) =
        V0_paper k x (finSumFinEquiv (Sum.inl j)) * 1 := by
      have h_term : ∀ l : Fin k, V0_paper k x (finSumFinEquiv (Sum.inl l)) * (if l = j then (1:ℚ) else 0) =
          if l = j then V0_paper k x (finSumFinEquiv (Sum.inl l)) * 1 else 0 := by
        intro l
        by_cases hlj : l = j
        · subst hlj; rw [if_pos rfl, if_pos rfl]
        · rw [if_neg hlj, if_neg hlj, mul_zero]
      rw [Finset.sum_congr rfl (fun l _ => h_term l), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    rw [h_single, mul_one]
  have hinr : (∑ l : Fin 1, V0_paper k x (finSumFinEquiv (Sum.inr l)) *
      match (finSumFinEquiv (m := k) (n := 1)).symm (finSumFinEquiv (Sum.inr l)) with
      | Sum.inl i => if i = j then (1:ℚ) else 0
      | Sum.inr _ => - zeta0 (finSumFinEquiv (Sum.inl j)) / zeta0 (lastIdx k)) = 0 := by
    have : (Finset.univ : Finset (Fin 1)) = {0} := rfl
    rw [this, Finset.sum_singleton]
    simp only [Equiv.symm_apply_apply]
    rw [V0_last_col_zero, zero_mul]
  rw [hinl, hinr, add_zero]
  dsimp [V0_paper]
  cases finSumFinEquiv.symm x with
  | inl _ => simp
  | inr _ => simp

#print axioms Karlin.V0_mul_U_zeta_concrete

/-- Block identity 4: $V_0 \Phi_1 = I_r - \frac{1}{r} \mathbf{1} \mathbf{1}^\top$. -/
theorem V0_mul_Phi1_concrete (k : ℕ) (zeta0 : Fin (k + 1) → ℚ) :
    V0_paper k * Phi1_concrete k zeta0 =
      1 - (k + 1 : ℚ)⁻¹ • outerProd (fun _ => 1) (fun _ => 1) := by
  dsimp [Phi1_concrete]
  rw [← Matrix.mul_assoc, V0_mul_U_zeta_concrete]
  ext x y
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply,
             Matrix.smul_apply, outerProd, smul_eq_mul, mul_one]
  have h_inv : 1 / (k + 1 : ℚ) = (k + 1 : ℚ)⁻¹ := one_div (k + 1 : ℚ)
  cases hx : finSumFinEquiv.symm x with
  | inl i =>
    have h_term : (∑ j : Fin k, (if i = j then (1:ℚ) else 0) * Pi_mat k j y) = Pi_mat k i y := by
      have : ∀ j : Fin k, (if i = j then (1:ℚ) else 0) * Pi_mat k j y = if j = i then Pi_mat k i y else 0 := by
        intro j; by_cases hij : i = j
        · subst hij; rw [if_pos rfl, if_pos rfl, one_mul]
        · have hji : j ≠ i := fun h => hij h.symm
          rw [if_neg hij, if_neg hji, zero_mul]
      rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    rw [h_term]
    dsimp [Pi_mat]
    cases hy : finSumFinEquiv.symm y with
    | inl l =>
      dsimp
      have h_xy : (x = y) ↔ (i = l) := by
        constructor
        · intro h; subst h; rw [hy] at hx; cases hx; rfl
        · intro h; subst h
          have hx_eq : x = finSumFinEquiv (Sum.inl i) := by rw [← hx, Equiv.apply_symm_apply]
          have hy_eq : y = finSumFinEquiv (Sum.inl i) := by rw [← hy, Equiv.apply_symm_apply]
          rw [hx_eq, hy_eq]
      by_cases hil : i = l
      · subst hil; rw [if_pos rfl, if_pos (h_xy.mpr rfl), h_inv]
      · rw [if_neg hil, if_neg (fun h => hil (h_xy.mp h)), h_inv]
    | inr _ =>
      dsimp
      have h_xy : x ≠ y := by
        intro h; subst h; rw [hy] at hx; contradiction
      rw [if_neg h_xy, h_inv]
      ring
  | inr vx =>
    have h_neg : (∑ j : Fin k, (-1 : ℚ) * Pi_mat k j y) = - ∑ j : Fin k, Pi_mat k j y := by
      rw [← Finset.mul_sum, neg_one_mul]
    rw [h_neg]
    dsimp [Pi_mat]
    cases hy : finSumFinEquiv.symm y with
    | inl l =>
      dsimp
      have h_sum : (∑ j : Fin k, ((if j = l then (1:ℚ) else 0) - 1 / (k + 1 : ℚ))) =
          1 - (k : ℚ) * (k + 1 : ℚ)⁻¹ := by
        rw [Finset.sum_sub_distrib]
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, h_inv]
      rw [h_sum]
      have hr : (k + 1 : ℚ) ≠ 0 := by positivity
      have h_calc : - (1 - (k : ℚ) * (k + 1 : ℚ)⁻¹) = - (k + 1 : ℚ)⁻¹ := by
        calc - (1 - (k : ℚ) * (k + 1 : ℚ)⁻¹)
          _ = -1 + (k : ℚ) * (k + 1 : ℚ)⁻¹ := by ring
          _ = - ((k + 1 : ℚ) * (k + 1 : ℚ)⁻¹) + (k : ℚ) * (k + 1 : ℚ)⁻¹ := by
            rw [mul_inv_cancel₀ hr]
          _ = - (k + 1 : ℚ)⁻¹ := by ring
      rw [h_calc]
      have h_xy : x ≠ y := by
        intro h; subst h; rw [hy] at hx; contradiction
      rw [if_neg h_xy, zero_sub]
    | inr vy =>
      dsimp
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, h_inv]
      have hr : (k + 1 : ℚ) ≠ 0 := by positivity
      have h_calc : - ((k : ℚ) * - (k + 1 : ℚ)⁻¹) = 1 - (k + 1 : ℚ)⁻¹ := by
        calc - ((k : ℚ) * - (k + 1 : ℚ)⁻¹)
          _ = (k : ℚ) * (k + 1 : ℚ)⁻¹ := by ring
          _ = ((k + 1 : ℚ) - 1) * (k + 1 : ℚ)⁻¹ := by ring
          _ = (k + 1 : ℚ) * (k + 1 : ℚ)⁻¹ - (k + 1 : ℚ)⁻¹ := by ring
          _ = 1 - (k + 1 : ℚ)⁻¹ := by rw [mul_inv_cancel₀ hr]
      rw [h_calc]
      have hvx : vx = 0 := Subsingleton.elim vx 0
      have hvy : vy = 0 := Subsingleton.elim vy 0
      rw [hvx] at hx
      rw [hvy] at hy
      have hx_eq : x = finSumFinEquiv (Sum.inr 0) := by rw [← hx, Equiv.apply_symm_apply]
      have hy_eq : y = finSumFinEquiv (Sum.inr 0) := by rw [← hy, Equiv.apply_symm_apply]
      have h_xy : x = y := by rw [hx_eq, hy_eq]
      rw [if_pos h_xy]

#print axioms Karlin.V0_mul_Phi1_concrete

/-- **Unconditional Concrete Right Inverse of $W$ (Section 7.2)**:
    $W_{\mathrm{concrete}} W^{-1}_{\mathrm{concrete}} = I_{k+1}$ with ZERO abstract matrix hypotheses. -/
theorem W_concrete_mul_Winv_concrete (k : ℕ) (T1 T2 lam : ℚ)
    (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0) (hlam : lam ≠ 0)
    (zeta0 : Fin (k + 1) → ℚ) (hzeta : zeta0 (lastIdx k) ≠ 0) :
    W_concrete k T1 T2 lam zeta0 * Winv_concrete k T1 T2 lam zeta0 = 1 := by
  dsimp [W_concrete, Winv_concrete]
  apply W_mul_Winv_paper ((T1 * lam) • zeta0) T1 T2 hT1 hT2 (V0_paper k) (Phi0_concrete k lam zeta0) (Phi1_concrete k zeta0)
  · have hcard : (Fintype.card (Fin (k + 1)) : ℚ) = (k + 1 : ℚ) := by simp
    rw [hcard]
    exact outerProd_one_mul_Phi0_concrete k T1 lam hlam zeta0 hzeta
  · exact V0_mul_Phi0_concrete k lam zeta0
  · exact outerProd_one_mul_Phi1_concrete k T1 lam zeta0 hzeta
  · have hcard : (Fintype.card (Fin (k + 1)) : ℚ) = (k + 1 : ℚ) := by simp
    rw [hcard]
    exact V0_mul_Phi1_concrete k zeta0

#print axioms Karlin.W_concrete_mul_Winv_concrete

/-- **Unconditional Concrete Left Inverse of $W$ (Section 7.2)**:
    $W^{-1}_{\mathrm{concrete}} W_{\mathrm{concrete}} = I_{k+1}$ with ZERO abstract matrix hypotheses. -/
theorem Winv_concrete_mul_W_concrete (k : ℕ) (T1 T2 lam : ℚ)
    (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0) (hlam : lam ≠ 0)
    (zeta0 : Fin (k + 1) → ℚ) (hzeta : zeta0 (lastIdx k) ≠ 0) :
    Winv_concrete k T1 T2 lam zeta0 * W_concrete k T1 T2 lam zeta0 = 1 := by
  rw [mul_eq_one_comm]
  exact W_concrete_mul_Winv_concrete k T1 T2 lam hT1 hT2 hlam zeta0 hzeta

#print axioms Karlin.Winv_concrete_mul_W_concrete

/-- **Two-Sided Sherman-Morrison Formula (Left Inverse)**:
    $W_E^{-1} W_E = I$ assuming $W^{-1} W = 1$ and non-zero denominator. -/
theorem sherman_morrison_rank1_left_inv {r : Type*} [Fintype r] [DecidableEq r]
    (W Winv : Matrix r r ℚ) (hW_left : Winv * W = 1)
    (u v : r → ℚ)
    (hdenom : 1 + dotProduct v (Matrix.mulVec Winv u) ≠ 0) :
    let d := 1 + dotProduct v (Matrix.mulVec Winv u)
    let WE := W + outerProd u v
    let WE_inv := Winv - d⁻¹ • (Winv * (outerProd u v * Winv))
    WE_inv * WE = 1 := by
  intro d WE WE_inv
  have hW_right : W * Winv = 1 := by
    rw [mul_eq_one_comm] at hW_left
    exact hW_left
  have h_right := sherman_morrison_rank1_inv W Winv hW_right u v hdenom
  dsimp [WE, WE_inv] at h_right ⊢
  rw [mul_eq_one_comm]
  exact h_right

#print axioms Karlin.sherman_morrison_rank1_left_inv

/-- Concrete rank-one updated reset block $W_E = W + u \otimes v$. -/
def WE_concrete (k : ℕ) (T1 T2 lam : ℚ) (zeta0 : Fin (k + 1) → ℚ) (u v : Fin (k + 1) → ℚ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  W_concrete k T1 T2 lam zeta0 + outerProd u v

/-- Concrete Sherman-Morrison inverse matrix $W_E^{-1}$. -/
def WE_inv_concrete (k : ℕ) (T1 T2 lam : ℚ) (zeta0 : Fin (k + 1) → ℚ) (u v : Fin (k + 1) → ℚ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  let Winv := Winv_concrete k T1 T2 lam zeta0
  let d := 1 + dotProduct v (Matrix.mulVec Winv u)
  Winv - d⁻¹ • (Winv * (outerProd u v * Winv))

/-- Concrete $W_E W_E^{-1} = 1$ with ZERO matrix hypotheses. -/
theorem WE_concrete_mul_inv (k : ℕ) (T1 T2 lam : ℚ)
    (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0) (hlam : lam ≠ 0)
    (zeta0 : Fin (k + 1) → ℚ) (hzeta : zeta0 (lastIdx k) ≠ 0)
    (u v : Fin (k + 1) → ℚ)
    (hdenom : 1 + dotProduct v (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) u) ≠ 0) :
    WE_concrete k T1 T2 lam zeta0 u v * WE_inv_concrete k T1 T2 lam zeta0 u v = 1 := by
  dsimp [WE_concrete, WE_inv_concrete]
  apply sherman_morrison_rank1_inv (W_concrete k T1 T2 lam zeta0) (Winv_concrete k T1 T2 lam zeta0)
  · exact W_concrete_mul_Winv_concrete k T1 T2 lam hT1 hT2 hlam zeta0 hzeta
  · exact hdenom

#print axioms Karlin.WE_concrete_mul_inv

/-- Concrete $W_E^{-1} W_E = 1$ with ZERO matrix hypotheses. -/
theorem WE_inv_concrete_mul_WE (k : ℕ) (T1 T2 lam : ℚ)
    (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0) (hlam : lam ≠ 0)
    (zeta0 : Fin (k + 1) → ℚ) (hzeta : zeta0 (lastIdx k) ≠ 0)
    (u v : Fin (k + 1) → ℚ)
    (hdenom : 1 + dotProduct v (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) u) ≠ 0) :
    WE_inv_concrete k T1 T2 lam zeta0 u v * WE_concrete k T1 T2 lam zeta0 u v = 1 := by
  rw [mul_eq_one_comm]
  exact WE_concrete_mul_inv k T1 T2 lam hT1 hT2 hlam zeta0 hzeta u v hdenom

#print axioms Karlin.WE_inv_concrete_mul_WE

/-- **Master Exact Quadratic Realization Theorem (Concrete $M^\top J M = E$, Eq. (1723))**:
    Holds unconditionally for the paper's concrete reset matrices with ZERO matrix hypotheses. -/
theorem M_transpose_mul_J_mul_M_concrete (k : ℕ) (T1 T2 lam : ℚ)
    (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0) (hlam : lam ≠ 0)
    (zeta0 : Fin (k + 1) → ℚ) (hzeta : zeta0 (lastIdx k) ≠ 0)
    (u v : Fin (k + 1) → ℚ)
    (hdenom : 1 + dotProduct v (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) u) ≠ 0)
    (eta kappa : ℚ) (Lr : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (E E_base : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (Fres : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hFres : Fres = E - E_base - eta • ((WE_concrete k T1 T2 lam zeta0 u v)ᵀ * Lr * (WE_concrete k T1 T2 lam zeta0 u v) +
                                         (W_concrete k T1 T2 lam zeta0)ᵀ * Lr * (W_concrete k T1 T2 lam zeta0)))
    (C_cross : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hC_cross : C_cross = kappa • (outerProd (fun _ => 1) (fun _ => 1)) + (Winv_concrete k T1 T2 lam zeta0)ᵀ * Fres * (WE_inv_concrete k T1 T2 lam zeta0 u v))
    (hEbase : (W_concrete k T1 T2 lam zeta0)ᵀ * (kappa • (outerProd (fun _ => 1) (fun _ => 1))) * (WE_concrete k T1 T2 lam zeta0 u v) = E_base) :
    eta • ((WE_concrete k T1 T2 lam zeta0 u v)ᵀ * Lr * (WE_concrete k T1 T2 lam zeta0 u v) +
           (W_concrete k T1 T2 lam zeta0)ᵀ * Lr * (W_concrete k T1 T2 lam zeta0)) +
    (W_concrete k T1 T2 lam zeta0)ᵀ * C_cross * (WE_concrete k T1 T2 lam zeta0 u v) = E := by
  apply M_transpose_mul_J_mul_M (WE_concrete k T1 T2 lam zeta0 u v) (W_concrete k T1 T2 lam zeta0)
    (WE_inv_concrete k T1 T2 lam zeta0 u v) (Winv_concrete k T1 T2 lam zeta0)
  · exact WE_inv_concrete_mul_WE k T1 T2 lam hT1 hT2 hlam zeta0 hzeta u v hdenom
  · have : (W_concrete k T1 T2 lam zeta0)ᵀ * (Winv_concrete k T1 T2 lam zeta0)ᵀ =
        (Winv_concrete k T1 T2 lam zeta0 * W_concrete k T1 T2 lam zeta0)ᵀ := by
      rw [Matrix.transpose_mul]
    rw [this, Winv_concrete_mul_W_concrete k T1 T2 lam hT1 hT2 hlam zeta0 hzeta, Matrix.transpose_one]
  · exact hFres
  · exact hC_cross
  · exact hEbase

#print axioms Karlin.M_transpose_mul_J_mul_M_concrete

/-- Row sum of $W_{\mathrm{concrete}}$: $\mathbf{1}_{k+1}^\top W_{\mathrm{concrete}} = (k+1)(T_1 \lambda) \zeta^\circ$. -/
theorem vecMul_one_W_concrete (k : ℕ) (T1 T2 lam : ℚ) (zeta0 : Fin (k + 1) → ℚ) :
    Matrix.vecMul (fun _ => 1) (W_concrete k T1 T2 lam zeta0) =
      ((k + 1 : ℚ) * T1 * lam) • zeta0 := by
  have hcard : (Fintype.card (Fin (k + 1)) : ℚ) = (k + 1 : ℚ) := by simp
  dsimp [W_concrete]
  have h := vecMul_one_W_paper ((T1 * lam) • zeta0) T2 (V0_paper k) (vecMul_one_V0 k)
  rw [hcard] at h
  rw [h]
  ext j
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

#print axioms Karlin.vecMul_one_W_concrete

/-- Row sum of rank-one update vector $u = e_0$: $\mathbf{1}^\top (u \otimes v) = v$. -/
theorem vecMul_one_outerProd_u (k : ℕ) (v : Fin (k + 1) → ℚ) :
    Matrix.vecMul (fun _ => 1) (outerProd (fun i : Fin (k + 1) => if i.val = 0 then (1:ℚ) else 0) v) = v := by
  ext j
  dsimp [Matrix.vecMul, dotProduct, outerProd]
  have h_term : ∀ x : Fin (k + 1), (1 : ℚ) * ((if x.val = 0 then (1:ℚ) else 0) * v j) =
      if x = ⟨0, Nat.succ_pos k⟩ then v j else 0 := by
    intro x
    simp only [one_mul]
    by_cases hx : x.val = 0
    · have hx_eq : x = ⟨0, Nat.succ_pos k⟩ := Fin.ext hx
      rw [if_pos hx, if_pos hx_eq, one_mul]
    · have hx_ne : x ≠ ⟨0, Nat.succ_pos k⟩ := fun h => hx (congr_arg Fin.val h)
      rw [if_neg hx, if_neg hx_ne, zero_mul]
  rw [Finset.sum_congr rfl (fun x _ => h_term x), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

#print axioms Karlin.vecMul_one_outerProd_u

/-- Row sum of $W_E$: $\mathbf{1}_{k+1}^\top W_E = (k+1)(T_1 \lambda) \zeta^\circ + (k+1)\lambda \ell_\Delta$. -/
theorem vecMul_one_WE_concrete (k : ℕ) (T1 T2 lam : ℚ) (zeta0 : Fin (k + 1) → ℚ)
    (ell_Delta : Fin (k + 1) → ℚ) :
    Matrix.vecMul (fun _ => 1) (WE_concrete k T1 T2 lam zeta0
      (fun i => if i.val = 0 then 1 else 0) (((k + 1 : ℚ) * lam) • ell_Delta)) =
      ((k + 1 : ℚ) * T1 * lam) • zeta0 + ((k + 1 : ℚ) * lam) • ell_Delta := by
  dsimp [WE_concrete]
  rw [Matrix.vecMul_add, vecMul_one_W_concrete, vecMul_one_outerProd_u]

#print axioms Karlin.vecMul_one_WE_concrete

/-- **Exact Concrete Base Matrix Realization (Discharging $E_{\mathrm{base}}$)**:
    $W_{\mathrm{concrete}}^\top (\kappa \mathbf{1}\mathbf{1}^\top) W_E = T_1 \zeta^\circ (\zeta^\circ)^\top + \zeta^\circ \ell_\Delta^\top$. -/
theorem W_concrete_transpose_mul_one_mul_WE_concrete (k : ℕ) (T1 T2 lam : ℚ)
    (hT1 : T1 ≠ 0) (hlam : lam ≠ 0)
    (zeta0 ell_Delta : Fin (k + 1) → ℚ) :
    let u : Fin (k + 1) → ℚ := fun i => if i.val = 0 then 1 else 0
    let v : Fin (k + 1) → ℚ := ((k + 1 : ℚ) * lam) • ell_Delta
    let kappa : ℚ := ((k + 1 : ℚ)^2 * T1 * lam^2)⁻¹
    (W_concrete k T1 T2 lam zeta0)ᵀ * (kappa • outerProd (fun _ => 1) (fun _ => 1)) *
      (WE_concrete k T1 T2 lam zeta0 u v) =
      T1 • outerProd zeta0 zeta0 + outerProd zeta0 ell_Delta := by
  intro u v kappa
  have h1 : (W_concrete k T1 T2 lam zeta0)ᵀ * (kappa • outerProd (fun _ => 1) (fun _ => 1)) =
      kappa • outerProd (Matrix.vecMul (fun _ => 1) (W_concrete k T1 T2 lam zeta0)) (fun _ => 1) := by
    rw [Matrix.mul_smul, mul_outerProd, Matrix.mulVec_transpose]
  have h2 : outerProd (Matrix.vecMul (fun _ => 1) (W_concrete k T1 T2 lam zeta0)) (fun _ => 1) *
      (WE_concrete k T1 T2 lam zeta0 u v) =
      outerProd (Matrix.vecMul (fun _ => 1) (W_concrete k T1 T2 lam zeta0))
        (Matrix.vecMul (fun _ => 1) (WE_concrete k T1 T2 lam zeta0 u v)) := by
    rw [outerProd_mul]
  rw [h1, Matrix.smul_mul, h2]
  rw [vecMul_one_W_concrete, vecMul_one_WE_concrete]
  ext i j
  simp only [Matrix.smul_apply, outerProd, Matrix.add_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  dsimp [kappa]
  have hk : (k + 1 : ℚ) ≠ 0 := by positivity
  have hden : (k + 1 : ℚ)^2 * T1 * lam^2 ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hk) hT1) (pow_ne_zero 2 hlam)
  have h_alg : ((k + 1 : ℚ) * T1 * lam * zeta0 i) *
      (((k + 1 : ℚ) * T1 * lam * zeta0 j) + ((k + 1 : ℚ) * lam * ell_Delta j)) =
      ((k + 1 : ℚ)^2 * T1 * lam^2) * (T1 * zeta0 i * zeta0 j + zeta0 i * ell_Delta j) := by ring
  rw [h_alg, ← mul_assoc, inv_mul_cancel₀ hden, one_mul]
  ring

#print axioms Karlin.W_concrete_transpose_mul_one_mul_WE_concrete

/-- **Fully Concrete Master Exact Quadratic Realization Theorem**:
    Realizes $M^\top J M = E$ for the paper's concrete matrices with $E_{\mathrm{base}}$
    completely discharged and ZERO uninstantiated matrix hypotheses. -/
theorem M_transpose_mul_J_mul_M_fully_concrete (k : ℕ) (T1 T2 lam : ℚ)
    (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0) (hlam : lam ≠ 0)
    (zeta0 : Fin (k + 1) → ℚ) (hzeta : zeta0 (lastIdx k) ≠ 0)
    (ell_Delta : Fin (k + 1) → ℚ)
    (u : Fin (k + 1) → ℚ) (hu : u = fun i => if i.val = 0 then 1 else 0)
    (v : Fin (k + 1) → ℚ) (hv : v = ((k + 1 : ℚ) * lam) • ell_Delta)
    (kappa : ℚ) (hkappa : kappa = ((k + 1 : ℚ)^2 * T1 * lam^2)⁻¹)
    (E_base : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hE_base : E_base = T1 • outerProd zeta0 zeta0 + outerProd zeta0 ell_Delta)
    (hdenom : 1 + dotProduct v (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) u) ≠ 0)
    (eta : ℚ) (Lr : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (Fres : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hFres : Fres = E - E_base - eta • ((WE_concrete k T1 T2 lam zeta0 u v)ᵀ * Lr * (WE_concrete k T1 T2 lam zeta0 u v) +
                                         (W_concrete k T1 T2 lam zeta0)ᵀ * Lr * (W_concrete k T1 T2 lam zeta0)))
    (C_cross : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hC_cross : C_cross = kappa • (outerProd (fun _ => 1) (fun _ => 1)) + (Winv_concrete k T1 T2 lam zeta0)ᵀ * Fres * (WE_inv_concrete k T1 T2 lam zeta0 u v)) :
    eta • ((WE_concrete k T1 T2 lam zeta0 u v)ᵀ * Lr * (WE_concrete k T1 T2 lam zeta0 u v) +
           (W_concrete k T1 T2 lam zeta0)ᵀ * Lr * (W_concrete k T1 T2 lam zeta0)) +
    (W_concrete k T1 T2 lam zeta0)ᵀ * C_cross * (WE_concrete k T1 T2 lam zeta0 u v) = E := by
  apply M_transpose_mul_J_mul_M_concrete k T1 T2 lam hT1 hT2 hlam zeta0 hzeta u v hdenom eta kappa Lr E E_base Fres hFres C_cross hC_cross
  subst hu hv hkappa hE_base
  exact W_concrete_transpose_mul_one_mul_WE_concrete k T1 T2 lam hT1 hlam zeta0 ell_Delta

#print axioms Karlin.M_transpose_mul_J_mul_M_fully_concrete


/-!
## Part 9: Section 5.2 & Section 6.1 Concrete Change-of-Basis $S_w, S_w^{-1}$ and Unconditional Binomial Cokernel Basis $Z^{(h)}$
-/

/-- Weak upper-triangular vanishing of $e^{N_0} - I_w$. -/
theorem expN0_one_sub_one_eq_zero_of_le {w : ℕ} {i j : Fin w} (h : i.val ≤ j.val) :
    (expN0 w 1 - 1) i j = 0 := by
  simp only [Matrix.sub_apply]
  by_cases hij : i = j
  · subst hij
    rw [expN0_apply_self, Matrix.one_apply_eq, sub_self]
  · have hlt : i.val < j.val := lt_of_le_of_ne h (fun hval => hij (Fin.ext hval))
    rw [expN0_apply_of_lt 1 hlt, Matrix.one_apply_ne hij, sub_zero]

#print axioms Karlin.expN0_one_sub_one_eq_zero_of_le

/-- First subdiagonal unit values of $e^{N_0} - I_w$. -/
theorem expN0_one_sub_one_subdiag {w : ℕ} {i j : Fin w} (h : i.val = j.val + 1) :
    (expN0 w 1 - 1) i j = 1 := by
  simp only [Matrix.sub_apply]
  have hne : i ≠ j := by
    intro heq
    have : i.val = j.val := congr_arg Fin.val heq
    omega
  rw [Matrix.one_apply_ne hne, sub_zero]
  dsimp [expN0]
  have hle : j.val ≤ i.val := by omega
  rw [if_pos hle]
  have hdiff : i.val - j.val = 1 := by omega
  rw [hdiff]
  simp

#print axioms Karlin.expN0_one_sub_one_subdiag

/-- Any strictly lower-triangular matrix satisfies $(L^p)_{i,j} = 0$ for $i < j + p$. -/
theorem strictly_lower_tri_pow_eq_zero_of_lt {w : ℕ} (L : Matrix (Fin w) (Fin w) ℚ)
    (hL : ∀ i j : Fin w, i.val ≤ j.val → L i j = 0)
    (p : ℕ) (i j : Fin w) (h : i.val < j.val + p) :
    (L ^ p) i j = 0 := by
  induction p generalizing i j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    have : i ≠ j := by
      intro heq
      have : i.val = j.val := congr_arg Fin.val heq
      omega
    rw [if_neg this]
  | succ p ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x.val ≤ j.val
    · rw [hL x j hx, mul_zero]
    · have hx_gt : j.val < x.val := not_le.mp hx
      have h_lt : i.val < x.val + p := by omega
      rw [ih i x h_lt, zero_mul]

#print axioms Karlin.strictly_lower_tri_pow_eq_zero_of_lt

/-- Nilpotency of strictly lower-triangular matrices: $L^w = 0$. -/
theorem strictly_lower_tri_pow_eq_zero {w : ℕ} (L : Matrix (Fin w) (Fin w) ℚ)
    (hL : ∀ i j : Fin w, i.val ≤ j.val → L i j = 0) :
    L ^ w = 0 := by
  ext i j
  apply strictly_lower_tri_pow_eq_zero_of_lt L hL w i j
  have : i.val < w := i.isLt
  omega

#print axioms Karlin.strictly_lower_tri_pow_eq_zero

/-- Unit subdiagonal values for powers of strictly lower-triangular matrices with unit subdiagonal. -/
theorem subdiag_one_pow_apply {w : ℕ} (L : Matrix (Fin w) (Fin w) ℚ)
    (hL_le : ∀ i j : Fin w, i.val ≤ j.val → L i j = 0)
    (hL_sub : ∀ i j : Fin w, i.val = j.val + 1 → L i j = 1)
    (p : ℕ) (i j : Fin w) (h : i.val = j.val + p) :
    (L ^ p) i j = 1 := by
  induction p generalizing i j with
  | zero =>
    have heq : i = j := Fin.ext (by omega)
    simp only [pow_zero, Matrix.one_apply, if_pos heq]
  | succ p ih =>
    rw [pow_succ, Matrix.mul_apply]
    by_cases hj1 : j.val + 1 < w
    · let x0 : Fin w := ⟨j.val + 1, hj1⟩
      have hx0_sub : x0.val = j.val + 1 := rfl
      have hx0_pow : i.val = x0.val + p := by omega
      have hx0_term : (L ^ p) i x0 * L x0 j = 1 := by
        rw [ih i x0 hx0_pow, hL_sub x0 j hx0_sub, mul_one]
      have h_other : ∀ x : Fin w, x ≠ x0 → (L ^ p) i x * L x j = 0 := by
        intro x hne
        by_cases hx_le : x.val ≤ j.val
        · rw [hL_le x j hx_le, mul_zero]
        · have hx_gt : j.val + 1 < x.val := by
            have : j.val < x.val := not_le.mp hx_le
            have : x.val ≠ j.val + 1 := fun h => hne (Fin.ext h)
            omega
          have : i.val < x.val + p := by omega
          rw [strictly_lower_tri_pow_eq_zero_of_lt L hL_le p i x this, zero_mul]
      have h_sum : (∑ x : Fin w, (L ^ p) i x * L x j) =
          ∑ x : Fin w, if x = x0 then (1 : ℚ) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = x0
        · subst hx; rw [if_pos rfl, hx0_term]
        · rw [if_neg hx, h_other x hx]
      rw [h_sum, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    · have : i.val ≥ w := by omega
      have : i.val < w := i.isLt
      omega

#print axioms Karlin.subdiag_one_pow_apply

/-- Concrete change-of-basis inverse matrix $S_w^{-1}$ with columns $(e^{N_0} - I)^j e_0$. -/
def S_inv_mat (w : ℕ) : Matrix (Fin w) (Fin w) ℚ :=
  Matrix.of fun i j =>
    if h0 : 0 < w then ((expN0 w 1 - 1) ^ j.val) i ⟨0, h0⟩ else 0

/-- Lower-triangular vanishing of $S_w^{-1}$. -/
theorem S_inv_mat_eq_zero_of_lt {w : ℕ} {i j : Fin w} (h : i.val < j.val) :
    S_inv_mat w i j = 0 := by
  dsimp [S_inv_mat]
  split_ifs with h0
  · apply strictly_lower_tri_pow_eq_zero_of_lt (expN0 w 1 - 1)
      (fun a b hab => expN0_one_sub_one_eq_zero_of_le hab)
    change i.val < 0 + j.val
    omega
  · rfl

#print axioms Karlin.S_inv_mat_eq_zero_of_lt

/-- Unit diagonal entries of $S_w^{-1}$. -/
theorem S_inv_mat_diag_eq_one {w : ℕ} (i : Fin w) :
    S_inv_mat w i i = 1 := by
  dsimp [S_inv_mat]
  have h0 : 0 < w := by
    have : i.val < w := i.isLt
    omega
  rw [dif_pos h0]
  apply subdiag_one_pow_apply (expN0 w 1 - 1)
    (fun a b hab => expN0_one_sub_one_eq_zero_of_le hab)
    (fun a b hab => expN0_one_sub_one_subdiag hab)
    i.val i ⟨0, h0⟩
  change i.val = 0 + i.val
  omega

#print axioms Karlin.S_inv_mat_diag_eq_one

/-- First column of $S_w^{-1}$ is $e_0$. -/
theorem S_inv_mat_col_zero {w : ℕ} (h0 : 0 < w) (i : Fin w) :
    S_inv_mat w i ⟨0, h0⟩ = if i.val = 0 then 1 else 0 := by
  dsimp [S_inv_mat]
  rw [dif_pos h0]
  have h_pow : ((expN0 w 1 - 1) ^ (0 : ℕ)) = 1 := pow_zero _
  have h_app : ((expN0 w 1 - 1) ^ (0 : ℕ)) i ⟨0, h0⟩ = (1 : Matrix (Fin w) (Fin w) ℚ) i ⟨0, h0⟩ := by
    rw [h_pow]
  rw [h_app, Matrix.one_apply]
  by_cases hi : i.val = 0
  · have : i = ⟨0, h0⟩ := Fin.ext hi
    rw [if_pos this, if_pos hi]
  · have : i ≠ ⟨0, h0⟩ := fun h => hi (congr_arg Fin.val h)
    rw [if_neg this, if_neg hi]

#print axioms Karlin.S_inv_mat_col_zero

/-- First row of $S_w^{-1}$ is $e_0^	op$. -/
theorem S_inv_mat_row_zero {w : ℕ} (h0 : 0 < w) (j : Fin w) :
    S_inv_mat w ⟨0, h0⟩ j = if j.val = 0 then 1 else 0 := by
  by_cases hj : j.val = 0
  · have : j = ⟨0, h0⟩ := Fin.ext hj
    subst this
    rw [if_pos rfl, S_inv_mat_diag_eq_one]
  · have hlt : (⟨0, h0⟩ : Fin w).val < j.val := by
      change 0 < j.val
      omega
    rw [if_neg hj, S_inv_mat_eq_zero_of_lt hlt]

#print axioms Karlin.S_inv_mat_row_zero

/-- Intertwining relation $(e^{N_0} - I) S_w^{-1} = S_w^{-1} N_w$. -/
theorem expN0_one_sub_one_mul_S_inv_mat (w : ℕ) :
    (expN0 w 1 - 1) * S_inv_mat w = S_inv_mat w * N_mat w := by
  by_cases h0 : w = 0
  · subst h0
    ext i
    exact isEmptyElim i
  have hw_pos : 0 < w := Nat.pos_of_ne_zero h0
  ext i j
  rw [mul_N_mat_apply, Matrix.mul_apply]
  have hS : ∀ x : Fin w, S_inv_mat w x j = ((expN0 w 1 - 1) ^ j.val) x ⟨0, hw_pos⟩ := by
    intro x
    dsimp [S_inv_mat]
    rw [dif_pos hw_pos]
  have hsum : (∑ x : Fin w, (expN0 w 1 - 1) i x * S_inv_mat w x j) =
      ((expN0 w 1 - 1) ^ (j.val + 1)) i ⟨0, hw_pos⟩ := by
    simp_rw [hS]
    have : ((expN0 w 1 - 1) ^ (j.val + 1)) = (expN0 w 1 - 1) * ((expN0 w 1 - 1) ^ j.val) := pow_succ' _ _
    rw [this, Matrix.mul_apply]
  rw [hsum]
  split_ifs with hd
  · dsimp [S_inv_mat]
    rw [dif_pos hw_pos]
  · have hj_last : j.val + 1 = w := by
      have : j.val < w := j.isLt
      omega
    rw [hj_last]
    have hnil := strictly_lower_tri_pow_eq_zero (expN0 w 1 - 1)
      (fun a b hab => expN0_one_sub_one_eq_zero_of_le hab)
    rw [hnil, Matrix.zero_apply]

#print axioms Karlin.expN0_one_sub_one_mul_S_inv_mat

/-- Shift intertwining $e^{N_0} S_w^{-1} = S_w^{-1} T_w$. -/
theorem expN0_one_mul_S_inv_mat (w : ℕ) :
    expN0 w 1 * S_inv_mat w = S_inv_mat w * T_mat w := by
  have hM : expN0 w 1 = (expN0 w 1 - 1) + 1 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]
    abel
  have hT : T_mat w = N_mat w + 1 := by
    dsimp [T_mat]
    ext i j
    simp only [Matrix.add_apply, Matrix.one_apply]
    ring
  rw [hM, hT]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  rw [expN0_one_sub_one_mul_S_inv_mat]

#print axioms Karlin.expN0_one_mul_S_inv_mat

/-- Strict lower triangularity of $S_w^{-1} - I$. -/
theorem S_inv_mat_sub_one_strictly_lower_tri {w : ℕ} (i j : Fin w) (h : i.val ≤ j.val) :
    (S_inv_mat w - 1) i j = 0 := by
  simp only [Matrix.sub_apply]
  by_cases hij : i = j
  · subst hij
    rw [S_inv_mat_diag_eq_one, Matrix.one_apply_eq, sub_self]
  · have hlt : i.val < j.val := lt_of_le_of_ne h (fun hval => hij (Fin.ext hval))
    rw [S_inv_mat_eq_zero_of_lt hlt, Matrix.one_apply_ne hij, sub_zero]

#print axioms Karlin.S_inv_mat_sub_one_strictly_lower_tri

/-- Concrete change-of-basis matrix $S_w = \sum_{p < w} (-1)^p (S_w^{-1} - 1)^p$. -/
def S_mat (w : ℕ) : Matrix (Fin w) (Fin w) ℚ :=
  ∑ p ∈ Finset.range w, (-1 : ℚ) ^ p • (S_inv_mat w - 1) ^ p

/-- Left inverse $S_w^{-1} S_w = I_w$. -/
theorem S_inv_mat_mul_S_mat (w : ℕ) :
    S_inv_mat w * S_mat w = 1 := by
  set A := S_inv_mat w - 1
  have hA_nil : A ^ w = 0 := strictly_lower_tri_pow_eq_zero A
    (fun a b hab => S_inv_mat_sub_one_strictly_lower_tri a b hab)
  have hS_inv : S_inv_mat w = 1 + A := by
    dsimp [A]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]
    abel
  rw [hS_inv]
  dsimp [S_mat, A]
  rw [Matrix.add_mul, Matrix.one_mul]
  rw [Matrix.mul_sum]
  have h_term : ∀ p, (S_inv_mat w - 1) * ((-1 : ℚ) ^ p • (S_inv_mat w - 1) ^ p) =
      - (((-1 : ℚ) ^ (p + 1)) • (S_inv_mat w - 1) ^ (p + 1)) := by
    intro p
    rw [Matrix.mul_smul, ← pow_succ' (S_inv_mat w - 1) p]
    have : (-1 : ℚ) ^ (p + 1) = - ((-1 : ℚ) ^ p) := by
      rw [pow_succ]
      ring
    rw [this, neg_smul, neg_neg]
  have h_sum2 : (∑ p ∈ Finset.range w, (S_inv_mat w - 1) * ((-1 : ℚ) ^ p • (S_inv_mat w - 1) ^ p)) =
      ∑ p ∈ Finset.range w, - (((-1 : ℚ) ^ (p + 1)) • (S_inv_mat w - 1) ^ (p + 1)) := by
    apply Finset.sum_congr rfl
    intro p _
    exact h_term p
  rw [h_sum2, ← Finset.sum_add_distrib]
  simp only [← sub_eq_add_neg]
  rw [Finset.sum_range_sub' (fun p => (-1 : ℚ) ^ p • (S_inv_mat w - 1) ^ p)]
  have h_pow0 : ((S_inv_mat w - 1) ^ (0 : ℕ)) = 1 := pow_zero _
  rw [pow_zero, h_pow0, one_smul, hA_nil, smul_zero, sub_zero]

#print axioms Karlin.S_inv_mat_mul_S_mat

/-- Right inverse $S_w S_w^{-1} = I_w$. -/
theorem S_mat_mul_S_inv_mat (w : ℕ) :
    S_mat w * S_inv_mat w = 1 := by
  rw [mul_eq_one_comm]
  exact S_inv_mat_mul_S_mat w

#print axioms Karlin.S_mat_mul_S_inv_mat

/-- Lower-triangular vanishing of $S_w$. -/
theorem S_mat_eq_zero_of_lt {w : ℕ} {i j : Fin w} (h : i.val < j.val) :
    S_mat w i j = 0 := by
  dsimp [S_mat]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro p _
  have hlt : i.val < j.val + p := by omega
  have := strictly_lower_tri_pow_eq_zero_of_lt (S_inv_mat w - 1)
    (fun a b hab => S_inv_mat_sub_one_strictly_lower_tri a b hab) p i j hlt
  rw [this, mul_zero]

#print axioms Karlin.S_mat_eq_zero_of_lt

/-- Unit diagonal entries of $S_w$. -/
theorem S_mat_diag_eq_one {w : ℕ} (i : Fin w) :
    S_mat w i i = 1 := by
  dsimp [S_mat]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hw_pos : 0 < w := i.isLt.trans_le' (Nat.zero_le _)
  have h_range : Finset.range w = insert 0 (Finset.Ico 1 w) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [h_range, Finset.sum_insert]
  · have h_pow0 : ((S_inv_mat w - 1) ^ (0 : ℕ)) = 1 := pow_zero _
    have h0 : (-1 : ℚ) ^ 0 * (((S_inv_mat w - 1) ^ (0 : ℕ) : Matrix (Fin w) (Fin w) ℚ) i i) = 1 := by
      rw [h_pow0, Matrix.one_apply_eq]
      simp
    have h_rest : (∑ p ∈ Finset.Ico 1 w, (-1 : ℚ) ^ p * (((S_inv_mat w - 1) ^ p) i i)) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have hp1 : 1 ≤ p := (Finset.mem_Ico.mp hp).1
      have hlt : i.val < i.val + p := by omega
      have := strictly_lower_tri_pow_eq_zero_of_lt (S_inv_mat w - 1)
        (fun a b hab => S_inv_mat_sub_one_strictly_lower_tri a b hab) p i i hlt
      rw [this, mul_zero]
    rw [h0, h_rest, add_zero]
  · simp

#print axioms Karlin.S_mat_diag_eq_one

/-- Intertwining relation $T_w S_w = S_w e^{N_0}$. -/
theorem T_mat_mul_S_mat (w : ℕ) :
    T_mat w * S_mat w = S_mat w * expN0 w 1 := by
  have h1 : S_mat w * (expN0 w 1 * S_inv_mat w) = T_mat w := by
    calc S_mat w * (expN0 w 1 * S_inv_mat w)
      _ = S_mat w * (S_inv_mat w * T_mat w) := by rw [expN0_one_mul_S_inv_mat]
      _ = (S_mat w * S_inv_mat w) * T_mat w := by rw [Matrix.mul_assoc]
      _ = 1 * T_mat w := by rw [S_mat_mul_S_inv_mat]
      _ = T_mat w := by rw [Matrix.one_mul]
  have h2 : (S_mat w * (expN0 w 1 * S_inv_mat w)) * S_mat w = S_mat w * expN0 w 1 := by
    calc (S_mat w * (expN0 w 1 * S_inv_mat w)) * S_mat w
      _ = S_mat w * expN0 w 1 * (S_inv_mat w * S_mat w) := by simp only [Matrix.mul_assoc]
      _ = S_mat w * expN0 w 1 * 1 := by rw [S_inv_mat_mul_S_mat]
      _ = S_mat w * expN0 w 1 := by rw [Matrix.mul_one]
  rw [h1] at h2
  exact h2

#print axioms Karlin.T_mat_mul_S_mat

/-- **Unconditional Intertwining Relation ($B_w S_w = S_w e^{-N_0}$)**:
    Holds unconditionally for every width $w$ with ZERO matrix hypotheses. -/
theorem B_mat_mul_S_mat (w : ℕ) :
    B_mat w * S_mat w = S_mat w * expN0 w (-1) := by
  have hBT : B_mat w * T_mat w = 1 := by
    change B_mat w * (1 + N_mat w) = 1
    exact B_mat_mul_one_add_N w
  have h1 : S_mat w = B_mat w * S_mat w * expN0 w 1 := by
    calc S_mat w
      _ = 1 * S_mat w := by rw [Matrix.one_mul]
      _ = (B_mat w * T_mat w) * S_mat w := by rw [← hBT]
      _ = B_mat w * (T_mat w * S_mat w) := by rw [Matrix.mul_assoc]
      _ = B_mat w * (S_mat w * expN0 w 1) := by rw [T_mat_mul_S_mat]
      _ = B_mat w * S_mat w * expN0 w 1 := by rw [Matrix.mul_assoc]
  have h_assoc : B_mat w * S_mat w * (expN0 w 1 * expN0 w (-1)) = (B_mat w * S_mat w * expN0 w 1) * expN0 w (-1) := by
    simp only [Matrix.mul_assoc]
  calc B_mat w * S_mat w
    _ = B_mat w * S_mat w * 1 := by rw [Matrix.mul_one]
    _ = B_mat w * S_mat w * (expN0 w 1 * expN0 w (-1)) := by rw [expN0_mul_neg_cancel w 1]
    _ = (B_mat w * S_mat w * expN0 w 1) * expN0 w (-1) := h_assoc
    _ = S_mat w * expN0 w (-1) := by rw [← h1]

#print axioms Karlin.B_mat_mul_S_mat

/-- Divided power basis vector $e_q(i) = q^i / i!$. -/
def divPowerBasis (w : ℕ) (q : ℕ) : Fin w → ℚ :=
  fun i => (q : ℚ) ^ i.val / (Nat.factorial i.val : ℚ)

/-- Step equation for divided power basis: $e_{q+1} = e^{N_0} e_q$. -/
theorem divPowerBasis_succ (w : ℕ) (q : ℕ) :
    divPowerBasis w (q + 1) = (expN0 w 1).mulVec (divPowerBasis w q) := by
  by_cases h0 : w = 0
  · subst h0
    ext i
    exact isEmptyElim i
  · have hw_pos : 0 < w := Nat.pos_of_ne_zero h0
    ext i
    have h_col : divPowerBasis w q = fun j => expN0 w (q : ℚ) j ⟨0, hw_pos⟩ := by
      ext j
      dsimp [divPowerBasis, expN0]
    have h_col_succ : divPowerBasis w (q + 1) = fun j => expN0 w ((q + 1 : ℕ) : ℚ) j ⟨0, hw_pos⟩ := by
      ext j
      dsimp [divPowerBasis, expN0]
    rw [h_col_succ, h_col]
    have h_mul : (expN0 w 1).mulVec (fun j => expN0 w (q : ℚ) j ⟨0, hw_pos⟩) i =
        (expN0 w 1 * expN0 w (q : ℚ)) i ⟨0, hw_pos⟩ := by
      simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [h_mul, expN0_mul_expN0]
    have h_scalar : (1 : ℚ) + (q : ℚ) = ((q + 1 : ℕ) : ℚ) := by
      push_cast
      ring
    rw [h_scalar]

#print axioms Karlin.divPowerBasis_succ

/-- **Change-of-Basis Maps Divided Powers to Binomial Basis ($S_w e_q = p(q)$)**:
    For all widths $w$ and phase indices $q \in \mathbb{N}$, $S_w (q^i / i!) = \binom{q}{i}$. -/
theorem S_mat_mulVec_divPowerBasis (w : ℕ) (q : ℕ) :
    (S_mat w).mulVec (divPowerBasis w q) = binomBasis w q := by
  induction q with
  | zero =>
    ext i
    by_cases h0 : w = 0
    · subst h0
      exact isEmptyElim i
    have hw_pos : 0 < w := Nat.pos_of_ne_zero h0
    have h_div0 : divPowerBasis w 0 = fun j => if j.val = 0 then 1 else 0 := by
      ext j
      dsimp [divPowerBasis]
      by_cases hj : j.val = 0
      · rw [if_pos hj, hj]
        simp
      · rw [if_neg hj]
        have : (0 : ℚ) ^ j.val = 0 := zero_pow hj
        rw [this, zero_div]
    have h_binom0 : binomBasis w 0 = fun j => if j.val = 0 then 1 else 0 := by
      ext j
      dsimp [binomBasis]
      by_cases hj : j.val = 0
      · rw [if_pos hj, hj]
        simp
      · rw [if_neg hj]
        have : Nat.choose 0 j.val = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [this, Nat.cast_zero]
    have h_col0 : (fun j => if j.val = 0 then (1 : ℚ) else 0) = fun j => S_inv_mat w j ⟨0, hw_pos⟩ := by
      ext j
      rw [S_inv_mat_col_zero hw_pos j]
    calc ((S_mat w).mulVec (divPowerBasis w 0)) i
      _ = ((S_mat w).mulVec (fun j => S_inv_mat w j ⟨0, hw_pos⟩)) i := by
        congr 1
        rw [h_div0, h_col0]
      _ = (S_mat w * S_inv_mat w) i ⟨0, hw_pos⟩ := by
        simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      _ = (1 : Matrix (Fin w) (Fin w) ℚ) i ⟨0, hw_pos⟩ := by rw [S_mat_mul_S_inv_mat]
      _ = if i.val = 0 then 1 else 0 := by
        rw [Matrix.one_apply]
        by_cases hi : i.val = 0
        · have : i = ⟨0, hw_pos⟩ := Fin.ext hi
          rw [if_pos this, if_pos hi]
        · have : i ≠ ⟨0, hw_pos⟩ := fun h => hi (congr_arg Fin.val h)
          rw [if_neg this, if_neg hi]
      _ = binomBasis w 0 i := by
        rw [h_binom0]
  | succ q ih =>
    rw [divPowerBasis_succ]
    rw [Matrix.mulVec_mulVec]
    rw [← T_mat_mul_S_mat]
    rw [← Matrix.mulVec_mulVec]
    rw [ih]
    exact (binomBasis_succ w q).symm

#print axioms Karlin.S_mat_mulVec_divPowerBasis

/-- Concrete binomial cokernel basis matrix $Z^{(h)} = Z_{\mathrm{binom}}(S_w, h)$. -/
def Z_binom_concrete (w h : ℕ) : Matrix (Fin w) (Fin w) ℚ :=
  Z_binom (S_mat w) h

/-- **Unconditional Binomial Adjoint Kernel Membership (Section 6.1)**:
    Every even-degree concrete binomial matrix satisfies $\mathcal{L}^*(Z^{(h)}) = 0$
    with ZERO uninstantiated matrix hypotheses. -/
theorem Z_binom_concrete_in_adjoint_kernel (w h : ℕ) (hh_ge : w ≤ h + 1) (hh : Even h) :
    L_adjoint (B_mat w) (Z_binom_concrete w h) = 0 := by
  apply Z_binom_in_adjoint_kernel hh_ge hh (B_mat w) (S_mat w) (B_mat_mul_S_mat w)

#print axioms Karlin.Z_binom_concrete_in_adjoint_kernel


/-!
## Part 10: Section 5.1 Bundle Transfer Matrices $E_\tau, E_{2\tau}, F_\tau$ & Lemma 5.3 Top-Column Cancellation
-/

/-- Polynomial scaling diagonal matrix $\mathrm{diag}(1, \tau, \tau^2, \dots, \tau^{w-1})$. -/
def scaleDiag (w : ℕ) (τ : ℕ) : Matrix (Fin w) (Fin w) ℚ :=
  Matrix.diagonal fun i => (τ : ℚ) ^ i.val

/-- Action of scaling matrix on divided powers: $\mathrm{scaleDiag}(\tau) e_q = e_{\tau q}$. -/
theorem scaleDiag_mulVec (w : ℕ) (τ q : ℕ) :
    (scaleDiag w τ).mulVec (divPowerBasis w q) = divPowerBasis w (τ * q) := by
  ext i
  dsimp [scaleDiag, divPowerBasis, Matrix.mulVec, dotProduct]
  have h_term : ∀ j : Fin w, (Matrix.diagonal (fun (i : Fin w) => (τ : ℚ) ^ i.val)) i j *
      ((q : ℚ) ^ j.val / (Nat.factorial j.val : ℚ)) =
      if j = i then (τ : ℚ) ^ i.val * ((q : ℚ) ^ i.val / (Nat.factorial i.val : ℚ)) else 0 := by
    intro j
    rw [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl]
    · have hji : j ≠ i := fun h => hij h.symm
      rw [if_neg hij, if_neg hji, zero_mul]
  rw [Finset.sum_congr rfl (fun j _ => h_term j), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  push_cast
  rw [mul_pow]
  ring

#print axioms Karlin.scaleDiag_mulVec

/-- Lower-triangular vanishing of scaleDiag. -/
theorem scaleDiag_eq_zero_of_lt {w : ℕ} (τ : ℕ) {i j : Fin w} (h : i.val < j.val) :
    scaleDiag w τ i j = 0 := by
  dsimp [scaleDiag]
  rw [Matrix.diagonal_apply]
  have : i ≠ j := fun heq => by
    have := congr_arg Fin.val heq
    omega
  rw [if_neg this]

#print axioms Karlin.scaleDiag_eq_zero_of_lt

/-- Conjugated polynomial bundle transfer matrix $\widetilde{E}_\tau = S_w \mathrm{scaleDiag}(\tau) S_w^{-1}$. -/
def E_tilde (w : ℕ) (τ : ℕ) : Matrix (Fin w) (Fin w) ℚ :=
  S_mat w * scaleDiag w τ * S_inv_mat w

/-- Lower-triangular matrix product is lower triangular. -/
theorem lower_tri_mul {w : ℕ} (A B : Matrix (Fin w) (Fin w) ℚ)
    (hA : ∀ i j : Fin w, i.val < j.val → A i j = 0)
    (hB : ∀ i j : Fin w, i.val < j.val → B i j = 0) :
    ∀ i j : Fin w, i.val < j.val → (A * B) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : i.val < x.val
  · rw [hA i x hx, zero_mul]
  · have : x.val < j.val := by omega
    rw [hB x j this, mul_zero]

#print axioms Karlin.lower_tri_mul

/-- Diagonal of lower-triangular matrix product. -/
theorem lower_tri_mul_diag {w : ℕ} (A B : Matrix (Fin w) (Fin w) ℚ)
    (hA : ∀ i j : Fin w, i.val < j.val → A i j = 0)
    (hB : ∀ i j : Fin w, i.val < j.val → B i j = 0) :
    ∀ i : Fin w, (A * B) i i = A i i * B i i := by
  intro i
  rw [Matrix.mul_apply]
  have h_single : ∀ x : Fin w, A i x * B x i = if x = i then A i i * B i i else 0 := by
    intro x
    by_cases hx : x = i
    · subst hx; rw [if_pos rfl]
    · rw [if_neg hx]
      by_cases hxi : i.val < x.val
      · rw [hA i x hxi, zero_mul]
      · have : x.val < i.val := lt_of_le_of_ne (not_lt.mp hxi) (fun heq => hx (Fin.ext heq))
        rw [hB x i this, mul_zero]
  rw [Finset.sum_congr rfl (fun x _ => h_single x), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

#print axioms Karlin.lower_tri_mul_diag

/-- Lower-triangular vanishing of $\widetilde{E}_\tau$. -/
theorem E_tilde_eq_zero_of_lt {w : ℕ} (τ : ℕ) {i j : Fin w} (h : i.val < j.val) :
    E_tilde w τ i j = 0 := by
  dsimp [E_tilde]
  have h1 : ∀ a b : Fin w, a.val < b.val → (S_mat w * scaleDiag w τ) a b = 0 := by
    apply lower_tri_mul (S_mat w) (scaleDiag w τ)
    · intro a b hab; exact S_mat_eq_zero_of_lt hab
    · intro a b hab; exact scaleDiag_eq_zero_of_lt τ hab
  have h2 : ∀ a b : Fin w, a.val < b.val → (S_mat w * scaleDiag w τ * S_inv_mat w) a b = 0 := by
    apply lower_tri_mul (S_mat w * scaleDiag w τ) (S_inv_mat w)
    · exact h1
    · intro a b hab; exact S_inv_mat_eq_zero_of_lt hab
  exact h2 i j h

#print axioms Karlin.E_tilde_eq_zero_of_lt

/-- Diagonal entries of $\widetilde{E}_\tau$: $(\widetilde{E}_\tau)_{i,i} = \tau^i$. -/
theorem E_tilde_diag (w : ℕ) (τ : ℕ) (i : Fin w) :
    E_tilde w τ i i = (τ : ℚ) ^ i.val := by
  dsimp [E_tilde]
  have h1_lt : ∀ a b : Fin w, a.val < b.val → (S_mat w * scaleDiag w τ) a b = 0 := by
    apply lower_tri_mul (S_mat w) (scaleDiag w τ)
    · intro a b hab; exact S_mat_eq_zero_of_lt hab
    · intro a b hab; exact scaleDiag_eq_zero_of_lt τ hab
  have h_diag2 := lower_tri_mul_diag (S_mat w * scaleDiag w τ) (S_inv_mat w) h1_lt
    (fun a b hab => S_inv_mat_eq_zero_of_lt hab) i
  have h_diag1 := lower_tri_mul_diag (S_mat w) (scaleDiag w τ)
    (fun a b hab => S_mat_eq_zero_of_lt hab)
    (fun a b hab => scaleDiag_eq_zero_of_lt τ hab) i
  rw [h_diag2, h_diag1, S_mat_diag_eq_one, S_inv_mat_diag_eq_one]
  dsimp [scaleDiag]
  rw [Matrix.diagonal_apply_eq]
  ring

#print axioms Karlin.E_tilde_diag

/-- Action of $\widetilde{E}_\tau$ on binomial basis: $\widetilde{E}_\tau p(q) = p(\tau q)$. -/
theorem E_tilde_mulVec_binomBasis (w τ q : ℕ) :
    (E_tilde w τ).mulVec (binomBasis w q) = binomBasis w (τ * q) := by
  dsimp [E_tilde]
  rw [Matrix.mul_assoc]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hS_inv : (S_inv_mat w).mulVec (binomBasis w q) = divPowerBasis w q := by
    calc (S_inv_mat w).mulVec (binomBasis w q)
      _ = (S_inv_mat w).mulVec ((S_mat w).mulVec (divPowerBasis w q)) := by
        rw [S_mat_mulVec_divPowerBasis]
      _ = (S_inv_mat w * S_mat w).mulVec (divPowerBasis w q) := by
        rw [Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin w) (Fin w) ℚ).mulVec (divPowerBasis w q) := by
        rw [S_inv_mat_mul_S_mat]
      _ = divPowerBasis w q := by
        simp only [Matrix.one_mulVec]
  rw [hS_inv]
  rw [scaleDiag_mulVec]
  exact S_mat_mulVec_divPowerBasis w (τ * q)

#print axioms Karlin.E_tilde_mulVec_binomBasis

/-- Truncated bundle transfer matrix $E_\tau \in \mathbb{Q}^{k \times (k+1)}$ from Section 5.1 (`eq:maps`). -/
def E_tau_mat (k τ : ℕ) : Matrix (Fin k) (Fin (k + 1)) ℚ :=
  Matrix.of fun i j => E_tilde (k + 1) τ ⟨i.val, by omega⟩ j

/-- Truncated bundle transfer matrix $E_{2\tau} = E_\tau(2\tau)$. -/
def E_2tau_mat (k τ : ℕ) : Matrix (Fin k) (Fin (k + 1)) ℚ :=
  E_tau_mat k (2 * τ)

/-- Bundle difference matrix $F_\tau \in \mathbb{Q}^{k \times (k+1)}$ from Section 5.1 (`eq:maps`). -/
def F_tau_mat (k τ : ℕ) : Matrix (Fin k) (Fin (k + 1)) ℚ :=
  Matrix.of fun i j =>
    E_tilde (k + 1) (2 * τ) ⟨i.val + 1, by omega⟩ j -
    E_tilde (k + 1) τ ⟨i.val + 1, by omega⟩ j

/-- Action of $E_\tau$ on binomial basis: $E_\tau p_k(q) = p_{k-1}(\tau q)$. -/
theorem E_tau_mat_mulVec_binomBasis (k τ q : ℕ) :
    (E_tau_mat k τ).mulVec (binomBasis (k + 1) q) = binomBasis k (τ * q) := by
  ext i
  dsimp [E_tau_mat, Matrix.mulVec, dotProduct, Matrix.of_apply]
  have hE := congr_fun (E_tilde_mulVec_binomBasis (k + 1) τ q) ⟨i.val, by omega⟩
  dsimp [Matrix.mulVec, dotProduct] at hE
  exact hE

#print axioms Karlin.E_tau_mat_mulVec_binomBasis

/-- Action of $E_{2\tau}$ on binomial basis: $E_{2\tau} p_k(q) = p_{k-1}(2\tau q)$. -/
theorem E_2tau_mat_mulVec_binomBasis (k τ q : ℕ) :
    (E_2tau_mat k τ).mulVec (binomBasis (k + 1) q) = binomBasis k (2 * τ * q) := by
  dsimp [E_2tau_mat]
  exact E_tau_mat_mulVec_binomBasis k (2 * τ) q

#print axioms Karlin.E_2tau_mat_mulVec_binomBasis

/-- Projection of $N_{k+1}$ multiplication onto row $i+1$: $(N_{k+1} p_k(\sigma))_{i+1} = p_{k-1}(\sigma)_i$. -/
theorem N_mat_mulVec_binomBasis_succ (k : ℕ) (σ : ℕ) (i : Fin k) :
    (N_mat (k + 1)).mulVec (binomBasis (k + 1) σ) ⟨i.val + 1, by omega⟩ = binomBasis k σ i := by
  dsimp [Matrix.mulVec, dotProduct, N_mat, binomBasis]
  have h_term : ∀ j : Fin (k + 1), (if (i.val + 1) = j.val + 1 then (1 : ℚ) else 0) * (σ.choose j.val : ℚ) =
      if j = ⟨i.val, by omega⟩ then (σ.choose i.val : ℚ) else 0 := by
    intro j
    by_cases hj : j = ⟨i.val, by omega⟩
    · subst hj
      rw [if_pos rfl, if_pos rfl, one_mul]
    · have h_ne : (i.val + 1) ≠ j.val + 1 := by
        intro h
        have : j.val = i.val := by omega
        exact hj (Fin.ext this)
      rw [if_neg h_ne, if_neg hj, zero_mul]
  rw [Finset.sum_congr rfl (fun j _ => h_term j), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

#print axioms Karlin.N_mat_mulVec_binomBasis_succ

/-- **Action of $F_\tau$ on Binomial Basis (Lemma 5.3)**:
    $F_\tau p_k(q) = \sum_{\sigma = \tau q}^{2\tau q - 1} p_{k-1}(\sigma)$. -/
theorem F_tau_mat_mulVec_binomBasis (k τ q : ℕ) (i : Fin k) :
    ((F_tau_mat k τ).mulVec (binomBasis (k + 1) q)) i =
      ∑ σ ∈ Finset.Ico (τ * q) (2 * τ * q), binomBasis k σ i := by
  have h_left : ((F_tau_mat k τ).mulVec (binomBasis (k + 1) q)) i =
      binomBasis (k + 1) (2 * τ * q) ⟨i.val + 1, by omega⟩ -
      binomBasis (k + 1) (τ * q) ⟨i.val + 1, by omega⟩ := by
    dsimp [F_tau_mat, Matrix.mulVec, dotProduct, Matrix.of_apply]
    have h_sub : (∑ j : Fin (k + 1),
        (E_tilde (k + 1) (2 * τ) ⟨i.val + 1, by omega⟩ j - E_tilde (k + 1) τ ⟨i.val + 1, by omega⟩ j) *
        binomBasis (k + 1) q j) =
        (∑ j : Fin (k + 1), E_tilde (k + 1) (2 * τ) ⟨i.val + 1, by omega⟩ j * binomBasis (k + 1) q j) -
        (∑ j : Fin (k + 1), E_tilde (k + 1) τ ⟨i.val + 1, by omega⟩ j * binomBasis (k + 1) q j) := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
    rw [h_sub]
    have h1 := congr_fun (E_tilde_mulVec_binomBasis (k + 1) (2 * τ) q) ⟨i.val + 1, by omega⟩
    have h2 := congr_fun (E_tilde_mulVec_binomBasis (k + 1) τ q) ⟨i.val + 1, by omega⟩
    dsimp [Matrix.mulVec, dotProduct] at h1 h2
    rw [h1, h2]
  rw [h_left]
  have h_le : τ * q ≤ 2 * τ * q := by nlinarith
  have h_sum := binomBasis_bundle_sum (k + 1) h_le ⟨i.val + 1, by omega⟩
  rw [← h_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact N_mat_mulVec_binomBasis_succ k σ i

#print axioms Karlin.F_tau_mat_mulVec_binomBasis

/-- **Lemma 5.3 Transfer Relation (Eq. (26) / `eq:maps`)**:
    $N_k F_\tau = E_{2\tau} - E_\tau$. -/
theorem N_mat_mul_F_tau_mat (k τ : ℕ) :
    N_mat k * F_tau_mat k τ = E_2tau_mat k τ - E_tau_mat k τ := by
  ext i j
  rw [N_mat_mul_apply]
  simp only [Matrix.sub_apply]
  dsimp [E_2tau_mat, E_tau_mat, F_tau_mat]
  split_ifs with hi
  · have h_val : i.val - 1 + 1 = i.val := by omega
    have heq : (⟨i.val - 1 + 1, by omega⟩ : Fin (k + 1)) = ⟨i.val, by omega⟩ := Fin.ext h_val
    rw [heq]
  · have hi0 : i.val = 0 := by omega
    have heq0 : (⟨i.val, by omega⟩ : Fin (k + 1)) = ⟨0, by omega⟩ := Fin.ext hi0
    rw [heq0]
    by_cases hj0 : j.val = 0
    · have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
      rw [hj_eq]
      have h1 := E_tilde_diag (k + 1) (2 * τ) ⟨0, by omega⟩
      have h2 := E_tilde_diag (k + 1) τ ⟨0, by omega⟩
      have h_val0 : (⟨0, by omega⟩ : Fin (k + 1)).val = 0 := rfl
      rw [h_val0] at h1 h2
      rw [pow_zero] at h1 h2
      change 0 = E_tilde (k + 1) (2 * τ) ⟨0, by omega⟩ ⟨0, by omega⟩ - E_tilde (k + 1) τ ⟨0, by omega⟩ ⟨0, by omega⟩
      rw [h1, h2, sub_self]
    · have hlt : (0 : ℕ) < j.val := by omega
      have h1 := E_tilde_eq_zero_of_lt (2 * τ) (show (⟨0, by omega⟩ : Fin (k + 1)).val < j.val by exact hlt)
      have h2 := E_tilde_eq_zero_of_lt τ (show (⟨0, by omega⟩ : Fin (k + 1)).val < j.val by exact hlt)
      rw [h1, h2, sub_zero]

#print axioms Karlin.N_mat_mul_F_tau_mat

/-- **Lemma 5.3 Top-Column Explicit Diagonal Entries (Eq. (18) / `eq:Fdiag`)**:
    $(F_\tau)_{j, j+1} = \tau^{j+1} (2^{j+1} - 1)$. -/
theorem F_tau_mat_diag (k : ℕ) (τ : ℕ) (j : Fin k) :
    F_tau_mat k τ j ⟨j.val + 1, by omega⟩ = (τ : ℚ) ^ (j.val + 1) * ((2 : ℚ) ^ (j.val + 1) - 1) := by
  dsimp [F_tau_mat]
  have h1 := E_tilde_diag (k + 1) (2 * τ) ⟨j.val + 1, by omega⟩
  have h2 := E_tilde_diag (k + 1) τ ⟨j.val + 1, by omega⟩
  rw [h1, h2]
  have : ((2 * τ : ℕ) : ℚ) = 2 * (τ : ℚ) := by push_cast; rfl
  rw [this, mul_pow]
  ring

#print axioms Karlin.F_tau_mat_diag



/-!
## Part 10b: Completing Bundled Gateway Lemma 5.3 (`lem:gateway`, Eq. `eq:top`)
-/

/-- Upper-triangular vanishing of $F_\tau$: $(F_\tau)_{j, c} = 0$ when $j + 1 < c$. -/
theorem F_tau_mat_eq_zero_of_gt (k : ℕ) (τ : ℕ) (j : Fin k) (c : Fin (k + 1))
    (h : j.val + 1 < c.val) :
    F_tau_mat k τ j c = 0 := by
  dsimp [F_tau_mat]
  have h1 := E_tilde_eq_zero_of_lt (2 * τ) (show (⟨j.val + 1, by omega⟩ : Fin (k + 1)).val < c.val from h)
  have h2 := E_tilde_eq_zero_of_lt τ (show (⟨j.val + 1, by omega⟩ : Fin (k + 1)).val < c.val from h)
  rw [h1, h2, sub_zero]

#print axioms Karlin.F_tau_mat_eq_zero_of_gt

/-- Last column of $E_\tau$ vanishes: $(E_\tau)_{i, k} = 0$ for all $i : \mathrm{Fin}\ k$. -/
theorem E_tau_mat_last_col_zero (k : ℕ) (τ : ℕ) (i : Fin k) :
    E_tau_mat k τ i ⟨k, by omega⟩ = 0 := by
  dsimp [E_tau_mat]
  exact E_tilde_eq_zero_of_lt τ (show (⟨i.val, by omega⟩ : Fin (k + 1)).val < (⟨k, by omega⟩ : Fin (k + 1)).val by exact i.isLt)

#print axioms Karlin.E_tau_mat_last_col_zero

/-- Last column of $E_{2\tau}$ vanishes: $(E_{2\tau})_{i, k} = 0$ for all $i : \mathrm{Fin}\ k$. -/
theorem E_2tau_mat_last_col_zero (k : ℕ) (τ : ℕ) (i : Fin k) :
    E_2tau_mat k τ i ⟨k, by omega⟩ = 0 := by
  dsimp [E_2tau_mat]
  exact E_tau_mat_last_col_zero k (2 * τ) i

#print axioms Karlin.E_2tau_mat_last_col_zero

/-- **Bundled Parent Transfer Relation**:
    $A (C F_\tau) = R (E_{2\tau} - E_\tau)$ when $A C = R N_k$. -/
theorem bundled_parent_transfer {m k : ℕ} (A : Matrix (Fin m) (Fin m) ℚ) (R C : Matrix (Fin m) (Fin k) ℚ)
    (τ : ℕ) (hAC : A * C = R * N_mat k) :
    A * (C * F_tau_mat k τ) = R * (E_2tau_mat k τ - E_tau_mat k τ) := by
  rw [← Matrix.mul_assoc, hAC, Matrix.mul_assoc, N_mat_mul_F_tau_mat]

#print axioms Karlin.bundled_parent_transfer

/-- Last column of bundled parent transfer product vanishes:
    $(A (C F_\tau))_{x, k} = 0$ for all $x : \mathrm{Fin}\ m$. -/
theorem bundled_parent_transfer_last_col_zero {m k : ℕ} (A : Matrix (Fin m) (Fin m) ℚ) (R C : Matrix (Fin m) (Fin k) ℚ)
    (τ : ℕ) (hAC : A * C = R * N_mat k) (x : Fin m) :
    (A * (C * F_tau_mat k τ)) x ⟨k, by omega⟩ = 0 := by
  rw [bundled_parent_transfer A R C τ hAC]
  rw [Matrix.mul_sub]
  simp only [Matrix.sub_apply]
  have h2 : (R * E_2tau_mat k τ) x ⟨k, by omega⟩ = 0 := by
    rw [Matrix.mul_apply]
    have : ∀ j : Fin k, R x j * E_2tau_mat k τ j ⟨k, by omega⟩ = 0 := by
      intro j
      rw [E_2tau_mat_last_col_zero, mul_zero]
    simp [this]
  have h1 : (R * E_tau_mat k τ) x ⟨k, by omega⟩ = 0 := by
    rw [Matrix.mul_apply]
    have : ∀ j : Fin k, R x j * E_tau_mat k τ j ⟨k, by omega⟩ = 0 := by
      intro j
      rw [E_tau_mat_last_col_zero, mul_zero]
    simp [this]
  rw [h2, h1, sub_zero]

#print axioms Karlin.bundled_parent_transfer_last_col_zero

/-- Row 0, column $k$ of $F_\tau$ vanishes when $2 \le k$. -/
theorem F_tau_mat_row_zero_last_col_zero (k : ℕ) (hk : 2 ≤ k) (τ : ℕ) :
    F_tau_mat k τ ⟨0, by omega⟩ ⟨k, by omega⟩ = 0 := by
  have : (⟨0, by omega⟩ : Fin k).val + 1 < (⟨k, by omega⟩ : Fin (k + 1)).val := by
    dsimp
    omega
  exact F_tau_mat_eq_zero_of_gt k τ ⟨0, by omega⟩ ⟨k, by omega⟩ this

#print axioms Karlin.F_tau_mat_row_zero_last_col_zero

/-- Bundled old-block count table $X_{\mathrm{bundled}} \in \mathbb{Q}^{(m+1) \times (k+1)}$
    with top $m$ rows $C F_\tau$ and bottom row $e_0^\top$. -/
def X_bundled {m k : ℕ} (C : Matrix (Fin m) (Fin k) ℚ) (τ : ℕ) :
    Matrix (Fin (m + 1)) (Fin (k + 1)) ℚ :=
  Matrix.of fun x c =>
    match finSumFinEquiv.symm x with
    | Sum.inl i => (C * F_tau_mat k τ) i c
    | Sum.inr _ => e0_row (k + 1) c

/-- **Lemma 5.3 Bundled Deficit Top-Column Vanishing (`eq:top`)**:
    For $k \ge 2$, under $A C = R N_k$ and $v^\top C = e_0^\top$, the top-column $k$
    of the bundled deficit $D = S N_{k+1} - G_O X_{\mathrm{bundled}}$ vanishes identically:
    $$(S N_{k+1} - G_O X_{\mathrm{bundled}})_{x, k} = 0$$
    for any score table $S$ and any old action $x : \mathrm{Fin}\ (m + 1)$. -/
theorem D_bundled_last_col_zero {m k : ℕ} (hk : 2 ≤ k)
    (A : Matrix (Fin m) (Fin m) ℚ) (v : Fin m → ℚ)
    (R C : Matrix (Fin m) (Fin k) ℚ) (τ : ℕ)
    (hAC : A * C = R * N_mat k)
    (hvC : Matrix.vecMul v C = e0_row k)
    (S : Matrix (Fin (m + 1)) (Fin (k + 1)) ℚ)
    (x : Fin (m + 1)) :
    (S * N_mat (k + 1) - adjoinGatewayEndpointG A v * X_bundled C τ) x ⟨k, by omega⟩ = 0 := by
  simp only [Matrix.sub_apply]
  let c_top : Fin (k + 1) := ⟨k, by omega⟩
  have hS : (S * N_mat (k + 1)) x c_top = 0 := by
    rw [mul_N_mat_apply]
    have h_val : c_top.val = k := rfl
    split_ifs with h
    · rw [h_val] at h
      omega
    · rfl
  rw [hS, zero_sub, neg_eq_zero]
  have hcomp :=
    (Equiv.sum_comp finSumFinEquiv fun y : Fin (m + 1) =>
      adjoinGatewayEndpointG A v x y * X_bundled C τ y c_top).symm
  rw [Matrix.mul_apply, hcomp, Fintype.sum_sum_type]
  have he0_top : e0_row (k + 1) c_top = 0 := by
    simp only [e0_row, c_top]
    split_ifs with h
    · omega
    · rfl
  have hX_inr : ∀ j : Fin 1, X_bundled C τ (finSumFinEquiv (Sum.inr j)) c_top = 0 := by
    intro j
    simp only [X_bundled, Matrix.of_apply, Equiv.symm_apply_apply, he0_top]
  simp only [hX_inr, mul_zero, Finset.sum_const_zero, add_zero]
  have hX_inl : ∀ j : Fin m,
      X_bundled C τ (finSumFinEquiv (Sum.inl j)) c_top = (C * F_tau_mat k τ) j c_top := by
    intro j
    simp only [X_bundled, Matrix.of_apply, Equiv.symm_apply_apply]
  simp_rw [hX_inl]
  cases hsym : finSumFinEquiv.symm x with
  | inl i =>
    have hG_inl : ∀ j : Fin m,
        adjoinGatewayEndpointG A v x (finSumFinEquiv (Sum.inl j)) = A i j := by
      intro j
      simp [adjoinGatewayEndpointG, hsym]
    simp_rw [hG_inl]
    have hAC_sum : (∑ j : Fin m, A i j * (C * F_tau_mat k τ) j c_top) =
        (A * (C * F_tau_mat k τ)) i c_top := rfl
    rw [hAC_sum]
    exact bundled_parent_transfer_last_col_zero A R C τ hAC i
  | inr _ =>
    by_cases hm : 0 < m
    · have hG_inr : ∀ j : Fin m,
          adjoinGatewayEndpointG A v x (finSumFinEquiv (Sum.inl j)) =
            A ⟨0, hm⟩ j + v j := by
        intro j
        simp [adjoinGatewayEndpointG, hsym, hm]
      simp_rw [hG_inr, add_mul, Finset.sum_add_distrib]
      have hAC_sum : (∑ j : Fin m, A ⟨0, hm⟩ j * (C * F_tau_mat k τ) j c_top) =
          (A * (C * F_tau_mat k τ)) ⟨0, hm⟩ c_top := rfl
      have hvC_sum : (∑ j : Fin m, v j * (C * F_tau_mat k τ) j c_top) =
          (Matrix.vecMul v (C * F_tau_mat k τ)) c_top := rfl
      rw [hAC_sum, hvC_sum]
      have h1 := bundled_parent_transfer_last_col_zero A R C τ hAC ⟨0, hm⟩
      rw [h1, zero_add, ← Matrix.vecMul_vecMul, hvC]
      dsimp [Matrix.vecMul, dotProduct]
      have h_term : ∀ j : Fin k, e0_row k j * F_tau_mat k τ j c_top =
          if j = ⟨0, by omega⟩ then F_tau_mat k τ ⟨0, by omega⟩ c_top else 0 := by
        intro j
        by_cases hj : j = ⟨0, by omega⟩
        · subst hj
          simp [e0_row]
        · rw [if_neg hj]
          dsimp [e0_row]
          have hj_val : j.val ≠ 0 := fun h => hj (Fin.ext h)
          rw [if_neg hj_val, zero_mul]
      rw [Finset.sum_congr rfl (fun j _ => h_term j), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      exact F_tau_mat_row_zero_last_col_zero k hk τ
    · have hm0 : m = 0 := by omega
      subst hm0
      simp

#print axioms Karlin.D_bundled_last_col_zero


/-!
## Part 11: Section 7.3 Lemma 7.1 (`lem:uniform`), Appendix A.1 Norm Bounds, and Section 8.1 Proposition 8.1 (`prop:nextweights`)
-/

/-- Entrywise $\ell_\infty$ bound predicate for matrices. -/
def EntrywiseAbsLe {α β : Type*} (A : Matrix α β ℚ) (B : ℚ) : Prop :=
  ∀ i j, |A i j| ≤ B

/-- Perturbation bound for strictly positive entries: $c_0 + \delta \ge c_0 - B > 0$. -/
theorem entry_pos_of_abs_perturbation (c0 B delta : ℚ) (hdelta : |delta| ≤ B) (hB : B < c0) :
    c0 + delta ≥ c0 - B ∧ 0 < c0 + delta := by
  have : -B ≤ delta := (abs_le.mp hdelta).1
  constructor
  · linarith
  · linarith

#print axioms Karlin.entry_pos_of_abs_perturbation

/-- Perturbation bound for strictly negative entries: $-c_0 + \delta < -\epsilon$. -/
theorem entry_neg_of_abs_perturbation (c0 B eps delta : ℚ) (hdelta : |delta| ≤ B) (hB : B < c0 - eps) :
    -c0 + delta < -eps := by
  have : delta ≤ B := (abs_le.mp hdelta).2
  linarith

#print axioms Karlin.entry_neg_of_abs_perturbation

/-- **Lemma 7.1 Cross-Coupling Positivity (`lem:uniform`)**:
    The perturbed cross-coupling matrix $C_\times = \kappa \mathbf{1} \mathbf{1}^\top + \Delta_\times$
    has strictly positive entries whenever $\|\Delta_\times\|_\infty < \kappa$. -/
theorem lem_7_1_C_cross_pos {m : ℕ} (kappa b_cross : ℚ) (Delta : Matrix (Fin m) (Fin m) ℚ)
    (h_b : EntrywiseAbsLe Delta b_cross) (h_lt : b_cross < kappa) (i j : Fin m) :
    (kappa • outerProd (fun _ : Fin m => (1:ℚ)) (fun _ : Fin m => (1:ℚ)) + Delta) i j ≥ kappa - b_cross ∧
    0 < (kappa • outerProd (fun _ : Fin m => (1:ℚ)) (fun _ : Fin m => (1:ℚ)) + Delta) i j := by
  have h_outer : (outerProd (fun _ : Fin m => (1:ℚ)) (fun _ : Fin m => (1:ℚ))) i j = 1 := by simp [outerProd]
  dsimp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [h_outer, mul_one]
  exact entry_pos_of_abs_perturbation kappa b_cross (Delta i j) (h_b i j) h_lt

#print axioms Karlin.lem_7_1_C_cross_pos

/-- Unperturbed reset coupling matrix $P_0 = [-a \mathbf{1}_r^\top \mid a \mathbf{1}_r^\top]$. -/
def P_coupled (r : ℕ) {m : ℕ} (a : Fin m → ℚ) : Matrix (Fin m) (Fin r ⊕ Fin r) ℚ :=
  Matrix.of fun i y =>
    match y with
    | Sum.inl _ => -a i
    | Sum.inr _ => a i

/-- **Lemma 7.1 Reset Coupling Signs and Waiting Margins (`lem:uniform`)**:
    For $P = P_0 + \Delta_P$, early resets satisfy $P_{x, \mathrm{early}} < -\epsilon$
    and late resets satisfy $P_{x, \mathrm{late}} > \epsilon$. -/
theorem lem_7_1_P_signs_and_waiting_margin {m : ℕ} (r : ℕ) (a : Fin m → ℚ)
    (amin bP eps : ℚ) (Delta_P : Matrix (Fin m) (Fin r ⊕ Fin r) ℚ)
    (ha : ∀ i, amin ≤ a i) (h_Delta : EntrywiseAbsLe Delta_P bP) (h_bound : eps + bP < amin) :
    (∀ (i : Fin m) (j : Fin r), (P_coupled r a + Delta_P) i (Sum.inl j) < -eps) ∧
    (∀ (i : Fin m) (j : Fin r), (P_coupled r a + Delta_P) i (Sum.inr j) > eps) := by
  constructor
  · intro i j
    have : (P_coupled r a + Delta_P) i (Sum.inl j) = -a i + Delta_P i (Sum.inl j) := by
      simp [P_coupled]
    rw [this]
    have hD : Delta_P i (Sum.inl j) ≤ bP := (abs_le.mp (h_Delta i (Sum.inl j))).2
    have hai : amin ≤ a i := ha i
    linarith
  · intro i j
    have : (P_coupled r a + Delta_P) i (Sum.inr j) = a i + Delta_P i (Sum.inr j) := by
      simp [P_coupled]
    rw [this]
    have hD : -bP ≤ Delta_P i (Sum.inr j) := (abs_le.mp (h_Delta i (Sum.inr j))).1
    have hai : amin ≤ a i := ha i
    linarith

#print axioms Karlin.lem_7_1_P_signs_and_waiting_margin

/-- **Lemma 7.1 Endpoint Waiting Margin (`eq:uniform-margins`)**:
    At the gateway endpoint $g$, the margin satisfies $-P_{g, \mathrm{inl}\ j} - c > \mathcal{A}_k + 3 > \mathcal{A}_k$. -/
theorem lem_7_1_endpoint_waiting_margin (Ak c : ℚ) (Delta : ℚ)
    (hc : 0 < c ∧ c < 1) (hDelta : |Delta| ≤ 1) (hAk : 0 ≤ Ak) :
    -(-(2 * (Ak + 3) - c) + Delta) - c > Ak + 3 ∧ Ak + 3 > Ak := by
  have hD : Delta ≤ 1 := (abs_le.mp hDelta).2
  constructor
  · linarith
  · linarith

#print axioms Karlin.lem_7_1_endpoint_waiting_margin

/-- **Proposition 8.1 Next-Order Positive Cone Weights (`prop:nextweights`)**:
    Under radius condition $T_2 > 2 B / \alpha$ (Eq. `eq:radius`), every coordinate
    of late weights $a_L = t_{\mathrm{rem}} W^{-1}$ satisfies $a_{L, j} > \alpha / 2 > 0$. -/
theorem prop_8_1_late_weights_strictly_positive {k : ℕ}
    (t_rem : Fin (k + 1) → ℚ) (Phi0 Phi1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (T1 T2 alpha B : ℚ)
    (hPhi0 : Matrix.vecMul t_rem (T1⁻¹ • Phi0) = alpha • (fun _ => 1))
    (hα : 0 < alpha)
    (hB : ∀ j, |Matrix.vecMul t_rem Phi1 j| ≤ B)
    (hT2_pos : 0 < T2)
    (hT2_radius : 2 * B < alpha * T2)
    (j : Fin (k + 1)) :
    Matrix.vecMul t_rem (W_inv_paper T1 T2 Phi0 Phi1) j > alpha / 2 ∧
    0 < Matrix.vecMul t_rem (W_inv_paper T1 T2 Phi0 Phi1) j := by
  have hdecomp := late_weight_decomposition t_rem T1 T2 alpha Phi0 Phi1 hPhi0
  have hj := congr_fun hdecomp j
  dsimp [W_inv_paper]
  rw [hj]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  have hBj : -B ≤ Matrix.vecMul t_rem Phi1 j := (abs_le.mp (hB j)).1
  have hinv : 0 < T2⁻¹ := inv_pos.mpr hT2_pos
  have h_lower : - (B * T2⁻¹) ≤ T2⁻¹ * Matrix.vecMul t_rem Phi1 j := by
    calc - (B * T2⁻¹) = T2⁻¹ * (-B) := by ring
    _ ≤ T2⁻¹ * Matrix.vecMul t_rem Phi1 j := mul_le_mul_of_nonneg_left hBj (le_of_lt hinv)
  have h_radius : B * T2⁻¹ < alpha / 2 := by
    have h_prod : 2 * B * T2⁻¹ < alpha * T2 * T2⁻¹ := mul_lt_mul_of_pos_right hT2_radius hinv
    rw [mul_assoc alpha T2 T2⁻¹, mul_inv_cancel₀ (ne_of_gt hT2_pos), mul_one] at h_prod
    linarith
  constructor
  · linarith
  · linarith

#print axioms Karlin.prop_8_1_late_weights_strictly_positive


/-!
## Part 12: Section 9 & Global Master Synthesis — Theorem 5.1 (`thm:lift`), Proposition 4.2 (`prop:recursive-family`), and Theorem 1.1 (`thm:main`)
-/

/-- **Proposition 4.2 Recursive Realized Clock Family (`prop:recursive-family`)**:
    For every order $k = d + 2 \ge 2$, the inductively constructed clock is a verified
    realized clock with $m_k = (k + 1)^2 - 6$, $n_k = (k + 1)^2 - 5$, skew-symmetric game matrix,
    and full column rank $k$. -/
theorem paper_prop_4_2_recursive_family (d : ℕ) :
    let rc := (groundedBundleTower d).L.rc
    rc.fc.clock.m = (d + 3) ^ 2 - 6 ∧
    Fintype.card (Option (Fin rc.fc.clock.m)) = (d + 3) ^ 2 - 5 ∧
    IsSkewSymmetric rc.gameMatrix ∧
    rc.fc.clock.C.transpose * rc.fc.L_C = 1 := by
  intro rc
  have hm : rc.fc.clock.m = (d + 3) ^ 2 - 6 := (groundedBundleTower d).hm
  have hcard : Fintype.card (Option (Fin rc.fc.clock.m)) = (d + 3) ^ 2 - 5 := by
    rw [Fintype.card_option, Fintype.card_fin, hm]
    set N := (d + 3) ^ 2
    have : 3 ≤ d + 3 := by omega
    have : 9 ≤ N := by
      change 3 ^ 2 ≤ (d + 3) ^ 2
      nlinarith
    omega
  exact ⟨hm, hcard, rc.gameMatrix_skew, rc.fc.hLC⟩

#print axioms Karlin.paper_prop_4_2_recursive_family

/-- **Theorem 1.1 Master All-Orders Duality Gap Theorem (`thm:main`)**:
    For every order $k = d + 2 \ge 2$, there exists a skew-symmetric game on
    $(k + 1)^2 - 5$ actions with a unique Fictitious Play trajectory from $(none, none)$
    satisfying two-sided duality gap bounds $\Theta(t^{-1/k})$ for all integer times $t \ge 1$. -/
theorem paper_thm_1_1_main (d : ℕ) :
    ∃ (rc : RealizedClock (d + 2)),
      rc.fc.clock.m = (d + 3) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (d + 3) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ (d + 2) * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ (d + 2) * (t : ℚ) ≤
          rc.c_high) :=
  all_orders_unconditional_karlin_theorem (d + 2) (by omega)

#print axioms Karlin.paper_thm_1_1_main

/-- **Unconditional Refutation of Karlin's Strong Conjecture Across All Orders $k \ge 3$**:
    Karlin's conjecture asserts convergence rate $O(1/t)$.
    For all orders $k \ge 3$, the true rate is $\Theta(t^{-1/k})$, strictly slower than $O(1/t)$. -/
theorem paper_karlin_conjecture_false_all_orders (k : ℕ) (hk : 3 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) :=
  karlin_conjecture_false_all_orders_unconditional k hk

#print axioms Karlin.paper_karlin_conjecture_false_all_orders

/-- **Complete Architecture Certificate for `master_v15.tex`**:
    Unifies the entire 12-part algebraic, inductive, and all-time pipeline
    from the paper into a single theorem. -/
theorem paper_master_v15_complete_architecture_certificate :
    (∀ (w h : ℕ), w ≤ h + 1 → Even h → L_adjoint (B_mat w) (Z_binom_concrete w h) = 0) ∧
    (∀ {k h : ℕ}, 0 < k → k < h → h ≤ 2 * k → Even h →
      ∀ (psi_hat : Fin (k + 1) → ℚ), psi_hat ⟨k, by omega⟩ = 0 →
      psi_hat ⟨k - 1, by omega⟩ ≠ 0 →
      ∀ (F_hat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ),
      F_hat ⟨k, by omega⟩ ⟨k, by omega⟩ = 0 →
      matInnerProd (Z_DP (k + 1) h) (F_hat - outerProd (solveHigherTestsDP k psi_hat F_hat) psi_hat) = 0) ∧
    (∀ {k : ℕ} (hk_pos : 0 < k) (hk_even : Even k)
      (F0_hat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
      (u v : Fin (k + 1) → ℚ)
      (hdenom : u ⟨k, by omega⟩ + v ⟨k, by omega⟩ ≠ 0),
      let dc := dc_even_paper k F0_hat (u ⟨k, by omega⟩) (v ⟨k, by omega⟩)
      let F_hat := F0_hat + dc • (outerProd (fun i => if i.val = 0 then 1 else 0) u +
                                  outerProd v (fun j => if j.val = 0 then 1 else 0))
      matInnerProd (Z_DP (k + 1) k) F_hat = 0 ∧
      ∀ h, k + 1 ≤ h → matInnerProd (Z_DP (k + 1) h) F_hat = matInnerProd (Z_DP (k + 1) h) F0_hat) ∧
    (∀ (k : ℕ) (T1 T2 lam : ℚ), T1 ≠ 0 → T2 ≠ 0 → lam ≠ 0 → ∀ (zeta0 : Fin (k + 1) → ℚ), zeta0 (lastIdx k) ≠ 0 →
      W_concrete k T1 T2 lam zeta0 * Winv_concrete k T1 T2 lam zeta0 = 1) ∧
    (∀ (k : ℕ) (T1 T2 lam : ℚ) (hT1 : T1 ≠ 0) (hT2 : T2 ≠ 0) (hlam : lam ≠ 0)
      (zeta0 : Fin (k + 1) → ℚ) (hzeta : zeta0 (lastIdx k) ≠ 0)
      (ell_Delta : Fin (k + 1) → ℚ)
      (u : Fin (k + 1) → ℚ) (hu : u = fun i => if i.val = 0 then 1 else 0)
      (v : Fin (k + 1) → ℚ) (hv : v = ((k + 1 : ℚ) * lam) • ell_Delta)
      (kappa : ℚ) (hkappa : kappa = ((k + 1 : ℚ)^2 * T1 * lam^2)⁻¹)
      (E_base : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
      (hE_base : E_base = T1 • outerProd zeta0 zeta0 + outerProd zeta0 ell_Delta)
      (hdenom : 1 + dotProduct v (Matrix.mulVec (Winv_concrete k T1 T2 lam zeta0) u) ≠ 0)
      (eta : ℚ) (Lr : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
      (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
      (Fres : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
      (hFres : Fres = E - E_base - eta • ((WE_concrete k T1 T2 lam zeta0 u v)ᵀ * Lr * (WE_concrete k T1 T2 lam zeta0 u v) +
                                           (W_concrete k T1 T2 lam zeta0)ᵀ * Lr * (W_concrete k T1 T2 lam zeta0)))
      (C_cross : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ),
      C_cross = kappa • (outerProd (fun _ => 1) (fun _ => 1)) + (Winv_concrete k T1 T2 lam zeta0)ᵀ * Fres * (WE_inv_concrete k T1 T2 lam zeta0 u v) →
      eta • ((WE_concrete k T1 T2 lam zeta0 u v)ᵀ * Lr * (WE_concrete k T1 T2 lam zeta0 u v) +
             (W_concrete k T1 T2 lam zeta0)ᵀ * Lr * (W_concrete k T1 T2 lam zeta0)) +
      (W_concrete k T1 T2 lam zeta0)ᵀ * C_cross * (WE_concrete k T1 T2 lam zeta0 u v) = E) ∧
    (∀ (k τ : ℕ), N_mat k * F_tau_mat k τ = E_2tau_mat k τ - E_tau_mat k τ) ∧
    (∀ (k τ : ℕ) (j : Fin k), F_tau_mat k τ j ⟨j.val + 1, by omega⟩ = (τ : ℚ) ^ (j.val + 1) * ((2 : ℚ) ^ (j.val + 1) - 1)) ∧
    (∀ {m : ℕ} (r : ℕ) (a : Fin m → ℚ) (amin bP eps : ℚ) (Delta_P : Matrix (Fin m) (Fin r ⊕ Fin r) ℚ),
      (∀ i, amin ≤ a i) → EntrywiseAbsLe Delta_P bP → eps + bP < amin →
      (∀ (i : Fin m) (j : Fin r), (P_coupled r a + Delta_P) i (Sum.inl j) < -eps) ∧
      (∀ (i : Fin m) (j : Fin r), (P_coupled r a + Delta_P) i (Sum.inr j) > eps)) ∧
    (∀ {k : ℕ} (t_rem : Fin (k + 1) → ℚ) (Phi0 Phi1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
      (T1 T2 alpha B : ℚ), Matrix.vecMul t_rem (T1⁻¹ • Phi0) = alpha • (fun _ => 1) →
      0 < alpha → (∀ j, |Matrix.vecMul t_rem Phi1 j| ≤ B) → 0 < T2 →
      2 * B < alpha * T2 → ∀ (j : Fin (k + 1)),
      Matrix.vecMul t_rem (W_inv_paper T1 T2 Phi0 Phi1) j > alpha / 2 ∧
      0 < Matrix.vecMul t_rem (W_inv_paper T1 T2 Phi0 Phi1) j) ∧
    (∀ (d : ℕ), ∃ (rc : RealizedClock (d + 2)),
      rc.fc.clock.m = (d + 3) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (d + 3) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ (d + 2) * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ (d + 2) * (t : ℚ) ≤
          rc.c_high)) := by
  refine ⟨Z_binom_concrete_in_adjoint_kernel,
          fun hk_pos hk_h hh_top hh_even psi_hat hpsi_k hpsi_prev F_hat hF_kk =>
            solveHigherTestsDP_solves_all_higher_tests hk_pos hk_h hh_top hh_even psi_hat hpsi_k hpsi_prev F_hat hF_kk,
          fun hk_pos hk_even F0_hat u v hdenom =>
            prop_7_1_all_tests_solved_even_k hk_pos hk_even F0_hat u v hdenom,
          W_concrete_mul_Winv_concrete,
          M_transpose_mul_J_mul_M_fully_concrete,
          N_mat_mul_F_tau_mat,
          F_tau_mat_diag,
          fun r a amin bP eps Delta_P ha h_Delta h_bound =>
            lem_7_1_P_signs_and_waiting_margin r a amin bP eps Delta_P ha h_Delta h_bound,
          fun t_rem Phi0 Phi1 T1 T2 alpha B hPhi0 hα hB hT2_pos hT2_radius j =>
            prop_8_1_late_weights_strictly_positive t_rem Phi0 Phi1 T1 T2 alpha B hPhi0 hα hB hT2_pos hT2_radius j,
          fun d => paper_thm_1_1_main d⟩

#print axioms Karlin.paper_master_v15_complete_architecture_certificate


/-- **Concrete Link 1 (Equation (1697))**:
    The generic concrete binomial test matrix $Z^{(2)}_{\mathrm{binom}}(3)$
    equals the explicit RPS test matrix $Z^{(2)}_{\mathrm{rps}}$. -/
theorem Z_binom_concrete_3_2_eq_Z2_rps : Z_binom_concrete 3 2 = Z2_rps := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals (
    simp [Z_binom_concrete, Z_binom, S_mat, S_inv_mat, Z_DP, expN0, V_antidiag, Z2_rps,
          pow_two, Matrix.one_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Finset.sum_range_succ]
    try norm_num
  )

#print axioms Karlin.Z_binom_concrete_3_2_eq_Z2_rps

/-- **Concrete Link 2: Exact Value of $F_1$ for $k=2$ (Equation (1223))**:
    $F_1 = \begin{pmatrix} 0 & 1 & 0 \\ 0 & 1 & 3 \end{pmatrix}$. -/
theorem F_tau_mat_2_1_eq : F_tau_mat 2 1 = !![0, 1, 0; 0, 1, 3] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals (
    simp [F_tau_mat, E_tilde, S_mat, S_inv_mat, expN0, scaleDiag, pow_two, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_three, Finset.sum_range_succ]
    try norm_num
  )

#print axioms Karlin.F_tau_mat_2_1_eq

/-- **Concrete Link 2: Exact Value of $F_2$ for $k=2$ (Equation (1223))**:
    $F_2 = \begin{pmatrix} 0 & 2 & 0 \\ 0 & 5 & 12 \end{pmatrix}$. -/
theorem F_tau_mat_2_2_eq : F_tau_mat 2 2 = !![0, 2, 0; 0, 5, 12] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals (
    simp [F_tau_mat, E_tilde, S_mat, S_inv_mat, expN0, scaleDiag, pow_two, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_three, Finset.sum_range_succ]
    try norm_num
  )

#print axioms Karlin.F_tau_mat_2_2_eq

/-- **Proposition 6.1 (`prop:seedadmissible` of `master_v15.tex`)**:
    Concrete seed admissibility for the rock-paper-scissors base ($k=2$):
    positive parent weights $a_P$, exact target row matching $a_P C_2 = t$,
    backward-shift transfer identity $t F_1 = \zeta^\circ + \zeta^\circ B_3 - (15/2) e_0$,
    and exact vanishing of the higher compatibility test $\langle Z^{(4)}_{\mathrm{binom}}, (D^\circ)^\top X \rangle = 0$. -/
theorem prop_6_1_rps_seed_admissible :
    let C2 : Matrix (Fin 3) (Fin 2) ℚ := !![5, 3; 6, 3; 7, 3]
    let aP : Fin 3 → ℚ := ![2/27, 2/27, 2/27]
    let t : Fin 2 → ℚ := ![4/3, 2/3]
    let zeta0 : Fin 3 → ℚ := ![4, 3/2, 1]
    (∀ i : Fin 3, 0 < aP i) ∧
    Matrix.vecMul aP C2 = t ∧
    Matrix.vecMul t (F_tau_mat 2 1) = zeta0 + Matrix.vecMul zeta0 (B_mat 3) - (15/2 : ℚ) • e0_row 3 ∧
    matInnerProd (Z_binom_concrete 3 4) D0tX_rps = 0 := by
  intro C2 aP t zeta0
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> { dsimp [aP]; norm_num }
  · ext j
    fin_cases j
    all_goals (
      simp [Matrix.vecMul, dotProduct, aP, C2, t, Fin.sum_univ_three]
      try norm_num
    )
  · have h_tF1 : Matrix.vecMul t (F_tau_mat 2 1) = ![0, 2, 2] := by
      rw [F_tau_mat_2_1_eq]
      ext j
      fin_cases j
      all_goals (
        simp [Matrix.vecMul, dotProduct, t, Fin.sum_univ_two]
        try norm_num
      )
    have h_RHS : zeta0 + Matrix.vecMul zeta0 (B_mat 3) - (15/2 : ℚ) • e0_row 3 = ![0, 2, 2] := by
      ext j
      fin_cases j
      all_goals (
        simp [zeta0, B_mat, e0_row, Matrix.vecHead, Matrix.vecTail]
        try norm_num
      )
    rw [h_tF1, h_RHS]
  · simp [matInnerProd, Z_binom_concrete, Z_binom, S_mat, S_inv_mat, Z_DP, expN0, V_antidiag, D0tX_rps,
          pow_two, Matrix.one_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Finset.sum_range_succ]

#print axioms Karlin.prop_6_1_rps_seed_admissible

/-- Projection of residual target onto concrete rank-one block $\Phi_0$ produces a uniform row. -/
theorem vecMul_Phi0_concrete (k : ℕ) (t_rem : Fin (k + 1) → ℚ) (T1 lam : ℚ) (zeta0 : Fin (k + 1) → ℚ) :
    Matrix.vecMul t_rem (T1⁻¹ • Phi0_concrete k lam zeta0) =
      (t_rem (lastIdx k) * (T1 * ((k + 1 : ℚ) * lam * zeta0 (lastIdx k)))⁻¹) • (fun _ => 1) := by
  ext j
  dsimp [Matrix.vecMul, dotProduct]
  have h_term : ∀ i : Fin (k + 1), t_rem i * (T1⁻¹ * Phi0_concrete k lam zeta0 i j) =
      if i = lastIdx k then t_rem (lastIdx k) * (T1 * ((k + 1 : ℚ) * lam * zeta0 (lastIdx k)))⁻¹ else 0 := by
    intro i
    dsimp [Phi0_concrete, lastIdx]
    split_ifs with hi
    · subst hi
      rw [← mul_inv, mul_assoc]
    · rw [mul_zero, mul_zero]
  rw [Finset.sum_congr rfl (fun i _ => h_term i), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  simp

#print axioms Karlin.vecMul_Phi0_concrete

/-- **Proposition 8.1 Concrete Next-Order Cone Weights (`prop:nextweights`)**:
    Concrete late weights $a_L = t_{\mathrm{rem}} W^{-1}$ are strictly positive
    $a_{L, j} > \alpha / 2 > 0$ and reconstruct the target $t_+ = \mu r_0 + a_L W$. -/
theorem prop_8_1_late_weights_concrete {k : ℕ}
    (t_rem : Fin (k + 1) → ℚ) (T1 T2 lam : ℚ) (zeta0 : Fin (k + 1) → ℚ)
    (hT1 : T1 ≠ 0) (hlam : lam ≠ 0) (hzeta : zeta0 (lastIdx k) ≠ 0)
    (B : ℚ)
    (hα : 0 < t_rem (lastIdx k) * (T1 * ((k + 1 : ℚ) * lam * zeta0 (lastIdx k)))⁻¹)
    (hB : ∀ j, |Matrix.vecMul t_rem (Phi1_concrete k zeta0) j| ≤ B)
    (hT2_pos : 0 < T2)
    (hT2_radius : 2 * B < (t_rem (lastIdx k) * (T1 * ((k + 1 : ℚ) * lam * zeta0 (lastIdx k)))⁻¹) * T2)
    (t_plus r0 : Fin (k + 1) → ℚ) (mu : ℚ)
    (htrem : t_rem = t_plus - mu • r0) :
    let alpha := t_rem (lastIdx k) * (T1 * ((k + 1 : ℚ) * lam * zeta0 (lastIdx k)))⁻¹
    (∀ j, Matrix.vecMul t_rem (Winv_concrete k T1 T2 lam zeta0) j > alpha / 2 ∧
          0 < Matrix.vecMul t_rem (Winv_concrete k T1 T2 lam zeta0) j) ∧
    mu • r0 + Matrix.vecMul (Matrix.vecMul t_rem (Winv_concrete k T1 T2 lam zeta0))
                           (W_concrete k T1 T2 lam zeta0) = t_plus := by
  intro alpha
  constructor
  · intro j
    have hPhi0 := vecMul_Phi0_concrete k t_rem T1 lam zeta0
    dsimp [Winv_concrete]
    exact prop_8_1_late_weights_strictly_positive t_rem (Phi0_concrete k lam zeta0) (Phi1_concrete k zeta0)
      T1 T2 alpha B hPhi0 hα hB hT2_pos hT2_radius j
  · have hT2 : T2 ≠ 0 := ne_of_gt hT2_pos
    rw [htrem, Matrix.vecMul_vecMul, Winv_concrete_mul_W_concrete k T1 T2 lam hT1 hT2 hlam zeta0 hzeta, Matrix.vecMul_one]
    abel

#print axioms Karlin.prop_8_1_late_weights_concrete

end Karlin

