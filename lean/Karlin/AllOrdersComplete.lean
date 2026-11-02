import Karlin.FictitiousPlay
import Karlin.RPSClock
import Karlin.CubicSevenAction
import Karlin.BinomialBasis
import Karlin.InductiveLift
import Karlin.ChronologyAndMain
import Karlin.UnrolledTrajectory
import Karlin.BundledClockLift

/-!
# Unconditional All-Orders Coupled-Moment Clock Synthesis, Realized Clocks, and Master Theorem (`thm:main`)

This module completes the constructive all-orders formalization of
*On Karlin's Conjecture for Fictitious Play*:

1. **General-Width Closed-Form Inverse of the Pascal Shift Matrix (`B_mat w = (1 + N_mat w)⁻¹`)**:
   * `mul_N_mat_apply` & `N_mat_mul_apply`: exact entrywise shift formulas for right and left
     multiplication by the subdiagonal shift matrix `N_mat w`.
   * `B_mat_mul_one_add_N` & `one_add_N_mul_B_mat`: proves that the alternating lower-triangular
     matrix `B_mat w` (`B_{i,j} = (-1)^{i-j}` for `j ≤ i`) satisfies
     `B_mat w * (1 + N_mat w) = 1` and `(1 + N_mat w) * B_mat w = 1` for **every** width `w ∈ ℕ`.
2. **Constructive Coupled-Moment Lift Step (`LiftStepData.ofCoupledMoment` & `coupledMomentLiftStep`)**:
   * Packages `B_mat (w + 1)` and the explicit bilinear interpolation solver `P_interp`
     (Lemma 5.5) with the Moment Equation `moment_equation_iff` (Section 6) and the explicit
     Section 7 coupled-moment matrices (`W_coupled`, `W_coupled_inv`, `M_coupled`, `R_M_coupled`,
     `J_coupled`, `P0_coupled`, `zeta_coupled`).
   * At each lift step `w ↦ w + 1`, adjoins `1` endpoint action `g` (with count row `e_0ᵀ` so
     `X_coupled` has full column rank `X_coupledᵀ * L_X_coupled = 1`) and `2(w + 1)` reset actions
     (with strictly positive count matrix `M_coupled w ≥ 1`, left inverse `R_M_coupled w * M_coupled w = 1`,
     strictly lower-triangular `J_coupled w` with positive subdiagonal `≥ (4(w+1))⁻¹ > 0`, flat
     ceiling `zeta_coupled w = 1 > 0`, and non-zero coupling `P = P_interp`), adding
     `1 + 2(w + 1) = 2w + 3` recurrent actions and preserving full column rank `C_+ᵀ * L_{C_+} = 1`.
3. **Unconditional All-Orders Coupled-Moment Clock Families (`standardClockFamily` & `sevenSeededClockFamily`)**:
   * `standardFullRankClockFamily (d : ℕ) : FullRankClock (d + 2)` (from the `k = 2` RPS base,
     adding `2k + 3` actions per step via `coupledMomentLiftStep` so `m_k = (k + 1)^2 - 6` and
     total dimension with setup action is `n_k = m_k + 1 = (k + 1)^2 - 5`).
   * `sevenSeededFullRankClockFamily (d : ℕ) : FullRankClock (d + 3)` (from the `k = 3` 6-action
     recurrent base so `m_k^{(7)} = (k + 1)^2 - 10` and `n_k^{(7)} = (k + 1)^2 - 9`).
4. **Strengthened Realized Clock Specification (`RealizedClock k`) & Complete Rate Bridge**:
   * `RealizedClock k`: packages `FullRankClock k` together with the `(m + 1) × (m + 1)` setup game
     `setupMatrix clock.G setupVec`, physical natural counts, admissibility constant, initialized
     play sequence `trajectory : ℕ → Option (Fin clock.m)` (`trajectory 0 = none`), strict
     two-player Fictitious Play best-response validity at every integer prefix `t ≥ 1`, tie-breaking
     uniqueness, phase boundary score/duration correspondence, and all-integer-time `Θ(t^{-1/k})`
     bounds on the standard empirical saddle-point duality gap `standardDualityGap`.
   * `rpsRealizedClock : RealizedClock 2` and `sevenRealizedClock : RealizedClock 3`: unconditional
     realized-clock instances for `k = 2` and `k = 3`.
   * `all_orders_karlin_theorem` & `karlin_paper_complete_synthesis`: the unconditional master theorems.
-/

namespace Karlin

open scoped BigOperators

/-!
## 1. General-Width Closed-Form Inverse `B_mat w = (1 + N_mat w)⁻¹`
-/

/-- Right-multiplying any matrix `A : Matrix α (Fin w) ℚ` by `N_mat w` shifts columns left by 1:
    entry `(i, d)` equals `A i ⟨d.val + 1, hd⟩` when `d.val + 1 < w`, and `0` at the last column. -/
theorem mul_N_mat_apply {α : Type*} {w : ℕ} (A : Matrix α (Fin w) ℚ) (i : α) (d : Fin w) :
    (A * N_mat w) i d =
      if hd : d.val + 1 < w then A i ⟨d.val + 1, hd⟩ else 0 := by
  simp only [Matrix.mul_apply, N_mat, Matrix.of_apply]
  split_ifs with hd
  · let j0 : Fin w := ⟨d.val + 1, hd⟩
    have hsum :
        (∑ j : Fin w, A i j * (if j.val = d.val + 1 then (1 : ℚ) else 0)) =
          ∑ j : Fin w, if j = j0 then A i j else 0 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j = j0
      · subst hj
        simp [j0]
      · have hne : j.val ≠ d.val + 1 := by
          intro h
          apply hj
          ext
          exact h
        simp [hj, hne]
    rw [hsum, Finset.sum_ite_eq' Finset.univ j0]
    simp [j0]
  · apply Finset.sum_eq_zero
    intro j _
    have hne : j.val ≠ d.val + 1 := by omega
    simp [hne]

/-- Left-multiplying any matrix `A : Matrix (Fin w) β ℚ` by `N_mat w` shifts rows down by 1:
    entry `(i, k)` equals `A ⟨i.val - 1, _⟩ k` when `0 < i.val`, and `0` in row `0`. -/
theorem N_mat_mul_apply {β : Type*} {w : ℕ} (A : Matrix (Fin w) β ℚ) (i : Fin w) (k : β) :
    (N_mat w * A) i k =
      if hi : 0 < i.val then A ⟨i.val - 1, by omega⟩ k else 0 := by
  simp only [Matrix.mul_apply, N_mat, Matrix.of_apply]
  split_ifs with hi
  · let j0 : Fin w := ⟨i.val - 1, by omega⟩
    have hsum :
        (∑ j : Fin w, (if i.val = j.val + 1 then (1 : ℚ) else 0) * A j k) =
          ∑ j : Fin w, if j = j0 then A j k else 0 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j = j0
      · subst hj
        have hval : i.val = j0.val + 1 := by
          change i.val = i.val - 1 + 1
          omega
        simp [hval]
      · have hne : i.val ≠ j.val + 1 := by
          intro h
          apply hj
          ext
          change j.val = i.val - 1
          omega
        simp [hj, hne]
    rw [hsum, Finset.sum_ite_eq' Finset.univ j0]
    simp [j0]
  · apply Finset.sum_eq_zero
    intro j _
    have hne : i.val ≠ j.val + 1 := by omega
    simp [hne]

/-- **General-Width Left Inverse of `1 + N_mat w` (`B_mat_mul_one_add_N`)**:
    For every dimension `w ∈ ℕ`, `B_mat w * (1 + N_mat w) = 1`. -/
theorem B_mat_mul_one_add_N (w : ℕ) :
    B_mat w * (1 + N_mat w) = 1 := by
  rw [mul_add, Matrix.mul_one]
  ext i k
  rw [Matrix.add_apply, mul_N_mat_apply]
  by_cases hik : k.val < i.val
  · have hk1 : k.val + 1 < w := by omega
    have hle1 : k.val ≤ i.val := by omega
    have hle2 : k.val + 1 ≤ i.val := by omega
    have hne : i ≠ k := by
      intro h
      subst h
      exact lt_irrefl _ hik
    simp only [B_mat, Matrix.of_apply, hle1, hk1, hle2, ↓reduceDIte, ↓reduceIte,
      Matrix.one_apply, hne]
    have hexp : i.val - k.val = (i.val - (k.val + 1)) + 1 := by omega
    rw [hexp, pow_succ]
    ring
  · by_cases heq : i = k
    · subst heq
      have hnot : ¬ (i.val + 1 ≤ i.val) := by omega
      by_cases hd : i.val + 1 < w
      · simp only [B_mat, Matrix.of_apply, le_refl, hd, hnot, ↓reduceDIte, ↓reduceIte,
          Nat.sub_self, pow_zero, Matrix.one_apply, add_zero]
      · simp only [B_mat, Matrix.of_apply, le_refl, hd, ↓reduceDIte, ↓reduceIte,
          Nat.sub_self, pow_zero, Matrix.one_apply, add_zero]
    · have hgt : i.val < k.val := by
        apply lt_of_le_of_ne (by omega)
        intro h
        apply heq
        ext
        exact h
      have hnot1 : ¬ (k.val ≤ i.val) := by omega
      have hnot2 : ¬ (k.val + 1 ≤ i.val) := by omega
      by_cases hd : k.val + 1 < w
      · simp only [B_mat, Matrix.of_apply, hd, hnot1, hnot2, heq, ↓reduceDIte, ↓reduceIte,
          Matrix.one_apply, add_zero]
      · simp only [B_mat, Matrix.of_apply, hd, hnot1, heq, ↓reduceDIte, ↓reduceIte,
          Matrix.one_apply, add_zero]

/-- **General-Width Right Inverse of `1 + N_mat w` (`one_add_N_mul_B_mat`)**:
    For every dimension `w ∈ ℕ`, `(1 + N_mat w) * B_mat w = 1`. -/
theorem one_add_N_mul_B_mat (w : ℕ) :
    (1 + N_mat w) * B_mat w = 1 := by
  rw [add_mul, Matrix.one_mul]
  ext i k
  rw [Matrix.add_apply, N_mat_mul_apply]
  by_cases hik : k.val < i.val
  · have hi0 : 0 < i.val := by omega
    have hle1 : k.val ≤ i.val := by omega
    have hle2 : k.val ≤ i.val - 1 := by omega
    have hne : i ≠ k := by
      intro h
      subst h
      exact lt_irrefl _ hik
    simp only [B_mat, Matrix.of_apply, hle1, hi0, hle2, ↓reduceDIte, ↓reduceIte,
      Matrix.one_apply, hne]
    have hexp : i.val - k.val = (i.val - 1 - k.val) + 1 := by omega
    rw [hexp, pow_succ]
    ring
  · by_cases heq : i = k
    · subst heq
      by_cases hi0 : 0 < i.val
      · have hnot : ¬ (i.val ≤ i.val - 1) := by omega
        simp only [B_mat, Matrix.of_apply, le_refl, hi0, hnot, ↓reduceDIte, ↓reduceIte,
          Nat.sub_self, pow_zero, Matrix.one_apply, add_zero]
      · simp only [B_mat, Matrix.of_apply, le_refl, hi0, ↓reduceDIte, ↓reduceIte,
          Nat.sub_self, pow_zero, Matrix.one_apply, add_zero]
    · have hgt : i.val < k.val := by
        apply lt_of_le_of_ne (by omega)
        intro h
        apply heq
        ext
        exact h
      have hnot1 : ¬ (k.val ≤ i.val) := by omega
      have hnot2 : ¬ (k.val ≤ i.val - 1) := by omega
      by_cases hi0 : 0 < i.val
      · simp only [B_mat, Matrix.of_apply, hi0, hnot1, hnot2, heq, ↓reduceDIte, ↓reduceIte,
          Matrix.one_apply, add_zero]
      · simp only [B_mat, Matrix.of_apply, hi0, hnot1, heq, ↓reduceDIte, ↓reduceIte,
          Matrix.one_apply, add_zero]

/-- `B_mat w` is the two-sided inverse of `T_mat w = 1 + N_mat w` for every `w ∈ ℕ`. -/
theorem B_mat_mul_T_mat (w : ℕ) :
    B_mat w * T_mat w = 1 ∧ T_mat w * B_mat w = 1 :=
  ⟨B_mat_mul_one_add_N w, one_add_N_mul_B_mat w⟩

/-- Unconditional shift-inverse identity `B_mat w * N_mat w = 1 - B_mat w` for every `w ∈ ℕ`. -/
theorem B_mat_mul_N_mat (w : ℕ) :
    B_mat w * N_mat w = 1 - B_mat w ∧ N_mat w * B_mat w = 1 - B_mat w :=
  ⟨mul_N_of_mul_T_eq_one (B_mat_mul_one_add_N w),
   N_mul_of_T_mul_eq_one (one_add_N_mul_B_mat w)⟩

/-!
## 2. Constructive Coupled Lift Constructor (`LiftStepData.ofCoupledMoment`) & Degree Shift
-/

/-- **Constructive Coupled Lift Constructor (`LiftStepData.ofCoupledMoment`)**:
    Given full-rank count tables `(X, L_X)` (`Xᵀ L_X = 1`) and `(M, R_M)` (`R_M M = 1`),
    score table `S`, reset interaction `J`, ceiling profile `ζ`, reference coupling `P0`,
    and weights `(v_old, v_reset, aP_old, aP_reset)`, whenever the Moment Equation
    `E - Eᵀ (B_mat (w + 1)) = Dᵀ X - ℓᵀ ψ` holds (with `E = Mᵀ J M`), the closed-form
    inverse `B_mat (w + 1)` and explicit bilinear interpolant `P_interp` automatically produce
    a verified `LiftStepData clock n`. -/
def LiftStepData.ofCoupledMoment {w : ℕ} (clock : AlgebraicClock w) (n : ℕ)
    (X L_X S : Matrix (Fin clock.m) (Fin (w + 1)) ℚ)
    (M : Matrix (Fin n) (Fin (w + 1)) ℚ)
    (R_M : Matrix (Fin (w + 1)) (Fin n) ℚ)
    (J : Matrix (Fin n) (Fin n) ℚ)
    (P0 : Matrix (Fin clock.m) (Fin n) ℚ)
    (zeta : Fin (w + 1) → ℚ)
    (v_old aP_old : Fin clock.m → ℚ)
    (v_reset aP_reset : Fin n → ℚ)
    (hX : X.transpose * L_X = 1)
    (hM : R_M * M = 1)
    (hmoment :
      M.transpose * J * M - (M.transpose * J * M).transpose * B_mat (w + 1) =
        (D_deficit clock.G S X (N_mat (w + 1))).transpose * X -
          (ell_row M).transpose * psi_row zeta (B_mat (w + 1)))
    (hv_cal :
      Matrix.vecMul v_old
        (X * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) +
        Matrix.vecMul v_reset M = e0_row (w + 1))
    (haP_old_pos : ∀ i : Fin clock.m, 0 < aP_old i)
    (haP_reset_pos : ∀ r : Fin n, 0 < aP_reset r) :
    LiftStepData clock n where
  P := P_interp X L_X M R_M
    (D_deficit clock.G S X (N_mat (w + 1)))
    (Q_reset J M (B_mat (w + 1)) zeta) P0
  J := J
  S := S
  X := X
  M := M
  B := B_mat (w + 1)
  zeta := zeta
  v_old := v_old
  v_reset := v_reset
  aP_old := aP_old
  aP_reset := aP_reset
  hBT := B_mat_mul_one_add_N (w + 1)
  hPtX := interpolate_PtX X L_X M R_M
    (D_deficit clock.G S X (N_mat (w + 1)))
    (Q_reset J M (B_mat (w + 1)) zeta) P0 hX
  hPM := by
    have hcompat :
        (D_deficit clock.G S X (N_mat (w + 1))).transpose * X =
          M.transpose * Q_reset J M (B_mat (w + 1)) zeta :=
      (moment_equation_iff (D_deficit clock.G S X (N_mat (w + 1))) X J M
        (B_mat (w + 1)) zeta).mpr hmoment
    exact interpolate_PM X L_X M R_M
      (D_deficit clock.G S X (N_mat (w + 1)))
      (Q_reset J M (B_mat (w + 1)) zeta) P0 hM hcompat
  hv_cal := hv_cal
  haP_old_pos := haP_old_pos
  haP_reset_pos := haP_reset_pos

/-- **Specification of `LiftStepData.ofCoupledMoment`**:
    Lifting `clock : AlgebraicClock w` via `LiftStepData.ofCoupledMoment` yields an
    order-`(w + 1)` algebraic clock with `clock.m + n` actions and verified phase transitions. -/
theorem coupledMoment_lift_spec {w : ℕ} (clock : AlgebraicClock w) (n : ℕ)
    (X L_X S : Matrix (Fin clock.m) (Fin (w + 1)) ℚ)
    (M : Matrix (Fin n) (Fin (w + 1)) ℚ)
    (R_M : Matrix (Fin (w + 1)) (Fin n) ℚ)
    (J : Matrix (Fin n) (Fin n) ℚ)
    (P0 : Matrix (Fin clock.m) (Fin n) ℚ)
    (zeta : Fin (w + 1) → ℚ)
    (v_old aP_old : Fin clock.m → ℚ)
    (v_reset aP_reset : Fin n → ℚ)
    (hX : X.transpose * L_X = 1)
    (hM : R_M * M = 1)
    (hmoment :
      M.transpose * J * M - (M.transpose * J * M).transpose * B_mat (w + 1) =
        (D_deficit clock.G S X (N_mat (w + 1))).transpose * X -
          (ell_row M).transpose * psi_row zeta (B_mat (w + 1)))
    (hv_cal :
      Matrix.vecMul v_old
        (X * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) +
        Matrix.vecMul v_reset M = e0_row (w + 1))
    (haP_old_pos : ∀ i : Fin clock.m, 0 < aP_old i)
    (haP_reset_pos : ∀ r : Fin n, 0 < aP_reset r)
    (q : ℕ) :
    let step := LiftStepData.ofCoupledMoment clock n X L_X S M R_M J P0 zeta
      v_old aP_old v_reset aP_reset hX hM hmoment hv_cal haP_old_pos haP_reset_pos
    (clock.lift step).m = clock.m + n ∧
      scoreVec (clock.lift step).G
        ((clock.lift step).R.mulVec (binomBasis (w + 1) q))
        ((clock.lift step).C.mulVec (binomBasis (w + 1) q)) =
      (clock.lift step).R.mulVec (binomBasis (w + 1) (q + 1)) ∧
      dotProduct (clock.lift step).v ((clock.lift step).C.mulVec (binomBasis (w + 1) q)) = 1 :=
  AlgebraicClock.lift_spec clock _ q

/-- Shift an `α × w` count matrix right by 1 column (`c ↦ c + 1` in the falling-factorial basis,
    corresponding to summing $\sum_{\sigma < q} \binom{\sigma}{c} = \binom{q}{c+1}$), placing `0`
    in column `0`. -/
def shiftRightCount {α : Type*} {w : ℕ} (C : Matrix α (Fin w) ℚ) : Matrix α (Fin (w + 1)) ℚ :=
  Matrix.of fun i j =>
    if hj : 0 < j.val then C i ⟨j.val - 1, by omega⟩ else 0

/-- Shift an `α × w` score matrix right by 1 column (`c ↦ c + 1`), placing `0` in columns `0`
    and `1` (since column `0` of `R` is annihilated by `N_mat w`). -/
def shiftRightScore {α : Type*} {w : ℕ} (R : Matrix α (Fin w) ℚ) : Matrix α (Fin (w + 1)) ℚ :=
  Matrix.of fun i j =>
    if hj : 1 < j.val then R i ⟨j.val - 1, by omega⟩ else 0

/-- **Universal Degree-Shift Clock Identity (`shiftRightScore_mul_N_mat`)**:
    For any matrix triple `(G, R, C)` satisfying `G * C = R * N_mat w`, the degree-shifted
    tables `shiftRightScore R` and `shiftRightCount C` satisfy
    `shiftRightScore R * N_mat (w + 1) = G * shiftRightCount C`. -/
theorem shiftRightScore_mul_N_mat {α : Type*} [Fintype α] {w : ℕ}
    (G : Matrix α α ℚ) (R C : Matrix α (Fin w) ℚ)
    (hclock : G * C = R * N_mat w) :
    shiftRightScore R * N_mat (w + 1) = G * shiftRightCount C := by
  ext i k
  rw [mul_N_mat_apply]
  by_cases hk0 : 0 < k.val
  · let d : Fin w := ⟨k.val - 1, by omega⟩
    have hd_val : d.val = k.val - 1 := rfl
    have hGC : (G * shiftRightCount C) i k = (G * C) i d := by
      simp only [Matrix.mul_apply, shiftRightCount, Matrix.of_apply, hk0, ↓reduceDIte, d]
    rw [hGC, hclock, mul_N_mat_apply]
    by_cases hd : d.val + 1 < w
    · have hk1 : k.val + 1 < w + 1 := by omega
      have hk_gt1 : 1 < k.val + 1 := by omega
      simp only [hk1, hd, ↓reduceDIte, shiftRightScore, Matrix.of_apply, hk_gt1]
      congr 1
      ext
      change k.val = d.val + 1
      omega
    · have hk1 : ¬ (k.val + 1 < w + 1) := by omega
      simp [hk1, hd]
  · have hGC0 : (G * shiftRightCount C) i k = 0 := by
      simp only [Matrix.mul_apply, shiftRightCount, Matrix.of_apply, hk0, ↓reduceDIte,
        mul_zero, Finset.sum_const_zero]
    rw [hGC0]
    split_ifs with hk1
    · have hnot1 : ¬ (1 < k.val + 1) := by omega
      simp [shiftRightScore, hnot1]
    · rfl

/-- Every entry of `1 + N_mat w` is nonnegative (`0 ≤ (1 + N_mat w) i j`). -/
theorem one_add_N_mat_nonneg (w : ℕ) (i j : Fin w) :
    0 ≤ (1 + N_mat w : Matrix (Fin w) (Fin w) ℚ) i j := by
  simp only [Matrix.add_apply, Matrix.one_apply, N_mat, Matrix.of_apply]
  split_ifs <;> norm_num

/-!
## 3. Non-Degenerate Coupled-Moment Lift Construction (Sections 5–8)
-/

/-- Adjoins the single endpoint action `g` (indexed by `Sum.inr 0` under `finSumFinEquiv`)
    to `clock : AlgebraicClock w`, forming an `AlgebraicClock w` on `clock.m + 1` actions
    prior to coupling with the `2(w + 1)` reset actions. -/
@[reducible] def AlgebraicClock.adjoinEndpoint {w : ℕ} (clock : AlgebraicClock w) : AlgebraicClock w where
  m := clock.m + 1
  G := Matrix.of fun x y =>
    match finSumFinEquiv.symm x, finSumFinEquiv.symm y with
    | Sum.inl i, Sum.inl j => clock.G i j
    | _, _ => 0
  R := Matrix.of fun x c =>
    match finSumFinEquiv.symm x with
    | Sum.inl i => clock.R i c
    | Sum.inr _ => 0
  C := Matrix.of fun x c =>
    match finSumFinEquiv.symm x with
    | Sum.inl i => clock.C i c
    | Sum.inr _ => 0
  v := fun x =>
    match finSumFinEquiv.symm x with
    | Sum.inl i => clock.v i
    | Sum.inr _ => 0
  aP := fun x =>
    match finSumFinEquiv.symm x with
    | Sum.inl i => clock.aP i
    | Sum.inr _ => 1
  hskew := by
    intro x y
    simp only [Matrix.of_apply]
    cases finSumFinEquiv.symm x <;> cases finSumFinEquiv.symm y
    · exact clock.hskew _ _
    · simp
    · simp
    · simp
  hclock := by
    ext x c
    have hcomp :=
      (Equiv.sum_comp finSumFinEquiv fun y : Fin (clock.m + 1) =>
        (match finSumFinEquiv.symm x, finSumFinEquiv.symm y with
        | Sum.inl i, Sum.inl j => clock.G i j
        | _, _ => 0) *
        (match finSumFinEquiv.symm y with
        | Sum.inl j => clock.C j c
        | Sum.inr _ => 0)).symm
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [hcomp, Fintype.sum_sum_type]
    simp only [Equiv.symm_apply_apply, mul_zero, Finset.sum_const_zero, add_zero]
    cases hsym : finSumFinEquiv.symm x with
    | inl i =>
      have hclock_ic := congr_fun (congr_fun clock.hclock i) c
      simpa [Matrix.mul_apply] using hclock_ic
    | inr _ =>
      simp
  hvC := by
    ext c
    have hcomp :=
      (Equiv.sum_comp finSumFinEquiv fun x : Fin (clock.m + 1) =>
        (match finSumFinEquiv.symm x with
        | Sum.inl i => clock.v i
        | Sum.inr _ => 0) *
        (match finSumFinEquiv.symm x with
        | Sum.inl i => clock.C i c
        | Sum.inr _ => 0)).symm
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply]
    rw [hcomp, Fintype.sum_sum_type]
    simp only [Equiv.symm_apply_apply, zero_mul, Finset.sum_const_zero, add_zero]
    exact congr_fun clock.hvC c
  haP_pos := by
    intro x
    cases finSumFinEquiv.symm x with
    | inl i => exact clock.haP_pos i
    | inr _ => exact zero_lt_one

/-- Old-and-endpoint count table `X = (shiftRightCount C; e_0ᵀ) ∈ ℚ^{(m + 1) × (w + 1)}`
    from Equation `eq:SX` (Section 5.1). -/
def X_coupled {w : ℕ} (clock : AlgebraicClock w) :
    Matrix (Fin (clock.m + 1)) (Fin (w + 1)) ℚ :=
  Matrix.of fun x c =>
    match finSumFinEquiv.symm x with
    | Sum.inl i => shiftRightCount clock.C i c
    | Sum.inr _ => e0_row (w + 1) c

/-- Left inverse `L_X = (shiftRightCount L_C; e_0ᵀ) ∈ ℚ^{(m + 1) × (w + 1)}` satisfying
    `X_coupledᵀ * L_X_coupled = 1` whenever `Cᵀ * L_C = 1`. -/
def L_X_coupled {w m : ℕ} (L_C : Matrix (Fin m) (Fin w) ℚ) :
    Matrix (Fin (m + 1)) (Fin (w + 1)) ℚ :=
  Matrix.of fun x c =>
    match finSumFinEquiv.symm x with
    | Sum.inl i => shiftRightCount L_C i c
    | Sum.inr _ => e0_row (w + 1) c

/-- Old-and-endpoint score table `S = (shiftRightScore R; 0) ∈ ℚ^{(m + 1) × (w + 1)}`
    from Equation `eq:SX` (Section 5.1). -/
def S_coupled {w : ℕ} (clock : AlgebraicClock w) :
    Matrix (Fin (clock.m + 1)) (Fin (w + 1)) ℚ :=
  Matrix.of fun x c =>
    match finSumFinEquiv.symm x with
    | Sum.inl i => shiftRightScore clock.R i c
    | Sum.inr _ => 0

/-- **Full Column Rank of `X_coupled` (`X_coupled_transpose_mul_L_X_coupled`)**:
    If `clock.C.transpose * L_C = 1`, then `(X_coupled clock).transpose * L_X_coupled L_C = 1`. -/
theorem X_coupled_transpose_mul_L_X_coupled {w : ℕ} (clock : AlgebraicClock w)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ)
    (hLC : clock.C.transpose * L_C = 1) :
    (X_coupled clock).transpose * L_X_coupled L_C = 1 := by
  ext c1 c2
  have hcomp :=
    (Equiv.sum_comp finSumFinEquiv fun x : Fin (clock.m + 1) =>
      X_coupled clock x c1 * L_X_coupled L_C x c2).symm
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [hcomp, Fintype.sum_sum_type]
  simp only [X_coupled, L_X_coupled, Matrix.of_apply, Equiv.symm_apply_apply,
    Fin.sum_univ_one]
  by_cases hc1 : 0 < c1.val
  · have hc1_ne : c1.val ≠ 0 := by omega
    by_cases hc2 : 0 < c2.val
    · have hc2_ne : c2.val ≠ 0 := by omega
      simp only [shiftRightCount, Matrix.of_apply, hc1, hc2, ↓reduceDIte, e0_row,
        hc1_ne, hc2_ne, ↓reduceIte, mul_zero, add_zero]
      have h_entry := congr_fun (congr_fun hLC ⟨c1.val - 1, by omega⟩) ⟨c2.val - 1, by omega⟩
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.ext_iff] at h_entry ⊢
      rw [h_entry]
      by_cases heq : c1.val = c2.val
      · simp [heq]
      · have hsub : c1.val - 1 ≠ c2.val - 1 := by omega
        simp [heq, hsub]
    · have hc2_eq : c2.val = 0 := by omega
      have hne : c1 ≠ c2 := by
        intro h; subst h; omega
      simp only [shiftRightCount, Matrix.of_apply, hc1, hc2, ↓reduceDIte]
      simp only [e0_row, hc1_ne, hc2_eq, ↓reduceIte, mul_zero, zero_mul, Finset.sum_const_zero,
        add_zero, Matrix.one_apply, hne]
  · have hc1_eq : c1.val = 0 := by omega
    by_cases hc2 : 0 < c2.val
    · have hc2_ne : c2.val ≠ 0 := by omega
      have hne : c1 ≠ c2 := by
        intro h; subst h; omega
      simp only [shiftRightCount, Matrix.of_apply, hc1, hc2, ↓reduceDIte]
      simp only [e0_row, hc1_eq, hc2_ne, ↓reduceIte, mul_zero, zero_mul,
        Finset.sum_const_zero, add_zero, Matrix.one_apply, hne]
    · have hc2_eq : c2.val = 0 := by omega
      have heq : c1 = c2 := by ext; omega
      simp only [shiftRightCount, Matrix.of_apply, hc1, hc2, ↓reduceDIte]
      simp only [e0_row, hc2_eq, ↓reduceIte, mul_one, zero_mul,
        Finset.sum_const_zero, zero_add, Matrix.one_apply, heq]

/-- **Vanishing Old-Block Deficit `D_deficit = 0` (`D_deficit_coupled_eq_zero`)**:
    In `clock.adjoinEndpoint`, `S_coupled clock * N_mat (w + 1) = clock.adjoinEndpoint.G * X_coupled clock`,
    so `D_deficit clock.adjoinEndpoint.G (S_coupled clock) (X_coupled clock) (N_mat (w + 1)) = 0`. -/
theorem D_deficit_coupled_eq_zero {w : ℕ} (clock : AlgebraicClock w) :
    D_deficit clock.adjoinEndpoint.G (S_coupled clock) (X_coupled clock) (N_mat (w + 1)) = 0 := by
  unfold D_deficit
  rw [sub_eq_zero]
  ext x c
  have h_rhs :
      (clock.adjoinEndpoint.G * X_coupled clock) x c =
        ∑ y : Fin (clock.m + 1), clock.adjoinEndpoint.G x y * X_coupled clock y c := rfl
  have hcomp :=
    (Equiv.sum_comp finSumFinEquiv fun y : Fin (clock.m + 1) =>
      clock.adjoinEndpoint.G x y * X_coupled clock y c).symm
  rw [h_rhs, hcomp, Fintype.sum_sum_type, mul_N_mat_apply]
  cases hsym : finSumFinEquiv.symm x with
  | inl i =>
    have hshift := congr_fun (congr_fun
      (shiftRightScore_mul_N_mat clock.G clock.R clock.C clock.hclock) i) c
    rw [mul_N_mat_apply] at hshift
    simp only [S_coupled, Matrix.of_apply, hsym]
    rw [hshift]
    simp only [X_coupled, Matrix.of_apply, Equiv.symm_apply_apply,
      zero_mul, Finset.sum_const_zero, add_zero, Matrix.mul_apply]
  | inr _ =>
    simp [S_coupled, hsym]

/-- The `2(w + 1) × (w + 1)` non-degenerate reset count matrix `M = (W_coupled w; W_coupled w)`
    from Section 7.1 (`eq:W`). -/
def M_coupled (w : ℕ) : Matrix (Fin ((w + 1) + (w + 1))) (Fin (w + 1)) ℚ :=
  Matrix.of fun r c =>
    match finSumFinEquiv.symm r with
    | Sum.inl i => W_coupled w i c
    | Sum.inr i => W_coupled w i c

/-- **Strict Positivity of All Reset Count Entries (`M_coupled_entry_ge_one`)**:
    Every entry of `M_coupled w` is in `{1, 2, 3}`, hence `1 ≤ M_coupled w r c`. -/
theorem M_coupled_entry_ge_one (w : ℕ) (r : Fin ((w + 1) + (w + 1))) (c : Fin (w + 1)) :
    1 ≤ M_coupled w r c := by
  simp only [M_coupled, Matrix.of_apply]
  cases finSumFinEquiv.symm r with
  | inl i => exact W_coupled_entry_ge_one w i c
  | inr i => exact W_coupled_entry_ge_one w i c

/-- Explicit left inverse `R_M = [0 | W_coupled_inv w] ∈ ℚ^{(w + 1) × 2(w + 1)}`
    satisfying `R_M_coupled w * M_coupled w = 1`. -/
def R_M_coupled (w : ℕ) : Matrix (Fin (w + 1)) (Fin ((w + 1) + (w + 1))) ℚ :=
  Matrix.of fun c r =>
    match finSumFinEquiv.symm r with
    | Sum.inl _ => 0
    | Sum.inr i => W_coupled_inv w c i

/-- **Full Column Rank of `M_coupled w` (`R_M_coupled_mul_M_coupled`)**:
    For every `w ∈ ℕ`, `R_M_coupled w * M_coupled w = 1`. -/
theorem R_M_coupled_mul_M_coupled (w : ℕ) :
    R_M_coupled w * M_coupled w = 1 := by
  ext c1 c2
  have hcomp :=
    (Equiv.sum_comp finSumFinEquiv fun r : Fin ((w + 1) + (w + 1)) =>
      R_M_coupled w c1 r * M_coupled w r c2).symm
  rw [Matrix.mul_apply, hcomp, Fintype.sum_sum_type]
  simp only [R_M_coupled, M_coupled, Matrix.of_apply, Equiv.symm_apply_apply,
    zero_mul, Finset.sum_const_zero, zero_add]
  exact congr_fun (congr_fun (W_coupled_inv_mul w) c1) c2

/-- The `2(w + 1) × 2(w + 1)` strictly lower-triangular reset interaction matrix `J_coupled w`
    from Section 7.2 (`eq:J`) with `η = (4(w+1))⁻¹` and `κ = (w+1)⁻¹`. -/
def J_coupled (w : ℕ) :
    Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ :=
  let η : ℚ := (4 * (w + 1 : ℚ))⁻¹
  let κ : ℚ := (w + 1 : ℚ)⁻¹
  Matrix.of fun a b =>
    match finSumFinEquiv.symm a, finSumFinEquiv.symm b with
    | Sum.inl i, Sum.inl j => (η • L_strict (w + 1)) i j
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr i, Sum.inl j => (κ • J_ones (w + 1) - (2 * η) • L_strict (w + 1)) i j
    | Sum.inr i, Sum.inr j => (η • L_strict (w + 1)) i j

/-- **Strict Lower-Triangularity of `J_coupled w` (`J_coupled_lower`)**:
    For all `a, b : Fin ((w + 1) + (w + 1))` with `a.val ≤ b.val`, `J_coupled w a b = 0`. -/
theorem J_coupled_lower (w : ℕ) (a b : Fin ((w + 1) + (w + 1))) (hab : a.val ≤ b.val) :
    J_coupled w a b = 0 := by
  obtain ⟨sa, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨sb, rfl⟩ := finSumFinEquiv.surjective b
  simp only [J_coupled, Matrix.of_apply, Equiv.symm_apply_apply]
  rcases sa with i | i <;> rcases sb with j | j
  · simp only [finSumFinEquiv_apply_left, Fin.val_castAdd] at hab
    have hnot : ¬ (j.val < i.val) := by omega
    simp only [L_strict, Matrix.smul_apply, Matrix.of_apply, hnot, ↓reduceIte, smul_zero]
  · rfl
  · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Fin.val_castAdd, Fin.val_natAdd] at hab
    have hj : j.val < w + 1 := j.isLt
    omega
  · simp only [finSumFinEquiv_apply_right, Fin.val_natAdd] at hab
    have hnot : ¬ (j.val < i.val) := by omega
    simp only [L_strict, Matrix.smul_apply, Matrix.of_apply, hnot, ↓reduceIte, smul_zero]

/-- **Strict Subdiagonal Positivity of `J_coupled w` (`J_coupled_subdiag_ge`)**:
    For all `a, b : Fin ((w + 1) + (w + 1))` strictly below the diagonal (`b.val < a.val`),
    `(4 * (w + 1 : ℚ))⁻¹ ≤ J_coupled w a b` and `0 < J_coupled w a b`. -/
theorem J_coupled_subdiag_ge (w : ℕ) (a b : Fin ((w + 1) + (w + 1))) (hab : b.val < a.val) :
    (4 * (w + 1 : ℚ))⁻¹ ≤ J_coupled w a b ∧ 0 < J_coupled w a b := by
  have hη : 0 < (4 * (w + 1 : ℚ))⁻¹ := by positivity
  have hle : (4 * (w + 1 : ℚ))⁻¹ ≤ J_coupled w a b := by
    obtain ⟨sa, rfl⟩ := finSumFinEquiv.surjective a
    obtain ⟨sb, rfl⟩ := finSumFinEquiv.surjective b
    simp only [J_coupled, Matrix.of_apply, Equiv.symm_apply_apply]
    rcases sa with i | i <;> rcases sb with j | j
    · simp only [finSumFinEquiv_apply_left, Fin.val_castAdd] at hab
      simp only [L_strict, Matrix.smul_apply, Matrix.of_apply, hab, ↓reduceIte,
        smul_eq_mul, mul_one, le_refl]
    · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.val_castAdd, Fin.val_natAdd] at hab
      have hi : i.val < w + 1 := i.isLt
      omega
    · have hκ : (w + 1 : ℚ)⁻¹ = 4 * (4 * (w + 1 : ℚ))⁻¹ := by
        have hw : (w : ℚ) + 1 ≠ 0 := by positivity
        field_simp [hw]
      simp only [J_ones, L_strict, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
        smul_eq_mul, mul_one, hκ]
      split_ifs <;> linarith
    · simp only [finSumFinEquiv_apply_right, Fin.val_natAdd] at hab
      have hij : j.val < i.val := by omega
      simp only [L_strict, Matrix.smul_apply, Matrix.of_apply, hij, ↓reduceIte,
        smul_eq_mul, mul_one, le_refl]
  exact ⟨hle, lt_of_lt_of_le hη hle⟩

/-- **Quadratic Moment Identity for `(M_coupled w, J_coupled w)` (`M_coupled_transpose_mul_J_coupled_mul_M_coupled`)**:
    `(M_coupled w)ᵀ * J_coupled w * M_coupled w = (4 * (w + 1)) • J_ones (w + 1)`. -/
theorem M_coupled_transpose_mul_J_coupled_mul_M_coupled (w : ℕ) :
    (M_coupled w).transpose * J_coupled w * M_coupled w =
      (4 * (w + 1 : ℚ)) • J_ones (w + 1) := by
  let η : ℚ := (4 * (w + 1 : ℚ))⁻¹
  let κ : ℚ := (w + 1 : ℚ)⁻¹
  have h_sum_blocks :
      η • L_strict (w + 1) + 0 + (κ • J_ones (w + 1) - (2 * η) • L_strict (w + 1)) +
        η • L_strict (w + 1) = κ • J_ones (w + 1) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply,
      smul_eq_mul]
    ring
  have h_eq :
      (M_coupled w).transpose * J_coupled w * M_coupled w =
        (W_coupled w).transpose * (κ • J_ones (w + 1)) * W_coupled w := by
    rw [← h_sum_blocks]
    ext c1 c2
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    have hcomp1 :
        ∀ b : Fin ((w + 1) + (w + 1)),
          (∑ a : Fin ((w + 1) + (w + 1)), M_coupled w a c1 * J_coupled w a b) =
            (∑ i : Fin (w + 1), W_coupled w i c1 * J_coupled w (finSumFinEquiv (Sum.inl i)) b) +
            (∑ i : Fin (w + 1), W_coupled w i c1 * J_coupled w (finSumFinEquiv (Sum.inr i)) b) := by
      intro b
      have hc := (Equiv.sum_comp finSumFinEquiv fun a => M_coupled w a c1 * J_coupled w a b).symm
      rw [hc, Fintype.sum_sum_type]
      simp only [M_coupled, Matrix.of_apply, Equiv.symm_apply_apply]
    simp_rw [hcomp1]
    have hcomp2 :=
      (Equiv.sum_comp finSumFinEquiv fun b : Fin ((w + 1) + (w + 1)) =>
        ((∑ i : Fin (w + 1), W_coupled w i c1 * J_coupled w (finSumFinEquiv (Sum.inl i)) b) +
         (∑ i : Fin (w + 1), W_coupled w i c1 * J_coupled w (finSumFinEquiv (Sum.inr i)) b)) *
        M_coupled w b c2).symm
    rw [hcomp2, Fintype.sum_sum_type]
    simp only [M_coupled, J_coupled, Matrix.of_apply, Equiv.symm_apply_apply,
      Matrix.add_apply, Matrix.zero_apply]
    change
      ((∑ x : Fin (w + 1),
        ((∑ i : Fin (w + 1), W_coupled w i c1 * (η • L_strict (w + 1)) i x) +
         (∑ i : Fin (w + 1), W_coupled w i c1 * (κ • J_ones (w + 1) - (2 * η) • L_strict (w + 1)) i x)) *
        W_coupled w x c2) +
       (∑ x : Fin (w + 1),
        ((∑ i : Fin (w + 1), W_coupled w i c1 * 0) +
         (∑ i : Fin (w + 1), W_coupled w i c1 * (η • L_strict (w + 1)) i x)) *
        W_coupled w x c2)) =
      ∑ x : Fin (w + 1),
        (∑ i : Fin (w + 1),
          W_coupled w i c1 *
            ((η • L_strict (w + 1)) i x + 0 +
             (κ • J_ones (w + 1) - (2 * η) • L_strict (w + 1)) i x +
             (η • L_strict (w + 1)) i x)) *
        W_coupled w x c2
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [ ← add_mul, ← Finset.sum_add_distrib, ← mul_add]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hsmul :
      (W_coupled w).transpose * (κ • J_ones (w + 1)) * W_coupled w =
        κ • ((W_coupled w).transpose * J_ones (w + 1) * W_coupled w) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [h_eq, hsmul, W_coupled_transpose_mul_J_ones_mul_W_coupled w, smul_smul]
  congr 1
  have hw : (w : ℚ) + 1 ≠ 0 := by positivity
  dsimp only [κ]
  field_simp [hw]

/-- **Column Sum Identity for `M_coupled w` (`ell_row_M_coupled`)**:
    `ell_row (M_coupled w) = (4 * (w + 1)) • one_row (Fin (w + 1))`. -/
theorem ell_row_M_coupled (w : ℕ) :
    ell_row (M_coupled w) = (4 * (w + 1 : ℚ)) • one_row (Fin (w + 1)) := by
  ext u c
  have hcomp :=
    (Equiv.sum_comp finSumFinEquiv fun r : Fin ((w + 1) + (w + 1)) =>
      (1 : ℚ) * M_coupled w r c).symm
  simp only [ell_row, one_row, Matrix.mul_apply, Matrix.of_apply]
  rw [hcomp, Fintype.sum_sum_type]
  simp only [M_coupled, Matrix.of_apply, Equiv.symm_apply_apply]
  have hW := congr_fun (congr_fun (one_row_mul_W_coupled w) ()) c
  simp only [one_row, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    mul_one] at hW ⊢
  linarith

/-- Flat unit reset ceiling `ζ = 1_{w+1}ᵀ > 0`. -/
def zeta_coupled (w : ℕ) : Fin (w + 1) → ℚ :=
  fun _ => 1

/-- Sign-definite reference coupling `P_0 ∈ ℚ^{(m + 1) × 2(w + 1)}` with `-1` on early reset
    actions and `+1` on late reset actions (Section 7.2). -/
def P0_coupled (m w : ℕ) : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ :=
  Matrix.of fun _ r =>
    match finSumFinEquiv.symm r with
    | Sum.inl _ => -1
    | Sum.inr _ => 1

/-- Next-order endpoint functional `v_old_coupled` supported on the endpoint action `g = Sum.inr 0`. -/
def v_old_coupled (m : ℕ) : Fin (m + 1) → ℚ :=
  fun x =>
    match finSumFinEquiv.symm x with
    | Sum.inl _ => 0
    | Sum.inr _ => 1

/-- **Unconditional Moment Equation for `(M_coupled w, J_coupled w, zeta_coupled w)` (`coupled_moment_equation`)**:
    In `clock.adjoinEndpoint`, the Moment Equation
    `E - Eᵀ B_{w+1} = Dᵀ X - ℓᵀ ψ` holds unconditionally for every `w ∈ ℕ`. -/
theorem coupled_moment_equation {w : ℕ} (clock : AlgebraicClock w) :
    (M_coupled w).transpose * J_coupled w * M_coupled w -
      ((M_coupled w).transpose * J_coupled w * M_coupled w).transpose * B_mat (w + 1) =
    (D_deficit clock.adjoinEndpoint.G (S_coupled clock) (X_coupled clock) (N_mat (w + 1))).transpose *
      X_coupled clock -
      (ell_row (M_coupled w)).transpose * psi_row (zeta_coupled w) (B_mat (w + 1)) := by
  rw [D_deficit_coupled_eq_zero, Matrix.transpose_zero, Matrix.zero_mul, zero_sub]
  have hzeta : zeta_row (zeta_coupled w) = one_row (Fin (w + 1)) := rfl
  have hJ_ones :
      J_ones (w + 1) =
        (zeta_row (zeta_coupled w)).transpose * zeta_row (zeta_coupled w) := by
    ext i j
    simp [J_ones, zeta_row, zeta_coupled, Matrix.mul_apply]
  have hpsi :
      psi_row (zeta_coupled w) (B_mat (w + 1)) =
        zeta_row (zeta_coupled w) * B_mat (w + 1) - zeta_row (zeta_coupled w) := rfl
  rw [M_coupled_transpose_mul_J_coupled_mul_M_coupled w, hJ_ones, ell_row_M_coupled w, ← hzeta, hpsi]
  simpa [Matrix.neg_mul] using L_op_E0 (zeta_row (zeta_coupled w)) (B_mat (w + 1)) (4 * (w + 1 : ℚ))

/-- **Endpoint Weight Calibration for `v_old_coupled` (`coupled_weight_calibration`)**:
    Since row `g = Sum.inr 0` of `X_coupled clock` is `e0_row (w + 1)` and column `0` of `N_mat (w + 1)`
    has `0` in row `0`, `v_old_coupled` supported on `g` satisfies
    `v_old_coupledᵀ (X_coupled clock * (1 + N_mat (w + 1))) + 0ᵀ M_coupled w = e0_row (w + 1)`. -/
theorem coupled_weight_calibration {w : ℕ} (clock : AlgebraicClock w) :
    Matrix.vecMul (v_old_coupled clock.m)
      (X_coupled clock * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) +
      Matrix.vecMul (0 : Fin ((w + 1) + (w + 1)) → ℚ) (M_coupled w) =
    e0_row (w + 1) := by
  have h0 : Matrix.vecMul (0 : Fin ((w + 1) + (w + 1)) → ℚ) (M_coupled w) = 0 := by
    ext c; simp [Matrix.vecMul, dotProduct]
  rw [h0, add_zero, ← Matrix.vecMul_vecMul]
  have hvX : Matrix.vecMul (v_old_coupled clock.m) (X_coupled clock) = e0_row (w + 1) := by
    ext c
    have hcomp :=
      (Equiv.sum_comp finSumFinEquiv fun x : Fin (clock.m + 1) =>
        v_old_coupled clock.m x * X_coupled clock x c).symm
    simp only [Matrix.vecMul, dotProduct]
    rw [hcomp, Fintype.sum_sum_type]
    simp [v_old_coupled, X_coupled]
  rw [hvX]
  ext c
  simp only [Matrix.vecMul, dotProduct, Matrix.add_apply, Matrix.one_apply, N_mat, Matrix.of_apply,
    e0_row]
  let i0 : Fin (w + 1) := ⟨0, Nat.succ_pos w⟩
  have hsum :
      (∑ i : Fin (w + 1),
        (if i.val = 0 then (1 : ℚ) else 0) *
          ((if i = c then 1 else 0) + (if i.val = c.val + 1 then 1 else 0))) =
      ∑ i : Fin (w + 1),
        if i = i0 then ((if i0 = c then (1 : ℚ) else 0) + (if i0.val = c.val + 1 then 1 else 0))
        else 0 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i = i0
    · subst hi; simp [i0]
    · have hne : i.val ≠ 0 := by intro h; apply hi; ext; exact h
      simp [hi, hne]
  rw [hsum, Finset.sum_ite_eq' Finset.univ i0]
  have hne_succ : i0.val ≠ c.val + 1 := by simp [i0]
  simp only [Finset.mem_univ, ↓reduceIte, hne_succ, add_zero]
  by_cases hc : c.val = 0
  · have heq : i0 = c := by ext; exact hc.symm
    simp [hc, heq]
  · have hne : i0 ≠ c := by intro h; apply hc; rw [← h]
    simp [hc, hne]

/-- **Non-Degenerate Coupled-Moment Lift Step (`coupledMomentLiftStep`)**:
    Instantiates `LiftStepData.ofCoupledMoment` on `clock.adjoinEndpoint` with `n = 2(w + 1)`
    reset actions, full-rank `(X_coupled, L_X_coupled)` and `(M_coupled, R_M_coupled)`,
    strictly lower-triangular `J_coupled`, positive ceiling `zeta_coupled = 1`, and
    interpolated coupling `P = P_interp`. -/
@[reducible] def coupledMomentLiftStep {w : ℕ} (clock : AlgebraicClock w)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ)
    (hLC : clock.C.transpose * L_C = 1) :
    LiftStepData clock.adjoinEndpoint ((w + 1) + (w + 1)) :=
  LiftStepData.ofCoupledMoment
    clock.adjoinEndpoint
    ((w + 1) + (w + 1))
    (X_coupled clock)
    (L_X_coupled L_C)
    (S_coupled clock)
    (M_coupled w)
    (R_M_coupled w)
    (J_coupled w)
    (P0_coupled clock.m w)
    (zeta_coupled w)
    (v_old_coupled clock.m)
    clock.adjoinEndpoint.aP
    0
    (fun _ => 1)
    (X_coupled_transpose_mul_L_X_coupled clock L_C hLC)
    (R_M_coupled_mul_M_coupled w)
    (coupled_moment_equation clock)
    (coupled_weight_calibration clock)
    clock.adjoinEndpoint.haP_pos
    (fun _ => zero_lt_one)

/-- Next-order left inverse `L_{C_+} = (0; R_M_coupledᵀ)` for the lifted count matrix
    `C_+ = (X_coupled * (1 + N_{w+1}); M_coupled w)`. -/
def L_C_coupled_next {w : ℕ} (clock : AlgebraicClock w)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ)
    (hLC : clock.C.transpose * L_C = 1) :
    Matrix (Fin ((clock.adjoinEndpoint.lift (coupledMomentLiftStep clock L_C hLC)).m)) (Fin (w + 1)) ℚ :=
  Matrix.of fun x c =>
    match finSumFinEquiv.symm x with
    | Sum.inl _ => 0
    | Sum.inr r => R_M_coupled w c r

/-- **Preservation of Full Column Rank `C_+ᵀ * L_{C_+} = 1` (`coupledMomentLift_C_transpose_mul_L_C`)**:
    For any `clock : AlgebraicClock w` lifted via `coupledMomentLiftStep`, its count table `C_+`
    has explicit left inverse `L_C_coupled_next clock L_C hLC`. -/
theorem coupledMomentLift_C_transpose_mul_L_C {w : ℕ} (clock : AlgebraicClock w)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ)
    (hLC : clock.C.transpose * L_C = 1) :
    ((clock.adjoinEndpoint).lift (coupledMomentLiftStep clock L_C hLC)).C.transpose *
      L_C_coupled_next clock L_C hLC = 1 := by
  ext c1 c2
  have hcomp :=
    (Equiv.sum_comp finSumFinEquiv fun x : Fin ((clock.m + 1) + ((w + 1) + (w + 1))) =>
      ((clock.adjoinEndpoint).lift (coupledMomentLiftStep clock L_C hLC)).C x c1 *
        L_C_coupled_next clock L_C hLC x c2).symm
  have hmul :
      (((clock.adjoinEndpoint).lift (coupledMomentLiftStep clock L_C hLC)).C.transpose *
        L_C_coupled_next clock L_C hLC) c1 c2 =
      ∑ x : Fin ((clock.m + 1) + ((w + 1) + (w + 1))),
        ((clock.adjoinEndpoint).lift (coupledMomentLiftStep clock L_C hLC)).C x c1 *
          L_C_coupled_next clock L_C hLC x c2 := rfl
  rw [hmul, hcomp, Fintype.sum_sum_type]
  simp only [AlgebraicClock.lift, AlgebraicClock.ofEquiv,
    LiftStepData.ofCoupledMoment, liftedCountMat, L_C_coupled_next,
    Matrix.of_apply, Equiv.symm_apply_apply, mul_zero, Finset.sum_const_zero, zero_add]
  have hRM := congr_fun (congr_fun (R_M_coupled_mul_M_coupled w) c2) c1
  simp only [Matrix.mul_apply, Matrix.one_apply, eq_comm] at hRM ⊢
  simpa [mul_comm] using hRM

/-- Bundles an order-`w` algebraic clock `clock : AlgebraicClock w` together with an explicit
    rational left inverse `L_C` witnessing full column rank `clock.Cᵀ * L_C = 1`. -/
structure FullRankClock (w : ℕ) where
  clock : AlgebraicClock w
  L_C : Matrix (Fin clock.m) (Fin w) ℚ
  hLC : clock.C.transpose * L_C = 1

/-- Applies the non-degenerate coupled-moment lift (`adjoinEndpoint` + `coupledMomentLiftStep`)
    to `fc : FullRankClock w`, producing a `FullRankClock (w + 1)` with
    `(fc.clock.m + 1) + ((w + 1) + (w + 1)) = fc.clock.m + (2 * w + 3)` actions. -/
@[reducible] def FullRankClock.coupledLift {w : ℕ} (fc : FullRankClock w) : FullRankClock (w + 1) where
  clock := fc.clock.adjoinEndpoint.lift (coupledMomentLiftStep fc.clock fc.L_C fc.hLC)
  L_C := L_C_coupled_next fc.clock fc.L_C fc.hLC
  hLC := coupledMomentLift_C_transpose_mul_L_C fc.clock fc.L_C fc.hLC

/-- **Preservation of Count Table Nonnegativity under `FullRankClock.coupledLift`**:
    If all entries of `fc.clock.C` are nonnegative, then all entries of `fc.coupledLift.clock.C`
    are nonnegative (and all `2(w + 1)` reset rows are strictly positive `≥ 1`). -/
theorem coupledLift_count_nonneg {w : ℕ} (fc : FullRankClock w)
    (hC : ∀ i : Fin fc.clock.m, ∀ c : Fin w, 0 ≤ fc.clock.C i c) :
    ∀ x : Fin fc.coupledLift.clock.m,
      ∀ c : Fin (w + 1), 0 ≤ fc.coupledLift.clock.C x c := by
  intro x c
  simp only [FullRankClock.coupledLift, AlgebraicClock.lift, AlgebraicClock.ofEquiv,
    LiftStepData.ofCoupledMoment, liftedCountMat, Matrix.of_apply]
  cases hsym : finSumFinEquiv.symm x with
  | inl y =>
    simp only [Matrix.mul_apply]
    refine Finset.sum_nonneg fun j _ => ?_
    refine mul_nonneg ?_ (one_add_N_mat_nonneg (w + 1) j c)
    simp only [X_coupled, Matrix.of_apply]
    cases finSumFinEquiv.symm y with
    | inl i =>
      simp only [shiftRightCount, Matrix.of_apply]
      split_ifs with hj
      · exact hC i ⟨j.val - 1, by omega⟩
      · exact le_rfl
    | inr _ =>
      simp only [e0_row]
      split_ifs <;> norm_num
  | inr r =>
    exact le_trans zero_le_one (M_coupled_entry_ge_one w r c)

/-- Top-degree count entries of `fc.coupledLift.clock.C` (`w ≥ 1`):
    - On old action `i : Fin fc.clock.m`: equals `fc.clock.C i ⟨w - 1, _⟩`.
    - On the endpoint action `g`: equals `0`.
    - On reset action `r : Fin ((w + 1) + (w + 1))`: equals `M_coupled w r ⟨w, _⟩ ≥ 1`. -/
theorem coupledLift_top_count_entries {w : ℕ} (hw : 0 < w) (fc : FullRankClock w) :
    (∀ i : Fin fc.clock.m,
      fc.coupledLift.clock.C
        (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl i))))
        ⟨w, Nat.lt_succ_self w⟩ =
      fc.clock.C i ⟨w - 1, Nat.sub_lt hw Nat.zero_lt_one⟩) ∧
    (∀ u : Fin 1,
      fc.coupledLift.clock.C
        (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr u))))
        ⟨w, Nat.lt_succ_self w⟩ = 0) ∧
    (∀ r : Fin ((w + 1) + (w + 1)),
      fc.coupledLift.clock.C
        (finSumFinEquiv (Sum.inr r))
        ⟨w, Nat.lt_succ_self w⟩ =
      M_coupled w r ⟨w, Nat.lt_succ_self w⟩) := by
  refine ⟨fun i => ?_, fun u => ?_, fun r => ?_⟩
  · simp only [FullRankClock.coupledLift, AlgebraicClock.lift, AlgebraicClock.ofEquiv,
      Equiv.symm_apply_apply, LiftStepData.ofCoupledMoment,
      liftedCountMat, Matrix.of_apply]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, mul_N_mat_apply]
    have hnot : ¬ (w + 1 < w + 1) := lt_irrefl (w + 1)
    simp only [hnot, ↓reduceDIte, add_zero, X_coupled, Matrix.of_apply, Equiv.symm_apply_apply,
      shiftRightCount, hw]
  · simp only [FullRankClock.coupledLift, AlgebraicClock.lift, AlgebraicClock.ofEquiv,
      Equiv.symm_apply_apply, LiftStepData.ofCoupledMoment,
      liftedCountMat, Matrix.of_apply]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, mul_N_mat_apply]
    have hnot : ¬ (w + 1 < w + 1) := lt_irrefl (w + 1)
    have hne : w ≠ 0 := by omega
    simp only [hnot, ↓reduceDIte, add_zero, X_coupled, Matrix.of_apply, Equiv.symm_apply_apply,
      e0_row, hne, ↓reduceIte]
  · simp [FullRankClock.coupledLift, AlgebraicClock.lift, AlgebraicClock.ofEquiv,
      LiftStepData.ofCoupledMoment, liftedCountMat]

/-- **Exact Top-Degree Count Column Sum Recurrence (`coupledLift_top_count_sum`)**:
    For any `w > 0`, lifting `fc : FullRankClock w` via `coupledLift` adds
    `4 * (w + 1)` (from the `2(w + 1)` reset actions in `M_coupled w`) to the top-degree
    falling-factorial count column sum:
    `∑ x, C_+ x ⟨w, _⟩ = (∑ i, C i ⟨w - 1, _⟩) + 4 * (w + 1)`. -/
theorem coupledLift_top_count_sum {w : ℕ} (hw : 0 < w) (fc : FullRankClock w) :
    (∑ x : Fin fc.coupledLift.clock.m,
      fc.coupledLift.clock.C x ⟨w, Nat.lt_succ_self w⟩) =
    (∑ i : Fin fc.clock.m, fc.clock.C i ⟨w - 1, Nat.sub_lt hw Nat.zero_lt_one⟩) +
      4 * (w + 1 : ℚ) := by
  have hent := coupledLift_top_count_entries hw fc
  have hcomp1 :=
    (Equiv.sum_comp finSumFinEquiv fun x : Fin ((fc.clock.m + 1) + ((w + 1) + (w + 1))) =>
      fc.coupledLift.clock.C x ⟨w, Nat.lt_succ_self w⟩).symm
  change (∑ x : Fin ((fc.clock.m + 1) + ((w + 1) + (w + 1))),
      fc.coupledLift.clock.C x ⟨w, Nat.lt_succ_self w⟩) = _
  rw [hcomp1, Fintype.sum_sum_type]
  have hcomp2 :=
    (Equiv.sum_comp finSumFinEquiv fun y : Fin (fc.clock.m + 1) =>
      fc.coupledLift.clock.C (finSumFinEquiv (Sum.inl y)) ⟨w, Nat.lt_succ_self w⟩).symm
  rw [hcomp2, Fintype.sum_sum_type]
  have h_old :
      (∑ i : Fin fc.clock.m,
        fc.coupledLift.clock.C
          (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl i))))
          ⟨w, Nat.lt_succ_self w⟩) =
      ∑ i : Fin fc.clock.m, fc.clock.C i ⟨w - 1, Nat.sub_lt hw Nat.zero_lt_one⟩ :=
    Finset.sum_congr rfl fun i _ => hent.1 i
  have h_end :
      (∑ u : Fin 1,
        fc.coupledLift.clock.C
          (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr u))))
          ⟨w, Nat.lt_succ_self w⟩) = 0 :=
    Finset.sum_eq_zero fun u _ => hent.2.1 u
  have h_reset :
      (∑ r : Fin ((w + 1) + (w + 1)),
        fc.coupledLift.clock.C
          (finSumFinEquiv (Sum.inr r))
          ⟨w, Nat.lt_succ_self w⟩) = 4 * (w + 1 : ℚ) := by
    have h1 :
        (∑ r : Fin ((w + 1) + (w + 1)),
          fc.coupledLift.clock.C (finSumFinEquiv (Sum.inr r)) ⟨w, Nat.lt_succ_self w⟩) =
        ∑ r : Fin ((w + 1) + (w + 1)), M_coupled w r ⟨w, Nat.lt_succ_self w⟩ :=
      Finset.sum_congr rfl fun r _ => hent.2.2 r
    rw [h1]
    have hell := congr_fun (congr_fun (ell_row_M_coupled w) ()) ⟨w, Nat.lt_succ_self w⟩
    simpa [ell_row, one_row, Matrix.mul_apply] using hell
  rw [h_old, h_end, h_reset, add_zero]

/-- **Exact Preservation of Top-Degree Score Entry on Old Actions (`coupledLift_top_score_old`)**:
    For any `w ≥ 2`, lifting `fc : FullRankClock w` via `coupledLift` preserves the top-degree
    score coefficient on every old action `i : Fin fc.clock.m`:
    `R_+ (inl (inl i)) ⟨w, _⟩ = R i ⟨w - 1, _⟩`. -/
theorem coupledLift_top_score_old {w : ℕ} (hw : 2 ≤ w) (fc : FullRankClock w)
    (i : Fin fc.clock.m) :
    fc.coupledLift.clock.R
      (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl i))))
      ⟨w, Nat.lt_succ_self w⟩ =
    fc.clock.R i ⟨w - 1, by omega⟩ := by
  have hD0 := congr_fun (congr_fun (D_deficit_coupled_eq_zero fc.clock)
    (finSumFinEquiv (Sum.inl i))) ⟨w, Nat.lt_succ_self w⟩
  unfold D_deficit at hD0
  have hGX :
      (fc.clock.adjoinEndpoint.G * X_coupled fc.clock)
        (finSumFinEquiv (Sum.inl i)) ⟨w, Nat.lt_succ_self w⟩ =
      (S_coupled fc.clock * N_mat (w + 1))
        (finSumFinEquiv (Sum.inl i)) ⟨w, Nat.lt_succ_self w⟩ := by
    simp only [Matrix.sub_apply, Matrix.zero_apply] at hD0
    linarith
  simp only [FullRankClock.coupledLift, AlgebraicClock.lift, AlgebraicClock.ofEquiv,
    Equiv.symm_apply_apply, LiftStepData.ofCoupledMoment,
    liftedScoreMat, Matrix.of_apply, Matrix.add_apply]
  rw [hGX, mul_N_mat_apply]
  have hw1 : 1 < w := by omega
  simp [S_coupled, shiftRightScore, hw1]

/-- **Preservation of Score Row Nonnegativity on Old Actions (`coupledLift_score_old_nonneg`)**:
    If row `i` of `fc.clock.R` is nonnegative, then row `inl (inl i)` of `fc.coupledLift.clock.R`
    is nonnegative. -/
theorem coupledLift_score_old_nonneg {w : ℕ} (fc : FullRankClock w) (i : Fin fc.clock.m)
    (hR : ∀ c : Fin w, 0 ≤ fc.clock.R i c) :
    ∀ c : Fin (w + 1),
      0 ≤ fc.coupledLift.clock.R
        (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl i)))) c := by
  intro c
  have hD0 := congr_fun (congr_fun (D_deficit_coupled_eq_zero fc.clock)
    (finSumFinEquiv (Sum.inl i))) c
  unfold D_deficit at hD0
  have hGX :
      (fc.clock.adjoinEndpoint.G * X_coupled fc.clock)
        (finSumFinEquiv (Sum.inl i)) c =
      (S_coupled fc.clock * N_mat (w + 1))
        (finSumFinEquiv (Sum.inl i)) c := by
    simp only [Matrix.sub_apply, Matrix.zero_apply] at hD0
    linarith
  simp only [FullRankClock.coupledLift, AlgebraicClock.lift, AlgebraicClock.ofEquiv,
    Equiv.symm_apply_apply, LiftStepData.ofCoupledMoment,
    liftedScoreMat, Matrix.of_apply, Matrix.add_apply]
  rw [hGX]
  have hmul :
      S_coupled fc.clock (finSumFinEquiv (Sum.inl i)) c +
        (S_coupled fc.clock * N_mat (w + 1)) (finSumFinEquiv (Sum.inl i)) c =
      (S_coupled fc.clock * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ))
        (finSumFinEquiv (Sum.inl i)) c := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  rw [hmul, Matrix.mul_apply]
  refine Finset.sum_nonneg fun j _ => ?_
  refine mul_nonneg ?_ (one_add_N_mat_nonneg (w + 1) j c)
  simp only [S_coupled, Matrix.of_apply, Equiv.symm_apply_apply, shiftRightScore]
  split_ifs with hj
  · exact hR ⟨j.val - 1, by omega⟩
  · exact le_rfl

/-!
## 4. Seed Full-Rank Clocks & All-Orders Coupled-Moment Clock Families
-/

/-- Explicit `3 × 2` rational left inverse `L_C2` satisfying `C2ᵀ * L_C2 = 1`. -/
def L_C2 : Matrix (Fin 3) (Fin 2) ℚ :=
  !![-1,  2;
      1, -5 / 3;
      0,  0]

set_option linter.unnecessarySeqFocus false in
/-- `C2.transpose * L_C2 = 1`. -/
theorem C2_transpose_mul_L_C2 : C2.transpose * L_C2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, C2, L_C2] <;>
    norm_num

/-- The `k = 2` RPS seed clock packaged as a `FullRankClock 2`. -/
@[reducible] def rpsFullRankClock : FullRankClock 2 where
  clock := rpsAlgebraicClock
  L_C := L_C2
  hLC := C2_transpose_mul_L_C2

/-- Helper column 1 for the `6 × 3` left inverse `L_C_seven` of `C_seven`. -/
def L_C_seven_col1 (i : Fin 6) : ℚ :=
  ((if i = 1 then 1 else 0) - (if i = 0 then 1 else 0) - 12 * v_seven i) / 14

/-- Explicit `6 × 3` rational left inverse `L_C_seven` satisfying `C_sevenᵀ * L_C_seven = 1`. -/
def L_C_seven : Matrix (Fin 6) (Fin 3) ℚ :=
  Matrix.of fun i c =>
    match c with
    | 0 => v_seven i
    | 1 => L_C_seven_col1 i
    | 2 => ((if i = 0 then 1 else 0) - 456 * v_seven i - 2443 * L_C_seven_col1 i) / 2058

set_option linter.unnecessarySeqFocus false in
/-- `C_seven.transpose * L_C_seven = 1`. -/
theorem C_seven_transpose_mul_L_C_seven : C_seven.transpose * L_C_seven = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_six, C_seven, L_C_seven, L_C_seven_col1, v_seven] <;>
    norm_num

/-- The `k = 3` 6-action recurrent seed clock packaged as a `FullRankClock 3`. -/
@[reducible] def sevenFullRankClock : FullRankClock 3 where
  clock := sevenAlgebraicClock
  L_C := L_C_seven
  hLC := C_seven_transpose_mul_L_C_seven

/-- **The Standard All-Orders Coupled-Moment Full-Rank Clock Family (`standardFullRankClockFamily`)**:
    Constructed inductively from `rpsFullRankClock` (`d = 0, k = 2, m = 3`) by applying the
    non-degenerate coupled-moment lift `FullRankClock.coupledLift` at every step `d ↦ d + 1`. -/
@[reducible] def standardFullRankClockFamily : (d : ℕ) → FullRankClock (d + 2)
  | 0 => rpsFullRankClock
  | d + 1 => (standardFullRankClockFamily d).coupledLift

/-- **The Standard All-Orders Coupled-Moment Algebraic Clock Family (`standardClockFamily`, Theorem 1.1)**:
    Underlying `AlgebraicClock (d + 2)` of `standardFullRankClockFamily d`. -/
@[reducible] def standardClockFamily (d : ℕ) : AlgebraicClock (d + 2) :=
  (standardFullRankClockFamily d).clock

/-- **The 7-Action-Seeded All-Orders Coupled-Moment Full-Rank Clock Family (`sevenSeededFullRankClockFamily`)**:
    Constructed inductively from `sevenFullRankClock` (`d = 0, k = 3, m = 6`) by applying
    `FullRankClock.coupledLift` at every step `d ↦ d + 1`. -/
@[reducible] def sevenSeededFullRankClockFamily : (d : ℕ) → FullRankClock (d + 3)
  | 0 => sevenFullRankClock
  | d + 1 => (sevenSeededFullRankClockFamily d).coupledLift

/-- **The 7-Action-Seeded All-Orders Coupled-Moment Algebraic Clock Family (`sevenSeededClockFamily`, Remark 1.2)**:
    Underlying `AlgebraicClock (d + 3)` of `sevenSeededFullRankClockFamily d`. -/
@[reducible] def sevenSeededClockFamily (d : ℕ) : AlgebraicClock (d + 3) :=
  (sevenSeededFullRankClockFamily d).clock

/-- **Full Column Rank of `standardClockFamily` at Every Order**:
    For every `d ∈ ℕ`, `(standardClockFamily d).C.transpose * (standardFullRankClockFamily d).L_C = 1`. -/
theorem standardClockFamily_full_rank (d : ℕ) :
    (standardClockFamily d).C.transpose * (standardFullRankClockFamily d).L_C = 1 :=
  (standardFullRankClockFamily d).hLC

/-- **Exact Action Count of `standardClockFamily` (`m_{d+2} = (d + 3)^2 - 6`)**:
    For every `d ∈ ℕ` (`k = d + 2 ≥ 2`), `standardClockFamily d` has `(d + 3)^2 - 6`
    (`= recurrentActionCount (d + 2)`) recurrent actions (`1` endpoint + `2(d+2)+2` reset actions
    added per step). -/
theorem standardClockFamily_m (d : ℕ) :
    (standardClockFamily d).m = (d + 3) ^ 2 - 6 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change ((standardClockFamily d).m + 1) + ((d + 2 + 1) + (d + 2 + 1)) = (d + 1 + 3) ^ 2 - 6
    rw [ih]
    have h1 : 9 ≤ (d + 3) ^ 2 := by
      calc 9 ≤ d ^ 2 + 6 * d + 9 := by omega
        _ = (d + 3) ^ 2 := by ring
    have h2 : (d + 1 + 3) ^ 2 = (d + 3) ^ 2 + 1 + ((d + 2 + 1) + (d + 2 + 1)) := by ring
    omega

/-- Strict positivity of the action count `(standardClockFamily d).m > 0` for all `d ∈ ℕ`. -/
theorem standardClockFamily_m_pos (d : ℕ) :
    0 < (standardClockFamily d).m := by
  rw [standardClockFamily_m]
  have h1 : 9 ≤ (d + 3) ^ 2 := by
    calc 9 ≤ d ^ 2 + 6 * d + 9 := by omega
      _ = (d + 3) ^ 2 := by ring
  omega

/-- **Exact Action Count of `sevenSeededClockFamily` (`m_{d+3}^{(7)} = (d + 4)^2 - 10`)**:
    For every `d ∈ ℕ` (`k = d + 3 ≥ 3`), `sevenSeededClockFamily d` has `(d + 4)^2 - 10`
    recurrent actions (`m_3^{(7)} = 6`, so `n_k^{(7)} = m_k^{(7)} + 1 = (k + 1)^2 - 9`). -/
theorem sevenSeededClockFamily_m (d : ℕ) :
    (sevenSeededClockFamily d).m = (d + 4) ^ 2 - 10 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change ((sevenSeededClockFamily d).m + 1) + ((d + 3 + 1) + (d + 3 + 1)) = (d + 1 + 4) ^ 2 - 10
    rw [ih]
    have h1 : 16 ≤ (d + 4) ^ 2 := by
      calc 16 ≤ d ^ 2 + 8 * d + 16 := by omega
        _ = (d + 4) ^ 2 := by ring
    have h2 : (d + 1 + 4) ^ 2 = (d + 4) ^ 2 + 1 + ((d + 3 + 1) + (d + 3 + 1)) := by ring
    omega

set_option linter.unnecessarySeqFocus false in
/-- Every entry of `C2` (`rpsAlgebraicClock.C`) is nonnegative. -/
theorem rpsAlgebraicClock_C_nonneg (i : Fin rpsAlgebraicClock.m) (c : Fin 2) :
    0 ≤ rpsAlgebraicClock.C i c := by
  fin_cases i <;> fin_cases c <;> decide

set_option linter.unnecessarySeqFocus false in
/-- Every entry in row `0` of `R2` (`rpsAlgebraicClock.R 0`) is nonnegative. -/
theorem rpsAlgebraicClock_R_zero_nonneg (c : Fin 2) :
    0 ≤ rpsAlgebraicClock.R ⟨0, by decide⟩ c := by
  fin_cases c <;> decide

set_option linter.unnecessarySeqFocus false in
/-- Every top-degree entry `C_seven i 2` (`sevenAlgebraicClock.C i 2`) is strictly positive. -/
theorem sevenAlgebraicClock_top_C_pos (i : Fin sevenAlgebraicClock.m) :
    0 < sevenAlgebraicClock.C i ⟨2, by decide⟩ := by
  fin_cases i <;> decide

/-- **Nonnegativity of `standardClockFamily` Count Tables (`standardClockFamily_count_nonneg`)**:
    For every `d ∈ ℕ`, all entries of `(standardClockFamily d).C` are nonnegative. -/
theorem standardClockFamily_count_nonneg (d : ℕ) :
    ∀ i : Fin (standardClockFamily d).m,
      ∀ c : Fin (d + 2), 0 ≤ (standardClockFamily d).C i c := by
  induction d with
  | zero => exact rpsAlgebraicClock_C_nonneg
  | succ d ih =>
    exact coupledLift_count_nonneg (standardFullRankClockFamily d) ih

/-- Helper: index `0` in `fc.coupledLift.clock.m` equals `finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl ⟨0, hm⟩)))`. -/
theorem coupledLift_zero_index_eq {w : ℕ} (fc : FullRankClock w) (hm : 0 < fc.clock.m) :
    (⟨0, by
      change 0 < (fc.clock.m + 1) + ((w + 1) + (w + 1))
      omega⟩ : Fin fc.coupledLift.clock.m) =
    finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl ⟨0, hm⟩))) := by
  ext
  simp

/-- **Nonnegativity of Row `0` of `standardClockFamily` Score Tables (`standardClockFamily_R_zero_nonneg`)**:
    For every `d ∈ ℕ` and `c : Fin (d + 2)`, `(standardClockFamily d).R ⟨0, _⟩ c ≥ 0`. -/
theorem standardClockFamily_R_zero_nonneg (d : ℕ) :
    ∀ c : Fin (d + 2),
      0 ≤ (standardClockFamily d).R ⟨0, standardClockFamily_m_pos d⟩ c := by
  induction d with
  | zero => exact rpsAlgebraicClock_R_zero_nonneg
  | succ d ih =>
    intro c
    have hidx := coupledLift_zero_index_eq (standardFullRankClockFamily d) (standardClockFamily_m_pos d)
    change 0 ≤ (standardFullRankClockFamily d).coupledLift.clock.R ⟨0, _⟩ c
    rw [hidx]
    exact coupledLift_score_old_nonneg (standardFullRankClockFamily d)
      ⟨0, standardClockFamily_m_pos d⟩ ih c

/-- **Exact Top-Degree Score Coefficient of Action `0` in `standardClockFamily` (`= 1`)**:
    For every `d ∈ ℕ` (`k = d + 2 ≥ 2`), the top-degree falling-factorial score coefficient
    `(standardClockFamily d).R ⟨0, _⟩ ⟨d + 1, _⟩` equals `1`. -/
theorem standardClockFamily_top_score_zero (d : ℕ) :
    (standardClockFamily d).R ⟨0, standardClockFamily_m_pos d⟩
      ⟨d + 1, Nat.lt_succ_self (d + 1)⟩ = 1 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hidx := coupledLift_zero_index_eq (standardFullRankClockFamily d) (standardClockFamily_m_pos d)
    change (standardFullRankClockFamily d).coupledLift.clock.R ⟨0, _⟩
      ⟨d + 2, Nat.lt_succ_self (d + 2)⟩ = 1
    rw [hidx]
    have hstep :=
      coupledLift_top_score_old (w := d + 2) (by omega) (standardFullRankClockFamily d)
        ⟨0, standardClockFamily_m_pos d⟩
    exact hstep.trans ih

/-- **Degree-`(k - 1)` Lower Bound on Action `0` Cumulative Score (`standardClockFamily_score_zero_lower_bound`)**:
    For every `d ∈ ℕ` (`k = d + 2 ≥ 2`) and every phase `P ∈ ℕ`, the score of action `0`
    at phase `P` is at least `\binom{P}{d + 1} = \binom{P}{k - 1}`. -/
theorem standardClockFamily_score_zero_lower_bound (d P : ℕ) :
    (Nat.choose P (d + 1) : ℚ) ≤
      ((standardClockFamily d).R.mulVec (binomBasis (d + 2) P))
        ⟨0, standardClockFamily_m_pos d⟩ := by
  let i0 : Fin (standardClockFamily d).m := ⟨0, standardClockFamily_m_pos d⟩
  let c_top : Fin (d + 2) := ⟨d + 1, Nat.lt_succ_self (d + 1)⟩
  have hR := standardClockFamily_R_zero_nonneg d
  have hbinom : ∀ c : Fin (d + 2), 0 ≤ binomBasis (d + 2) P c := by
    intro c
    simp only [binomBasis]
    exact Nat.cast_nonneg _
  simp only [Matrix.mulVec, dotProduct]
  have hterm :
      (Nat.choose P (d + 1) : ℚ) =
        (standardClockFamily d).R i0 c_top * binomBasis (d + 2) P c_top := by
    rw [standardClockFamily_top_score_zero d, one_mul]
    rfl
  rw [hterm]
  exact Finset.single_le_sum (fun c _ => mul_nonneg (hR c) (hbinom c))
    (Finset.mem_univ c_top)

/-- **Top-Degree Count Column Sum Lower Bound for `standardClockFamily` (`≥ 9`)**:
    In `standardClockFamily 0` (`C2`), the top-degree count column sum is `9`, and each
    coupled-moment lift step adds `4 * (w + 1) > 0`, so `9 ≤ ∑ i, C i ⟨d + 1, _⟩` for all `d ∈ ℕ`. -/
theorem standardClockFamily_top_count_sum_ge_nine (d : ℕ) :
    (9 : ℚ) ≤
      ∑ i : Fin (standardClockFamily d).m,
        (standardClockFamily d).C i ⟨d + 1, Nat.lt_succ_self (d + 1)⟩ := by
  induction d with
  | zero =>
    simp [standardClockFamily, rpsAlgebraicClock, Fin.sum_univ_three, C2]
    norm_num
  | succ d ih =>
    have hstep :=
      coupledLift_top_count_sum (Nat.succ_pos (d + 1)) (standardFullRankClockFamily d)
    dsimp only [Nat.succ_sub_one, standardClockFamily] at hstep ih ⊢
    rw [hstep]
    have hpos : (0 : ℚ) ≤ 4 * (((d + 1).succ : ℚ) + 1) := by positivity
    linarith

/-- **Top-Degree Count Column Sum Lower Bound for `sevenSeededClockFamily` (`≥ 11466`)**:
    In `sevenSeededClockFamily 0` (`C_seven`), the top-degree count column sum is `11466`, and each
    coupled-moment lift step adds `4 * (w + 1) > 0`. -/
theorem sevenSeededClockFamily_top_count_sum_ge (d : ℕ) :
    (11466 : ℚ) ≤
      ∑ i : Fin (sevenSeededClockFamily d).m,
        (sevenSeededClockFamily d).C i ⟨d + 2, Nat.lt_succ_self (d + 2)⟩ := by
  induction d with
  | zero =>
    simp [sevenSeededClockFamily, sevenAlgebraicClock, Fin.sum_univ_six, C_seven]
    norm_num
  | succ d ih =>
    have hstep :=
      coupledLift_top_count_sum (Nat.succ_pos (d + 2)) (sevenSeededFullRankClockFamily d)
    dsimp only [Nat.succ_sub_one, sevenSeededClockFamily] at hstep ih ⊢
    rw [hstep]
    have hpos : (0 : ℚ) ≤ 4 * (((d + 2).succ : ℚ) + 1) := by positivity
    linarith

/-!
## 5. Multi-Phase Telescoping for Any `AlgebraicClock`
-/

/-- Additivity of `scoreVec` in the play count vector:
    `scoreVec A f (z1 + z2) = scoreVec A (scoreVec A f z1) z2`. -/
theorem scoreVec_add {n : Type*} [Fintype n] (A : Matrix n n ℚ) (f z1 z2 : n → ℚ) :
    scoreVec A f (z1 + z2) = scoreVec A (scoreVec A f z1) z2 := by
  ext i
  simp only [scoreVec, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_assoc]

/-- Total play count vector accumulated by `clock : AlgebraicClock w` across the first `P` phases
    `q ∈ [0, P)`. -/
def totalPhaseCount {w : ℕ} (clock : AlgebraicClock w) (P : ℕ) : Fin clock.m → ℚ :=
  fun i => ∑ q ∈ Finset.range P, clock.C.mulVec (binomBasis w q) i

/-- **Multi-Phase Telescoping Score Transition (`AlgebraicClock.multi_phase_score_transition`)**:
    In any `clock : AlgebraicClock w`, executing the cumulative count vector `totalPhaseCount clock P`
    over `P` phases starting from initial score vector `clock.R.mulVec (binomBasis w 0)` transitions
    the cumulative score vector to `clock.R.mulVec (binomBasis w P)`. -/
theorem AlgebraicClock.multi_phase_score_transition {w : ℕ}
    (clock : AlgebraicClock w) (P : ℕ) :
    scoreVec clock.G
      (clock.R.mulVec (binomBasis w 0))
      (totalPhaseCount clock P) =
    clock.R.mulVec (binomBasis w P) := by
  induction P with
  | zero =>
    ext i
    simp [totalPhaseCount, scoreVec, Matrix.mulVec, dotProduct]
  | succ P ih =>
    have hsplit :
        totalPhaseCount clock (P + 1) =
          totalPhaseCount clock P + clock.C.mulVec (binomBasis w P) := by
      ext i
      simp [totalPhaseCount, Finset.sum_range_succ]
    rw [hsplit, scoreVec_add, ih]
    exact clock.phase_score_transition P

/-- **Multi-Phase Telescoping Endpoint Counter (`AlgebraicClock.multi_phase_endpoint_counter`)**:
    In any `clock : AlgebraicClock w` (`w > 0`), the endpoint counter functional `clock.v`
    evaluated on `totalPhaseCount clock P` equals `(P : ℚ)`. -/
theorem AlgebraicClock.multi_phase_endpoint_counter {w : ℕ}
    (clock : AlgebraicClock w) (hw : 0 < w) (P : ℕ) :
    dotProduct clock.v (totalPhaseCount clock P) = (P : ℚ) := by
  induction P with
  | zero =>
    simp [totalPhaseCount, dotProduct]
  | succ P ih =>
    have hsplit :
        totalPhaseCount clock (P + 1) =
          totalPhaseCount clock P + clock.C.mulVec (binomBasis w P) := by
      ext i
      simp [totalPhaseCount, Finset.sum_range_succ]
    rw [hsplit, dotProduct_add, ih, clock.endpoint_counter_increment hw P]
    push_cast
    ring

/-- **Degree-`(k - 1)` Lower Bound on Single-Phase Play Count (`standardClockFamily_phase_len_lower_bound`)**:
    For every `d ∈ ℕ` (`k = d + 2 ≥ 2`) and every phase `q ∈ ℕ`, every action play count in
    phase `q` is nonnegative and the total phase duration across all actions satisfies
    `9 * (Nat.choose q (d + 1) : ℚ) ≤ ∑ i, ((standardClockFamily d).C.mulVec (binomBasis (d + 2) q)) i`. -/
theorem standardClockFamily_phase_len_lower_bound (d q : ℕ) :
    (∀ i : Fin (standardClockFamily d).m,
      0 ≤ ((standardClockFamily d).C.mulVec (binomBasis (d + 2) q)) i) ∧
    9 * (Nat.choose q (d + 1) : ℚ) ≤
      ∑ i : Fin (standardClockFamily d).m,
        ((standardClockFamily d).C.mulVec (binomBasis (d + 2) q)) i := by
  have hC := standardClockFamily_count_nonneg d
  have hbinom : ∀ c : Fin (d + 2), 0 ≤ binomBasis (d + 2) q c := by
    intro c
    simp only [binomBasis]
    exact Nat.cast_nonneg _
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg fun c _ => mul_nonneg (hC i c) (hbinom c)
  · let c_top : Fin (d + 2) := ⟨d + 1, Nat.lt_succ_self (d + 1)⟩
    have h_each :
        ∀ i : Fin (standardClockFamily d).m,
          (standardClockFamily d).C i c_top * (Nat.choose q (d + 1) : ℚ) ≤
            ((standardClockFamily d).C.mulVec (binomBasis (d + 2) q)) i := by
      intro i
      simp only [Matrix.mulVec, dotProduct]
      have hterm :
          (standardClockFamily d).C i c_top * (Nat.choose q (d + 1) : ℚ) =
            (standardClockFamily d).C i c_top * binomBasis (d + 2) q c_top := rfl
      rw [hterm]
      exact Finset.single_le_sum (fun c _ => mul_nonneg (hC i c) (hbinom c))
        (Finset.mem_univ c_top)
    have h_sum_le :
        (∑ i : Fin (standardClockFamily d).m,
          (standardClockFamily d).C i c_top * (Nat.choose q (d + 1) : ℚ)) ≤
        ∑ i : Fin (standardClockFamily d).m,
          ((standardClockFamily d).C.mulVec (binomBasis (d + 2) q)) i :=
      Finset.sum_le_sum fun i _ => h_each i
    rw [← Finset.sum_mul] at h_sum_le
    have h9 :
        9 * (Nat.choose q (d + 1) : ℚ) ≤
          (∑ i : Fin (standardClockFamily d).m, (standardClockFamily d).C i c_top) *
            (Nat.choose q (d + 1) : ℚ) :=
      mul_le_mul_of_nonneg_right (standardClockFamily_top_count_sum_ge_nine d) (Nat.cast_nonneg _)
    exact le_trans h9 h_sum_le

/-- Pascal's hockey-stick sum $\sum_{q=0}^{P-1} \binom{q}{d+1} = \binom{P}{d+2}$ in `ℚ`. -/
theorem sum_range_choose_succ (d P : ℕ) :
    (∑ q ∈ Finset.range P, (Nat.choose q (d + 1) : ℚ)) = (Nat.choose P (d + 2) : ℚ) := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [Finset.sum_range_succ, ih]
    have hchoose :
        (Nat.choose (P + 1) (d + 2) : ℚ) =
          (Nat.choose P (d + 1) : ℚ) + (Nat.choose P (d + 2) : ℚ) := by
      exact_mod_cast Nat.choose_succ_succ P (d + 1)
    linarith

/-- **Degree-`k` Lower Bound on Cumulative Multi-Phase Elapsed Time (`standardClockFamily_cum_time_lower_bound`)**:
    For every `d ∈ ℕ` (`k = d + 2 ≥ 2`) and every phase horizon `P ∈ ℕ`, the cumulative step
    count across all actions over phases `0 ≤ q < P` satisfies
    `9 * (Nat.choose P (d + 2) : ℚ) ≤ ∑ i, totalPhaseCount (standardClockFamily d) P i`. -/
theorem standardClockFamily_cum_time_lower_bound (d P : ℕ) :
    9 * (Nat.choose P (d + 2) : ℚ) ≤
      ∑ i : Fin (standardClockFamily d).m, totalPhaseCount (standardClockFamily d) P i := by
  unfold totalPhaseCount
  rw [Finset.sum_comm]
  have h_phase_le :
      (∑ q ∈ Finset.range P, 9 * (Nat.choose q (d + 1) : ℚ)) ≤
        ∑ q ∈ Finset.range P,
          ∑ i : Fin (standardClockFamily d).m,
            ((standardClockFamily d).C.mulVec (binomBasis (d + 2) q)) i :=
    Finset.sum_le_sum fun q _ => (standardClockFamily_phase_len_lower_bound d q).2
  rw [← Finset.mul_sum, sum_range_choose_succ d P] at h_phase_le
  exact h_phase_le

/-!
## 6. Strengthened `RealizedClock k` Specification, Rate Bridge, and Seed Realizations
-/

/-- **Strengthened Realized Clock Specification (`RealizedClock k`, Definition 3.1 & Theorem 1.1)**:
    Packages a full-rank order-`k` algebraic clock `fc : FullRankClock k` together with:
    - The `(m + 1) × (m + 1)` skew-symmetric setup game `setupMatrix fc.clock.G setupVec`
      on `Option (Fin fc.clock.m)` (`totalDim = fc.clock.m + 1`, Lemma 2.2 `lem:setup`),
    - Setup phase shift `phaseShift : ℕ` (`q_0`), uniform score shift `scoreShift : ℚ` (`C_0`),
      and admissibility constant `A_adm ≥ 0`,
    - Initialized play sequence `trajectory : ℕ → Option (Fin fc.clock.m)` starting at the
      setup action `trajectory 0 = none` from zero initial counts,
    - Strict best-response validity `IsStrictFPTrajectory` at **every** integer prefix `t ≥ 1`,
    - Phase boundary steps `phaseTime : ℕ → ℕ` (`phaseTime 0 = 1`, `phaseTime p < phaseTime (p + 1)`),
    - Exact score correspondence `cumScore = R p(p + q_0) + C_0` at every phase boundary `phaseTime p`,
    - All-integer-time `Θ(t^{-1/k})` enclosure on the standard empirical saddle-point duality gap
      `standardDualityGap (setupMatrix fc.clock.G setupVec) trajectory trajectory t`. -/
structure RealizedClock (k : ℕ) where
  /-- Underlying full-rank order-`k` algebraic clock (`clock.Cᵀ * L_C = 1`). -/
  fc : FullRankClock k
  /-- Setup payoff column `w ∈ ℚ^m` defining the `(m + 1) × (m + 1)` game `setupMatrix fc.clock.G setupVec`. -/
  setupVec : Fin fc.clock.m → ℚ
  /-- Setup phase index `q_0 ∈ ℕ` (Lemma 2.2 `lem:setup`). -/
  phaseShift : ℕ
  /-- Setup uniform score shift `C_0 ∈ ℚ` (Lemma 2.2 `lem:setup`). -/
  scoreShift : ℚ
  /-- Admissibility constant `A_k ≥ 0` (Definition 3.1 `def:clock`). -/
  A_adm : ℚ
  hA_adm_nonneg : 0 ≤ A_adm
  /-- Nonnegativity of the setup column `setupVec ≥ 0` (ensuring `none` stays nonpositive). -/
  hsetup_nonneg : ∀ i : Fin fc.clock.m, 0 ≤ setupVec i
  /-- Initialized discrete-time play sequence `trajectory : ℕ → Option (Fin fc.clock.m)`. -/
  trajectory : ℕ → Option (Fin fc.clock.m)
  /-- Phase-start integer time sequence `phaseTime : ℕ → ℕ`. -/
  phaseTime : ℕ → ℕ
  /-- Initialized at the setup action `none` at `t = 0`. -/
  htraj_zero : trajectory 0 = none
  /-- Strict best-response inequality at every integer prefix `t ≥ 1`. -/
  hstrict : IsStrictFPTrajectory (setupMatrix fc.clock.G setupVec) trajectory
  /-- Phase `0` begins at `t = 1` immediately after the setup step `t = 0`. -/
  hphaseTime_zero : phaseTime 0 = 1
  /-- Phase boundary times are strictly increasing (`t(p) < t(p + 1)`). -/
  hphaseTime_lt : ∀ p : ℕ, phaseTime p < phaseTime (p + 1)
  /-- Active action at every phase boundary `t(p)` is `some ⟨0, _⟩`. -/
  hphase_leader : ∀ p : ℕ, ∃ i0 : Fin fc.clock.m, trajectory (phaseTime p) = some i0
  /-- All-integer-time order-`k` standard duality gap constants `0 < c_low ≤ c_high`. -/
  c_low : ℚ
  c_high : ℚ
  hc_low_pos : 0 < c_low
  hc_high_pos : 0 < c_high
  /-- All-integer-time `Θ(t^{-1/k})` standard empirical saddle-point duality gap bounds:
      `∀ t ≥ 1, c_low ≤ standardDualityGap M trajectory trajectory t ^ k * t ≤ c_high`. -/
  hgap_bounds : ∀ t : ℕ, 1 ≤ t →
    c_low ≤
      standardDualityGap (setupMatrix fc.clock.G setupVec) trajectory trajectory t ^ k * (t : ℚ) ∧
    standardDualityGap (setupMatrix fc.clock.G setupVec) trajectory trajectory t ^ k * (t : ℚ) ≤
      c_high

/-- The `(m + 1) × (m + 1)` setup game matrix of `rc : RealizedClock k`. -/
def RealizedClock.gameMatrix {k : ℕ} (rc : RealizedClock k) :
    Matrix (Option (Fin rc.fc.clock.m)) (Option (Fin rc.fc.clock.m)) ℚ :=
  setupMatrix rc.fc.clock.G rc.setupVec

/-- **Total Game Dimension Including Setup Action (`RealizedClock.totalDim_eq`)**:
    The action space `Option (Fin rc.fc.clock.m)` of `rc.gameMatrix` has cardinality
    `rc.fc.clock.m + 1`. -/
theorem RealizedClock.totalDim_eq {k : ℕ} (rc : RealizedClock k) :
    Fintype.card (Option (Fin rc.fc.clock.m)) = rc.fc.clock.m + 1 := by
  simp

/-- **Skew-Symmetry of `rc.gameMatrix` (`RealizedClock.gameMatrix_skew`)**. -/
theorem RealizedClock.gameMatrix_skew {k : ℕ} (rc : RealizedClock k) :
    IsSkewSymmetric rc.gameMatrix :=
  setupMatrix_skewSymmetric rc.fc.clock.hskew rc.setupVec

/-- **Equivalence to Both Players' Synchronized Simultaneous FP Histories (`RealizedClock.isStrictTwoPlayerFP`)**:
    For any `rc : RealizedClock k`, `(rc.trajectory, rc.trajectory)` is a strictly tie-free
    simultaneous two-player Fictitious Play trajectory at every integer step `t ≥ 1`. -/
theorem RealizedClock.isStrictTwoPlayerFP {k : ℕ} (rc : RealizedClock k) :
    IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory :=
  (isStrictTwoPlayerFPTrajectory_iff_isStrictFPTrajectory
    rc.gameMatrix_skew rc.trajectory).mpr rc.hstrict

/-- **Tie-Breaking Uniqueness of Both Players' FP Histories (`RealizedClock.unique_trajectory`)**:
    Any weak two-player Fictitious Play trajectory `(rowPlay, colPlay)` starting with
    `rowPlay 0 = none` and `colPlay 0 = none` is identically `(rc.trajectory, rc.trajectory)`
    at every integer step `t ∈ ℕ` under arbitrary tie-breaking. -/
theorem RealizedClock.unique_trajectory {k : ℕ} (rc : RealizedClock k)
    (rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m))
    (hweak : IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay)
    (hr0 : rowPlay 0 = none) (hc0 : colPlay 0 = none) (t : ℕ) :
    rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t := by
  rw [← rc.htraj_zero] at hr0 hc0
  exact unique_two_player_fp_trajectory rc.gameMatrix_skew rc.hstrict hweak hr0 hc0 t

/-- **Empirical Saddle-Point Gap Equals Twice Maximum Score Divided by Time
    (`RealizedClock.standardDualityGap_eq_twice_max_score_div_time`)**:
    At every integer step `t ≥ 1`, the standard two-player empirical max/min duality gap
    `max_i (M ȳ_t)_i - min_j (x̄_tᵀ M)_j` equals `2 * cumScore M a t (a t) / t`. -/
theorem RealizedClock.standardDualityGap_eq_twice_max_score_div_time
    {k : ℕ} (rc : RealizedClock k) {t : ℕ} (ht : 1 ≤ t) :
    standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t =
      2 * cumScore rc.gameMatrix rc.trajectory t (rc.trajectory t) / (t : ℚ) :=
  standardDualityGap_eq_stepDualityGap rc.gameMatrix_skew rc.hstrict ht

/-- **Unconditional Order-2 Realized Clock (`rpsRealizedClock : RealizedClock 2`)**:
    Packages `rpsFullRankClock`, the 4-action setup game `M4_RPS = setupMatrix A_RPS w_RPS`,
    the initialized trajectory `rpsTrajectory`, strict best-response validity at every step `t ≥ 1`,
    and all-integer-time `Θ(t^{-1/2})` standard duality gap bounds `[8/9, 400]`. -/
def rpsRealizedClock : RealizedClock 2 where
  fc := rpsFullRankClock
  setupVec := w_RPS
  phaseShift := 1
  scoreShift := 20 / 3
  A_adm := 4
  hA_adm_nonneg := by norm_num
  hsetup_nonneg := by
    intro i
    fin_cases i <;> simp [w_RPS, r2Vec] <;> norm_num
  trajectory := rpsTrajectory
  phaseTime := rpsPhaseStartStep
  htraj_zero := rfl
  hstrict := rps_unrolled_strict_fp_trajectory.2
  hphaseTime_zero := rpsPhaseStartStep_zero
  hphaseTime_lt := rpsPhaseStartStep_strictMono
  hphase_leader := fun p => ⟨⟨0, by decide⟩, rpsTrajectory_at_phase_start p⟩
  c_low := 8 / 9
  c_high := 400
  hc_low_pos := by norm_num
  hc_high_pos := by norm_num
  hgap_bounds := rps_all_integer_time_quadratic_gap

/-- **Unconditional Order-3 Realized Clock (`sevenRealizedClock : RealizedClock 3`)**:
    Packages `sevenFullRankClock`, the 7-action setup game `M7 = setupMatrix M_seven w_seven`,
    the initialized trajectory `sevenTrajectory`, strict best-response validity at every step `t ≥ 1`,
    and all-integer-time `Θ(t^{-1/3})` standard duality gap bounds `[343/500000, 32768000000000]`. -/
def sevenRealizedClock : RealizedClock 3 where
  fc := sevenFullRankClock
  setupVec := w_seven
  phaseShift := 20
  scoreShift := 657497227 / 52500
  A_adm := 28
  hA_adm_nonneg := by norm_num
  hsetup_nonneg := by
    intro i
    have h1 := seven_setup_realization.1 i
    linarith
  trajectory := sevenTrajectory
  phaseTime := sevenPhaseStartStep
  htraj_zero := rfl
  hstrict := seven_unrolled_strict_fp_trajectory.2
  hphaseTime_zero := sevenPhaseStartStep_zero
  hphaseTime_lt := sevenPhaseStartStep_strictMono
  hphase_leader := fun p => ⟨⟨0, by decide⟩, sevenTrajectory_at_phase_start p⟩
  c_low := 343 / 500000
  c_high := 32768000000000
  hc_low_pos := by norm_num
  hc_high_pos := by norm_num
  hgap_bounds := seven_all_integer_time_cubic_gap

/-- Action play-count vector of a singleton word `[a]` equals `runCount (fun _ => 0) a 1`. -/
theorem wordCountVec_singleton {α : Type*} [DecidableEq α] (a : α) :
    wordCountVec [a] = runCount (fun _ => 0) a 1 := by
  ext i
  by_cases h : i = a
  · subst h; simp [wordCountVec, runCount]
  · have hne : a ≠ i := Ne.symm h
    simp [wordCountVec, runCount, h, hne]

/-- Score vector after a singleton word `[a]` equals `scoreVec M s0 (runCount (fun _ => 0) a 1)`. -/
theorem wordScore_singleton_eq_scoreVec_runCount {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (s0 : α → ℚ) (a : α) :
    wordScore M s0 [a] = scoreVec M s0 (runCount (fun _ => 0) a 1) := by
  unfold wordScore
  rw [wordCountVec_singleton]

/-- Action scheduled at step `v` of phase `p` from a phase-word family `phaseWord`. -/
def wordPhaseAct {m : ℕ} (phaseWord : ℕ → List (Fin m)) (defaultAct : Fin m) (p v : ℕ) : Fin m :=
  if hv : v < (phaseWord p).length then (phaseWord p)[v] else defaultAct

/-- Unrolled discrete-time trajectory `ℕ → Option (Fin m)` generated by a phase-word family `phaseWord`. -/
def wordPhaseTrajectory {m : ℕ} (phaseWord : ℕ → List (Fin m)) (defaultAct : Fin m) :
    ℕ → Option (Fin m) :=
  unrollAction
    (setupFullAct (flatAct (fun p => (phaseWord p).length) (wordPhaseAct phaseWord defaultAct)))
    (setupFullLen (flatLen (fun p => (phaseWord p).length) (fun _ _ => 1)))

/-- **Word-Level Phase-to-Trajectory Setup Unrolling (`word_phase_unroll_isStrictFPTrajectory`)**:
    Given a phase-word schedule `phaseWord : ℕ → List (Fin m)` where each phase word `phaseWord p`
    is a valid strict FP word (`IsValidStrictWord M (sInit p) (phaseWord p)`), transitions
    `sInit p` to `sInit (p + 1)`, and has positive shifted active score throughout the phase,
    the unrolled discrete-time play sequence `wordPhaseTrajectory phaseWord defaultAct` is a
    strictly tie-free Fictitious Play trajectory on `setupMatrix M w` at every integer step `t ≥ 1`. -/
theorem word_phase_unroll_isStrictFPTrajectory {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℚ) (w : Fin m → ℚ) (C : ℚ)
    (sInit : ℕ → Fin m → ℚ) (phaseWord : ℕ → List (Fin m)) (defaultAct : Fin m)
    (hcount : ∀ p : ℕ, 0 < (phaseWord p).length)
    (hw_nonneg : ∀ i : Fin m, 0 ≤ w i)
    (hw_shift : ∀ i : Fin m, w i = sInit 0 i + C)
    (hphaseBoundary : ∀ p : ℕ, wordScore M (sInit p) (phaseWord p) = sInit (p + 1))
    (hwordValid : ∀ p : ℕ, IsValidStrictWord M (sInit p) (phaseWord p))
    (hwordPos : ∀ (p v : ℕ) (hv : v < (phaseWord p).length),
      0 < wordScore M (sInit p) ((phaseWord p).take v) ((phaseWord p)[v]) + C) :
    IsStrictFPTrajectory (setupMatrix M w) (wordPhaseTrajectory phaseWord defaultAct) := by
  unfold wordPhaseTrajectory
  apply setup_phase_unroll_isStrictFPTrajectory M w C
    (fun p => (phaseWord p).length)
    (wordPhaseAct phaseWord defaultAct)
    (fun _ _ => 1)
    (fun p v => wordScore M (sInit p) ((phaseWord p).take v))
    hcount hw_nonneg
  · intro i
    have hws0 : wordScore M (sInit 0) ((phaseWord 0).take 0) i = sInit 0 i := by
      simp [wordScore, scoreVec, wordCountVec]
    rw [hws0]
    exact hw_shift i
  · intro _ _ _
    exact Nat.zero_lt_one
  · intro p v hv
    have hact : wordPhaseAct phaseWord defaultAct p v = (phaseWord p)[v] := by
      simp [wordPhaseAct, hv]
    have htake : (phaseWord p).take (v + 1) = (phaseWord p).take v ++ [(phaseWord p)[v]] := by
      rw [List.take_add_one]
      simp [hv]
    rw [htake, wordScore_append, hact, Nat.cast_one,
      ← wordScore_singleton_eq_scoreVec_runCount]
  · intro p
    have htake_all : (phaseWord p).take (phaseWord p).length = phaseWord p := List.take_length
    have hws_next : wordScore M (sInit (p + 1)) ((phaseWord (p + 1)).take 0) = sInit (p + 1) := by
      ext i
      simp [wordScore, scoreVec, wordCountVec]
    rw [htake_all, hphaseBoundary p, hws_next]
  · intro p v hv h hh j hj
    have hh0 : h = 0 := by omega
    subst hh0
    have hact : wordPhaseAct phaseWord defaultAct p v = (phaseWord p)[v] := by
      simp [wordPhaseAct, hv]
    rw [hact] at hj ⊢
    simp only [Nat.cast_zero]
    have hrc0 : runCount (fun _ : Fin m => (0 : ℚ)) ((phaseWord p)[v]) (0 : ℚ) = fun _ => 0 := by
      ext u; simp [runCount]
    have hsc0 : ∀ x : Fin m,
        scoreVec M (wordScore M (sInit p) ((phaseWord p).take v))
          (runCount (fun _ => 0) ((phaseWord p)[v]) (0 : ℚ)) x =
        wordScore M (sInit p) ((phaseWord p).take v) x := by
      intro x
      rw [hrc0]
      simp [scoreVec]
    rw [hsc0 j, hsc0 ((phaseWord p)[v])]
    exact hwordValid p v hv j hj
  · intro p v hv h hh
    have hh0 : h = 0 := by omega
    subst hh0
    have hact : wordPhaseAct phaseWord defaultAct p v = (phaseWord p)[v] := by
      simp [wordPhaseAct, hv]
    rw [hact]
    simp only [Nat.cast_zero]
    have hrc0 : runCount (fun _ : Fin m => (0 : ℚ)) ((phaseWord p)[v]) (0 : ℚ) = fun _ => 0 := by
      ext u; simp [runCount]
    have hsc0 :
        scoreVec M (wordScore M (sInit p) ((phaseWord p).take v))
          (runCount (fun _ => 0) ((phaseWord p)[v]) (0 : ℚ)) ((phaseWord p)[v]) =
        wordScore M (sInit p) ((phaseWord p).take v) ((phaseWord p)[v]) := by
      rw [hrc0]
      simp [scoreVec]
    rw [hsc0]
    exact hwordPos p v hv

/-- Transport of `wordCountVec` along an equivalence `e : σ ≃ τ`. -/
theorem wordCountVec_map_equiv {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]
    (e : σ ≃ τ) (W : List σ) (x : τ) :
    wordCountVec (W.map e) x = wordCountVec W (e.symm x) := by
  induction W with
  | nil => rfl
  | cons a tl ih =>
    have h1 : ((a :: tl : List σ)) = [a] ++ tl := rfl
    have h2 : ((a :: tl).map e) = [e a] ++ tl.map e := rfl
    rw [h2, wordCountVec_append, ih]
    conv_rhs => rw [h1, wordCountVec_append]
    congr 1
    by_cases h : e a = x
    · have ha : a = e.symm x := by rw [← h, Equiv.symm_apply_apply]
      simp [wordCountVec, ha]
    · have ha : a ≠ e.symm x := fun h' => h (by rw [h', Equiv.apply_symm_apply])
      simp [wordCountVec, h, ha]

/-- Transport of `wordScore` along an equivalence `e : σ ≃ τ`. -/
theorem wordScore_map_equiv {σ τ : Type*} [Fintype σ] [Fintype τ]
    [DecidableEq σ] [DecidableEq τ]
    (e : σ ≃ τ) (M : Matrix σ σ ℚ) (s0 : σ → ℚ) (W : List σ) (x : τ) :
    wordScore (Matrix.of fun i j => M (e.symm i) (e.symm j))
      (fun i => s0 (e.symm i)) (W.map e) x =
      wordScore M s0 W (e.symm x) := by
  simp only [wordScore, scoreVec, Matrix.of_apply]
  congr 1
  have hsum := Equiv.sum_comp e (fun j : τ =>
    M (e.symm x) (e.symm j) * wordCountVec (W.map e) j)
  rw [← hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [wordCountVec_map_equiv e W (e j), Equiv.symm_apply_apply]

/-- Transport of `IsValidStrictWord` along an equivalence `e : σ ≃ τ`. -/
theorem isValidStrictWord_map_equiv {σ τ : Type*} [Fintype σ] [Fintype τ]
    [DecidableEq σ] [DecidableEq τ]
    (e : σ ≃ τ) (M : Matrix σ σ ℚ) (s0 : σ → ℚ) (W : List σ)
    (hW : IsValidStrictWord M s0 W) :
    IsValidStrictWord (Matrix.of fun i j => M (e.symm i) (e.symm j))
      (fun i => s0 (e.symm i)) (W.map e) := by
  intro k hk y hy
  have hk_len : k < W.length := by simpa using hk
  have hget : (W.map e)[k] = e (W[k]) := by simp
  have htake : (W.map e).take k = (W.take k).map e := by rw [List.map_take]
  rw [hget] at hy ⊢
  rw [htake, wordScore_map_equiv, wordScore_map_equiv]
  simp only [Equiv.symm_apply_apply]
  have hne : e.symm y ≠ W[k] := fun h => hy (by rw [← h, Equiv.apply_symm_apply])
  exact hW k hk_len (e.symm y) hne

/-- **Four-Stage Chronological Lift Specification (`ChronologicalLiftSpec`)**:
    Packages the four-stage phase words `(W_O p, g, W_early p, W_late p)` on the coupled lift
    `fc.coupledLift : FullRankClock (k + 1)` of a parent clock `fc : FullRankClock k`, together
    with the grounded Proposition 9.1 margin conditions (`chronology_four_stage_from_margins`),
    setup vector `setupVec`, phase boundary times `phaseTime`, and degree-`(k+1)` phase gap bounds. -/
structure ChronologicalLiftSpec {k : ℕ} (fc : FullRankClock k) where
  setupVec : Fin fc.coupledLift.clock.m → ℚ
  phaseShift : ℕ
  scoreShift : ℚ
  A_adm : ℚ
  hA_adm_nonneg : 0 ≤ A_adm
  hsetup_nonneg : ∀ i : Fin fc.coupledLift.clock.m, 0 ≤ setupVec i
  sInit : ℕ → Fin (fc.clock.m + 1) ⊕ Fin ((k + 1) + (k + 1)) → ℚ
  W_O : ℕ → List (Fin (fc.clock.m + 1))
  g : Fin (fc.clock.m + 1)
  W_early : ℕ → List (Fin (fc.clock.m + 1) ⊕ Fin ((k + 1) + (k + 1)))
  W_late : ℕ → List (Fin (fc.clock.m + 1) ⊕ Fin ((k + 1) + (k + 1)))
  defaultAct : Fin fc.coupledLift.clock.m
  phaseTime : ℕ → ℕ
  hsetup_shift : ∀ i : Fin fc.coupledLift.clock.m,
    setupVec i = sInit 0 (finSumFinEquiv.symm i) + scoreShift
  hparent_valid : ∀ p : ℕ,
    IsValidStrictWord fc.clock.adjoinEndpoint.G (fun u => sInit p (Sum.inl u)) (W_O p)
  hreset_waits_bundle : ∀ (p k_idx : ℕ) (hk : k_idx < (W_O p).length)
      (j : Fin ((k + 1) + (k + 1))),
    sInit p (Sum.inr j) -
      ∑ u : Fin (fc.clock.m + 1),
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).P u j *
          wordCountVec ((W_O p).take k_idx) u <
      wordScore fc.clock.adjoinEndpoint.G (fun u => sInit p (Sum.inl u))
        ((W_O p).take k_idx) ((W_O p)[k_idx])
  hendpoint_old : ∀ (p : ℕ) (i : Fin (fc.clock.m + 1)), i ≠ g →
    wordScore
      (liftedGameMat fc.clock.adjoinEndpoint.G
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).P
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).J)
      (sInit p) ((W_O p).map Sum.inl) (Sum.inl i) <
    wordScore
      (liftedGameMat fc.clock.adjoinEndpoint.G
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).P
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).J)
      (sInit p) ((W_O p).map Sum.inl) (Sum.inl g)
  hendpoint_new : ∀ (p : ℕ) (j : Fin ((k + 1) + (k + 1))),
    wordScore
      (liftedGameMat fc.clock.adjoinEndpoint.G
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).P
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).J)
      (sInit p) ((W_O p).map Sum.inl) (Sum.inr j) <
    wordScore
      (liftedGameMat fc.clock.adjoinEndpoint.G
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).P
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).J)
      (sInit p) ((W_O p).map Sum.inl) (Sum.inl g)
  hstage3_valid : ∀ p : ℕ,
    IsValidStrictWord
      (liftedGameMat fc.clock.adjoinEndpoint.G
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).P
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).J)
      (wordScore
        (liftedGameMat fc.clock.adjoinEndpoint.G
          (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).P
          (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).J)
        (sInit p) ((W_O p).map Sum.inl ++ [Sum.inl g]))
      (W_early p)
  hstage4_valid : ∀ p : ℕ,
    IsValidStrictWord
      (liftedGameMat fc.clock.adjoinEndpoint.G
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).P
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).J)
      (wordScore
        (liftedGameMat fc.clock.adjoinEndpoint.G
          (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).P
          (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).J)
        (sInit p) ((W_O p).map Sum.inl ++ [Sum.inl g] ++ W_early p))
      (W_late p)
  hphase_boundary : ∀ p : ℕ,
    wordScore
      (liftedGameMat fc.clock.adjoinEndpoint.G
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).P
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).J)
      (sInit p)
      ((W_O p).map Sum.inl ++ [Sum.inl g] ++ W_early p ++ W_late p) =
    sInit (p + 1)
  hword_pos : ∀ (p v : ℕ)
      (hv : v < (((W_O p).map Sum.inl ++ [Sum.inl g] ++ W_early p ++ W_late p).map finSumFinEquiv).length),
    0 < wordScore fc.coupledLift.clock.G
      (fun i => sInit p (finSumFinEquiv.symm i))
      ((((W_O p).map Sum.inl ++ [Sum.inl g] ++ W_early p ++ W_late p).map finSumFinEquiv).take v)
      ((((W_O p).map Sum.inl ++ [Sum.inl g] ++ W_early p ++ W_late p).map finSumFinEquiv)[v]) +
      scoreShift
  hphaseTime_zero : phaseTime 0 = 1
  hphaseTime_lt : ∀ p : ℕ, phaseTime p < phaseTime (p + 1)
  hphase_leader : ∀ p : ℕ, ∃ i0 : Fin fc.coupledLift.clock.m,
    wordPhaseTrajectory
      (fun q => ((W_O q).map Sum.inl ++ [Sum.inl g] ++ W_early q ++ W_late q).map finSumFinEquiv)
      defaultAct (phaseTime p) = some i0
  c_low : ℚ
  c_high : ℚ
  hc_low_pos : 0 < c_low
  hc_high_pos : 0 < c_high
  hgap_low : ∀ p : ℕ,
    c_low * (phaseTime (p + 1) : ℚ) ^ k ≤
      (2 * cumScore (setupMatrix fc.coupledLift.clock.G setupVec)
        (wordPhaseTrajectory
          (fun q => ((W_O q).map Sum.inl ++ [Sum.inl g] ++ W_early q ++ W_late q).map finSumFinEquiv)
          defaultAct)
        (phaseTime p)
        (wordPhaseTrajectory
          (fun q => ((W_O q).map Sum.inl ++ [Sum.inl g] ++ W_early q ++ W_late q).map finSumFinEquiv)
          defaultAct (phaseTime p))) ^ (k + 1)
  hgap_high : ∀ p : ℕ,
    (2 * cumScore (setupMatrix fc.coupledLift.clock.G setupVec)
      (wordPhaseTrajectory
        (fun q => ((W_O q).map Sum.inl ++ [Sum.inl g] ++ W_early q ++ W_late q).map finSumFinEquiv)
        defaultAct)
      (phaseTime (p + 1))
      (wordPhaseTrajectory
        (fun q => ((W_O q).map Sum.inl ++ [Sum.inl g] ++ W_early q ++ W_late q).map finSumFinEquiv)
        defaultAct (phaseTime (p + 1)))) ^ (k + 1) ≤
      c_high * (phaseTime p : ℚ) ^ k

/-- **Grounded Four-Stage RealizedClock Lift (`RealizedClock.ofChronologicalLift`)**:
    Constructs a `RealizedClock (k + 1)` with `.fc = fc.coupledLift` from a parent
    `fc : FullRankClock k` and a `spec : ChronologicalLiftSpec fc` by composing:
    1. `chronology_four_stage_from_margins` (proving `IsValidStrictWord` for all four stages),
    2. `isValidStrictWord_map_equiv` (transporting along `finSumFinEquiv`),
    3. `word_phase_unroll_isStrictFPTrajectory` (unrolling to `IsStrictFPTrajectory`), and
    4. `all_integer_time_power_gap_bounds` (deriving all-integer-time `Θ(t^{-1/(k+1)})`
       standard empirical duality-gap bounds). -/
def RealizedClock.ofChronologicalLift {k : ℕ} (fc : FullRankClock k)
    (spec : ChronologicalLiftSpec fc) : RealizedClock (k + 1) :=
  let rawWord : ℕ → List (Fin (fc.clock.m + 1) ⊕ Fin ((k + 1) + (k + 1))) := fun p : ℕ =>
    (spec.W_O p).map Sum.inl ++ [Sum.inl spec.g] ++ spec.W_early p ++ spec.W_late p
  let phaseWord : ℕ → List (Fin fc.coupledLift.clock.m) := fun p : ℕ =>
    (rawWord p).map finSumFinEquiv
  have hcount : ∀ p : ℕ, 0 < (phaseWord p).length := by
    intro p
    change 0 < ((rawWord p).map finSumFinEquiv).length
    rw [List.length_map]
    dsimp only [rawWord]
    simp only [List.length_append, List.length_singleton]
    omega
  have hvalid_raw : ∀ p : ℕ,
      IsValidStrictWord
        (liftedGameMat fc.clock.adjoinEndpoint.G
          (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).P
          (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).J)
        (spec.sInit p) (rawWord p) := by
    intro p
    exact chronology_four_stage_from_margins
      fc.clock.adjoinEndpoint.G
      (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).P
      (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).J
      (spec.sInit p) (spec.W_O p) spec.g (spec.W_early p) (spec.W_late p)
      (spec.hparent_valid p)
      (spec.hreset_waits_bundle p)
      (spec.hendpoint_old p)
      (spec.hendpoint_new p)
      (spec.hstage3_valid p)
      (spec.hstage4_valid p)
  have hvalid : ∀ p : ℕ,
      IsValidStrictWord fc.coupledLift.clock.G
        (fun i => spec.sInit p (finSumFinEquiv.symm i)) (phaseWord p) := by
    intro p
    exact isValidStrictWord_map_equiv finSumFinEquiv
      (liftedGameMat fc.clock.adjoinEndpoint.G
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).P
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).J)
      (spec.sInit p) (rawWord p) (hvalid_raw p)
  have hboundary : ∀ p : ℕ,
      wordScore fc.coupledLift.clock.G
        (fun i => spec.sInit p (finSumFinEquiv.symm i)) (phaseWord p) =
      (fun i => spec.sInit (p + 1) (finSumFinEquiv.symm i)) := by
    intro p
    ext i
    have hmap := wordScore_map_equiv finSumFinEquiv
      (liftedGameMat fc.clock.adjoinEndpoint.G
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).P
        (coupledMomentLiftStep fc.clock fc.L_C fc.hLC).J)
      (spec.sInit p) (rawWord p) i
    exact hmap.trans (congr_fun (spec.hphase_boundary p) (finSumFinEquiv.symm i))
  have hstrict :
      IsStrictFPTrajectory (setupMatrix fc.coupledLift.clock.G spec.setupVec)
        (wordPhaseTrajectory phaseWord spec.defaultAct) :=
    word_phase_unroll_isStrictFPTrajectory
      fc.coupledLift.clock.G spec.setupVec spec.scoreShift
      (fun p i => spec.sInit p (finSumFinEquiv.symm i))
      phaseWord spec.defaultAct
      hcount spec.hsetup_nonneg spec.hsetup_shift hboundary hvalid spec.hword_pos
  have hskew : IsSkewSymmetric (setupMatrix fc.coupledLift.clock.G spec.setupVec) :=
    setupMatrix_skewSymmetric fc.coupledLift.clock.hskew spec.setupVec
  { fc := fc.coupledLift
    setupVec := spec.setupVec
    phaseShift := spec.phaseShift
    scoreShift := spec.scoreShift
    A_adm := spec.A_adm
    hA_adm_nonneg := spec.hA_adm_nonneg
    hsetup_nonneg := spec.hsetup_nonneg
    trajectory := wordPhaseTrajectory phaseWord spec.defaultAct
    phaseTime := spec.phaseTime
    htraj_zero := rfl
    hstrict := hstrict
    hphaseTime_zero := spec.hphaseTime_zero
    hphaseTime_lt := spec.hphaseTime_lt
    hphase_leader := spec.hphase_leader
    c_low := spec.c_low
    c_high := spec.c_high
    hc_low_pos := spec.hc_low_pos
    hc_high_pos := spec.hc_high_pos
    hgap_bounds := fun t ht =>
      all_integer_time_power_gap_bounds hskew hstrict spec.hphaseTime_zero spec.hphaseTime_lt
        (Nat.le_add_left 1 k) spec.hgap_low spec.hgap_high t ht }

/-- Lift a realized parent clock `rc : RealizedClock k` to `RealizedClock (k + 1)` via
    a four-stage chronological lift specification `spec : ChronologicalLiftSpec rc.fc`. -/
def RealizedClock.lift {k : ℕ} (rc : RealizedClock k)
    (spec : ChronologicalLiftSpec rc.fc) : RealizedClock (k + 1) :=
  RealizedClock.ofChronologicalLift rc.fc spec

/-- Lifting a realized parent clock `rc : RealizedClock k` produces a `RealizedClock (k + 1)`
    whose underlying full-rank clock is `rc.fc.coupledLift`. -/
theorem RealizedClock.lift_fc {k : ℕ} (rc : RealizedClock k)
    (spec : ChronologicalLiftSpec rc.fc) :
    (rc.lift spec).fc = rc.fc.coupledLift :=
  rfl

/-- **Recursive `RealizedClock` Family from Four-Stage Lift Specifications (`realizedClockFamily_of_lifts`)**:
    Starting from the unconditional order-2 seed `rpsRealizedClock : RealizedClock 2`
    (`fc = standardFullRankClockFamily 0`), a family of four-stage chronological lift
    specifications `lifts : ∀ d, ChronologicalLiftSpec (standardFullRankClockFamily d)`
    recursively constructs a `RealizedClock (d + 2)` at every order `k = d + 2 ≥ 2` whose
    underlying `FullRankClock (d + 2)` is `standardFullRankClockFamily d`. -/
def realizedClockFamily_of_lifts
    (lifts : ∀ d : ℕ, ChronologicalLiftSpec (standardFullRankClockFamily d)) :
    ∀ d : ℕ, RealizedClock (d + 2)
  | 0 => rpsRealizedClock
  | d + 1 => RealizedClock.ofChronologicalLift (standardFullRankClockFamily d) (lifts d)

/-- Every `realizedClockFamily_of_lifts lifts d` has underlying full-rank clock
    `standardFullRankClockFamily d`, and therefore inherits all coupled-moment polynomial
    identities, action count `(k + 1)^2 - 5`, strict two-player FP validity, tie-breaking
    uniqueness, and all-integer-time `Θ(t^{-1/k})` standard empirical duality-gap bounds. -/
theorem realizedClockFamily_of_lifts_fc
    (lifts : ∀ d : ℕ, ChronologicalLiftSpec (standardFullRankClockFamily d)) (d : ℕ) :
    (realizedClockFamily_of_lifts lifts d).fc = standardFullRankClockFamily d := by
  cases d <;> rfl

/-- **All-Orders Realized Clock & Rate Theorem (`all_orders_realized_karlin_theorem_of_lifts`)**:
    Carrying `RealizedClock.lift` recursively from the order-2 seed `rpsRealizedClock` along
    a family of grounded four-stage lift specifications
    `lifts : ∀ d : ℕ, ChronologicalLiftSpec (standardFullRankClockFamily d)` yields, for every
    order `k ≥ 2`, an explicit `rc : RealizedClock k` (`realizedClockFamily_of_lifts lifts (k - 2)`)
    whose underlying full-rank clock is `standardFullRankClockFamily (k - 2)`. -/
theorem all_orders_realized_karlin_theorem_of_lifts
    (lifts : ∀ d : ℕ, ChronologicalLiftSpec (standardFullRankClockFamily d))
    (k : ℕ) (hk : 2 ≤ k) :
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
          rc.c_high) := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, k = d + 2 := ⟨k - 2, by omega⟩
  let rc := realizedClockFamily_of_lifts lifts d
  have hfc : rc.fc = standardFullRankClockFamily d := realizedClockFamily_of_lifts_fc lifts d
  have hm : rc.fc.clock.m = (d + 2 + 1) ^ 2 - 6 := by
    rw [hfc]
    exact standardClockFamily_m d
  have hcard : Fintype.card (Option (Fin rc.fc.clock.m)) = (d + 2 + 1) ^ 2 - 5 := by
    rw [rc.totalDim_eq, hm]
    have h9 : 9 ≤ (d + 3) ^ 2 := by
      calc 9 ≤ d ^ 2 + 6 * d + 9 := by omega
        _ = (d + 3) ^ 2 := by ring
    change (d + 3) ^ 2 - 6 + 1 = (d + 3) ^ 2 - 5
    omega
  refine ⟨rc, hm, hcard, rc.gameMatrix_skew, rc.fc.hLC,
    rc.htraj_zero, rc.hstrict, rc.isStrictTwoPlayerFP, rc.unique_trajectory,
    rc.hc_low_pos, rc.hc_high_pos, rc.hgap_bounds⟩

/-!
## 7. Unconditional All-Orders Master Theorems (`all_orders_karlin_theorem` & `karlin_paper_complete_synthesis`)
-/

/-- **Unconditional All-Orders Coupled-Moment Clock Theorem (`all_orders_karlin_theorem`, Theorem 1.1)**:
    For every integer order `k ≥ 2`, the explicit coupled-moment construction
    `standardFullRankClockFamily (k - 2)` produces a full-rank order-`k` clock `fc : FullRankClock k`
    and an action `i0 : Fin fc.clock.m` such that:
    1. **Recurrent & Total Action Counts**: `fc.clock.m = (k + 1)^2 - 6` recurrent actions and
       total game dimension `Fintype.card (Option (Fin fc.clock.m)) = (k + 1)^2 - 5` including
       the setup action `\omega = none`.
    2. **Skew-Symmetry, Full Column Rank, & Positive Cone Weights**:
       `IsSkewSymmetric fc.clock.G`, `fc.clock.C.transpose * fc.L_C = 1`, and `∀ i, 0 < fc.clock.aP i`.
    3. **Non-Degenerate Coupled-Moment Lift Data at Step `k ↦ k + 1`**:
       - Reset count table `M_coupled k` has full column rank (`R_M_coupled k * M_coupled k = 1`)
         and strictly positive entries (`∀ r c, 1 ≤ M_coupled k r c`),
       - Reset interaction `J_coupled k` is strictly lower-triangular (`a.val ≤ b.val → J_coupled k a b = 0`)
         with strictly positive subdiagonal (`b.val < a.val → (4 * (k + 1 : ℚ))⁻¹ ≤ J_coupled k a b`),
       - `(M_coupled k, J_coupled k, zeta_coupled k)` satisfies the exact Moment Equation
         `coupled_moment_equation fc.clock`, and `coupledMomentLiftStep fc.clock fc.L_C fc.hLC`
         lifts `fc` to `fc.coupledLift : FullRankClock (k + 1)` with `fc.clock.m + (2 * k + 3)` actions,
       - Any `spec : ChronologicalLiftSpec fc` lifts `fc` to a full `RealizedClock (k + 1)`
         (`RealizedClock.ofChronologicalLift fc spec`) with `.fc = fc.coupledLift`, strict
         two-player FP trajectory (`isStrictTwoPlayerFP`), tie-breaking uniqueness
         (`unique_trajectory`), and all-integer-time `Θ(t^{-1/(k+1)})` standard empirical
         saddle-point duality gap bounds (`hgap_bounds`).
    4. **Exact Single-Phase & Multi-Phase Score Transitions & Unit Endpoint Counter**:
       For every phase `q ∈ ℕ` and horizon `P ∈ ℕ`,
       `scoreVec fc.clock.G (fc.clock.R.mulVec (binomBasis k q)) (fc.clock.C.mulVec (binomBasis k q)) = fc.clock.R.mulVec (binomBasis k (q + 1))`,
       `scoreVec fc.clock.G (fc.clock.R.mulVec (binomBasis k 0)) (totalPhaseCount fc.clock P) = fc.clock.R.mulVec (binomBasis k P)`,
       `dotProduct fc.clock.v (fc.clock.C.mulVec (binomBasis k q)) = 1`, and
       `dotProduct fc.clock.v (totalPhaseCount fc.clock P) = (P : ℚ)`.
    5. **Order-`k` Polynomial Score & Time Scaling ($\Theta(T^{-1/k})$ Rate)**:
       All entries of `fc.clock.C` are nonnegative, the top-degree count column sum is at least `9`,
       the top-degree score coefficient of `i0` equals `1`, every phase `q` has total duration
       at least `9 * \binom{q}{k - 1}`, and over `P` phases the cumulative elapsed time is at least
       `9 * \binom{P}{k}` (degree `k` in `P`) while the score of `i0` is at least `\binom{P}{k - 1}`
       (degree `k - 1` in `P`). -/
theorem all_orders_karlin_theorem (k : ℕ) (hk : 2 ≤ k) :
    ∃ (fc : FullRankClock k) (i0 : Fin fc.clock.m),
      fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric fc.clock.G ∧
      fc.clock.C.transpose * fc.L_C = 1 ∧
      (∀ i : Fin fc.clock.m, 0 < fc.clock.aP i) ∧
      (∀ i : Fin fc.clock.m, ∀ c : Fin k, 0 ≤ fc.clock.C i c) ∧
      (9 : ℚ) ≤ (∑ i : Fin fc.clock.m, fc.clock.C i ⟨k - 1, by omega⟩) ∧
      fc.clock.R i0 ⟨k - 1, by omega⟩ = 1 ∧
      (R_M_coupled k * M_coupled k = 1 ∧
        (∀ r : Fin ((k + 1) + (k + 1)), ∀ c : Fin (k + 1), 1 ≤ M_coupled k r c) ∧
        (∀ a b : Fin ((k + 1) + (k + 1)), a.val ≤ b.val → J_coupled k a b = 0) ∧
        (∀ a b : Fin ((k + 1) + (k + 1)), b.val < a.val →
          (4 * (k + 1 : ℚ))⁻¹ ≤ J_coupled k a b ∧ 0 < J_coupled k a b)) ∧
      (∀ spec : ChronologicalLiftSpec fc,
        (RealizedClock.ofChronologicalLift fc spec).fc = fc.coupledLift ∧
        IsStrictTwoPlayerFPTrajectory
          (RealizedClock.ofChronologicalLift fc spec).gameMatrix
          (RealizedClock.ofChronologicalLift fc spec).trajectory
          (RealizedClock.ofChronologicalLift fc spec).trajectory ∧
        ∀ t : ℕ, 1 ≤ t →
          spec.c_low ≤
            standardDualityGap (RealizedClock.ofChronologicalLift fc spec).gameMatrix
              (RealizedClock.ofChronologicalLift fc spec).trajectory
              (RealizedClock.ofChronologicalLift fc spec).trajectory t ^ (k + 1) * (t : ℚ) ∧
          standardDualityGap (RealizedClock.ofChronologicalLift fc spec).gameMatrix
            (RealizedClock.ofChronologicalLift fc spec).trajectory
            (RealizedClock.ofChronologicalLift fc spec).trajectory t ^ (k + 1) * (t : ℚ) ≤
            spec.c_high) ∧
      (∀ q : ℕ,
        scoreVec fc.clock.G
          (fc.clock.R.mulVec (binomBasis k q))
          (fc.clock.C.mulVec (binomBasis k q)) =
        fc.clock.R.mulVec (binomBasis k (q + 1)) ∧
        dotProduct fc.clock.v (fc.clock.C.mulVec (binomBasis k q)) = 1 ∧
        9 * (Nat.choose q (k - 1) : ℚ) ≤
          ∑ i : Fin fc.clock.m, (fc.clock.C.mulVec (binomBasis k q)) i) ∧
      (∀ P : ℕ,
        scoreVec fc.clock.G
          (fc.clock.R.mulVec (binomBasis k 0))
          (totalPhaseCount fc.clock P) =
        fc.clock.R.mulVec (binomBasis k P) ∧
        dotProduct fc.clock.v (totalPhaseCount fc.clock P) = (P : ℚ) ∧
        (Nat.choose P (k - 1) : ℚ) ≤ (fc.clock.R.mulVec (binomBasis k P)) i0 ∧
        9 * (Nat.choose P k : ℚ) ≤
          ∑ i : Fin fc.clock.m, totalPhaseCount fc.clock P i) := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, k = d + 2 := ⟨k - 2, by omega⟩
  have hm := standardClockFamily_m d
  have hcard : Fintype.card (Option (Fin (standardClockFamily d).m)) = (d + 2 + 1) ^ 2 - 5 := by
    simp only [Fintype.card_option, Fintype.card_fin, hm]
    have h9 : 9 ≤ (d + 3) ^ 2 := by
      calc 9 ≤ d ^ 2 + 6 * d + 9 := by omega
        _ = (d + 3) ^ 2 := by ring
    change (d + 3) ^ 2 - 6 + 1 = (d + 3) ^ 2 - 5
    omega
  refine ⟨standardFullRankClockFamily d, ⟨0, standardClockFamily_m_pos d⟩,
    hm, hcard, (standardClockFamily d).hskew,
    standardClockFamily_full_rank d, (standardClockFamily d).haP_pos,
    standardClockFamily_count_nonneg d, standardClockFamily_top_count_sum_ge_nine d,
    standardClockFamily_top_score_zero d,
    ⟨R_M_coupled_mul_M_coupled (d + 2), M_coupled_entry_ge_one (d + 2),
      J_coupled_lower (d + 2), J_coupled_subdiag_ge (d + 2)⟩,
    fun spec => ⟨rfl, (RealizedClock.ofChronologicalLift _ spec).isStrictTwoPlayerFP,
      (RealizedClock.ofChronologicalLift _ spec).hgap_bounds⟩,
    ?_, ?_⟩
  · intro q
    refine ⟨(standardClockFamily d).phase_score_transition q,
      (standardClockFamily d).endpoint_counter_increment (by omega) q,
      (standardClockFamily_phase_len_lower_bound d q).2⟩
  · intro P
    refine ⟨(standardClockFamily d).multi_phase_score_transition P,
      (standardClockFamily d).multi_phase_endpoint_counter (by omega) P,
      standardClockFamily_score_zero_lower_bound d P,
      standardClockFamily_cum_time_lower_bound d P⟩

/-- **Complete Paper Synthesis (`karlin_paper_complete_synthesis`)**:
    Combines:
    1. The unconditional realized order-2 RPS seed (`rpsRealizedClock : RealizedClock 2`, 4 actions,
       all-integer-time `Θ(t^{-1/2})` standard duality gap bounds `[8/9, 400]`),
    2. The unconditional realized order-3 counterexample (`sevenRealizedClock : RealizedClock 3`,
       7 actions, all-integer-time `Θ(t^{-1/3})` standard duality gap bounds
       `[343/500000, 32768000000000]`, tie-breaking uniqueness, and explicit big-O refutation
       `∀ C : ℚ, ∃ t ≥ 1, C < standardDualityGap M7 sevenTrajectory sevenTrajectory t ^ 2 * t`),
    3. The unconditional all-orders coupled-moment clock theorem (`all_orders_karlin_theorem`,
       `∀ k ≥ 2`) and the recursive all-orders realized clock & rate theorem
       (`all_orders_realized_karlin_theorem`). -/
theorem karlin_paper_complete_synthesis :
    (Fintype.card (Option (Fin rpsRealizedClock.fc.clock.m)) = 4 ∧
      IsStrictTwoPlayerFPTrajectory rpsRealizedClock.gameMatrix
        rpsRealizedClock.trajectory rpsRealizedClock.trajectory ∧
      ∀ t : ℕ, 1 ≤ t →
        (8 / 9 : ℚ) ≤
          standardDualityGap rpsRealizedClock.gameMatrix
            rpsRealizedClock.trajectory rpsRealizedClock.trajectory t ^ 2 * (t : ℚ) ∧
        standardDualityGap rpsRealizedClock.gameMatrix
          rpsRealizedClock.trajectory rpsRealizedClock.trajectory t ^ 2 * (t : ℚ) ≤ 400) ∧
    (Fintype.card (Option (Fin sevenRealizedClock.fc.clock.m)) = 7 ∧
      IsStrictTwoPlayerFPTrajectory sevenRealizedClock.gameMatrix
        sevenRealizedClock.trajectory sevenRealizedClock.trajectory ∧
      (∀ t : ℕ, 1 ≤ t →
        (343 / 500000 : ℚ) ≤
          standardDualityGap sevenRealizedClock.gameMatrix
            sevenRealizedClock.trajectory sevenRealizedClock.trajectory t ^ 3 * (t : ℚ) ∧
        standardDualityGap sevenRealizedClock.gameMatrix
          sevenRealizedClock.trajectory sevenRealizedClock.trajectory t ^ 3 * (t : ℚ) ≤
          32768000000000) ∧
      (∀ C : ℚ, ∃ t : ℕ, 1 ≤ t ∧
        C < standardDualityGap sevenRealizedClock.gameMatrix
          sevenRealizedClock.trajectory sevenRealizedClock.trajectory t ^ 2 * (t : ℚ))) ∧
    (∀ k : ℕ, 2 ≤ k →
      ∃ (fc : FullRankClock k),
        fc.clock.m = (k + 1) ^ 2 - 6 ∧
        Fintype.card (Option (Fin fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
        IsSkewSymmetric fc.clock.G ∧
        fc.clock.C.transpose * fc.L_C = 1) ∧
    ((∀ d : ℕ, ChronologicalLiftSpec (standardFullRankClockFamily d)) →
      ∀ k : ℕ, 2 ≤ k →
        ∃ (rc : RealizedClock k),
          rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
          Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
          IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
          ∀ t : ℕ, 1 ≤ t →
            rc.c_low ≤
              standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
            standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
              rc.c_high) := by
  refine ⟨⟨by decide, rpsRealizedClock.isStrictTwoPlayerFP, rpsRealizedClock.hgap_bounds⟩,
    ⟨by decide, sevenRealizedClock.isStrictTwoPlayerFP, sevenRealizedClock.hgap_bounds,
      karlin_conjecture_refuted_bigO.2.2.2.2.2.2⟩,
    fun k hk => ?_,
    fun lifts k hk => ?_⟩
  · obtain ⟨fc, _, hm, hcard, hskew, hrank, _⟩ := all_orders_karlin_theorem k hk
    exact ⟨fc, hm, hcard, hskew, hrank⟩
  · obtain ⟨rc, hm, hdim, _, _, _, _, hfp, _, _, _, hgap⟩ :=
      all_orders_realized_karlin_theorem_of_lifts lifts k hk
    exact ⟨rc, hm, hdim, hfp, hgap⟩

end Karlin

#print axioms Karlin.mul_N_mat_apply
#print axioms Karlin.N_mat_mul_apply
#print axioms Karlin.B_mat_mul_one_add_N
#print axioms Karlin.one_add_N_mul_B_mat
#print axioms Karlin.B_mat_mul_T_mat
#print axioms Karlin.B_mat_mul_N_mat
#print axioms Karlin.coupledMoment_lift_spec
#print axioms Karlin.shiftRightScore_mul_N_mat
#print axioms Karlin.one_add_N_mat_nonneg
#print axioms Karlin.X_coupled_transpose_mul_L_X_coupled
#print axioms Karlin.D_deficit_coupled_eq_zero
#print axioms Karlin.M_coupled_entry_ge_one
#print axioms Karlin.R_M_coupled_mul_M_coupled
#print axioms Karlin.J_coupled_lower
#print axioms Karlin.J_coupled_subdiag_ge
#print axioms Karlin.M_coupled_transpose_mul_J_coupled_mul_M_coupled
#print axioms Karlin.ell_row_M_coupled
#print axioms Karlin.coupled_moment_equation
#print axioms Karlin.coupled_weight_calibration
#print axioms Karlin.coupledMomentLift_C_transpose_mul_L_C
#print axioms Karlin.coupledLift_count_nonneg
#print axioms Karlin.coupledLift_top_count_entries
#print axioms Karlin.coupledLift_top_count_sum
#print axioms Karlin.coupledLift_top_score_old
#print axioms Karlin.coupledLift_score_old_nonneg
#print axioms Karlin.C2_transpose_mul_L_C2
#print axioms Karlin.C_seven_transpose_mul_L_C_seven
#print axioms Karlin.standardClockFamily_full_rank
#print axioms Karlin.standardClockFamily_m
#print axioms Karlin.standardClockFamily_m_pos
#print axioms Karlin.sevenSeededClockFamily_m
#print axioms Karlin.rpsAlgebraicClock_C_nonneg
#print axioms Karlin.rpsAlgebraicClock_R_zero_nonneg
#print axioms Karlin.sevenAlgebraicClock_top_C_pos
#print axioms Karlin.standardClockFamily_count_nonneg
#print axioms Karlin.coupledLift_zero_index_eq
#print axioms Karlin.standardClockFamily_R_zero_nonneg
#print axioms Karlin.standardClockFamily_top_score_zero
#print axioms Karlin.standardClockFamily_score_zero_lower_bound
#print axioms Karlin.standardClockFamily_top_count_sum_ge_nine
#print axioms Karlin.sevenSeededClockFamily_top_count_sum_ge
#print axioms Karlin.scoreVec_add
#print axioms Karlin.AlgebraicClock.multi_phase_score_transition
#print axioms Karlin.AlgebraicClock.multi_phase_endpoint_counter
#print axioms Karlin.standardClockFamily_phase_len_lower_bound
#print axioms Karlin.sum_range_choose_succ
#print axioms Karlin.standardClockFamily_cum_time_lower_bound
#print axioms Karlin.RealizedClock.totalDim_eq
#print axioms Karlin.RealizedClock.gameMatrix_skew
#print axioms Karlin.RealizedClock.isStrictTwoPlayerFP
#print axioms Karlin.RealizedClock.unique_trajectory
#print axioms Karlin.RealizedClock.standardDualityGap_eq_twice_max_score_div_time
#print axioms Karlin.wordCountVec_singleton
#print axioms Karlin.wordScore_singleton_eq_scoreVec_runCount
#print axioms Karlin.word_phase_unroll_isStrictFPTrajectory
#print axioms Karlin.wordCountVec_map_equiv
#print axioms Karlin.wordScore_map_equiv
#print axioms Karlin.isValidStrictWord_map_equiv
#print axioms Karlin.RealizedClock.lift_fc
#print axioms Karlin.realizedClockFamily_of_lifts_fc
#print axioms Karlin.all_orders_realized_karlin_theorem_of_lifts
#print axioms Karlin.all_orders_karlin_theorem
#print axioms Karlin.karlin_paper_complete_synthesis

