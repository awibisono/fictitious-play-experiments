import Karlin.FictitiousPlay
import Karlin.RPSClock
import Karlin.CubicSevenAction
import Karlin.BinomialBasis
import Karlin.InductiveLift
import Karlin.ChronologyAndMain
import Karlin.UnrolledTrajectory

/-!
# Bundled Algebraic Clock Structure, Inductive Lift, and Unrolled Phase Chronology

This module packages:

1. **The Bundled `AlgebraicClock w` Structure and Seed Instantiations**:
   * `AlgebraicClock w`: bundles `(m, G, R, C, v, aP)` together with `IsSkewSymmetric G`,
     `G * C = R * N_mat w`, `vᵀ * C = e_0ᵀ`, and `aP > 0`.
   * `rpsAlgebraicClock : AlgebraicClock 2` (`m = 3`, Theorem 2.1 / Section 3).
   * `sevenAlgebraicClock : AlgebraicClock 3` (`m = 6`, Theorem E.1 / Section 4).
2. **Universal Clock Consequences**:
   * `AlgebraicClock.phase_score_transition`: exact phase-to-phase score evolution
     `scoreVec clock.G (clock.R p_w(q)) (clock.C p_w(q)) = clock.R p_w(q + 1)`.
   * `AlgebraicClock.endpoint_counter_increment`: unit endpoint counter increment
     `vᵀ (C p_w(q)) = 1` at every phase `q ∈ ℕ`.
   * `AlgebraicClock.cone_identity` & `AlgebraicClock.scaled_skew`: Lemma 6.1 invariants.
3. **Bundled Inductive Clock Lift (`AlgebraicClock w → AlgebraicClock (w + 1)`)**:
   * `liftedGameMat_skew`: skew-symmetry of `G_+ = [[G_O, P], [-Pᵀ, J - Jᵀ]]`.
   * `liftedGameMat_mul_liftedCountMat`: full block-matrix clock equation `G_+ * C_+ = R_+ * N`.
   * `liftedWeightVec_mul_liftedCountMat`: full block-vector weight calibration `v_+ᵀ * C_+ = e_0ᵀ`.
   * `AlgebraicClock.lift` & `AlgebraicClock.lift_spec`: maps `clock : AlgebraicClock w` and
     `LiftStepData clock n` to `AlgebraicClock (w + 1)` with `clock.m + n` recurrent actions.
4. **Unrolled Cubic Phase Chronology for `M7` (`karlin_conjecture_disproof_unrolled`)**:
   * `seven_phase_start_time`: proves that the discrete step `t_p = sevenPhaseStartStep p` at the
     start of phase `p ∈ ℕ` in `sevenTrajectory` satisfies the exact cubic polynomial
     `2 * (t_p : ℚ) = 3822 * p^3 + 214491 * p^2 + 4109779 * p + 2`.
   * `karlin_conjecture_disproof_unrolled`: combines `IsSkewSymmetric M7`,
     `IsStrictFPTrajectory M7 sevenTrajectory`, and the exact cubic phase-start time and
     quadratic phase-start score formulas.
-/

namespace Karlin

/-!
## 1. The Bundled `AlgebraicClock` Structure
-/

/-- An order-`w` algebraic clock (`w = k` in the paper's falling-factorial basis `p_w(q)`)
    packaging `m` recurrent actions, a skew-symmetric payoff matrix `G ∈ ℚ^{m × m}`,
    phase-start score table `R ∈ ℚ^{m × w}`, phase action-count table `C ∈ ℚ^{m × w}`,
    endpoint counter row `v ∈ ℚ^m`, and positive cone weight vector `aP ∈ ℚ^m`. -/
structure AlgebraicClock (w : ℕ) where
  /-- Number of recurrent actions in the clock. -/
  m : ℕ
  /-- Skew-symmetric recurrent payoff matrix `G ∈ ℚ^{m × m}`. -/
  G : Matrix (Fin m) (Fin m) ℚ
  /-- Phase-start score table `R ∈ ℚ^{m × w}` in the falling-factorial basis `p_w(q)`. -/
  R : Matrix (Fin m) (Fin w) ℚ
  /-- Phase action-count table `C ∈ ℚ^{m × w}` in the falling-factorial basis `p_w(q)`. -/
  C : Matrix (Fin m) (Fin w) ℚ
  /-- Endpoint counter row `v ∈ ℚ^m` satisfying `vᵀ * C = e_0ᵀ`. -/
  v : Fin m → ℚ
  /-- Positive cone weight vector `aP ∈ ℚ^m` satisfying `aP_i > 0`. -/
  aP : Fin m → ℚ
  /-- The recurrent payoff matrix `G` is skew-symmetric (`Gᵀ = -G`). -/
  hskew : IsSkewSymmetric G
  /-- The algebraic clock table equation `G * C = R * N_mat w`. -/
  hclock : G * C = R * N_mat w
  /-- The endpoint counter calibration `vᵀ * C = e_0ᵀ`. -/
  hvC : Matrix.vecMul v C = e0_row w
  /-- All cone weights are strictly positive (`aP_i > 0`). -/
  haP_pos : ∀ i : Fin m, 0 < aP i

/-- **Universal Phase Score Transition (`AlgebraicClock.phase_score_transition`)**:
    In any `clock : AlgebraicClock w`, executing the phase-`q` count bundle
    `clock.C.mulVec (binomBasis w q)` from entry score vector `clock.R.mulVec (binomBasis w q)`
    advances the score vector to `clock.R.mulVec (binomBasis w (q + 1))`. -/
theorem AlgebraicClock.phase_score_transition {w : ℕ} (clock : AlgebraicClock w) (q : ℕ) :
    scoreVec clock.G (clock.R.mulVec (binomBasis w q)) (clock.C.mulVec (binomBasis w q)) =
      clock.R.mulVec (binomBasis w (q + 1)) :=
  clock_phase_transition clock.G clock.R clock.C clock.hclock q

/-- **Universal Endpoint Counter Increment (`AlgebraicClock.endpoint_counter_increment`)**:
    In any `clock : AlgebraicClock w` (`w > 0`), the weighted phase action count
    `vᵀ (C p_w(q))` equals `1` at every phase `q ∈ ℕ`. -/
theorem AlgebraicClock.endpoint_counter_increment {w : ℕ} (clock : AlgebraicClock w)
    (hw : 0 < w) (q : ℕ) :
    dotProduct clock.v (clock.C.mulVec (binomBasis w q)) = 1 :=
  clock_endpoint_increment_eq_one hw clock.v clock.C clock.hvC q

/-- **Universal Cone Identity (`AlgebraicClock.cone_identity`, Lemma 6.1)**:
    Every `clock : AlgebraicClock w` satisfies `Cᵀ * G * C = Cᵀ * R * N_mat w`. -/
theorem AlgebraicClock.cone_identity {w : ℕ} (clock : AlgebraicClock w) :
    clock.C.transpose * clock.G * clock.C = clock.C.transpose * clock.R * N_mat w := by
  rw [Matrix.mul_assoc, clock.hclock, ← Matrix.mul_assoc]

/-- **Universal Scaled Skew-Symmetry (`AlgebraicClock.scaled_skew`, Lemma 6.1)**:
    Scaling `clock.G` on both sides by `diag(clock.aP)` preserves skew-symmetry. -/
theorem AlgebraicClock.scaled_skew {w : ℕ} (clock : AlgebraicClock w) :
    IsSkewSymmetric (Matrix.of fun i j : Fin clock.m => clock.G i j * clock.aP i * clock.aP j) := by
  intro i j
  simp only [Matrix.of_apply]
  have hij := clock.hskew i j
  rw [hij]
  ring

/-!
## 2. Concrete Seed Instances (`w = 2` RPS Clock and `w = 3` 7-Action Clock)
-/

set_option linter.unnecessarySeqFocus false in
/-- The 3-action RPS clock (`w = 2, m = 3`, Section 3) packaged as an `AlgebraicClock 2`. -/
def rpsAlgebraicClock : AlgebraicClock 2 where
  m := 3
  G := A_RPS
  R := R2
  C := C2
  v := v_RPS
  aP := aP_RPS
  hskew := A_RPS_skew
  hclock := by
    have hN2 : N2 = N_mat 2 := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [← hN2]
    exact A_RPS_mul_C2_eq_R2_mul_N2
  hvC := by
    ext j
    fin_cases j <;>
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, v_RPS, C2, e0_row] <;> norm_num
  haP_pos := rps_admissible_weights.1

/-- Verification that `rpsAlgebraicClock` has `m = 3` recurrent actions and advances phase scores
    with unit endpoint counter increment. -/
theorem rpsAlgebraicClock_spec (q : ℕ) :
    rpsAlgebraicClock.m = 3 ∧
      scoreVec rpsAlgebraicClock.G
        (rpsAlgebraicClock.R.mulVec (binomBasis 2 q))
        (rpsAlgebraicClock.C.mulVec (binomBasis 2 q)) =
      rpsAlgebraicClock.R.mulVec (binomBasis 2 (q + 1)) ∧
      dotProduct rpsAlgebraicClock.v (rpsAlgebraicClock.C.mulVec (binomBasis 2 q)) = 1 :=
  ⟨rfl, rpsAlgebraicClock.phase_score_transition q,
    rpsAlgebraicClock.endpoint_counter_increment (by decide) q⟩

set_option linter.unnecessarySeqFocus false in
/-- The 6-action recurrent core+guard clock of `M_seven` (`w = 3, m = 6`, Section 4 / Appendix E)
    packaged as an `AlgebraicClock 3`. -/
def sevenAlgebraicClock : AlgebraicClock 3 where
  m := 6
  G := M_seven
  R := R_seven
  C := C_seven
  v := v_seven
  aP := aP_seven
  hskew := M_seven_skew
  hclock := by
    have hN3 : N3 = N_mat 3 := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [← hN3]
    exact M_seven_mul_C_eq_R_mul_N3
  hvC := by
    ext j
    fin_cases j <;>
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_six, v_seven, C_seven, e0_row] <;> norm_num
  haP_pos := seven_admissible_weights.1

/-- Verification that `sevenAlgebraicClock` has `m = 6` recurrent actions and advances phase scores
    with unit endpoint counter increment. -/
theorem sevenAlgebraicClock_spec (q : ℕ) :
    sevenAlgebraicClock.m = 6 ∧
      scoreVec sevenAlgebraicClock.G
        (sevenAlgebraicClock.R.mulVec (binomBasis 3 q))
        (sevenAlgebraicClock.C.mulVec (binomBasis 3 q)) =
      sevenAlgebraicClock.R.mulVec (binomBasis 3 (q + 1)) ∧
      dotProduct sevenAlgebraicClock.v (sevenAlgebraicClock.C.mulVec (binomBasis 3 q)) = 1 :=
  ⟨rfl, sevenAlgebraicClock.phase_score_transition q,
    sevenAlgebraicClock.endpoint_counter_increment (by decide) q⟩

/-!
## 3. Block-Matrix Lifted Game and Rotated Clock Tables on `α ⊕ β`
-/

/-- The lifted skew-symmetric recurrent payoff matrix
    `G_+ = [[G_O, P], [-Pᵀ, J - Jᵀ]]` on `α ⊕ β` (Section 5, Eq. `G_plus`). -/
def liftedGameMat {α β : Type*}
    (G_O : Matrix α α ℚ) (P : Matrix α β ℚ) (J : Matrix β β ℚ) :
    Matrix (α ⊕ β) (α ⊕ β) ℚ :=
  Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose)

/-- The rotated next-order score table `R_+ = (S + G_O * X, 1_n ζ - J * M)` on `α ⊕ β`
    (Section 8, Eq. `R_plus`). -/
def liftedScoreMat {α β γ : Type*} [Fintype α] [Fintype β]
    (G_O : Matrix α α ℚ) (J : Matrix β β ℚ)
    (S X : Matrix α γ ℚ) (M : Matrix β γ ℚ) (zeta : γ → ℚ) :
    Matrix (α ⊕ β) γ ℚ :=
  Matrix.of fun x c =>
    match x with
    | Sum.inl i => (S + G_O * X) i c
    | Sum.inr r => (one_zeta β zeta - J * M) r c

/-- The rotated next-order action-count table `C_+ = (X * (1 + N), M)` on `α ⊕ β`
    (Section 8, Eq. `C_plus`). -/
def liftedCountMat {α β γ : Type*} [Fintype γ] [DecidableEq γ]
    (X : Matrix α γ ℚ) (M : Matrix β γ ℚ) (N : Matrix γ γ ℚ) :
    Matrix (α ⊕ β) γ ℚ :=
  Matrix.of fun x c =>
    match x with
    | Sum.inl i => (X * (1 + N : Matrix γ γ ℚ)) i c
    | Sum.inr r => M r c

/-- The combined next-order weight vector `v_+ = (u_+, w_+)` on `α ⊕ β`
    (Section 8, Proposition 8.2). -/
def liftedWeightVec {α β : Type*} (u_plus : α → ℚ) (w_plus : β → ℚ) : α ⊕ β → ℚ
  | Sum.inl i => u_plus i
  | Sum.inr r => w_plus r

/-- **Skew-Symmetry of the Lifted Block Game (`liftedGameMat_skew`)**:
    If `G_O` is skew-symmetric, then `liftedGameMat G_O P J = [[G_O, P], [-Pᵀ, J - Jᵀ]]`
    is skew-symmetric for any coupling matrix `P` and reset matrix `J`. -/
theorem liftedGameMat_skew {α β : Type*}
    (G_O : Matrix α α ℚ) (P : Matrix α β ℚ) (J : Matrix β β ℚ)
    (hG : IsSkewSymmetric G_O) :
    IsSkewSymmetric (liftedGameMat G_O P J) := by
  intro x y
  cases x with
  | inl i =>
    cases y with
    | inl i' => exact hG i i'
    | inr r => simp [liftedGameMat, Matrix.fromBlocks]
  | inr r =>
    cases y with
    | inl i => simp [liftedGameMat, Matrix.fromBlocks]
    | inr r' =>
      simp [liftedGameMat, Matrix.fromBlocks]

/-- **Full Block-Matrix Clock Lift Equation (`liftedGameMat_mul_liftedCountMat`, Proposition 8.1)**:
    When `B * (1 + N) = 1`, `Pᵀ * X = Q_reset J M B ζ`, and `P * M = S * N - G_O * X`,
    the combined block matrix `G_+ = liftedGameMat G_O P J` and rotated tables
    `C_+ = liftedCountMat X M N`, `R_+ = liftedScoreMat G_O J S X M ζ` satisfy the single
    matrix identity `G_+ * C_+ = R_+ * N`. -/
theorem liftedGameMat_mul_liftedCountMat {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq γ]
    (G_O : Matrix α α ℚ) (P : Matrix α β ℚ) (J : Matrix β β ℚ)
    (S X : Matrix α γ ℚ) (M : Matrix β γ ℚ) (B N : Matrix γ γ ℚ) (zeta : γ → ℚ)
    (hBT : B * (1 + N) = 1)
    (hPtX : P.transpose * X = Q_reset J M B zeta)
    (hPM : P * M = S * N - G_O * X) :
    liftedGameMat G_O P J * liftedCountMat X M N =
      liftedScoreMat G_O J S X M zeta * N := by
  have hlift := master_algebraic_clock_lift G_O P J S X M B N zeta hBT hPtX hPM
  ext x c
  cases x with
  | inl i =>
    have h1 := congr_fun (congr_fun hlift.1 i) c
    simpa [liftedGameMat, liftedCountMat, liftedScoreMat, Matrix.mul_apply,
      Fintype.sum_sum_type] using h1
  | inr r =>
    have h2 := congr_fun (congr_fun hlift.2 r) c
    simpa [liftedGameMat, liftedCountMat, liftedScoreMat, Matrix.mul_apply,
      Fintype.sum_sum_type] using h2

/-- **Full Block-Vector Weight Calibration (`liftedWeightVec_mul_liftedCountMat`, Proposition 8.2)**:
    When `u_+ᵀ (X * (1 + N_mat w)) + w_+ᵀ M = e_0ᵀ`, the combined weight vector
    `v_+ = liftedWeightVec u_+ w_+` and rotated count table `C_+ = liftedCountMat X M (N_mat w)`
    satisfy `v_+ᵀ * C_+ = e_0ᵀ`. -/
theorem liftedWeightVec_mul_liftedCountMat {α β : Type*} [Fintype α] [Fintype β]
    {w : ℕ}
    (X : Matrix α (Fin w) ℚ) (M : Matrix β (Fin w) ℚ)
    (u_plus : α → ℚ) (w_plus : β → ℚ)
    (hw_cal :
      Matrix.vecMul u_plus (X * (1 + N_mat w : Matrix (Fin w) (Fin w) ℚ)) +
        Matrix.vecMul w_plus M = e0_row w) :
    Matrix.vecMul (liftedWeightVec u_plus w_plus) (liftedCountMat X M (N_mat w)) = e0_row w := by
  ext c
  have hc := congr_fun hw_cal c
  simpa [Matrix.vecMul, dotProduct, liftedWeightVec, liftedCountMat,
    Fintype.sum_sum_type] using hc

/-!
## 4. Reindexing Clocks Along Type Equivalences and Bundled Inductive Step
-/

/-- Transport a clock over an arbitrary finite index type `σ` along an equivalence `e : σ ≃ Fin m'`
    to obtain an `AlgebraicClock w`. -/
def AlgebraicClock.ofEquiv {σ : Type*} [Fintype σ] {w m' : ℕ}
    (e : σ ≃ Fin m')
    (G : Matrix σ σ ℚ) (R C : Matrix σ (Fin w) ℚ) (v aP : σ → ℚ)
    (hskew : IsSkewSymmetric G)
    (hclock : G * C = R * N_mat w)
    (hvC : Matrix.vecMul v C = e0_row w)
    (haP_pos : ∀ s : σ, 0 < aP s) :
    AlgebraicClock w where
  m := m'
  G := Matrix.of fun i j => G (e.symm i) (e.symm j)
  R := Matrix.of fun i c => R (e.symm i) c
  C := Matrix.of fun i c => C (e.symm i) c
  v := fun i => v (e.symm i)
  aP := fun i => aP (e.symm i)
  hskew := by
    intro i j
    simp only [Matrix.of_apply]
    exact hskew (e.symm i) (e.symm j)
  hclock := by
    ext i c
    have hc := congr_fun (congr_fun hclock (e.symm i)) c
    simp only [Matrix.mul_apply, Matrix.of_apply] at hc ⊢
    rw [← hc]
    exact Equiv.sum_comp e.symm (fun s => G (e.symm i) s * C s c)
  hvC := by
    ext c
    have hc := congr_fun hvC c
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply] at hc ⊢
    rw [← hc]
    exact Equiv.sum_comp e.symm (fun s => v s * C s c)
  haP_pos := fun i => haP_pos (e.symm i)

/-- **Bundled Inductive Lift Step Data (`LiftStepData clock n`)**:
    Packages the coupling block `P`, reset gadget matrices `(J, M)`, lifted old-action tables
    `(S, X)`, ceiling profile `ζ`, basis-change inverse `B = (I + N_{w+1})^{-1}`, endpoint
    counter weights `(v_old, v_reset)`, and positive cone weights `(aP_old, aP_reset)` that
    lift an order-`w` clock `clock : AlgebraicClock w` to order `w + 1` with `n` new reset actions. -/
structure LiftStepData {w : ℕ} (clock : AlgebraicClock w) (n : ℕ) where
  /-- Coupling block `P ∈ ℚ^{m × n}` between old actions and new reset actions. -/
  P : Matrix (Fin clock.m) (Fin n) ℚ
  /-- Strictly upper-triangular reset interaction matrix `J ∈ ℚ^{n × n}`. -/
  J : Matrix (Fin n) (Fin n) ℚ
  /-- Lifted old-action score table `S ∈ ℚ^{m × (w + 1)}`. -/
  S : Matrix (Fin clock.m) (Fin (w + 1)) ℚ
  /-- Lifted old-action count table `X ∈ ℚ^{m × (w + 1)}`. -/
  X : Matrix (Fin clock.m) (Fin (w + 1)) ℚ
  /-- Reset action count table `M ∈ ℚ^{n × (w + 1)}`. -/
  M : Matrix (Fin n) (Fin (w + 1)) ℚ
  /-- Basis-change inverse `B = (1 + N_mat (w + 1))⁻¹`. -/
  B : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ
  /-- Reset ceiling polynomial coefficients `ζ ∈ ℚ^{w + 1}`. -/
  zeta : Fin (w + 1) → ℚ
  /-- Next-order old-action endpoint counter row `v_old ∈ ℚ^m`. -/
  v_old : Fin clock.m → ℚ
  /-- Next-order reset-action endpoint counter row `v_reset ∈ ℚ^n`. -/
  v_reset : Fin n → ℚ
  /-- Next-order old-action positive cone weights `aP_old ∈ ℚ^m`. -/
  aP_old : Fin clock.m → ℚ
  /-- Next-order reset-action positive cone weights `aP_reset ∈ ℚ^n`. -/
  aP_reset : Fin n → ℚ
  /-- `B` is the left inverse of `1 + N_mat (w + 1)`. -/
  hBT : B * (1 + N_mat (w + 1)) = 1
  /-- First interpolation equation `Pᵀ * X = Q_reset J M B ζ`. -/
  hPtX : P.transpose * X = Q_reset J M B zeta
  /-- Second interpolation equation `P * M = S * N_mat (w + 1) - clock.G * X`. -/
  hPM : P * M = S * N_mat (w + 1) - clock.G * X
  /-- Endpoint counter weight calibration `v_oldᵀ (X (1 + N_{w+1})) + v_resetᵀ M = e_0ᵀ`. -/
  hv_cal :
    Matrix.vecMul v_old
      (X * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) +
      Matrix.vecMul v_reset M = e0_row (w + 1)
  /-- Positivity of old-action cone weights `aP_old > 0`. -/
  haP_old_pos : ∀ i : Fin clock.m, 0 < aP_old i
  /-- Positivity of reset-action cone weights `aP_reset > 0`. -/
  haP_reset_pos : ∀ r : Fin n, 0 < aP_reset r

/-- **The Bundled Inductive Clock Lift (`AlgebraicClock.lift`, Theorem 5.1 `thm:lift`)**:
    Given `clock : AlgebraicClock w` and `step : LiftStepData clock n`, produces the
    next-order `AlgebraicClock (w + 1)` with `clock.m + n` recurrent actions. -/
def AlgebraicClock.lift {w n : ℕ} (clock : AlgebraicClock w)
    (step : LiftStepData clock n) : AlgebraicClock (w + 1) :=
  AlgebraicClock.ofEquiv finSumFinEquiv
    (liftedGameMat clock.G step.P step.J)
    (liftedScoreMat clock.G step.J step.S step.X step.M step.zeta)
    (liftedCountMat step.X step.M (N_mat (w + 1)))
    (liftedWeightVec step.v_old step.v_reset)
    (liftedWeightVec step.aP_old step.aP_reset)
    (liftedGameMat_skew clock.G step.P step.J clock.hskew)
    (liftedGameMat_mul_liftedCountMat clock.G step.P step.J step.S step.X step.M
      step.B (N_mat (w + 1)) step.zeta step.hBT step.hPtX step.hPM)
    (liftedWeightVec_mul_liftedCountMat step.X step.M
      step.v_old step.v_reset step.hv_cal)
    (fun s => by
      cases s with
      | inl i => exact step.haP_old_pos i
      | inr r => exact step.haP_reset_pos r)

/-- **Master Bundled Lift Specification (`AlgebraicClock.lift_spec`)**:
    The lifted clock `clock.lift step : AlgebraicClock (w + 1)` has `clock.m + n` recurrent
    actions, advances its order-`(w + 1)` phase score vector from `R_+ p_{w+1}(q)` to
    `R_+ p_{w+1}(q + 1)` across every phase `q ∈ ℕ`, and maintains unit endpoint counter
    increment `v_+ᵀ (C_+ p_{w+1}(q)) = 1`. -/
theorem AlgebraicClock.lift_spec {w n : ℕ} (clock : AlgebraicClock w)
    (step : LiftStepData clock n) (q : ℕ) :
    (clock.lift step).m = clock.m + n ∧
      scoreVec (clock.lift step).G
        ((clock.lift step).R.mulVec (binomBasis (w + 1) q))
        ((clock.lift step).C.mulVec (binomBasis (w + 1) q)) =
      (clock.lift step).R.mulVec (binomBasis (w + 1) (q + 1)) ∧
      dotProduct (clock.lift step).v ((clock.lift step).C.mulVec (binomBasis (w + 1) q)) = 1 :=
  ⟨rfl, (clock.lift step).phase_score_transition q,
    (clock.lift step).endpoint_counter_increment (Nat.succ_pos w) q⟩

/-!
## 5. Unrolled Cubic Phase Chronology for `M7` (`karlin_conjecture_disproof_unrolled`)
-/

/-- The discrete step `t_p` at the start of phase `p ∈ ℕ` (`k = p + 20`) in `sevenTrajectory`. -/
def sevenPhaseStartStep (p : ℕ) : ℕ :=
  runStart (setupFullLen (flatLen sevenPhaseRunCount sevenPhaseLen))
    (runStart sevenPhaseRunCount p + 1)

/-- At phase `p` and intra-phase run index `v < sevenPhaseRunCount p`, the flattened run length
    equals `sevenPhaseLen p v`. -/
theorem seven_fullLen_at_phase_offset (p v : ℕ) (hv : v < sevenPhaseRunCount p) :
    setupFullLen (flatLen sevenPhaseRunCount sevenPhaseLen)
      (runStart sevenPhaseRunCount p + v + 1) =
    sevenPhaseLen p v := by
  have hcount : ∀ q : ℕ, 0 < sevenPhaseRunCount q := by
    intro q; unfold sevenPhaseRunCount; omega
  have hp : flatPhase sevenPhaseRunCount (runStart sevenPhaseRunCount p + v) = p := by
    unfold flatPhase
    exact runIndexOfStep_at_offset hcount p v hv
  have hoff : flatOffset sevenPhaseRunCount (runStart sevenPhaseRunCount p + v) = v := by
    unfold flatOffset
    rw [hp]
    omega
  simp [setupFullLen, flatLen, hp, hoff]

/-- Cumulative step count after `N` core sub-cycles (`3 * N` runs) in phase `p` of `sevenTrajectory`. -/
theorem seven_runStart_core_triples (p N : ℕ) (hN : 3 * N ≤ 21 * p + 438) :
    (runStart (setupFullLen (flatLen sevenPhaseRunCount sevenPhaseLen))
      (runStart sevenPhaseRunCount p + (3 * N) + 1) : ℚ) =
    (sevenPhaseStartStep p : ℚ) +
      9 * (N : ℚ) ^ 2 + 18 * (21 * (p : ℚ) + 430) * (N : ℚ) := by
  induction N with
  | zero =>
    simp [sevenPhaseStartStep]
  | succ N ih =>
    have hN_le : 3 * N ≤ 21 * p + 438 := by omega
    have hih := ih hN_le
    have hr3 :
        runStart sevenPhaseRunCount p + (3 * (N + 1)) + 1 =
          runStart sevenPhaseRunCount p + (3 * N) + 1 + 1 + 1 + 1 := by omega
    rw [hr3, runStart_succ, runStart_succ, runStart_succ]
    have ha0 : runStart sevenPhaseRunCount p + (3 * N) + 1 + 1 + 1 =
        runStart sevenPhaseRunCount p + (3 * N + 2) + 1 := by omega
    have ha1 : runStart sevenPhaseRunCount p + (3 * N) + 1 + 1 =
        runStart sevenPhaseRunCount p + (3 * N + 1) + 1 := by omega
    rw [ha0, ha1]
    have hv0 : 3 * N < sevenPhaseRunCount p := by unfold sevenPhaseRunCount; omega
    have hv1 : 3 * N + 1 < sevenPhaseRunCount p := by unfold sevenPhaseRunCount; omega
    have hv2 : 3 * N + 2 < sevenPhaseRunCount p := by unfold sevenPhaseRunCount; omega
    rw [seven_fullLen_at_phase_offset p (3 * N) hv0,
        seven_fullLen_at_phase_offset p (3 * N + 1) hv1,
        seven_fullLen_at_phase_offset p (3 * N + 2) hv2]
    have hc0 : 3 * N < 21 * p + 438 := by omega
    have hc1 : 3 * N + 1 < 21 * p + 438 := by omega
    have hc2 : 3 * N + 2 < 21 * p + 438 := by omega
    have hd0 : (3 * N) / 3 = N := by omega
    have hd1 : (3 * N + 1) / 3 = N := by omega
    have hd2 : (3 * N + 2) / 3 = N := by omega
    have hm0 : (3 * N) % 3 = 0 := by omega
    have hm1 : (3 * N + 1) % 3 = 1 := by omega
    have hm2 : (3 * N + 2) % 3 = 2 := by omega
    have hl0 : sevenPhaseLen p (3 * N) = 6 * (21 * (p + 20) + 10 + N) + 1 := by
      simp [sevenPhaseLen, hc0, hd0, hm0]
    have hl1 : sevenPhaseLen p (3 * N + 1) = 6 * (21 * (p + 20) + 10 + N) + 3 := by
      simp [sevenPhaseLen, hc1, hd1, hm1]
    have hl2 : sevenPhaseLen p (3 * N + 2) = 6 * (21 * (p + 20) + 10 + N) + 5 := by
      simp [sevenPhaseLen, hc2, hd2, hm2]
    rw [hl0, hl1, hl2]
    push_cast
    rw [hih]
    ring

/-- **Exact Cubic Phase-Start Time (`seven_phase_start_time`)**:
    In the unrolled 7-action trajectory `sevenTrajectory`, the discrete step `sevenPhaseStartStep p`
    at the start of phase `p ∈ ℕ` (`k = p + 20`) satisfies
    `2 * (sevenPhaseStartStep p : ℚ) = 3822 * p^3 + 214491 * p^2 + 4109779 * p + 2`. -/
theorem seven_phase_start_time (p : ℕ) :
    2 * (sevenPhaseStartStep p : ℚ) =
      3822 * (p : ℚ) ^ 3 + 214491 * (p : ℚ) ^ 2 + 4109779 * (p : ℚ) + 2 := by
  induction p with
  | zero =>
    have h0 : sevenPhaseStartStep 0 = 1 := rfl
    rw [h0]
    norm_num
  | succ p ih =>
    have hr_inner :
        runStart sevenPhaseRunCount (p + 1) + 1 =
          runStart sevenPhaseRunCount p + (3 * (7 * p + 146)) + 1 + 1 + 1 + 1 := by
      rw [runStart_succ]
      unfold sevenPhaseRunCount
      omega
    have hstep : sevenPhaseStartStep (p + 1) =
        runStart (setupFullLen (flatLen sevenPhaseRunCount sevenPhaseLen))
          (runStart sevenPhaseRunCount p + (3 * (7 * p + 146)) + 1 + 1 + 1 + 1) := by
      unfold sevenPhaseStartStep
      rw [hr_inner]
    rw [hstep, runStart_succ, runStart_succ, runStart_succ]
    have ha2 : runStart sevenPhaseRunCount p + (3 * (7 * p + 146)) + 1 + 1 + 1 =
        runStart sevenPhaseRunCount p + (21 * p + 440) + 1 := by omega
    have ha1 : runStart sevenPhaseRunCount p + (3 * (7 * p + 146)) + 1 + 1 =
        runStart sevenPhaseRunCount p + (21 * p + 439) + 1 := by omega
    have ha0 : runStart sevenPhaseRunCount p + (3 * (7 * p + 146)) + 1 =
        runStart sevenPhaseRunCount p + (21 * p + 438) + 1 := by omega
    rw [ha2, ha1]
    have hv0 : 21 * p + 438 < sevenPhaseRunCount p := by unfold sevenPhaseRunCount; omega
    have hv1 : 21 * p + 439 < sevenPhaseRunCount p := by unfold sevenPhaseRunCount; omega
    have hv2 : 21 * p + 440 < sevenPhaseRunCount p := by unfold sevenPhaseRunCount; omega
    rw [seven_fullLen_at_phase_offset p (21 * p + 440) hv2,
        seven_fullLen_at_phase_offset p (21 * p + 439) hv1]
    rw [ha0]
    rw [seven_fullLen_at_phase_offset p (21 * p + 438) hv0, ← ha0]
    have hcore := seven_runStart_core_triples p (7 * p + 146) (by omega)
    have hg0 : sevenPhaseLen p (21 * p + 438) = 882 * p ^ 2 + 32976 * p + 319218 := by
      simp [sevenPhaseLen]
    have hg1 : sevenPhaseLen p (21 * p + 439) = 882 * p ^ 2 + 37680 * p + 403222 := by
      have h1 : ¬ (21 * p + 439 < 21 * p + 438) := by omega
      simp [sevenPhaseLen, h1]
    have hg2 : sevenPhaseLen p (21 * p + 440) = 882 * p ^ 2 + 21804 * p + 119722 := by
      have h1 : ¬ (21 * p + 440 < 21 * p + 438) := by omega
      simp [sevenPhaseLen, h1]
    rw [hg0, hg1, hg2]
    push_cast
    rw [hcore]
    push_cast
    linear_combination ih

/-- At the start of recurrent run `u` (`r = u + 1`), the cumulative score of every recurrent
    action `some i` in `setupMatrix M w` equals `recEntryScore u i + C`. -/
theorem setup_cumScore_at_runStart_some {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℚ) (w : Fin m → ℚ) (C : ℚ)
    (recAct : ℕ → Fin m) (recLen : ℕ → ℕ)
    (recEntryScore : ℕ → Fin m → ℚ)
    (hrecLen : ∀ u : ℕ, 0 < recLen u)
    (hw_shift : ∀ i : Fin m, w i = recEntryScore 0 i + C)
    (hrecStep : ∀ u : ℕ,
      recEntryScore (u + 1) =
        scoreVec M (recEntryScore u) (runCount (fun _ => 0) (recAct u) (recLen u : ℚ)))
    (u : ℕ) (i : Fin m) :
    cumScore (setupMatrix M w)
      (unrollAction (setupFullAct recAct) (setupFullLen recLen))
      (runStart (setupFullLen recLen) (u + 1)) (some i) =
    recEntryScore u i + C := by
  have hlen : ∀ r : ℕ, 0 < setupFullLen recLen r := by
    intro r
    rcases r with _ | v
    · exact Nat.zero_lt_one
    · exact hrecLen v
  induction u generalizing i with
  | zero =>
    have hr1 : runStart (setupFullLen recLen) 1 = runStart (setupFullLen recLen) 0 + 1 := rfl
    rw [hr1]
    have h0 : 1 ≤ setupFullLen recLen 0 := le_rfl
    have hstep0 := congr_fun
      (cumScore_add_offset (setupMatrix M w) (setupFullAct recAct) hlen 0 1 h0) (some i)
    rw [hstep0]
    have hinit : cumScore (setupMatrix M w)
        (unrollAction (setupFullAct recAct) (setupFullLen recLen))
        (runStart (setupFullLen recLen) 0) = (fun _ => 0) := rfl
    rw [hinit]
    have hact0 : setupFullAct recAct 0 = none := rfl
    rw [hact0, Nat.cast_one]
    have hs1 := setupMatrix_score_after_step_one M w i
    rw [hs1]
    exact hw_shift i
  | succ u ih =>
    have hr_succ :
        runStart (setupFullLen recLen) (u + 1 + 1) =
          runStart (setupFullLen recLen) (u + 1) + recLen u := by
      rw [runStart_succ]
      rfl
    rw [hr_succ]
    have hle : recLen u ≤ setupFullLen recLen (u + 1) := le_rfl
    have hstep := congr_fun
      (cumScore_add_offset (setupMatrix M w) (setupFullAct recAct) hlen (u + 1) (recLen u) hle)
      (some i)
    rw [hstep]
    have hact : setupFullAct recAct (u + 1) = some (recAct u) := rfl
    rw [hact, scoreVec_setupMatrix_some, hrecStep u]
    simp only [scoreVec, ih]
    ring

/-- At the start of every phase `p ∈ ℕ`, `sevenTrajectory` plays action `some 0`. -/
theorem sevenTrajectory_at_phase_start (p : ℕ) :
    sevenTrajectory (sevenPhaseStartStep p) = some 0 := by
  have hlen : ∀ r : ℕ, 0 < setupFullLen (flatLen sevenPhaseRunCount sevenPhaseLen) r := by
    intro r
    rcases r with _ | u
    · exact Nat.zero_lt_one
    · change 0 < flatLen sevenPhaseRunCount sevenPhaseLen u
      unfold flatLen sevenPhaseLen
      split_ifs with h1 h2 h3
      · have hmod : flatOffset sevenPhaseRunCount u % 3 = 0 ∨
            flatOffset sevenPhaseRunCount u % 3 = 1 ∨
            flatOffset sevenPhaseRunCount u % 3 = 2 := by omega
        rcases hmod with hm | hm | hm <;> simp [hm]
      · positivity
      · positivity
      · positivity
  have hcount : ∀ q : ℕ, 0 < sevenPhaseRunCount q := by
    intro q; unfold sevenPhaseRunCount; omega
  have h0 : 0 < setupFullLen (flatLen sevenPhaseRunCount sevenPhaseLen)
      (runStart sevenPhaseRunCount p + 1) := hlen _
  have hunroll := unrollAction_at_offset
    (setupFullAct (flatAct sevenPhaseRunCount sevenPhaseAct)) hlen
    (runStart sevenPhaseRunCount p + 1) 0 h0
  simp only [Nat.add_zero] at hunroll
  unfold sevenTrajectory sevenPhaseStartStep
  rw [hunroll]
  have hp : flatPhase sevenPhaseRunCount (runStart sevenPhaseRunCount p) = p := by
    unfold flatPhase
    exact runIndexOfStep_at_offset hcount p 0 (hcount p)
  have hoff : flatOffset sevenPhaseRunCount (runStart sevenPhaseRunCount p) = 0 := by
    unfold flatOffset
    rw [hp]
    omega
  have hlt : 0 < 21 * p + 438 := by omega
  simp [setupFullAct, flatAct, hp, hoff, sevenPhaseAct, hlt]

/-- **Exact Quadratic Phase-Start Cumulative Score (`seven_phase_start_score`)**:
    At the start of phase `p ∈ ℕ` (`t_p = sevenPhaseStartStep p`), the cumulative score
    `cumScore M7 sevenTrajectory t_p (some i)` of every recurrent action `some i` in `M7`
    equals `V_seven (p + 20) i + 657497227 / 52500`. -/
theorem seven_phase_start_score (p : ℕ) (i : Fin 6) :
    cumScore M7 sevenTrajectory (sevenPhaseStartStep p) (some i) =
      V_seven ((p : ℚ) + 20) i + 657497227 / 52500 := by
  have hcount : ∀ q : ℕ, 0 < sevenPhaseRunCount q := by
    intro q; unfold sevenPhaseRunCount; omega
  have hrecLen : ∀ u : ℕ, 0 < flatLen sevenPhaseRunCount sevenPhaseLen u := by
    intro u
    unfold flatLen sevenPhaseLen
    split_ifs with h1 h2 h3
    · have hmod : flatOffset sevenPhaseRunCount u % 3 = 0 ∨
          flatOffset sevenPhaseRunCount u % 3 = 1 ∨
          flatOffset sevenPhaseRunCount u % 3 = 2 := by omega
      rcases hmod with hm | hm | hm <;> simp [hm]
    · positivity
    · positivity
    · positivity
  have hw_shift : ∀ j : Fin 6,
      w_seven j = flatScore sevenPhaseRunCount sevenPhaseScore 0 j + 657497227 / 52500 := by
    intro j
    have h0 : flatPhase sevenPhaseRunCount 0 = 0 := by
      unfold flatPhase
      exact runIndexOfStep_at_offset hcount 0 0 (hcount 0)
    have hoff0 : flatOffset sevenPhaseRunCount 0 = 0 := by
      unfold flatOffset
      rw [h0, runStart_zero]
    have hs0 : sevenPhaseScore 0 0 = V_seven 20 := by
      simp [sevenPhaseScore]
      have h430 : (430 : ℚ) = 21 * (20 : ℚ) + 10 := by norm_num
      rw [h430]
      exact stateCoreStart_at_begin 20
    simp [flatScore, h0, hoff0, hs0, seven_setup_realization.2 j]
  have hphaseStep : ∀ q v : ℕ, v < sevenPhaseRunCount q →
      sevenPhaseScore q (v + 1) =
        scoreVec M_seven (sevenPhaseScore q v)
          (runCount (fun _ => 0) (sevenPhaseAct q v) (sevenPhaseLen q v : ℚ)) := by
    intro q v hv
    unfold sevenPhaseRunCount at hv
    by_cases hcore : v < 21 * q + 438
    · have hmod : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
      rcases hmod with hm0 | hm1 | hm2
      · have hv1 : v + 1 < 21 * q + 438 := by omega
        have hdiv : (v + 1) / 3 = v / 3 := by omega
        have hm_next : (v + 1) % 3 = 1 := by omega
        have hact : sevenPhaseAct q v = 0 := by simp [sevenPhaseAct, hcore, hm0]
        have hlen : (sevenPhaseLen q v : ℚ) =
            6 * ((21 * (q + 20) + 10 + v / 3 : ℕ) : ℚ) + 1 := by
          simp [sevenPhaseLen, hcore, hm0]
        have hs0 : sevenPhaseScore q v =
            stateCoreStart ((q : ℚ) + 20) ((21 * (q + 20) + 10 + v / 3 : ℕ) : ℚ) := by
          simp [sevenPhaseScore, hcore, hm0]
        have hs1 : sevenPhaseScore q (v + 1) =
            stateCoreAfterR1 ((q : ℚ) + 20) ((21 * (q + 20) + 10 + v / 3 : ℕ) : ℚ) := by
          simp [sevenPhaseScore, hv1, hdiv, hm_next]
        rw [hs0, hs1, hact, hlen]
        exact (seven_core_full_transitions ((q : ℚ) + 20)
          ((21 * (q + 20) + 10 + v / 3 : ℕ) : ℚ)).1.symm
      · have hv1 : v + 1 < 21 * q + 438 := by omega
        have hdiv : (v + 1) / 3 = v / 3 := by omega
        have hm_next : (v + 1) % 3 = 2 := by omega
        have hact : sevenPhaseAct q v = 1 := by simp [sevenPhaseAct, hcore, hm1]
        have hlen : (sevenPhaseLen q v : ℚ) =
            6 * ((21 * (q + 20) + 10 + v / 3 : ℕ) : ℚ) + 3 := by
          simp [sevenPhaseLen, hcore, hm1]
        have hs0 : sevenPhaseScore q v =
            stateCoreAfterR1 ((q : ℚ) + 20) ((21 * (q + 20) + 10 + v / 3 : ℕ) : ℚ) := by
          simp [sevenPhaseScore, hcore, hm1]
        have hs1 : sevenPhaseScore q (v + 1) =
            stateCoreAfterR2 ((q : ℚ) + 20) ((21 * (q + 20) + 10 + v / 3 : ℕ) : ℚ) := by
          simp [sevenPhaseScore, hv1, hdiv, hm_next]
        rw [hs0, hs1, hact, hlen]
        exact (seven_core_full_transitions ((q : ℚ) + 20)
          ((21 * (q + 20) + 10 + v / 3 : ℕ) : ℚ)).2.1.symm
      · have hdiv : (v + 1) / 3 = v / 3 + 1 := by omega
        have hm_next : (v + 1) % 3 = 0 := by omega
        have hact : sevenPhaseAct q v = 2 := by simp [sevenPhaseAct, hcore, hm2]
        have hlen : (sevenPhaseLen q v : ℚ) =
            6 * ((21 * (q + 20) + 10 + v / 3 : ℕ) : ℚ) + 5 := by
          simp [sevenPhaseLen, hcore, hm2]
        have hs0 : sevenPhaseScore q v =
            stateCoreAfterR2 ((q : ℚ) + 20) ((21 * (q + 20) + 10 + v / 3 : ℕ) : ℚ) := by
          simp [sevenPhaseScore, hcore, hm2]
        rw [hs0, hact, hlen]
        rw [(seven_core_full_transitions ((q : ℚ) + 20)
          ((21 * (q + 20) + 10 + v / 3 : ℕ) : ℚ)).2.2]
        by_cases hv1 : v + 1 < 21 * q + 438
        · have hs1 : sevenPhaseScore q (v + 1) =
              stateCoreStart ((q : ℚ) + 20)
                ((21 * (q + 20) + 10 + (v + 1) / 3 : ℕ) : ℚ) := by
            simp [sevenPhaseScore, hv1, hm_next]
          rw [hs1, hdiv]
          have hcast : ((21 * (q + 20) + 10 + (v / 3 + 1) : ℕ) : ℚ) =
              ((21 * (q + 20) + 10 + v / 3 : ℕ) : ℚ) + 1 := by
            push_cast; ring
          rw [hcast]
        · have hv_end : v + 1 = 21 * q + 438 := by omega
          have hdiv_end : v / 3 = 7 * q + 145 := by omega
          have hs1 : sevenPhaseScore q (v + 1) = stateBeforeG1 ((q : ℚ) + 20) := by
            simp [sevenPhaseScore, hv_end]
          rw [hs1, hdiv_end]
          have hcast : ((21 * (q + 20) + 10 + (7 * q + 145) : ℕ) : ℚ) + 1 =
              28 * ((q : ℚ) + 20) + 16 := by
            push_cast; ring
          rw [hcast, stateCoreStart_at_end]
    · have hg : v = 21 * q + 438 ∨ v = 21 * q + 439 ∨ v = 21 * q + 440 := by omega
      rcases hg with hg1 | hg2 | hg3
      · subst hg1
        have hlen : (sevenPhaseLen q (21 * q + 438) : ℚ) = L_seven ((q : ℚ) + 20) 0 := by
          simp [sevenPhaseLen, L_seven]; ring
        have hs0 : sevenPhaseScore q (21 * q + 438) = stateBeforeG1 ((q : ℚ) + 20) := by
          simp [sevenPhaseScore]
        have hs1 : sevenPhaseScore q (21 * q + 438 + 1) = stateBeforeG2 ((q : ℚ) + 20) := by
          have h1 : ¬ (21 * q + 438 + 1 < 21 * q + 438) := by omega
          have h3 : 21 * q + 438 + 1 = 21 * q + 439 := by omega
          simp [sevenPhaseScore, h1, h3]
        have hact : sevenPhaseAct q (21 * q + 438) = 3 := by simp [sevenPhaseAct]
        rw [hs0, hs1, hact, hlen]
        exact (seven_guard_transitions ((q : ℚ) + 20)).1.symm
      · subst hg2
        have hlen : (sevenPhaseLen q (21 * q + 439) : ℚ) = L_seven ((q : ℚ) + 20) 1 := by
          have h1 : ¬ (21 * q + 439 < 21 * q + 438) := by omega
          simp [sevenPhaseLen, h1, L_seven]; ring
        have hs0 : sevenPhaseScore q (21 * q + 439) = stateBeforeG2 ((q : ℚ) + 20) := by
          have h1 : ¬ (21 * q + 439 < 21 * q + 438) := by omega
          simp [sevenPhaseScore, h1]
        have hs1 : sevenPhaseScore q (21 * q + 439 + 1) = stateBeforeG3 ((q : ℚ) + 20) := by
          have h1 : ¬ (21 * q + 439 + 1 < 21 * q + 438) := by omega
          have h4 : 21 * q + 439 + 1 = 21 * q + 440 := by omega
          simp [sevenPhaseScore, h1, h4]
        have hact : sevenPhaseAct q (21 * q + 439) = 4 := by
          have h1 : ¬ (21 * q + 439 < 21 * q + 438) := by omega
          simp [sevenPhaseAct, h1]
        rw [hs0, hs1, hact, hlen]
        exact (seven_guard_transitions ((q : ℚ) + 20)).2.1.symm
      · subst hg3
        have hlen : (sevenPhaseLen q (21 * q + 440) : ℚ) = L_seven ((q : ℚ) + 20) 2 := by
          have h1 : ¬ (21 * q + 440 < 21 * q + 438) := by omega
          simp [sevenPhaseLen, h1, L_seven]; ring
        have hs0 : sevenPhaseScore q (21 * q + 440) = stateBeforeG3 ((q : ℚ) + 20) := by
          have h1 : ¬ (21 * q + 440 < 21 * q + 438) := by omega
          simp [sevenPhaseScore, h1]
        have hs1 : sevenPhaseScore q (21 * q + 440 + 1) =
            V_seven ((q : ℚ) + 20 + 1) := by
          have h1 : ¬ (21 * q + 440 + 1 < 21 * q + 438) := by omega
          simp [sevenPhaseScore, h1]; congr 1; ring
        have hact : sevenPhaseAct q (21 * q + 440) = 5 := by
          have h1 : ¬ (21 * q + 440 < 21 * q + 438) := by omega
          simp [sevenPhaseAct, h1]
        rw [hs0, hs1, hact, hlen]
        exact (seven_guard_transitions ((q : ℚ) + 20)).2.2.symm
  have hphaseBoundary : ∀ q : ℕ,
      sevenPhaseScore q (sevenPhaseRunCount q) = sevenPhaseScore (q + 1) 0 := by
    intro q
    unfold sevenPhaseRunCount
    have h1 : ¬ (21 * q + 441 < 21 * q + 438) := by omega
    have lhs_eq : sevenPhaseScore q (21 * q + 441) = V_seven (((q + 1 : ℕ) : ℚ) + 20) := by
      simp [sevenPhaseScore, h1]
    have rhs_eq : sevenPhaseScore (q + 1) 0 = V_seven (((q + 1 : ℕ) : ℚ) + 20) := by
      have h0 : 0 < 21 * (q + 1) + 438 := by omega
      simp [sevenPhaseScore, h0]
      exact stateCoreStart_at_begin ((q : ℚ) + 1 + 20)
    rw [lhs_eq, rhs_eq]
  have hrecStep : ∀ u : ℕ,
      flatScore sevenPhaseRunCount sevenPhaseScore (u + 1) =
        scoreVec M_seven (flatScore sevenPhaseRunCount sevenPhaseScore u)
          (runCount (fun _ => 0)
            (flatAct sevenPhaseRunCount sevenPhaseAct u)
            (flatLen sevenPhaseRunCount sevenPhaseLen u : ℚ)) := by
    intro u
    let q := flatPhase sevenPhaseRunCount u
    let v := flatOffset sevenPhaseRunCount u
    have hspec := runIndexOfStep_spec hcount u
    have hr_le : runStart sevenPhaseRunCount q ≤ u := hspec.1
    have hu_lt : u < runStart sevenPhaseRunCount (q + 1) := hspec.2
    rw [runStart_succ] at hu_lt
    have hv_def : v = u - runStart sevenPhaseRunCount q := rfl
    have hv : v < sevenPhaseRunCount q := by omega
    have h_rhs :
        scoreVec M_seven (flatScore sevenPhaseRunCount sevenPhaseScore u)
          (runCount (fun _ => 0) (flatAct sevenPhaseRunCount sevenPhaseAct u)
            (flatLen sevenPhaseRunCount sevenPhaseLen u : ℚ)) =
        sevenPhaseScore q (v + 1) := (hphaseStep q v hv).symm
    rw [h_rhs]
    by_cases hv1 : v + 1 < sevenPhaseRunCount q
    · have hu1 : u + 1 = runStart sevenPhaseRunCount q + (v + 1) := by omega
      have hq1 : flatPhase sevenPhaseRunCount (u + 1) = q := by
        unfold flatPhase
        rw [hu1, runIndexOfStep_at_offset hcount q (v + 1) hv1]
      have hoff1 : flatOffset sevenPhaseRunCount (u + 1) = v + 1 := by
        unfold flatOffset
        rw [hq1, hu1]
        omega
      simp [flatScore, hq1, hoff1]
    · have hv_eq : v + 1 = sevenPhaseRunCount q := by omega
      have hu1 : u + 1 = runStart sevenPhaseRunCount (q + 1) + 0 := by
        rw [runStart_succ]
        omega
      have hq1 : flatPhase sevenPhaseRunCount (u + 1) = q + 1 := by
        unfold flatPhase
        rw [hu1, runIndexOfStep_at_offset hcount (q + 1) 0 (hcount (q + 1))]
      have hoff1 : flatOffset sevenPhaseRunCount (u + 1) = 0 := by
        unfold flatOffset
        rw [hq1, hu1]
        omega
      simp only [flatScore, hq1, hoff1]
      rw [← hphaseBoundary q, hv_eq]
  have hscore := setup_cumScore_at_runStart_some M_seven w_seven (657497227 / 52500)
    (flatAct sevenPhaseRunCount sevenPhaseAct)
    (flatLen sevenPhaseRunCount sevenPhaseLen)
    (flatScore sevenPhaseRunCount sevenPhaseScore)
    hrecLen hw_shift hrecStep (runStart sevenPhaseRunCount p) i
  unfold M7 sevenTrajectory sevenPhaseStartStep
  rw [hscore]
  have hp : flatPhase sevenPhaseRunCount (runStart sevenPhaseRunCount p) = p := by
    unfold flatPhase
    exact runIndexOfStep_at_offset hcount p 0 (hcount p)
  have hoff : flatOffset sevenPhaseRunCount (runStart sevenPhaseRunCount p) = 0 := by
    unfold flatOffset
    rw [hp]
    omega
  have hlt : 0 < 21 * p + 438 := by omega
  have hp0 : sevenPhaseScore p 0 = V_seven ((p : ℚ) + 20) := by
    simp [sevenPhaseScore, hlt]
    exact stateCoreStart_at_begin ((p : ℚ) + 20)
  simp [flatScore, hp, hoff, hp0]

/-- **Master Unrolled 7-Action Counterexample Theorem (`karlin_conjecture_disproof_unrolled`)**:
    Stated purely in terms of `IsSkewSymmetric`, `IsStrictFPTrajectory`, and `cumScore`:
    1. `IsSkewSymmetric M7`: `M7` is a 7×7 skew-symmetric rational game.
    2. `IsStrictFPTrajectory M7 sevenTrajectory`: `sevenTrajectory` is a strictly tie-free
       Fictitious Play trajectory at every integer step `t ≥ 1` from zero initial counts at `t = 0`.
    3. At the start of every phase `p ∈ ℕ` (`t_p = sevenPhaseStartStep p`), the active best
       response is `sevenTrajectory t_p = some 0`, its cumulative payoff `cumScore M7 sevenTrajectory t_p (some 0)`
       is an explicit quadratic polynomial in `p`, and the elapsed step count `t_p` is an
       explicit cubic polynomial in `p`, witnessing the `Ω(T^{-1/3})` duality gap and refuting
       Karlin's Conjecture. -/
theorem karlin_conjecture_disproof_unrolled :
    IsSkewSymmetric M7 ∧
    IsStrictFPTrajectory M7 sevenTrajectory ∧
    ∀ p : ℕ,
      sevenTrajectory (sevenPhaseStartStep p) = some 0 ∧
      cumScore M7 sevenTrajectory (sevenPhaseStartStep p) (some 0) =
        7 * ((p : ℚ) + 20) ^ 2 + (106 / 21) * ((p : ℚ) + 20) + 105001 / 5000 +
          657497227 / 52500 ∧
      2 * (sevenPhaseStartStep p : ℚ) =
        3822 * (p : ℚ) ^ 3 + 214491 * (p : ℚ) ^ 2 + 4109779 * (p : ℚ) + 2 := by
  refine ⟨seven_unrolled_strict_fp_trajectory.1, seven_unrolled_strict_fp_trajectory.2, ?_⟩
  intro p
  refine ⟨sevenTrajectory_at_phase_start p, ?_, seven_phase_start_time p⟩
  rw [seven_phase_start_score p 0]
  simp [V_seven, W_seven]

/-!
## 7. All-Integer-Time Standard Duality Gap Bounds and Explicit Big-O Refutation
-/

/-- Phase-start integer step `t_p = runStart (setupFullLen rpsRecLen) (3 * p + 1)` for `M4_RPS`. -/
def rpsPhaseStartStep (p : ℕ) : ℕ :=
  runStart (setupFullLen rpsRecLen) (3 * p + 1)

theorem rpsPhaseStartStep_zero : rpsPhaseStartStep 0 = 1 := rfl

theorem rpsPhaseStartStep_strictMono (p : ℕ) :
    rpsPhaseStartStep p < rpsPhaseStartStep (p + 1) := by
  have h1 := rps_phase_start_time p
  have h2 := rps_phase_start_time (p + 1)
  unfold rpsPhaseStartStep
  have hp : (0 : ℚ) ≤ (p : ℚ) := Nat.cast_nonneg p
  have hlt : (runStart (setupFullLen rpsRecLen) (3 * p + 1) : ℚ) <
      (runStart (setupFullLen rpsRecLen) (3 * (p + 1) + 1) : ℚ) := by
    push_cast at h2
    nlinarith
  exact_mod_cast hlt

theorem rpsTrajectory_at_phase_start (p : ℕ) :
    rpsTrajectory (rpsPhaseStartStep p) = some 0 := by
  have hlen : ∀ r : ℕ, 0 < setupFullLen rpsRecLen r := by
    intro r
    rcases r with _ | u
    · exact Nat.zero_lt_one
    · simp [setupFullLen, rpsRecLen]
  have h0 : 0 < setupFullLen rpsRecLen (3 * p + 1) := hlen _
  have hunroll := unrollAction_at_offset (setupFullAct rpsRecAct) hlen (3 * p + 1) 0 h0
  simp only [Nat.add_zero] at hunroll
  unfold rpsTrajectory rpsPhaseStartStep
  rw [hunroll]
  have hmod : (3 * p) % 3 = 0 := by omega
  simp [setupFullAct, rpsRecAct, hmod]

theorem rps_phase_start_score (p : ℕ) (i : Fin 3) :
    cumScore M4_RPS rpsTrajectory (rpsPhaseStartStep p) (some i) =
      r2Vec ((p : ℚ) + 1) i + 20 / 3 := by
  have hrecLen : ∀ u : ℕ, 0 < rpsRecLen u := by
    intro u; unfold rpsRecLen; omega
  have hw_shift : ∀ j : Fin 3, w_RPS j = rpsRecEntryScore 0 j + 20 / 3 := by
    intro j; simp [w_RPS, rpsRecEntryScore]
  have hrecStep : ∀ u : ℕ,
      rpsRecEntryScore (u + 1) =
        scoreVec A_RPS (rpsRecEntryScore u) (runCount (fun _ => 0) (rpsRecAct u) (rpsRecLen u : ℚ)) := by
    intro u
    ext j
    have hmod : u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · have hdiv : (u + 1) / 3 = u / 3 := by omega
      have hm1 : (u + 1) % 3 = 1 := by omega
      have hlen_eq : (rpsRecLen u : ℚ) = 3 * (((u / 3 : ℕ) : ℚ) + 1) + 5 := by
        unfold rpsRecLen
        exact_mod_cast (by omega : u + 8 = 3 * (u / 3 + 1) + 5)
      simp only [rpsRecEntryScore, rpsRecAct, h0, hdiv, hm1, hlen_eq]
      exact (rps_run0_transition (((u / 3 : ℕ) : ℚ) + 1) j).symm
    · have hdiv : (u + 1) / 3 = u / 3 := by omega
      have hm2 : (u + 1) % 3 = 2 := by omega
      have hlen_eq : (rpsRecLen u : ℚ) = 3 * (((u / 3 : ℕ) : ℚ) + 1) + 6 := by
        unfold rpsRecLen
        exact_mod_cast (by omega : u + 8 = 3 * (u / 3 + 1) + 6)
      simp only [rpsRecEntryScore, rpsRecAct, h1, hdiv, hm2, hlen_eq]
      exact (rps_run1_transition (((u / 3 : ℕ) : ℚ) + 1) j).symm
    · have hdiv : (u + 1) / 3 = u / 3 + 1 := by omega
      have hm0 : (u + 1) % 3 = 0 := by omega
      have hlen_eq : (rpsRecLen u : ℚ) = 3 * (((u / 3 : ℕ) : ℚ) + 1) + 7 := by
        unfold rpsRecLen
        exact_mod_cast (by omega : u + 8 = 3 * (u / 3 + 1) + 7)
      simp only [rpsRecEntryScore, rpsRecAct, h2, hdiv, hm0, hlen_eq]
      have hcast : (((u / 3 + 1 : ℕ) : ℚ) + 1) = (((u / 3 : ℕ) : ℚ) + 1) + 1 := by
        push_cast; ring
      rw [hcast]
      exact (rps_run2_transition (((u / 3 : ℕ) : ℚ) + 1) j).symm
  have hscore := setup_cumScore_at_runStart_some A_RPS w_RPS (20 / 3)
    rpsRecAct rpsRecLen rpsRecEntryScore hrecLen hw_shift hrecStep (3 * p) i
  unfold M4_RPS rpsTrajectory rpsPhaseStartStep
  rw [hscore]
  have hdiv : (3 * p) / 3 = p := by omega
  have hmod : (3 * p) % 3 = 0 := by omega
  simp [rpsRecEntryScore, hdiv, hmod]

/-- **All-Integer-Time `Θ(t^{-1/2})` Standard Duality Gap Bounds for the 4-Action RPS Seed
    (`rps_all_integer_time_quadratic_gap`)**:
    At every integer step `t ≥ 1`, the standard two-player empirical saddle-point gap of
    `(M4_RPS, rpsTrajectory, rpsTrajectory)` satisfies:
    `8 / 9 ≤ standardDualityGap M4_RPS rpsTrajectory rpsTrajectory t ^ 2 * t ≤ 400`. -/
theorem rps_all_integer_time_quadratic_gap (t : ℕ) (ht : 1 ≤ t) :
    (8 / 9 : ℚ) ≤ standardDualityGap M4_RPS rpsTrajectory rpsTrajectory t ^ 2 * (t : ℚ) ∧
      standardDualityGap M4_RPS rpsTrajectory rpsTrajectory t ^ 2 * (t : ℚ) ≤ 400 := by
  apply all_integer_time_power_gap_bounds
    rps_unrolled_strict_fp_trajectory.1 rps_unrolled_strict_fp_trajectory.2
    rpsPhaseStartStep_zero rpsPhaseStartStep_strictMono (by norm_num : 1 ≤ 2)
  · intro p
    rw [rpsTrajectory_at_phase_start p, rps_phase_start_score p 0]
    have ht1 := rps_phase_start_time (p + 1)
    change 2 * (rpsPhaseStartStep (p + 1) : ℚ) =
      9 * ((p + 1 : ℕ) : ℚ) ^ 2 + 45 * ((p + 1 : ℕ) : ℚ) + 2 at ht1
    push_cast at ht1
    have hp : (0 : ℚ) ≤ (p : ℚ) := Nat.cast_nonneg p
    simp [r2Vec]
    nlinarith [sq_nonneg (p : ℚ)]
  · intro p
    rw [rpsTrajectory_at_phase_start (p + 1), rps_phase_start_score (p + 1) 0]
    have ht0 := rps_phase_start_time p
    change 2 * (rpsPhaseStartStep p : ℚ) =
      9 * (p : ℚ) ^ 2 + 45 * (p : ℚ) + 2 at ht0
    have hp : (0 : ℚ) ≤ (p : ℚ) := Nat.cast_nonneg p
    simp [r2Vec]
    nlinarith [sq_nonneg (p : ℚ)]
  · exact ht

theorem sevenPhaseStartStep_zero : sevenPhaseStartStep 0 = 1 := rfl

theorem sevenPhaseStartStep_strictMono (p : ℕ) :
    sevenPhaseStartStep p < sevenPhaseStartStep (p + 1) := by
  have h1 := seven_phase_start_time p
  have h2 := seven_phase_start_time (p + 1)
  have hp : (0 : ℚ) ≤ (p : ℚ) := Nat.cast_nonneg p
  have hp2 : (0 : ℚ) ≤ (p : ℚ) ^ 2 := sq_nonneg (p : ℚ)
  have hp3 : (0 : ℚ) ≤ (p : ℚ) ^ 3 := pow_nonneg hp 3
  have hlt : (sevenPhaseStartStep p : ℚ) < (sevenPhaseStartStep (p + 1) : ℚ) := by
    push_cast at h2
    linarith
  exact_mod_cast hlt

/-- **All-Integer-Time `Θ(t^{-1/3})` Standard Duality Gap Bounds for the 7-Action Game `M7`
    (`seven_all_integer_time_cubic_gap`)**:
    At every integer step `t ≥ 1`, the standard two-player empirical saddle-point gap of
    `(M7, sevenTrajectory, sevenTrajectory)` satisfies:
    `343 / 500000 ≤ standardDualityGap M7 sevenTrajectory sevenTrajectory t ^ 3 * t ≤ 32768000000000`. -/
theorem seven_all_integer_time_cubic_gap (t : ℕ) (ht : 1 ≤ t) :
    (343 / 500000 : ℚ) ≤ standardDualityGap M7 sevenTrajectory sevenTrajectory t ^ 3 * (t : ℚ) ∧
      standardDualityGap M7 sevenTrajectory sevenTrajectory t ^ 3 * (t : ℚ) ≤ 32768000000000 := by
  have hdeg : ∀ p : ℕ,
      (343 / 500000 : ℚ) * (sevenPhaseStartStep (p + 1) : ℚ) ^ (3 - 1) ≤
        (2 * cumScore M7 sevenTrajectory (sevenPhaseStartStep p)
          (sevenTrajectory (sevenPhaseStartStep p))) ^ 3 ∧
      (2 * cumScore M7 sevenTrajectory (sevenPhaseStartStep (p + 1))
        (sevenTrajectory (sevenPhaseStartStep (p + 1)))) ^ 3 ≤
        32768000000000 * (sevenPhaseStartStep p : ℚ) ^ (3 - 1) := by
    intro p
    have hmain := karlin_conjecture_disproof_unrolled.2.2
    have hp_spec := hmain p
    have hp1_spec := hmain (p + 1)
    rw [hp_spec.1, hp1_spec.1]
    have hHp := hp_spec.2.1
    have htp := hp_spec.2.2
    have hHp1 := hp1_spec.2.1
    have htp1 := hp1_spec.2.2
    push_cast at hHp1 htp1
    have hp : (0 : ℚ) ≤ (p : ℚ) := Nat.cast_nonneg p
    have hp2 : (0 : ℚ) ≤ (p : ℚ) ^ 2 := sq_nonneg (p : ℚ)
    have hp3 : (0 : ℚ) ≤ (p : ℚ) ^ 3 := pow_nonneg hp 3
    have h1 : (14 : ℚ) * ((p : ℚ) + 20) ^ (3 - 1) ≤
        2 * cumScore M7 sevenTrajectory (sevenPhaseStartStep p) (some 0) := by
      change (14 : ℚ) * ((p : ℚ) + 20) ^ 2 ≤
        2 * cumScore M7 sevenTrajectory (sevenPhaseStartStep p) (some 0)
      linarith
    have h2 : (sevenPhaseStartStep (p + 1) : ℚ) ≤ 2000 * ((p : ℚ) + 20) ^ 3 := by
      linarith
    have h3 : 2 * cumScore M7 sevenTrajectory (sevenPhaseStartStep (p + 1)) (some 0) ≤
        32000 * ((p : ℚ) + 1) ^ (3 - 1) := by
      change 2 * cumScore M7 sevenTrajectory (sevenPhaseStartStep (p + 1)) (some 0) ≤
        32000 * ((p : ℚ) + 1) ^ 2
      linarith
    have h4 : (1 : ℚ) * ((p : ℚ) + 1) ^ 3 ≤ (sevenPhaseStartStep p : ℚ) := by
      linarith
    have hbounds := power_gap_phase_bounds_of_deg_bounds
      (by norm_num : (0 : ℚ) ≤ 14)
      (by norm_num : (0 : ℚ) < 2000)
      (by linarith : (0 : ℚ) ≤ (p : ℚ) + 20)
      (by norm_num : (0 : ℚ) ≤ 32000)
      (by norm_num : (0 : ℚ) < 1)
      (by linarith : (0 : ℚ) ≤ (p : ℚ) + 1)
      (Nat.cast_nonneg (sevenPhaseStartStep (p + 1)))
      (by linarith : 0 ≤ 2 * cumScore M7 sevenTrajectory (sevenPhaseStartStep (p + 1)) (some 0))
      h1 h2 h3 h4
    have hcl_eq : (14 : ℚ) ^ 3 / (2000 : ℚ) ^ (3 - 1) = 343 / 500000 := by norm_num
    have hch_eq : (32000 : ℚ) ^ 3 / (1 : ℚ) ^ (3 - 1) = 32768000000000 := by norm_num
    rw [hcl_eq, hch_eq] at hbounds
    exact hbounds
  exact all_integer_time_power_gap_bounds
    seven_unrolled_strict_fp_trajectory.1 seven_unrolled_strict_fp_trajectory.2
    sevenPhaseStartStep_zero sevenPhaseStartStep_strictMono (by norm_num : 1 ≤ 3)
    (fun p => (hdeg p).1) (fun p => (hdeg p).2) t ht

/-- At every phase boundary `t_p = sevenPhaseStartStep p`, the quadratic scaled gap
    `standardDualityGap M7 sevenTrajectory sevenTrajectory t_p ^ 2 * t_p` grows at least
    linearly in `p + 1`:
    `(196 / 2164047) * (p + 1) ≤ standardDualityGap M7 sevenTrajectory sevenTrajectory t_p ^ 2 * t_p`. -/
theorem seven_phase_start_quadratic_gap_divergence (p : ℕ) :
    (196 / 2164047 : ℚ) * ((p : ℚ) + 1) ≤
      standardDualityGap M7 sevenTrajectory sevenTrajectory (sevenPhaseStartStep p) ^ 2 *
        (sevenPhaseStartStep p : ℚ) := by
  have htp_pos_nat : 1 ≤ sevenPhaseStartStep p := by
    have hle := add_one_le_of_strictMono_tStart
      sevenPhaseStartStep_zero sevenPhaseStartStep_strictMono p
    omega
  have htp_pos : (0 : ℚ) < (sevenPhaseStartStep p : ℚ) := by exact_mod_cast htp_pos_nat
  rw [standardDualityGap_eq_stepDualityGap
    seven_unrolled_strict_fp_trajectory.1 seven_unrolled_strict_fp_trajectory.2 htp_pos_nat]
  unfold stepDualityGap
  have hmain := karlin_conjecture_disproof_unrolled.2.2 p
  rw [hmain.1]
  have hHp := hmain.2.1
  have htp := hmain.2.2
  have hp : (0 : ℚ) ≤ (p : ℚ) := Nat.cast_nonneg p
  have hp2 : (0 : ℚ) ≤ (p : ℚ) ^ 2 := sq_nonneg (p : ℚ)
  have hp3 : (0 : ℚ) ≤ (p : ℚ) ^ 3 := pow_nonneg hp 3
  have hH_lower : 14 * ((p : ℚ) + 1) ^ 2 ≤
      2 * cumScore M7 sevenTrajectory (sevenPhaseStartStep p) (some 0) := by
    linarith
  have hH_sq :
      (14 * ((p : ℚ) + 1) ^ 2) ^ 2 ≤
        (2 * cumScore M7 sevenTrajectory (sevenPhaseStartStep p) (some 0)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hH_lower 2
  have ht_upper : (sevenPhaseStartStep p : ℚ) ≤ 2164047 * ((p : ℚ) + 1) ^ 3 := by
    linarith
  have hpow_id :
      (2 * cumScore M7 sevenTrajectory (sevenPhaseStartStep p) (some 0) /
        (sevenPhaseStartStep p : ℚ)) ^ 2 * (sevenPhaseStartStep p : ℚ) =
      (2 * cumScore M7 sevenTrajectory (sevenPhaseStartStep p) (some 0)) ^ 2 /
        (sevenPhaseStartStep p : ℚ) := by
    have ht_ne : (sevenPhaseStartStep p : ℚ) ≠ 0 := ne_of_gt htp_pos
    rw [div_pow, sq (sevenPhaseStartStep p : ℚ)]
    field_simp
  rw [hpow_id, le_div_iff₀ htp_pos]
  have hmul :
      (196 / 2164047 : ℚ) * ((p : ℚ) + 1) * (sevenPhaseStartStep p : ℚ) ≤
        (196 / 2164047 : ℚ) * ((p : ℚ) + 1) * (2164047 * ((p : ℚ) + 1) ^ 3) :=
    mul_le_mul_of_nonneg_left ht_upper (by positivity)
  have hring :
      (196 / 2164047 : ℚ) * ((p : ℚ) + 1) * (2164047 * ((p : ℚ) + 1) ^ 3) =
        (14 * ((p : ℚ) + 1) ^ 2) ^ 2 := by
    ring
  rw [hring] at hmul
  exact le_trans hmul hH_sq

/-- **Complete Two-Player & Big-O Refutation of Karlin's Conjecture
    (`karlin_conjecture_refuted_bigO`, Theorem 1.1 & Theorem E.1)**:
    For the 7-action skew-symmetric zero-sum game `M7`:
    1. `Fintype.card (Option (Fin 6)) = 7` and `IsSkewSymmetric M7`.
    2. `sevenTrajectory 0 = none` and `(sevenTrajectory, sevenTrajectory)` is a strictly tie-free
       simultaneous two-player Fictitious Play trajectory at every integer step `t ≥ 1` from
       zero initial counts.
    3. **Tie-Breaking Uniqueness**: Any weak two-player Fictitious Play trajectory `(rowPlay, colPlay)`
       starting with `rowPlay 0 = none` and `colPlay 0 = none` equals `(sevenTrajectory, sevenTrajectory)`
       at every integer step `t ∈ ℕ`.
    4. **All-Integer-Time `Θ(t^{-1/3})` Empirical Saddle-Point Gap**:
       For every integer step `t ≥ 1`,
       `343 / 500000 ≤ standardDualityGap M7 sevenTrajectory sevenTrajectory t ^ 3 * t ≤ 32768000000000`.
    5. **Explicit Big-O Refutation of the `O(t^{-1/2})` Rate**:
       For every rational constant `C : ℚ`, there exists an integer step `t ≥ 1` such that
       `C < standardDualityGap M7 sevenTrajectory sevenTrajectory t ^ 2 * t`
       (i.e. `standardDualityGap M7 sevenTrajectory sevenTrajectory t ≠ O(t^{-1/2})`). -/
theorem karlin_conjecture_refuted_bigO :
    Fintype.card (Option (Fin 6)) = 7 ∧
    IsSkewSymmetric M7 ∧
    sevenTrajectory 0 = none ∧
    IsStrictTwoPlayerFPTrajectory M7 sevenTrajectory sevenTrajectory ∧
    (∀ rowPlay colPlay : ℕ → Option (Fin 6),
      IsWeakTwoPlayerFPTrajectory M7 rowPlay colPlay →
      rowPlay 0 = none → colPlay 0 = none →
      ∀ t : ℕ, rowPlay t = sevenTrajectory t ∧ colPlay t = sevenTrajectory t) ∧
    (∀ t : ℕ, 1 ≤ t →
      (343 / 500000 : ℚ) ≤ standardDualityGap M7 sevenTrajectory sevenTrajectory t ^ 3 * (t : ℚ) ∧
        standardDualityGap M7 sevenTrajectory sevenTrajectory t ^ 3 * (t : ℚ) ≤ 32768000000000) ∧
    (∀ C : ℚ, ∃ t : ℕ, 1 ≤ t ∧
      C < standardDualityGap M7 sevenTrajectory sevenTrajectory t ^ 2 * (t : ℚ)) := by
  have hskew := seven_unrolled_strict_fp_trajectory.1
  have hstrict := seven_unrolled_strict_fp_trajectory.2
  have h0 : sevenTrajectory 0 = none := rfl
  refine ⟨by decide, hskew, h0,
    (isStrictTwoPlayerFPTrajectory_iff_isStrictFPTrajectory hskew sevenTrajectory).mpr hstrict,
    fun rowPlay colPlay hweak hr0 hc0 t =>
      unique_two_player_fp_trajectory hskew hstrict hweak hr0 hc0 t,
    seven_all_integer_time_cubic_gap, ?_⟩
  intro C
  let p : ℕ := ⌈C * (2164047 / 196)⌉₊
  refine ⟨sevenPhaseStartStep p, ?_, ?_⟩
  · have hle := add_one_le_of_strictMono_tStart
      sevenPhaseStartStep_zero sevenPhaseStartStep_strictMono p
    omega
  · have hceil : C * (2164047 / 196) ≤ (p : ℚ) := Nat.le_ceil (C * (2164047 / 196))
    have hlt : C < (196 / 2164047 : ℚ) * ((p : ℚ) + 1) := by linarith
    exact lt_of_lt_of_le hlt (seven_phase_start_quadratic_gap_divergence p)

end Karlin

#print axioms Karlin.AlgebraicClock.phase_score_transition
#print axioms Karlin.AlgebraicClock.endpoint_counter_increment
#print axioms Karlin.AlgebraicClock.cone_identity
#print axioms Karlin.AlgebraicClock.scaled_skew
#print axioms Karlin.rpsAlgebraicClock_spec
#print axioms Karlin.sevenAlgebraicClock_spec
#print axioms Karlin.liftedGameMat_skew
#print axioms Karlin.liftedGameMat_mul_liftedCountMat
#print axioms Karlin.liftedWeightVec_mul_liftedCountMat
#print axioms Karlin.AlgebraicClock.lift_spec
#print axioms Karlin.seven_fullLen_at_phase_offset
#print axioms Karlin.seven_runStart_core_triples
#print axioms Karlin.seven_phase_start_time
#print axioms Karlin.setup_cumScore_at_runStart_some
#print axioms Karlin.sevenTrajectory_at_phase_start
#print axioms Karlin.seven_phase_start_score
#print axioms Karlin.karlin_conjecture_disproof_unrolled
#print axioms Karlin.rpsPhaseStartStep_zero
#print axioms Karlin.rpsPhaseStartStep_strictMono
#print axioms Karlin.rpsTrajectory_at_phase_start
#print axioms Karlin.rps_phase_start_score
#print axioms Karlin.rps_all_integer_time_quadratic_gap
#print axioms Karlin.sevenPhaseStartStep_zero
#print axioms Karlin.sevenPhaseStartStep_strictMono
#print axioms Karlin.seven_all_integer_time_cubic_gap
#print axioms Karlin.seven_phase_start_quadratic_gap_divergence
#print axioms Karlin.karlin_conjecture_refuted_bigO
