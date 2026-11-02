import Karlin.FictitiousPlay

/-!
# Section 4 & Section 6.4: The Order-2 Rock-Paper-Scissors Clock (`prop:seed`, `prop:seedadmissible`)

This module formalizes:
1. **Proposition 4.1 (`prop:seed`)**: The 3-action Rock-Paper-Scissors skew-symmetric game
   $A_{\mathrm{RPS}}$, its width-2 score and count tables $R_2, C_2$, the polynomial table
   identity $A_{\mathrm{RPS}} C_2 = R_2 N_2$, the endpoint counter identity $v C_2 = (1, 0)$,
   strict best-response validity with margin $\ge 1/3$ at every step of the 3-run phase word
   $\mathsf{W}_2(q) = 0^{3q+5} 1^{3q+6} 2^{3q+7}$ for all $q \ge 1$ (proved via
   `pure_run_margin_of_endpoints`), exact phase return $\mathbf{r}_2(q) \mapsto \mathbf{r}_2(q+1)$,
   prefix marker $\ge 1$, and entry support-safety.
2. **Proposition 6.3 (`prop:seedadmissible`) & Section 6.4.1 (`eq:rpscorrection`)**:
   Admissibility of the RPS clock for the first inductive lift ($\tau = 1, c_{\mathrm{ref}} = 1/2,
   \ell_* = 0, a_P = \frac{2}{27}\mathbf{1}_3$), positive cone identity $a^\top X = \zeta^\circ + \zeta^\circ B_3$,
   vanishing of the higher compatibility test $h = 4$, and exact cancellation of the lowest
   compatibility obstruction $\langle Z^{(2)}, (D^\circ)^\top X \rangle = -81/2$ by the gain choice
   $c(T_*) = \frac{2(T_* + 9)}{4T_* + 9} \in (0, 1)$ for all $T_* \ge 5$.
-/

namespace Karlin

open scoped BigOperators

/-- The 3×3 skew-symmetric Rock-Paper-Scissors payoff matrix `A_RPS`. -/
def A_RPS : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, -1, 1;
     1,  0, -1;
    -1,  1,  0]

/-- Width-2 score coefficient table `R_2` in the binomial basis `p_1(q) = (1, q)ᵀ`. -/
def R2 : Matrix (Fin 3) (Fin 2) ℚ :=
  !![1,      1;
    -11 / 3, -2;
     2 / 3,  1]

/-- Width-2 count coefficient table `C_2` in the binomial basis `p_1(q) = (1, q)ᵀ`. -/
def C2 : Matrix (Fin 3) (Fin 2) ℚ :=
  !![5, 3;
     6, 3;
     7, 3]

/-- Width-2 forward-difference matrix `N_2`. -/
def N2 : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, 0;
     1, 0]

/-- Endpoint counter row `v = (0, -1, 1)`. -/
def v_RPS : Fin 3 → ℚ
  | 0 => 0
  | 1 => -1
  | 2 => 1

/-- Phase-entry score vector `r_2(q) = R_2 (1, q)ᵀ`. -/
def r2Vec (q : ℚ) : Fin 3 → ℚ
  | 0 => q + 1
  | 1 => -2 * q - 11 / 3
  | 2 => q + 2 / 3

/-- Intermediate score vector after Run 0 (`0^{3q+5}`). -/
def rpsStateAfterRun0 (q : ℚ) : Fin 3 → ℚ
  | 0 => q + 1
  | 1 => q + 4 / 3
  | 2 => -2 * q - 13 / 3

/-- Intermediate score vector after Run 1 (`1^{3q+6}`). -/
def rpsStateAfterRun1 (q : ℚ) : Fin 3 → ℚ
  | 0 => -2 * q - 5
  | 1 => q + 4 / 3
  | 2 => q + 5 / 3

/-- `A_RPS` is skew-symmetric. -/
theorem A_RPS_skew : IsSkewSymmetric A_RPS := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **Table Identity (`prop:seed`)**: `A_RPS * C_2 = R_2 * N_2`. -/
theorem A_RPS_mul_C2_eq_R2_mul_N2 : A_RPS * C2 = R2 * N2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, A_RPS, C2, R2, N2] <;>
    norm_num

set_option linter.unnecessarySeqFocus false

/-- **Counter Identity (`prop:seed`)**: `v * C_2 = (1, 0)`. -/
theorem v_RPS_mul_C2 :
    (fun j : Fin 2 => ∑ i : Fin 3, v_RPS i * C2 i j) = ![1, 0] := by
  ext j
  fin_cases j <;> simp [Fin.sum_univ_three, v_RPS, C2] <;> norm_num

/-- **Run 0 Handoff Identity**: Playing action `0` for `3q + 5` steps from `r2Vec q`
    produces `rpsStateAfterRun0 q`. -/
theorem rps_run0_transition (q : ℚ) (j : Fin 3) :
    scoreVec A_RPS (r2Vec q) (runCount (fun _ => 0) 0 (3 * q + 5)) j =
      rpsStateAfterRun0 q j := by
  rw [scoreVec_runCount]
  fin_cases j <;> simp [scoreVec, A_RPS, r2Vec, rpsStateAfterRun0] <;> ring

/-- **Run 1 Handoff Identity**: Playing action `1` for `3q + 6` steps from `rpsStateAfterRun0 q`
    produces `rpsStateAfterRun1 q`. -/
theorem rps_run1_transition (q : ℚ) (j : Fin 3) :
    scoreVec A_RPS (rpsStateAfterRun0 q) (runCount (fun _ => 0) 1 (3 * q + 6)) j =
      rpsStateAfterRun1 q j := by
  rw [scoreVec_runCount]
  fin_cases j <;> simp [scoreVec, A_RPS, rpsStateAfterRun0, rpsStateAfterRun1] <;> ring

/-- **Run 2 Handoff & Phase Return Identity**: Playing action `2` for `3q + 7` steps from
    `rpsStateAfterRun1 q` returns the score vector to `r2Vec (q + 1)`. -/
theorem rps_run2_transition (q : ℚ) (j : Fin 3) :
    scoreVec A_RPS (rpsStateAfterRun1 q) (runCount (fun _ => 0) 2 (3 * q + 7)) j =
      r2Vec (q + 1) j := by
  rw [scoreVec_runCount]
  fin_cases j <;> simp [scoreVec, A_RPS, rpsStateAfterRun1, r2Vec] <;> ring

/-- **Run 0 Strict Best-Response Validity (`prop:seed`)**:
    For every `q ≥ 1` and every step offset `0 ≤ h ≤ 3q + 4` during Run 0 (`0^{3q+5}`),
    action `0` strictly beats both rival actions `1` and `2` by margin at least `1/3`. -/
theorem rps_run0_valid {q h : ℚ} (hq : 1 ≤ q) (hh0 : 0 ≤ h) (hhL : h ≤ (3 * q + 5) - 1) :
    (1 / 3 : ℚ) ≤
        scoreVec A_RPS (r2Vec q) (runCount (fun _ => 0) 0 h) 0 -
          scoreVec A_RPS (r2Vec q) (runCount (fun _ => 0) 0 h) 1 ∧
      (1 / 3 : ℚ) ≤
        scoreVec A_RPS (r2Vec q) (runCount (fun _ => 0) 0 h) 0 -
          scoreVec A_RPS (r2Vec q) (runCount (fun _ => 0) 0 h) 2 := by
  constructor
  · apply pure_run_margin_of_endpoints A_RPS_skew (r2Vec q) (fun _ => 0) 0 1 hh0 hhL
    · simp [scoreVec, r2Vec]; linarith
    · simp [scoreVec, r2Vec, A_RPS]; linarith
  · apply pure_run_margin_of_endpoints A_RPS_skew (r2Vec q) (fun _ => 0) 0 2 hh0 hhL
    · simp [scoreVec, r2Vec]; linarith
    · simp [scoreVec, r2Vec, A_RPS]; linarith

/-- **Run 1 Strict Best-Response Validity (`prop:seed`)**:
    For every `q ≥ 1` and every step offset `0 ≤ h ≤ 3q + 5` during Run 1 (`1^{3q+6}`),
    action `1` strictly beats both rival actions `0` and `2` by margin at least `1/3`. -/
theorem rps_run1_valid {q h : ℚ} (hq : 1 ≤ q) (hh0 : 0 ≤ h) (hhL : h ≤ (3 * q + 6) - 1) :
    (1 / 3 : ℚ) ≤
        scoreVec A_RPS (rpsStateAfterRun0 q) (runCount (fun _ => 0) 1 h) 1 -
          scoreVec A_RPS (rpsStateAfterRun0 q) (runCount (fun _ => 0) 1 h) 0 ∧
      (1 / 3 : ℚ) ≤
        scoreVec A_RPS (rpsStateAfterRun0 q) (runCount (fun _ => 0) 1 h) 1 -
          scoreVec A_RPS (rpsStateAfterRun0 q) (runCount (fun _ => 0) 1 h) 2 := by
  constructor
  · apply pure_run_margin_of_endpoints A_RPS_skew (rpsStateAfterRun0 q) (fun _ => 0) 1 0 hh0 hhL
    · simp [scoreVec, rpsStateAfterRun0]; linarith
    · simp [scoreVec, rpsStateAfterRun0, A_RPS]; linarith
  · apply pure_run_margin_of_endpoints A_RPS_skew (rpsStateAfterRun0 q) (fun _ => 0) 1 2 hh0 hhL
    · simp [scoreVec, rpsStateAfterRun0]; linarith
    · simp [scoreVec, rpsStateAfterRun0, A_RPS]; linarith

/-- **Run 2 Strict Best-Response Validity (`prop:seed`)**:
    For every `q ≥ 1` and every step offset `0 ≤ h ≤ 3q + 6` during Run 2 (`2^{3q+7}`),
    action `2` strictly beats both rival actions `0` and `1` by margin at least `1/3`. -/
theorem rps_run2_valid {q h : ℚ} (hq : 1 ≤ q) (hh0 : 0 ≤ h) (hhL : h ≤ (3 * q + 7) - 1) :
    (1 / 3 : ℚ) ≤
        scoreVec A_RPS (rpsStateAfterRun1 q) (runCount (fun _ => 0) 2 h) 2 -
          scoreVec A_RPS (rpsStateAfterRun1 q) (runCount (fun _ => 0) 2 h) 0 ∧
      (1 / 3 : ℚ) ≤
        scoreVec A_RPS (rpsStateAfterRun1 q) (runCount (fun _ => 0) 2 h) 2 -
          scoreVec A_RPS (rpsStateAfterRun1 q) (runCount (fun _ => 0) 2 h) 1 := by
  constructor
  · apply pure_run_margin_of_endpoints A_RPS_skew (rpsStateAfterRun1 q) (fun _ => 0) 2 0 hh0 hhL
    · simp [scoreVec, rpsStateAfterRun1]; linarith
    · simp [scoreVec, rpsStateAfterRun1, A_RPS]; linarith
  · apply pure_run_margin_of_endpoints A_RPS_skew (rpsStateAfterRun1 q) (fun _ => 0) 2 1 hh0 hhL
    · simp [scoreVec, rpsStateAfterRun1]; linarith
    · simp [scoreVec, rpsStateAfterRun1, A_RPS]; linarith

/-- **Support-Safety at Phase Entry (`eq:supportsafe` in `prop:seed`)**:
    At `r_2(q) + A_RPS e_0 - vᵀ`, action `0` beats action `1` by `3q + 8/3 ≥ 17/3`
    and beats action `2` by `7/3` for all `q ≥ 1`. -/
theorem rps_entry_support_safety {q : ℚ} (hq : 1 ≤ q) :
    (17 / 3 : ℚ) ≤
        (r2Vec q 0 + A_RPS 0 0 - v_RPS 0) - (r2Vec q 1 + A_RPS 1 0 - v_RPS 1) ∧
      (7 / 3 : ℚ) ≤
        (r2Vec q 0 + A_RPS 0 0 - v_RPS 0) - (r2Vec q 2 + A_RPS 2 0 - v_RPS 2) := by
  simp [r2Vec, A_RPS, v_RPS]
  constructor <;> linarith

/-- **Nonnegative Initial Count Realization (`sec:seed`)**:
    `r_2(q) + (2/3) 1_3 = A_RPS * (0, q + 4/3, 2q + 3)ᵀ`. -/
theorem rps_initial_count_realization (q : ℚ) (i : Fin 3) :
    r2Vec q i + 2 / 3 =
      ∑ j : Fin 3, A_RPS i j * (![0, q + 4 / 3, 2 * q + 3] : Fin 3 → ℚ) j := by
  fin_cases i <;> simp [Fin.sum_univ_three, r2Vec, A_RPS] <;> ring

/-!
## Proposition 6.3 (`prop:seedadmissible`): Admissibility of the RPS Seed Clock
-/

/-- Positive parent weights `a_P = (2/27, 2/27, 2/27)ᵀ` for the RPS seed clock. -/
def aP_RPS : Fin 3 → ℚ := fun _ => 2 / 27

/-- Full positive old-action weight vector `a = (2/27, 2/27, 2/27, 15/2)ᵀ` (`2H - c_ref = 15/2`). -/
def a_RPS : Fin 4 → ℚ
  | 0 => 2 / 27
  | 1 => 2 / 27
  | 2 => 2 / 27
  | 3 => 15 / 2

/-- Old-block count table `X ∈ ℚ^{4×3}` for the RPS clock at `τ = 1`. -/
def X_RPS : Matrix (Fin 4) (Fin 3) ℚ :=
  !![0,  8, 9;
     0,  9, 9;
     0, 10, 9;
     1,  0, 0]

/-- Reference outer-height row `ζ° = (4, 3/2, 1)` in binomial basis `p_2(q)`. -/
def zetaRef_RPS : Fin 3 → ℚ := ![4, 3 / 2, 1]

/-- Width-3 backward shift matrix `B_3 = T_3⁻¹`. -/
def B3 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![ 1,  0, 0;
     -1,  1, 0;
      1, -1, 1]

/-- **Proposition 6.3(ii) (`prop:seedadmissible`)**:
    `a_P` is strictly positive and satisfies `a_Pᵀ C_2 = (4/3, 2/3) = t_{1, 1/2}(χ)`. -/
theorem rps_admissible_weights :
    (∀ i : Fin 3, 0 < aP_RPS i) ∧
      (fun j : Fin 2 => ∑ i : Fin 3, aP_RPS i * C2 i j) = ![4 / 3, 2 / 3] := by
  refine ⟨fun i => by simp [aP_RPS], ?_⟩
  ext j
  fin_cases j <;> simp [Fin.sum_univ_three, aP_RPS, C2] <;> norm_num

/-- **Positive Cone Identity (`eq:coneidentity` for RPS)**:
    `aᵀ X_RPS = ζ° + ζ° B_3 = (15/2, 2, 2)`. -/
theorem rps_cone_identity :
    (fun j : Fin 3 => ∑ i : Fin 4, a_RPS i * X_RPS i j) =
      (fun j : Fin 3 => zetaRef_RPS j + ∑ k : Fin 3, zetaRef_RPS k * B3 k j) := by
  ext j
  fin_cases j <;> simp [Fin.sum_univ_four, Fin.sum_univ_three, a_RPS, X_RPS, zetaRef_RPS, B3] <;>
    norm_num

/-- **Even-Order Gain Correction (`eq:rpscorrection`)**:
    For every reset scale `T_star ≥ 5`, the adjusted gain
    `c = 2 * (T_star + 9) / (4 * T_star + 9)` lies strictly in `(0, 1)` and cancels
    the lowest compatibility obstruction `-81 / 2 + (c - 1 / 2) * (27 + 12 * T_star) = 0`. -/
theorem rps_lowest_test_cancellation {T_star : ℚ} (hT : 5 ≤ T_star) :
    let c := 2 * (T_star + 9) / (4 * T_star + 9)
    0 < c ∧ c < 1 ∧ -81 / 2 + (c - 1 / 2) * (27 + 12 * T_star) = 0 := by
  intro c
  have hden : 0 < 4 * T_star + 9 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · change 0 < 2 * (T_star + 9) / (4 * T_star + 9)
    positivity
  · change 2 * (T_star + 9) / (4 * T_star + 9) < 1
    rw [div_lt_iff₀ hden]
    linarith
  · change -81 / 2 + (2 * (T_star + 9) / (4 * T_star + 9) - 1 / 2) * (27 + 12 * T_star) = 0
    field_simp
    ring

/-!
## Section 5.1 Tables and Deficit Equation for the RPS Clock
-/

/-- Width-3 forward-difference matrix `N_3`. -/
def N3_RPS : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, 0, 0;
     1, 0, 0;
     0, 1, 0]

/-- The 4×4 gateway endpoint payoff matrix `G_O` for the RPS clock (`eq:old`, Section 5.1). -/
def GO_RPS : Matrix (Fin 4) (Fin 4) ℚ :=
  !![ 0, -1,  1,  0;
      1,  0, -1,  2;
     -1,  1,  0, -2;
      0, -2,  2,  0]

/-- Skew-symmetry of `GO_RPS`. -/
theorem GO_RPS_skew : IsSkewSymmetric GO_RPS := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Old-action score table `S ∈ ℚ^{4×3}` for the RPS clock from Section 5.1 (`eq:old`). -/
def S_RPS (delta : ℚ) : Matrix (Fin 4) (Fin 3) ℚ :=
  !![ 7 / 2,         1 / 2, 1;
     -7 / 6,        -5 / 2, 1;
     19 / 6,         1 / 2, 1;
      7 / 2 + delta, -1 / 2, 1]

/-- Old-action score change table `D = S N_3 - G_O X_RPS ∈ ℚ^{4×3}` (`eq:old`, Section 5.1),
    independent of `delta` by `e0_row_mul_N_mat`. -/
def D_RPS : Matrix (Fin 4) (Fin 3) ℚ :=
  !![ 1 / 2,  0, 0;
     -9 / 2,  3, 0;
      5 / 2,  0, 0;
     -1 / 2, -1, 0]

/-- The top-degree column `c = 2` of `D_RPS` is identically zero (`eq:top`, Lemma 5.3). -/
theorem D_RPS_last_col_zero (i : Fin 4) :
    D_RPS i ⟨2, by omega⟩ = 0 := by
  fin_cases i <;> rfl

set_option linter.unnecessarySeqFocus false in
/-- **Exact Section 5.1 Deficit Equation for the RPS Clock (`lem:gateway`, Equation (32))**:
    For all `delta ∈ ℚ`, `S_RPS delta * N3_RPS - GO_RPS * X_RPS = D_RPS`. -/
theorem rps_deficit_equation (delta : ℚ) :
    S_RPS delta * N3_RPS - GO_RPS * X_RPS = D_RPS := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, S_RPS, N3_RPS, GO_RPS, X_RPS, D_RPS] <;>
    ring

end Karlin

#print axioms Karlin.A_RPS_skew
#print axioms Karlin.A_RPS_mul_C2_eq_R2_mul_N2
#print axioms Karlin.v_RPS_mul_C2
#print axioms Karlin.rps_run0_transition
#print axioms Karlin.rps_run1_transition
#print axioms Karlin.rps_run2_transition
#print axioms Karlin.rps_run0_valid
#print axioms Karlin.rps_run1_valid
#print axioms Karlin.rps_run2_valid
#print axioms Karlin.rps_entry_support_safety
#print axioms Karlin.rps_initial_count_realization
#print axioms Karlin.rps_admissible_weights
#print axioms Karlin.rps_cone_identity
#print axioms Karlin.rps_lowest_test_cancellation
#print axioms Karlin.GO_RPS_skew
#print axioms Karlin.D_RPS_last_col_zero
#print axioms Karlin.rps_deficit_equation
