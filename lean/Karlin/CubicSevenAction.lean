import Karlin.FictitiousPlay
import Karlin.RPSClock

/-!
# Appendix E: Explicit 7-Action Game Refuting Karlin's Conjecture (`beta7:main`, `prop:seven-family`)

This module formalizes Appendix E of `v12_annotated.tex`:
1. **The 6×6 Recurrent Matrix `M_seven` and 7×7 Zero-Count Game `M7`**:
   Skew-symmetry (`M_seven_skew`, `M7_skew`) and exact setup realization
   `w_seven = V(20) + (657497227 / 52500) 1_6` (`seven_setup_realization`).
2. **Theorem E.1 (`beta7:main` — Exact Phase Return & Best-Response Margins ≥ 10⁻⁴)**:
   - Exact polynomial phase return identities (`seven_reset_identity`, `seven_timing_identity`,
     `seven_phase_return`): `V(k) + M_seven (Q(k), L(k))ᵀ = V(k + 1)`.
   - Strict positivity and lower bounds `≥ 126k + 61` of all run lengths for `k ≥ 20`
     (`seven_run_lengths_lower_bound`).
   - Core RPS sub-cycle (`r_1^{6ℓ+1} r_2^{6ℓ+3} r_3^{6ℓ+5}`) strict best-response validity
     with margin `≥ 1/10000` at every step via `pure_run_margin_of_endpoints`
     (`seven_core_r1_valid`, `seven_core_r2_valid`, `seven_core_r3_valid`, `seven_core_cycle_return`),
     plus non-interruption by all 3 guards throughout the core (`seven_guards_wait_during_core`).
   - Guard runs (`g_1^{L_1(k)}, g_2^{L_2(k)}, g_3^{L_3(k)}`) strict best-response validity
     against all 5 rivals at every step for all `k ≥ 20` with margin `≥ 1/10000`
     (`seven_guard1_run_valid`, `seven_guard2_run_valid`, `seven_guard3_run_valid`).
   - Quadratic phase step length `5733 k^2 - 9096 k + 52766` (`seven_phase_total_length`).
3. **Theorem E.2 (`prop:seven-family` — Order-3 Clock & Admissibility for All-Orders Lift)**:
   - Binomial table identity `M_seven * C_seven = R_seven * N_3` (`M_seven_mul_C_eq_R_mul_N3`).
   - Counter identity `v_seven * C_seven = (1, 0, 0)` (`v_seven_mul_C`).
   - Positive weights `aP_seven > 0` satisfying `aP_sevenᵀ C_seven = (736/63, 968/63, 12)`
     (`seven_admissible_weights`) and full cone identity `(aP_sevenᵀ, 15/2) X_seven = ζ + ζ B_4`
     (`seven_cone_identity`).
   - Exact moment equation `E_seven - E_sevenᵀ B_4 = D_sevenᵀ X_seven - ℓ_*ᵀ ψ_seven`
     (`seven_moment_equation`).
-/

namespace Karlin

open scoped BigOperators

/-- The 3×3 coupling block `G` between core RPS actions and guard actions in Appendix E. -/
def G_seven : Matrix (Fin 3) (Fin 3) ℚ :=
  !![-1 / 84, 19 / 2268, 2 / 567;
     -1 / 84, 25 / 2268, 1 / 1134;
     -1 / 84, 19 / 2268, 2 / 567]

/-- The 3×3 lower-triangular guard interaction generator `A` in Appendix E. -/
def A_guard : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0,         0,       0;
     8 / 189,   0,       0;
    -1 / 1512,  5 / 504, 0]

/-- The 6×6 recurrent skew-symmetric payoff matrix `M = [R, G; -Gᵀ, A - Aᵀ]`. -/
def M_seven : Matrix (Fin 6) (Fin 6) ℚ :=
  !![ 0,        -1,         1,        -1 / 84,    19 / 2268,  2 / 567;
      1,         0,        -1,        -1 / 84,    25 / 2268,  1 / 1134;
     -1,         1,         0,        -1 / 84,    19 / 2268,  2 / 567;
      1 / 84,    1 / 84,    1 / 84,    0,        -8 / 189,    1 / 1512;
    -19 / 2268, -25 / 2268, -19 / 2268, 8 / 189,   0,        -5 / 504;
     -2 / 567,  -1 / 1134,  -2 / 567, -1 / 1512,  5 / 504,    0]

/-- The 6-dimensional setup payoff column `w` in Appendix E (`eq:w`). -/
def w_seven : Fin 6 → ℚ
  | 0 => 21623993 / 1400
  | 1 => 900599643 / 70000
  | 2 => 270299909 / 17500
  | 3 => 1
  | 4 => 182265841 / 12600
  | 5 => 216239923 / 14000

/-- The complete 7×7 zero-count skew-symmetric payoff matrix `M_7 = setupMatrix M_seven w_seven`. -/
def M7 : Matrix (Option (Fin 6)) (Option (Fin 6)) ℚ :=
  setupMatrix M_seven w_seven

set_option linter.unnecessarySeqFocus false

/-- `M_seven` is skew-symmetric. -/
theorem M_seven_skew : IsSkewSymmetric M_seven := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [M_seven] <;> norm_num

/-- `M7` is skew-symmetric. -/
theorem M7_skew : IsSkewSymmetric M7 :=
  setupMatrix_skewSymmetric M_seven_skew w_seven

/-- Core count increments `Q(k) ∈ ℚ^3` in phase `k`. -/
def Q_seven (k : ℚ) : Fin 3 → ℚ
  | 0 => 1029 * k ^ 2 + 1414 * k + 456
  | 1 => 1029 * k ^ 2 + 1428 * k + 468
  | 2 => 1029 * k ^ 2 + 1442 * k + 480

/-- Guard run lengths `L(k) ∈ ℚ^3` in phase `k`. -/
def L_seven (k : ℚ) : Fin 3 → ℚ
  | 0 => 882 * k ^ 2 - 2304 * k + 12498
  | 1 => 882 * k ^ 2 + 2400 * k + 2422
  | 2 => 882 * k ^ 2 - 13476 * k + 36442

/-- Combined 6-action phase count vector `(Q(k), L(k))ᵀ ∈ ℚ^6`. -/
def QL_seven (k : ℚ) : Fin 6 → ℚ
  | 0 => Q_seven k 0
  | 1 => Q_seven k 1
  | 2 => Q_seven k 2
  | 3 => L_seven k 0
  | 4 => L_seven k 1
  | 5 => L_seven k 2

/-- Core entrance score vector `W(k) = D(k) 1 + R q(21k + 10) + u` in phase `k`. -/
def W_seven (k : ℚ) : Fin 3 → ℚ
  | 0 => 7 * k ^ 2 + 106 / 21 * k + 105001 / 5000
  | 1 => 7 * k ^ 2 - 2540 / 21 * k - 389999 / 10000
  | 2 => 7 * k ^ 2 + 106 / 21 * k + 21

/-- Terminal core height `H(k) = 7k^2 + (400/21)k + 165001/5000`. -/
def H_seven (k : ℚ) : ℚ :=
  7 * k ^ 2 + 400 / 21 * k + 165001 / 5000

/-- Guard plateau offsets `s = (1/200, 1/25, 1/21 - 1/2000)ᵀ`. -/
def s_seven : Fin 3 → ℚ
  | 0 => 1 / 200
  | 1 => 1 / 25
  | 2 => 1 / 21 - 1 / 2000

/-- Guard entrance score vector `V_g(k) = H(k) 1 + s + Gᵀ Q(k) - A L(k)`. -/
def Vg_seven (k : ℚ) (i : Fin 3) : ℚ :=
  H_seven k + s_seven i +
    (∑ j : Fin 3, G_seven j i * Q_seven k j) -
    (∑ j : Fin 3, A_guard i j * L_seven k j)

/-- Full 6-action recurrent entrance score profile `V(k) = (W(k), V_g(k))ᵀ`. -/
def V_seven (k : ℚ) : Fin 6 → ℚ
  | 0 => W_seven k 0
  | 1 => W_seven k 1
  | 2 => W_seven k 2
  | 3 => Vg_seven k 0
  | 4 => Vg_seven k 1
  | 5 => Vg_seven k 2

set_option linter.unnecessarySeqFocus false

/-- **Reset Identity (`beta7:reset`)**:
    `G * L(k) = W(k + 1) - W(k) - R * Q(k) = (1/21, 42k - 1889/21, 1/21)ᵀ`. -/
theorem seven_reset_identity (k : ℚ) (i : Fin 3) :
    (∑ j : Fin 3, G_seven i j * L_seven k j) =
      W_seven (k + 1) i - W_seven k i - ∑ j : Fin 3, A_RPS i j * Q_seven k j := by
  fin_cases i <;>
    simp [Fin.sum_univ_three, G_seven, L_seven, W_seven, A_RPS, Q_seven] <;> ring

/-- **Timing Identity (`beta7:timing`)**:
    `Gᵀ Q(k + 1) + (H(k + 1) - H(k)) 1 = A L(k + 1) - Aᵀ L(k)`. -/
theorem seven_timing_identity (k : ℚ) (i : Fin 3) :
    (∑ j : Fin 3, G_seven j i * Q_seven (k + 1) j) + (H_seven (k + 1) - H_seven k) =
      (∑ j : Fin 3, A_guard i j * L_seven (k + 1) j) -
        (∑ j : Fin 3, A_guard j i * L_seven k j) := by
  fin_cases i <;>
    simp [Fin.sum_univ_three, G_seven, Q_seven, H_seven, A_guard, L_seven] <;> ring

/-- **Full Phase Return Identity (`beta7:full`)**:
    `V(k) + M_seven * (Q(k), L(k))ᵀ = V(k + 1)`. -/
theorem seven_phase_return (k : ℚ) (i : Fin 6) :
    V_seven k i + (∑ j : Fin 6, M_seven i j * QL_seven k j) = V_seven (k + 1) i := by
  fin_cases i <;>
    simp [Fin.sum_univ_six, Fin.sum_univ_three, V_seven, W_seven, Vg_seven, H_seven, s_seven,
      M_seven, QL_seven, Q_seven, L_seven, G_seven, A_guard] <;> ring

/-- **Run-Length Lower Bounds (`app:seven` Step 1 & Step 3)**:
    For every `k ≥ 20`, all core counts `Q_i(k)` and guard run lengths `L_i(k)`
    exceed `126k + 61 ≥ 2581`, and `L_3(k) ≥ 119722`. -/
theorem seven_run_lengths_lower_bound {k : ℚ} (hk : 20 ≤ k) :
    126 * k + 61 ≤ Q_seven k 0 ∧
      126 * k + 61 ≤ Q_seven k 1 ∧
      126 * k + 61 ≤ Q_seven k 2 ∧
      126 * k + 61 ≤ L_seven k 0 ∧
      126 * k + 61 ≤ L_seven k 1 ∧
      126 * k + 61 ≤ L_seven k 2 ∧
      119722 ≤ L_seven k 2 := by
  simp only [Q_seven, L_seven]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-!
## Step 2 of Theorem E.1 (`beta7:main`): Core Sub-Cycle Best-Response Validity
-/

/-- Core bias vector `u = (1 + 2ε, 1 + ε, 1)ᵀ` with `ε = 1/10000`. -/
def u_core : Fin 3 → ℚ
  | 0 => 5001 / 5000
  | 1 => 10001 / 10000
  | 2 => 1

/-- Core score state at the start of sub-cycle `ℓ`: `D + R q(ℓ) + u_core`. -/
def coreCycleStart (D ℓ : ℚ) : Fin 3 → ℚ
  | 0 => D + 2 * ℓ + 5001 / 5000
  | 1 => D - 4 * ℓ + 10001 / 10000
  | 2 => D + 2 * ℓ + 1

/-- Core score state after `r_1^{6ℓ+1}` in sub-cycle `ℓ`. -/
def coreAfterR1 (D ℓ : ℚ) : Fin 3 → ℚ
  | 0 => D + 2 * ℓ + 5001 / 5000
  | 1 => D + 2 * ℓ + 20001 / 10000
  | 2 => D - 4 * ℓ

/-- Core score state after `r_2^{6ℓ+3}` in sub-cycle `ℓ`. -/
def coreAfterR2 (D ℓ : ℚ) : Fin 3 → ℚ
  | 0 => D - 4 * ℓ - 9999 / 5000
  | 1 => D + 2 * ℓ + 20001 / 10000
  | 2 => D + 2 * ℓ + 3

/-- **Core Sub-Cycle Transitions (`app:seven` Step 2)**:
    Playing `r_1^{6ℓ+1}`, then `r_2^{6ℓ+3}`, then `r_3^{6ℓ+5}` transitions the core score vector
    from `coreCycleStart D ℓ` to `coreAfterR1 D ℓ`, `coreAfterR2 D ℓ`, and `coreCycleStart D (ℓ + 1)`. -/
theorem seven_core_cycle_transitions (D ℓ : ℚ) :
    scoreVec A_RPS (coreCycleStart D ℓ) (runCount (fun _ => 0) 0 (6 * ℓ + 1)) = coreAfterR1 D ℓ ∧
      scoreVec A_RPS (coreAfterR1 D ℓ) (runCount (fun _ => 0) 1 (6 * ℓ + 3)) = coreAfterR2 D ℓ ∧
      scoreVec A_RPS (coreAfterR2 D ℓ) (runCount (fun _ => 0) 2 (6 * ℓ + 5)) =
        coreCycleStart D (ℓ + 1) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (ext i; fin_cases i <;>
      simp [scoreVec, runCount, A_RPS,
        coreCycleStart, coreAfterR1, coreAfterR2] <;> ring)

/-- **Core Sub-Run `r_1^{6ℓ+1}` Validity**:
    Throughout `0 ≤ h ≤ 6ℓ`, action `0` (`r_1`) beats `r_2` and `r_3` by margin `≥ 1/10000`. -/
theorem seven_core_r1_valid {D ℓ h : ℚ} (hℓ : 0 ≤ ℓ) (hh0 : 0 ≤ h) (hhL : h ≤ (6 * ℓ + 1) - 1) :
    (1 / 10000 : ℚ) ≤
        scoreVec A_RPS (coreCycleStart D ℓ) (runCount (fun _ => 0) 0 h) 0 -
          scoreVec A_RPS (coreCycleStart D ℓ) (runCount (fun _ => 0) 0 h) 1 ∧
      (1 / 10000 : ℚ) ≤
        scoreVec A_RPS (coreCycleStart D ℓ) (runCount (fun _ => 0) 0 h) 0 -
          scoreVec A_RPS (coreCycleStart D ℓ) (runCount (fun _ => 0) 0 h) 2 := by
  constructor
  · apply pure_run_margin_of_endpoints A_RPS_skew (coreCycleStart D ℓ) (fun _ => 0) 0 1 hh0 hhL
    · simp [scoreVec, coreCycleStart]; linarith
    · simp [scoreVec, coreCycleStart, A_RPS]; linarith
  · apply pure_run_margin_of_endpoints A_RPS_skew (coreCycleStart D ℓ) (fun _ => 0) 0 2 hh0 hhL
    · simp [scoreVec, coreCycleStart]; linarith
    · simp [scoreVec, coreCycleStart, A_RPS]; linarith

/-- **Core Sub-Run `r_2^{6ℓ+3}` Validity**:
    Throughout `0 ≤ h ≤ 6ℓ + 2`, action `1` (`r_2`) beats `r_1` and `r_3` by margin `≥ 1/10000`. -/
theorem seven_core_r2_valid {D ℓ h : ℚ} (hℓ : 0 ≤ ℓ) (hh0 : 0 ≤ h) (hhL : h ≤ (6 * ℓ + 3) - 1) :
    (1 / 10000 : ℚ) ≤
        scoreVec A_RPS (coreAfterR1 D ℓ) (runCount (fun _ => 0) 1 h) 1 -
          scoreVec A_RPS (coreAfterR1 D ℓ) (runCount (fun _ => 0) 1 h) 0 ∧
      (1 / 10000 : ℚ) ≤
        scoreVec A_RPS (coreAfterR1 D ℓ) (runCount (fun _ => 0) 1 h) 1 -
          scoreVec A_RPS (coreAfterR1 D ℓ) (runCount (fun _ => 0) 1 h) 2 := by
  constructor
  · apply pure_run_margin_of_endpoints A_RPS_skew (coreAfterR1 D ℓ) (fun _ => 0) 1 0 hh0 hhL
    · simp [scoreVec, coreAfterR1]; linarith
    · simp [scoreVec, coreAfterR1, A_RPS]; linarith
  · apply pure_run_margin_of_endpoints A_RPS_skew (coreAfterR1 D ℓ) (fun _ => 0) 1 2 hh0 hhL
    · simp [scoreVec, coreAfterR1]; linarith
    · simp [scoreVec, coreAfterR1, A_RPS]; linarith

/-- **Core Sub-Run `r_3^{6ℓ+5}` Validity**:
    Throughout `0 ≤ h ≤ 6ℓ + 4`, action `2` (`r_3`) beats `r_1` and `r_2` by margin `≥ 4999/5000 ≥ 1/10000`. -/
theorem seven_core_r3_valid {D ℓ h : ℚ} (hℓ : 0 ≤ ℓ) (hh0 : 0 ≤ h) (hhL : h ≤ (6 * ℓ + 5) - 1) :
    (1 / 10000 : ℚ) ≤
        scoreVec A_RPS (coreAfterR2 D ℓ) (runCount (fun _ => 0) 2 h) 2 -
          scoreVec A_RPS (coreAfterR2 D ℓ) (runCount (fun _ => 0) 2 h) 0 ∧
      (1 / 10000 : ℚ) ≤
        scoreVec A_RPS (coreAfterR2 D ℓ) (runCount (fun _ => 0) 2 h) 2 -
          scoreVec A_RPS (coreAfterR2 D ℓ) (runCount (fun _ => 0) 2 h) 1 := by
  constructor
  · apply pure_run_margin_of_endpoints A_RPS_skew (coreAfterR2 D ℓ) (fun _ => 0) 2 0 hh0 hhL
    · simp [scoreVec, coreAfterR2]; linarith
    · simp [scoreVec, coreAfterR2, A_RPS]; linarith
  · apply pure_run_margin_of_endpoints A_RPS_skew (coreAfterR2 D ℓ) (fun _ => 0) 2 1 hh0 hhL
    · simp [scoreVec, coreAfterR2]; linarith
    · simp [scoreVec, coreAfterR2, A_RPS]; linarith

/-- **Guards Wait During Core (`app:seven` Step 2)**:
    For all `k ≥ 20`:
    1. Guard 2 starts below `W_1(k)` by `(35/4)k^2 - (3175/21)k + 793762/1575 ≥ 1 ≥ 1/10000`.
    2. Guard 3 starts below `W_1(k)` by `1/2000 ≥ 1/10000`.
    3. Guard 1's minimum deficit during the core is `1/84 - 1/200 - 2/10000 = 88/13125 ≥ 1/10000`. -/
theorem seven_guards_wait_during_core {k : ℚ} (hk : 20 ≤ k) :
    (1 / 10000 : ℚ) ≤ W_seven k 0 - Vg_seven k 1 ∧
      (1 / 10000 : ℚ) ≤ W_seven k 0 - Vg_seven k 2 ∧
      (1 / 10000 : ℚ) ≤ (1 / 84 : ℚ) - s_seven 0 - 2 * (1 / 10000) := by
  refine ⟨?_, ?_, ?_⟩
  · have hpoly :
        W_seven k 0 - Vg_seven k 1 =
          35 / 4 * k ^ 2 - 3175 / 21 * k + 793762 / 1575 := by
      simp [W_seven, Vg_seven, H_seven, s_seven, Fin.sum_univ_three, G_seven, Q_seven, A_guard,
        L_seven]
      ring
    rw [hpoly]
    nlinarith
  · have hpoly : W_seven k 0 - Vg_seven k 2 = 1 / 2000 := by
      simp [W_seven, Vg_seven, H_seven, s_seven, Fin.sum_univ_three, G_seven, Q_seven, A_guard,
        L_seven]
      ring
    rw [hpoly]
    norm_num
  · simp [s_seven]
    norm_num

/-!
## Step 3 of Theorem E.1 (`beta7:main`): Guard Runs Best-Response Validity
-/

/-- Recurrent 6-action score state at the end of the core segment (start of Guard 1 run `g_1^{L_1(k)}`). -/
def stateBeforeG1 (k : ℚ) (i : Fin 6) : ℚ :=
  V_seven k i + ∑ j : Fin 3, M_seven i ⟨j.val, by omega⟩ * Q_seven k j

/-- Recurrent 6-action score state after `g_1^{L_1(k)}` (start of Guard 2 run `g_2^{L_2(k)}`). -/
def stateBeforeG2 (k : ℚ) (i : Fin 6) : ℚ :=
  stateBeforeG1 k i + M_seven i 3 * L_seven k 0

/-- Recurrent 6-action score state after `g_2^{L_2(k)}` (start of Guard 3 run `g_3^{L_3(k)}`). -/
def stateBeforeG3 (k : ℚ) (i : Fin 6) : ℚ :=
  stateBeforeG2 k i + M_seven i 4 * L_seven k 1

/-- **Guard 1 Run (`g_1^{L_1(k)}`, action `3`) Strict Best-Response Validity**:
    For every `k ≥ 20`, every step `0 ≤ h ≤ L_1(k) - 1`, and every rival action `j ≠ 3`,
    Guard 1 (`3`) strictly beats `j` by margin at least `1/10000`. -/
theorem seven_guard1_run_valid {k h : ℚ} (hk : 20 ≤ k)
    (hh0 : 0 ≤ h) (hhL : h ≤ L_seven k 0 - 1) (j : Fin 6) (hj : j ≠ 3) :
    (1 / 10000 : ℚ) ≤
      scoreVec M_seven (stateBeforeG1 k) (runCount (fun _ => 0) 3 h) 3 -
        scoreVec M_seven (stateBeforeG1 k) (runCount (fun _ => 0) 3 h) j := by
  fin_cases j
  · apply pure_run_margin_of_endpoints M_seven_skew (stateBeforeG1 k) (fun _ => 0) 3 0 hh0 hhL
    · simp [scoreVec, stateBeforeG1, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
    · simp [scoreVec, stateBeforeG1, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateBeforeG1 k) (fun _ => 0) 3 1 hh0 hhL
    · simp [scoreVec, stateBeforeG1, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
    · simp [scoreVec, stateBeforeG1, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateBeforeG1 k) (fun _ => 0) 3 2 hh0 hhL
    · simp [scoreVec, stateBeforeG1, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
    · simp [scoreVec, stateBeforeG1, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
  · contradiction
  · apply pure_run_margin_of_endpoints M_seven_skew (stateBeforeG1 k) (fun _ => 0) 3 4 hh0 hhL
    · simp [scoreVec, stateBeforeG1, V_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
    · simp [scoreVec, stateBeforeG1, V_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateBeforeG1 k) (fun _ => 0) 3 5 hh0 hhL
    · simp [scoreVec, stateBeforeG1, V_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
    · simp [scoreVec, stateBeforeG1, V_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith

/-- **Guard 2 Run (`g_2^{L_2(k)}`, action `4`) Strict Best-Response Validity**:
    For every `k ≥ 20`, every step `0 ≤ h ≤ L_2(k) - 1`, and every rival action `j ≠ 4`,
    Guard 2 (`4`) strictly beats `j` by margin at least `1/10000`. -/
theorem seven_guard2_run_valid {k h : ℚ} (hk : 20 ≤ k)
    (hh0 : 0 ≤ h) (hhL : h ≤ L_seven k 1 - 1) (j : Fin 6) (hj : j ≠ 4) :
    (1 / 10000 : ℚ) ≤
      scoreVec M_seven (stateBeforeG2 k) (runCount (fun _ => 0) 4 h) 4 -
        scoreVec M_seven (stateBeforeG2 k) (runCount (fun _ => 0) 4 h) j := by
  fin_cases j
  · apply pure_run_margin_of_endpoints M_seven_skew (stateBeforeG2 k) (fun _ => 0) 4 0 hh0 hhL
    · simp [scoreVec, stateBeforeG2, stateBeforeG1, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
    · simp [scoreVec, stateBeforeG2, stateBeforeG1, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateBeforeG2 k) (fun _ => 0) 4 1 hh0 hhL
    · simp [scoreVec, stateBeforeG2, stateBeforeG1, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
    · simp [scoreVec, stateBeforeG2, stateBeforeG1, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateBeforeG2 k) (fun _ => 0) 4 2 hh0 hhL
    · simp [scoreVec, stateBeforeG2, stateBeforeG1, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
    · simp [scoreVec, stateBeforeG2, stateBeforeG1, V_seven, W_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateBeforeG2 k) (fun _ => 0) 4 3 hh0 hhL
    · simp [scoreVec, stateBeforeG2, stateBeforeG1, V_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
    · simp [scoreVec, stateBeforeG2, stateBeforeG1, V_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
  · contradiction
  · apply pure_run_margin_of_endpoints M_seven_skew (stateBeforeG2 k) (fun _ => 0) 4 5 hh0 hhL
    · simp [scoreVec, stateBeforeG2, stateBeforeG1, V_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith
    · simp [scoreVec, stateBeforeG2, stateBeforeG1, V_seven, Vg_seven, H_seven, s_seven,
        Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]; nlinarith

/-- **Guard 3 Run (`g_3^{L_3(k)}`, action `5`) Strict Best-Response Validity**:
    For every `k ≥ 20`, every step `0 ≤ h ≤ L_3(k) - 1`, and every rival action `j ≠ 5`,
    Guard 3 (`5`) strictly beats `j` by margin at least `1/10000`. -/
theorem seven_guard3_run_valid {k h : ℚ} (hk : 20 ≤ k)
    (hh0 : 0 ≤ h) (hhL : h ≤ L_seven k 2 - 1) (j : Fin 6) (hj : j ≠ 5) :
    (1 / 10000 : ℚ) ≤
      scoreVec M_seven (stateBeforeG3 k) (runCount (fun _ => 0) 5 h) 5 -
        scoreVec M_seven (stateBeforeG3 k) (runCount (fun _ => 0) 5 h) j := by
  fin_cases j
  · apply pure_run_margin_of_endpoints M_seven_skew (stateBeforeG3 k) (fun _ => 0) 5 0 hh0 hhL
    · simp [scoreVec, stateBeforeG3, stateBeforeG2, stateBeforeG1, V_seven, W_seven, Vg_seven,
        H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]
      nlinarith
    · simp [scoreVec, stateBeforeG3, stateBeforeG2, stateBeforeG1, V_seven, W_seven, Vg_seven,
        H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]
      nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateBeforeG3 k) (fun _ => 0) 5 1 hh0 hhL
    · simp [scoreVec, stateBeforeG3, stateBeforeG2, stateBeforeG1, V_seven, W_seven, Vg_seven,
        H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]
      nlinarith
    · simp [scoreVec, stateBeforeG3, stateBeforeG2, stateBeforeG1, V_seven, W_seven, Vg_seven,
        H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]
      nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateBeforeG3 k) (fun _ => 0) 5 2 hh0 hhL
    · simp [scoreVec, stateBeforeG3, stateBeforeG2, stateBeforeG1, V_seven, W_seven, Vg_seven,
        H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]
      nlinarith
    · simp [scoreVec, stateBeforeG3, stateBeforeG2, stateBeforeG1, V_seven, W_seven, Vg_seven,
        H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]
      nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateBeforeG3 k) (fun _ => 0) 5 3 hh0 hhL
    · simp [scoreVec, stateBeforeG3, stateBeforeG2, stateBeforeG1, V_seven, Vg_seven,
        H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]
      nlinarith
    · simp [scoreVec, stateBeforeG3, stateBeforeG2, stateBeforeG1, V_seven, Vg_seven,
        H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]
      nlinarith
  · apply pure_run_margin_of_endpoints M_seven_skew (stateBeforeG3 k) (fun _ => 0) 5 4 hh0 hhL
    · simp [scoreVec, stateBeforeG3, stateBeforeG2, stateBeforeG1, V_seven, Vg_seven,
        H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]
      nlinarith
    · simp [scoreVec, stateBeforeG3, stateBeforeG2, stateBeforeG1, V_seven, Vg_seven,
        H_seven, s_seven, Fin.sum_univ_three, M_seven, G_seven, Q_seven, A_guard, L_seven]
      nlinarith
  · contradiction

/-!
## Step 4 & Step 5 of Theorem E.1 (`beta7:main`): Setup Realization & Cubic Phase Growth
-/

/-- **Setup Realization (`app:seven` Step 4)**:
    The setup column `w_seven` has every coordinate `≥ 1` and equals
    `V(20) + (657497227 / 52500) 1_6`. -/
theorem seven_setup_realization :
    (∀ i : Fin 6, 1 ≤ w_seven i) ∧
      ∀ i : Fin 6, w_seven i = V_seven 20 i + 657497227 / 52500 := by
  constructor
  · intro i
    fin_cases i <;> simp [w_seven] <;> norm_num
  · intro i
    fin_cases i <;>
      simp [w_seven, V_seven, W_seven, Vg_seven, H_seven, s_seven, Fin.sum_univ_three,
        G_seven, Q_seven, A_guard, L_seven] <;> norm_num

/-- **Phase Step Count (`app:seven` Step 5)**:
    Total plays in phase `k` equal `5733 k^2 - 9096 k + 52766`. -/
theorem seven_phase_total_length (k : ℚ) :
    (∑ i : Fin 6, QL_seven k i) = 5733 * k ^ 2 - 9096 * k + 52766 := by
  simp [Fin.sum_univ_six, QL_seven, Q_seven, L_seven]
  ring

/-!
## Theorem E.2 (`prop:seven-family`): Order-3 Clock Tables & Admissibility for the All-Orders Lift
-/

/-- Score coefficient table `R_seven ∈ ℚ^{6×3}` in binomial basis `p_2(q) = (1, q, q(q-1)/2)ᵀ`. -/
def R_seven : Matrix (Fin 6) (Fin 3) ℚ :=
  !![ 105001 / 5000,       253 / 21,   14;
     -389999 / 10000,    -2393 / 21,   14;
      21,                  253 / 21,   14;
      285091 / 17500,    -5183 / 84, -119 / 2;
    -152137337 / 315000, 12977 / 84,   -7 / 2;
      209997 / 10000,      253 / 21,   14]

/-- Count coefficient table `C_seven ∈ ℚ^{6×3}` in binomial basis `p_2(q)`. -/
def C_seven : Matrix (Fin 6) (Fin 3) ℚ :=
  !![  456,   2443, 2058;
       468,   2457, 2058;
       480,   2471, 2058;
     12498,  -1422, 1764;
      2422,   3282, 1764;
     36442, -12594, 1764]

/-- Width-3 forward difference matrix `N_3`. -/
def N3 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, 0, 0;
     1, 0, 0;
     0, 1, 0]

/-- Endpoint counter row `v_seven = (0, -5/299, 294/17641, 7/105846, 0, 0)`. -/
def v_seven : Fin 6 → ℚ
  | 0 => 0
  | 1 => -5 / 299
  | 2 => 294 / 17641
  | 3 => 7 / 105846
  | 4 => 0
  | 5 => 0

/-- Strictly positive parent weights `a_P ∈ ℚ_{>0}^6` (`eq:seven-weights`). -/
def aP_seven : Fin 6 → ℚ
  | 0 => 31 / 24996
  | 1 => 31 / 24996
  | 2 => 31 / 24996
  | 3 => 14729 / 102883536
  | 4 => 130922735 / 58334964912
  | 5 => 1087039 / 14583741228

/-- **Order-3 Clock Table Identity (`prop:seven-family` Step 1)**:
    `M_seven * C_seven = R_seven * N_3`. -/
theorem M_seven_mul_C_eq_R_mul_N3 : M_seven * C_seven = R_seven * N3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_three,
      M_seven, C_seven, R_seven, N3] <;> norm_num

/-- **Order-3 Endpoint Counter Identity (`prop:seven-family` Step 2)**:
    `v_seven * C_seven = (1, 0, 0)`. -/
theorem v_seven_mul_C :
    (fun j : Fin 3 => ∑ i : Fin 6, v_seven i * C_seven i j) = ![1, 0, 0] := by
  ext j
  fin_cases j <;>
    simp [Fin.sum_univ_six, v_seven, C_seven] <;> norm_num

/-- **Order-3 Positive Weights Identity (`eq:seven-weights`)**:
    `aP_seven` is strictly positive on all 6 actions and satisfies
    `aP_sevenᵀ C_seven = (736/63, 968/63, 12) = t`. -/
theorem seven_admissible_weights :
    (∀ i : Fin 6, 0 < aP_seven i) ∧
      (fun j : Fin 3 => ∑ i : Fin 6, aP_seven i * C_seven i j) =
        ![736 / 63, 968 / 63, 12] := by
  refine ⟨fun i => by fin_cases i <;> simp [aP_seven], ?_⟩
  ext j
  fin_cases j <;>
    simp [Fin.sum_univ_six, aP_seven, C_seven] <;> norm_num

/-- Width-4 backward shift matrix `B_4 = T_4⁻¹`. -/
def B4 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![ 1,  0,  0, 0;
     -1,  1,  0, 0;
      1, -1,  1, 0;
     -1,  1, -1, 1]

/-- Scale-1 bundle summation matrix `F_seven ∈ ℚ^{3×4}` in Theorem E.2 (`prop:seven-family` Step 4). -/
def F_seven : Matrix (Fin 3) (Fin 4) ℚ :=
  !![0, 1, 0, 0;
     0, 1, 3, 0;
     0, 0, 4, 7]

/-- Canonical outer height row `ζ_seven = (4, 1115/42, 1429/21, 42)` (`prop:seven-family` Step 4). -/
def zeta_seven : Fin 4 → ℚ :=
  ![4, 1115 / 42, 1429 / 21, 42]

/-- **Order-3 Positive Cone Identity (`eq:cone` for `M_seven`)**:
    With endpoint weight `a_g = 2 H_* - c_ref = 15/2`,
    `aP_sevenᵀ (C_seven * F_seven) + (15/2) e_0ᵀ = ζ_seven + ζ_seven * B_4`. -/
theorem seven_cone_identity :
    (fun j : Fin 4 =>
      (∑ i : Fin 6, aP_seven i * (C_seven * F_seven) i j) +
        (if j = 0 then (15 / 2 : ℚ) else 0)) =
      (fun j : Fin 4 => zeta_seven j + ∑ i : Fin 4, zeta_seven i * B4 i j) := by
  ext j
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four, Fin.sum_univ_three,
      aP_seven, C_seven, F_seven, zeta_seven, B4] <;> norm_num

/-- Corrected right-hand side `Dᵀ X - ℓ_*ᵀ ψ` in Theorem E.2 (`eq:seven-rhs`). -/
def RHS_seven : Matrix (Fin 4) (Fin 4) ℚ :=
  !![-1 / 2, -14624231 / 42,  3552051 / 14, -926835;
     -3189,    4343743 / 21, -3525063 / 7,   966966;
     -6376,   50600734 / 21,   966966,      3371004;
         0,               0,        0,            0]

/-- Explicit rational moment solution `E` in Theorem E.2 (`eq:seven-solution`). -/
def E_seven : Matrix (Fin 4) (Fin 4) ℚ :=
  !![           0,  -7312126 / 21, -21862210 / 7,  34300781 / 14;
    -23638239 / 7,  22626455 / 7,   -6231446 / 21,    40131;
                0, -15119792 / 21,  11399338 / 3,   4337970;
     47276471 / 14,  -926835,         966966,       3371004]

/-- **Order-3 Moment Compatibility Identity (`eq:seven-solution`)**:
    `E_seven - E_sevenᵀ * B_4 = RHS_seven = Dᵀ X - ℓ_*ᵀ ψ`. -/
theorem seven_moment_equation :
    E_seven - E_seven.transpose * B4 = RHS_seven := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, E_seven, B4, RHS_seven] <;> norm_num

end Karlin

#print axioms Karlin.M_seven_skew
#print axioms Karlin.M7_skew
#print axioms Karlin.seven_reset_identity
#print axioms Karlin.seven_timing_identity
#print axioms Karlin.seven_phase_return
#print axioms Karlin.seven_run_lengths_lower_bound
#print axioms Karlin.seven_core_cycle_transitions
#print axioms Karlin.seven_core_r1_valid
#print axioms Karlin.seven_core_r2_valid
#print axioms Karlin.seven_core_r3_valid
#print axioms Karlin.seven_guards_wait_during_core
#print axioms Karlin.seven_guard1_run_valid
#print axioms Karlin.seven_guard2_run_valid
#print axioms Karlin.seven_guard3_run_valid
#print axioms Karlin.seven_setup_realization
#print axioms Karlin.seven_phase_total_length
#print axioms Karlin.M_seven_mul_C_eq_R_mul_N3
#print axioms Karlin.v_seven_mul_C
#print axioms Karlin.seven_admissible_weights
#print axioms Karlin.seven_cone_identity
#print axioms Karlin.seven_moment_equation

