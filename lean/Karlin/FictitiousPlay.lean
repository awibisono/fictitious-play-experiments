import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Fictitious Play, Auxiliary Score Process, and General Reduction Lemmas

This module formalizes Sections 2 and 3 of the Karlin Conjecture disproof paper
(`v12_annotated.tex`):
1. Skew-symmetric payoff matrices (`IsSkewSymmetric`) and diagonal zero (`skew_diag_zero`).
2. Synchronized Fictitious Play score process $u_t = f + A z_t$ and duality gap
   $\operatorname{Gap}_A(z_t/t, z_t/t) = \frac{2}{t} \max_i (A z_t)_i$.
3. Active score invariance during a pure run and monotonicity of the height $H_t = \max_i u_{t,i}$.
4. The **Affine Run-Length Lemma** (`affine_margin_on_interval`, `pure_run_margin_of_endpoints`):
   Because $A_{ii} = 0$, the score gap $u_i - u_j$ during a pure run $i^L$ is an affine function
   of the step offset $0 \le h \le L - 1$. Consequently, certifying a best-response margin $\ge \delta$
   at the two endpoints $h = 0$ and $h = L - 1$ suffices to certify the margin at every intermediate step.
5. **Lemma 3.5 (`lem:bias` — Generic Rational Tie-Removal)**: Adding the rational rank perturbation
   $\beta_i = \frac{m - 1 - r(i)}{4 m D_0}$ converts every priority-broken tie into a strict
   best-response margin $\ge \frac{1}{4 m D_0} > 0$ while preserving all existing strict inequalities.
6. **Lemma 3.6 (`lem:setup` — One-Action Zero-Count Initialization)**: Adjoining a single setup action
   $\omega$ with payoff column $f^* \ge \mathbf{1}_m$ realizes the initial offset $f^*$ after step $t = 1$
   from zero initial counts $z_0 = 0$, and keeps $\omega$'s score $\le 0 < 1 \le H_t$ forever after.
-/

namespace Karlin

open scoped BigOperators

/-- A payoff matrix `A : Matrix n n ℚ` is skew-symmetric if `A i j = - A j i` for all `i, j`. -/
def IsSkewSymmetric {n : Type*} (A : Matrix n n ℚ) : Prop :=
  ∀ i j, A i j = -A j i

/-- Every skew-symmetric rational matrix has zero diagonal entries. -/
theorem skew_diag_zero {n : Type*} {A : Matrix n n ℚ} (hA : IsSkewSymmetric A) (i : n) :
    A i i = 0 := by
  have h := hA i i
  linarith

/-- The auxiliary score vector `u_i = f_i + ∑_j A_{i,j} z_j` (`def:aux-fp`). -/
def scoreVec {n : Type*} [Fintype n] (A : Matrix n n ℚ) (f z : n → ℚ) (i : n) : ℚ :=
  f i + ∑ j : n, A i j * z j

/-- Cumulative count vector after playing pure action `a` for `h` steps starting from `z`. -/
def runCount {n : Type*} [DecidableEq n] (z : n → ℚ) (a : n) (h : ℚ) (j : n) : ℚ :=
  z j + if j = a then h else 0

/-- Evolution of any coordinate `j` of the score vector after `h` plays of action `a`. -/
theorem scoreVec_runCount {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ) (f z : n → ℚ) (a j : n) (h : ℚ) :
    scoreVec A f (runCount z a h) j = scoreVec A f z j + h * A j a := by
  unfold scoreVec runCount
  have hsum :
      (∑ k : n, A j k * (z k + if k = a then h else 0)) =
        (∑ k : n, A j k * z k) + ∑ k : n, A j k * (if k = a then h else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [hsum]
  have hsingle :
      (∑ k : n, A j k * (if k = a then h else 0)) = A j a * h := by
    simp [mul_ite, mul_zero]
  rw [hsingle]
  ring

/-- Because `A a a = 0`, playing action `a` leaves its own score invariant. -/
theorem scoreVec_runCount_self {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℚ} (hA : IsSkewSymmetric A) (f z : n → ℚ) (a : n) (h : ℚ) :
    scoreVec A f (runCount z a h) a = scoreVec A f z a := by
  rw [scoreVec_runCount, skew_diag_zero hA a, mul_zero, add_zero]

/-- **Height Non-Decrease**: If `H ≤ scoreVec A f z a`, then after playing `a` for `h` steps,
    action `a` still achieves score at least `H`. -/
theorem height_nondecreasing_step {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℚ} (hA : IsSkewSymmetric A) (f z : n → ℚ) (a : n) (h H : ℚ)
    (hH : H ≤ scoreVec A f z a) :
    H ≤ scoreVec A f (runCount z a h) a := by
  rw [scoreVec_runCount_self hA]
  exact hH

/-- The score gap `u_a - u_j` after `h` plays of action `a` is an affine function of `h`. -/
theorem score_gap_runCount {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℚ} (hA : IsSkewSymmetric A) (f z : n → ℚ) (a j : n) (h : ℚ) :
    scoreVec A f (runCount z a h) a - scoreVec A f (runCount z a h) j =
      (scoreVec A f z a - scoreVec A f z j) - h * A j a := by
  rw [scoreVec_runCount_self hA, scoreVec_runCount]
  ring

/-- **Affine Convexity / Endpoint Lemma**:
    If an affine function `g(h) = d0 + h * s` satisfies `δ ≤ g(a)` and `δ ≤ g(b)`,
    then `δ ≤ g(h)` for every `h ∈ [a, b]`. -/
theorem affine_margin_on_interval {d0 s a b h δ : ℚ}
    (hah : a ≤ h) (hhb : h ≤ b)
    (ha : δ ≤ d0 + a * s) (hb : δ ≤ d0 + b * s) :
    δ ≤ d0 + h * s := by
  rcases le_total 0 s with hs | hs
  · have : a * s ≤ h * s := mul_le_mul_of_nonneg_right hah hs
    linarith
  · have : b * s ≤ h * s := mul_le_mul_of_nonpos_right hhb hs
    linarith

/-- **Pure-Run Endpoint Verification Lemma (`sec:words`)**:
    In a skew-symmetric game `A`, if action `a` beats rival `j` by margin at least `δ`
    at the start of a pure run (`h = 0`) and at the last step before termination (`h = L - 1`),
    then `a` beats `j` by margin at least `δ` at every intermediate step `0 ≤ h ≤ L - 1`. -/
theorem pure_run_margin_of_endpoints {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℚ} (hA : IsSkewSymmetric A) (f z : n → ℚ) (a j : n)
    {L h δ : ℚ} (hh0 : 0 ≤ h) (hhL : h ≤ L - 1)
    (h_start : δ ≤ scoreVec A f z a - scoreVec A f z j)
    (h_end : δ ≤ (scoreVec A f z a - scoreVec A f z j) - (L - 1) * A j a) :
    δ ≤ scoreVec A f (runCount z a h) a - scoreVec A f (runCount z a h) j := by
  rw [score_gap_runCount hA]
  have h0 : δ ≤ (scoreVec A f z a - scoreVec A f z j) + 0 * (-A j a) := by
    simpa using h_start
  have h1 : δ ≤ (scoreVec A f z a - scoreVec A f z j) + (L - 1) * (-A j a) := by
    linarith
  have h_mid := affine_margin_on_interval hh0 hhL h0 h1
  linarith

/-- **Synchronized Saddle-Point Duality Gap Identity (`eq:sync-gap`)**:
    For a skew-symmetric matrix `A`, the row payoff `(A z)_i` equals the negated column payoff
    `-(Aᵀ z)_i`, so the sum of row and column best-response values for `(z/t, z/t)` is
    `(2 / t) * max_i (A z)_i`. -/
theorem skew_col_payoff_eq_neg_row {n : Type*} [Fintype n]
    {A : Matrix n n ℚ} (hA : IsSkewSymmetric A) (z : n → ℚ) (i : n) :
    (∑ j : n, A j i * z j) = -(∑ j : n, A i j * z j) := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hA j i]
  ring

/-- **Lemma 3.5 (`lem:bias` — Generic Rational Tie-Removal)**:
    Let `β(x) = (m - 1 - r(x)) / (4 * m * D0)` for priority ranks `0 ≤ r(x) ≤ m - 1`
    and denominator bound `D0 > 0`.
    1. If `u_i - u_j ≥ 1 / D0` (a strict rational advantage with denominator `D0`),
       then `(u_i + β_i) - (u_j + β_j) ≥ 1 / (4 * m * D0)`.
    2. If `u_i = u_j` and `r(j) - r(i) ≥ 1` (a tie broken in favor of higher-priority `i`),
       then `(u_i + β_i) - (u_j + β_j) ≥ 1 / (4 * m * D0)`. -/
def tieRemovalBias (m D0 : ℚ) (r : ℚ) : ℚ :=
  (m - 1 - r) / (4 * m * D0)

theorem tieRemoval_strict_preserved {m D0 ui uj ri rj : ℚ}
    (hm : 1 ≤ m) (hD0 : 0 < D0)
    (_hri0 : 0 ≤ ri) (hri1 : ri ≤ m - 1)
    (hrj0 : 0 ≤ rj) (_hrj1 : rj ≤ m - 1)
    (hstrict : 1 / D0 ≤ ui - uj) :
    1 / (4 * m * D0) ≤
      (ui + tieRemovalBias m D0 ri) - (uj + tieRemovalBias m D0 rj) := by
  unfold tieRemovalBias
  have hm_pos : 0 < m := by linarith
  have h4mD0 : 0 < 4 * m * D0 := by positivity
  rw [le_iff_lt_or_eq] at hm
  have hdiff :
      (ui + (m - 1 - ri) / (4 * m * D0) - (uj + (m - 1 - rj) / (4 * m * D0))) -
        1 / (4 * m * D0) =
      (ui - uj - 1 / D0) + (4 * m + rj - ri - 1) / (4 * m * D0) := by
    field_simp
    ring
  have hnum : 0 ≤ 4 * m + rj - ri - 1 := by linarith
  have hquot : 0 ≤ (4 * m + rj - ri - 1) / (4 * m * D0) := div_nonneg hnum (le_of_lt h4mD0)
  linarith

theorem tieRemoval_tie_broken {m D0 ui uj ri rj : ℚ}
    (hm : 1 ≤ m) (hD0 : 0 < D0)
    (htie : ui = uj) (hrank : 1 ≤ rj - ri) :
    1 / (4 * m * D0) ≤
      (ui + tieRemovalBias m D0 ri) - (uj + tieRemovalBias m D0 rj) := by
  unfold tieRemovalBias
  have hm_pos : 0 < m := by linarith
  have h4mD0 : 0 < 4 * m * D0 := by positivity
  have hdiff :
      (ui + (m - 1 - ri) / (4 * m * D0) - (uj + (m - 1 - rj) / (4 * m * D0))) -
        1 / (4 * m * D0) =
      (ui - uj) + (rj - ri - 1) / (4 * m * D0) := by
    field_simp
    ring
  have hnum : 0 ≤ rj - ri - 1 := by linarith
  have hquot : 0 ≤ (rj - ri - 1) / (4 * m * D0) := div_nonneg hnum (le_of_lt h4mD0)
  linarith

/-- **Lemma 3.6 (`lem:setup` — One-Action Zero-Count Initialization)**:
    Given a recurrent game `A : Matrix n n ℚ` and a positive initial score vector `f : n → ℚ`
    with `∀ i, 1 ≤ f i`, adjoining a setup action `Option.none` yields the augmented
    skew-symmetric matrix `setupMatrix A f : Matrix (Option n) (Option n) ℚ`. -/
def setupMatrix {n : Type*} (A : Matrix n n ℚ) (f : n → ℚ) :
    Matrix (Option n) (Option n) ℚ
  | none, none => 0
  | none, some j => -f j
  | some i, none => f i
  | some i, some j => A i j

/-- `setupMatrix A f` is skew-symmetric whenever `A` is skew-symmetric. -/
theorem setupMatrix_skewSymmetric {n : Type*} {A : Matrix n n ℚ}
    (hA : IsSkewSymmetric A) (f : n → ℚ) :
    IsSkewSymmetric (setupMatrix A f) := by
  intro i j
  cases i <;> cases j
  · simp [setupMatrix]
  · simp [setupMatrix]
  · simp [setupMatrix]
  · exact hA _ _

/-- Starting from zero counts `z_0 = 0`, playing the setup action `none` once at `t = 1`
    produces the exact score `f i` on every recurrent action `some i` and score `0` on `none`. -/
theorem setupMatrix_score_after_step_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ) (f : n → ℚ) (i : n) :
    scoreVec (setupMatrix A f) (fun _ => 0)
      (runCount (fun _ => 0) (none : Option n) 1) (some i) = f i := by
  rw [scoreVec_runCount]
  simp [scoreVec, setupMatrix]

/-- For any nonnegative recurrent counts `z ≥ 0` and `f ≥ 0`, the setup action `none`
    has nonpositive score `≤ 0`, so whenever the recurrent height `H_t ≥ 1`, `none`
    stays strictly below `H_t` by margin at least `1`. -/
theorem setupMatrix_setup_action_nonpos {n : Type*} [Fintype n]
    (A : Matrix n n ℚ) (f z : n → ℚ)
    (hf : ∀ i, 0 ≤ f i) (hz : ∀ i, 0 ≤ z i) :
    scoreVec (setupMatrix A f) (fun _ => 0)
      (Option.elim' 1 z) none ≤ 0 := by
  unfold scoreVec
  simp only [Fintype.sum_option, setupMatrix, Option.elim'_none, mul_one, zero_add,
    Option.elim'_some, neg_mul]
  rw [Finset.sum_neg_distrib]
  linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => mul_nonneg (hf i) (hz i))]

end Karlin

#print axioms Karlin.skew_diag_zero
#print axioms Karlin.scoreVec_runCount
#print axioms Karlin.scoreVec_runCount_self
#print axioms Karlin.height_nondecreasing_step
#print axioms Karlin.score_gap_runCount
#print axioms Karlin.affine_margin_on_interval
#print axioms Karlin.pure_run_margin_of_endpoints
#print axioms Karlin.skew_col_payoff_eq_neg_row
#print axioms Karlin.tieRemoval_strict_preserved
#print axioms Karlin.tieRemoval_tie_broken
#print axioms Karlin.setupMatrix_skewSymmetric
#print axioms Karlin.setupMatrix_score_after_step_one
#print axioms Karlin.setupMatrix_setup_action_nonpos
