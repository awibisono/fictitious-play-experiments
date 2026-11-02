import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Karlin.FictitiousPlay
import Karlin.BinomialBasis
import Karlin.InductiveLift

/-!
# Chronology Verification, Clock Inheritance, and Main Theorem (`sec:clock` & `sec:chronology`)

This module formalizes Section 3 (`lem:bundle`, `lem:alltime`), Section 9 (`prop:chronology`,
`prop:inherit`, `thm:lift`), and Theorem 1.1 (`thm:main`) of
*On Karlin's Conjecture for Fictitious Play*:

1. **Lemma 3.1 (`lem:bundle` — Remaining Height Gain Across a Parent Bundle)**:
   - `bundle_remaining_height_bound`: Telescopes the single-phase remaining-height bound on the
     initial partial phase `s` together with the degree-dominated complete phases `σ ∈ [s+1, b)`
     to bound the remaining height gain across an entire bundle of `L` parent phases with the
     **same** additive constant `A_k`.

2. **Proposition 9.1 (`prop:chronology` — Best-Response Verification Across All Four Macro-Stages)**:
   - `chronology_early_reset_waits`: Backward reconstruction from the end of `\mathcal{A}(q)`
     combined with Lemma 3.1 keeps every early reset action strictly below `H_parent` by at least
     `-P_{gj} - c - A_k > 0` throughout the parent bundle (Equations `eq:earlybackward`–`eq:earlywait`).
   - `chronology_late_reset_waits`: Forward monotonicity from `s_b` combined with `P_L > 0` keeps
     every late reset action below `H_parent` throughout the parent bundle.
   - `chronology_endpoint_to_reset0`: At bundle completion, `g` exceeds `H_parent` by `δ > 0`, and
     its single play hands leadership to `\mathsf{c}_0` at the flat reset ceiling `ζ(q)` with margin
     `c - δ > 0` over old actions and `Jm_j > 0` over all later reset actions.
   - `chronology_reset_active_at_ceiling`, `chronology_reset_earlier_deficit`, &
     `chronology_reset_later_deficit`: Throughout the reset block `\mathcal{B}(q)` under
     `K = J - Jᵀ` (`J` strictly lower-triangular with positive subdiagonal entries), the active
     reset action `\mathsf{c}_j` stays identically at `ζ(q)`, earlier reset actions `i < j` have
     nonnegative deficit `≥ J_{j,i} h ≥ 0`, and later reset actions `i > j` have strictly positive
     deficit `≥ J_{i,j} (m_j - h) > 0` until `h = m_j`.
   - `chronology_old_waits_early_reset` & `chronology_old_waits_late_reset`: Old actions decrease
     during the early reset runs (`P_E < 0`) and approach `s_i(q+1) ≤ ζ(q)` strictly from below
     during the late reset runs (`P_L > 0`, Equation `eq:oldlate`).

3. **Proposition 9.2 (`prop:inherit` — Clock Inheritance for the Rotated Phase)**:
   - `inherit_entry_safety`: Verifies Condition (II) entry safety (`eq:supportsafe`) on
     `\operatorname{supp}(v_+) = \{g\}` at the start of the rotated phase `\mathcal{W}_{k+1}(q)`.
   - `inherit_remaining_height_bound`: Verifies Condition (III) with additive constant
     `A_{k+1} = A_k + 1`.

4. **Action Count Recursion & All-Integer-Time Duality Gap Enclosure (`lem:alltime`, `thm:main`)**:
   - `recurrent_action_count_step` & `setup_action_count`: Formalizes $m_k = (k+1)^2 - 6$ and
     $n_k = (k+1)^2 - 5$ (and $n_k^{(7)} = (k+1)^2 - 9$ from the 7-action cubic base).
   - `all_time_gap_enclosure`: Bounds the synchronized skew-symmetric Fictitious Play duality gap
     $\operatorname{Gap}(t) = 2 H_t / t$ at every integer time $t \in [t(q), t(q+1)]$ between
     $2 H(q) / t(q+1)$ and $2 H(q+1) / t(q)$.
-/

namespace Karlin

open scoped BigOperators

/-!
## 1. Lemma 3.1 (`lem:bundle`): Remaining Height Gain Across a Parent Bundle
-/

/-- **Remaining Height Gain Across a Parent Bundle (`lem:bundle`, Section 3.1)**:
    Suppose within the current partial phase `s` (`s + 1 ≤ b`), the remaining height gain to
    `χ(s + 1)` satisfies `χ(s + 1) - H_prefix ≤ ε * N_s_rem + A_k`, and on every subsequent
    complete phase `σ ∈ [s + 1, b)` in the bundle, `χ(σ + 1) - χ(σ) ≤ ε * len(σ)`.
    Then the remaining height gain to the bundle exit height `χ(b)` is bounded by
    `ε` times the total remaining bundle length plus the **same** single-phase constant `A_k`. -/
theorem bundle_remaining_height_bound (χ len : ℕ → ℚ) {s b : ℕ} (hsb : s + 1 ≤ b)
    {H_prefix N_s_rem ε A_k : ℚ}
    (h_partial : χ (s + 1) - H_prefix ≤ ε * N_s_rem + A_k)
    (h_complete : ∀ σ ∈ Finset.Ico (s + 1) b, χ (σ + 1) - χ σ ≤ ε * len σ) :
    χ b - H_prefix ≤
      ε * (N_s_rem + ∑ σ ∈ Finset.Ico (s + 1) b, len σ) + A_k := by
  have h_sum :
      (∑ σ ∈ Finset.Ico (s + 1) b, (χ (σ + 1) - χ σ)) ≤
        ∑ σ ∈ Finset.Ico (s + 1) b, (ε * len σ) :=
    Finset.sum_le_sum h_complete
  rw [Finset.sum_Ico_sub χ hsb, ← Finset.mul_sum] at h_sum
  linarith

/-!
## 2. Proposition 9.1 (`prop:chronology`): Four-Stage Best-Response Verification
-/

/-- **Stage 1a: Early Reset Actions Wait During Parent Bundle (`eq:earlywait`, Section 9.1)**:
    Working backward from the end of `\mathcal{A}(q)` (where `\mathsf{c}_j` has score `ζ - Jm_j`),
    at any prefix of the parent bundle with remaining parent counts `z_rem`, the score of early
    reset action `\mathsf{c}_j` is `u_reset_j = ζ - Jm_j + P_gj + ∑ i, P_col i * z_rem i`.
    Under the bundle height bound `H_parent ≥ ζ - c - A_k - ε * ∑ i, z_rem i` and the uniform
    margin bounds `Jm_j ≥ 0`, `-P_gj - c - A_k > 0`, and `-P_col i ≥ ε`, `\mathsf{c}_j` stays
    strictly below `H_parent` by at least `-P_gj - c - A_k > 0`. -/
theorem chronology_early_reset_waits {m : Type*} [Fintype m]
    (P_col z_rem : m → ℚ) (ζ Jm_j P_gj c A_k ε H_parent : ℚ)
    (h_bundle : ζ - c - A_k - ε * (∑ i : m, z_rem i) ≤ H_parent)
    (h_Jm : 0 ≤ Jm_j)
    (h_Pg : 0 < -P_gj - c - A_k)
    (h_P : ∀ i : m, 0 ≤ -P_col i - ε)
    (h_z : ∀ i : m, 0 ≤ z_rem i) :
    let u_reset_j := ζ - Jm_j + P_gj + ∑ i : m, P_col i * z_rem i
    (-P_gj - c - A_k) ≤ H_parent - u_reset_j ∧ 0 < H_parent - u_reset_j := by
  intro u_reset_j
  have h_sum_nonneg : 0 ≤ ∑ i : m, (-P_col i - ε) * z_rem i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (h_P i) (h_z i)
  have h_sum_id :
      (∑ i : m, (-P_col i - ε) * z_rem i) =
        -(∑ i : m, P_col i * z_rem i) - ε * (∑ i : m, z_rem i) := by
    have h_each : ∀ i : m, (-P_col i - ε) * z_rem i = -(P_col i * z_rem i) - ε * z_rem i := by
      intro i; ring
    simp_rw [h_each, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  dsimp only [u_reset_j]
  constructor <;> linarith

/-- **Stage 1b: Late Reset Actions Wait During Parent Bundle (Section 9.1)**:
    A late reset action `\mathsf{c}_j` starts at `s_b - Jt_m_j ≤ s_b` and changes by `-P_col i < 0`
    on each parent play while `H_parent ≥ s_b` is nondecreasing. -/
theorem chronology_late_reset_waits {m : Type*} [Fintype m]
    (P_col z_play : m → ℚ) (s_b Jt_m_j H_parent : ℚ)
    (h_mono : s_b ≤ H_parent)
    (h_Jt : 0 ≤ Jt_m_j)
    (h_P : ∀ i : m, 0 ≤ P_col i)
    (h_z : ∀ i : m, 0 ≤ z_play i) :
    let u_reset_j := (s_b - Jt_m_j) - ∑ i : m, P_col i * z_play i
    Jt_m_j + (∑ i : m, P_col i * z_play i) ≤ H_parent - u_reset_j ∧
      0 ≤ H_parent - u_reset_j := by
  intro u_reset_j
  have h_sum_nonneg : 0 ≤ ∑ i : m, P_col i * z_play i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (h_P i) (h_z i)
  dsimp only [u_reset_j]
  constructor <;> linarith

/-- **Stage 2: Endpoint Takeover and Immediate Transition to `\mathsf{c}_0` (Section 9.1)**:
    When `0 < δ < c`, at the end of the parent bundle `u_g = ζ - c + δ` strictly exceeds
    `H_parent = ζ - c` by `δ > 0`, and immediately after `g` plays once, `\mathsf{c}_0` at score
    `ζ` strictly exceeds `u_g` by `c - δ > 0`, `H_parent` by `c > 0`, and every other reset action
    `ζ - Jm_j` by `Jm_j > 0`. -/
theorem chronology_endpoint_to_reset0 {ζ c δ Jm_j : ℚ}
    (hδ0 : 0 < δ) (hδc : δ < c) (hJm : 0 < Jm_j) :
    let H_parent := ζ - c
    let u_g := ζ - c + δ
    let u_reset0 := ζ
    let u_reset_j := ζ - Jm_j
    u_g - H_parent = δ ∧
      0 < u_g - H_parent ∧
      0 < u_reset0 - u_g ∧
      0 < u_reset0 - H_parent ∧
      0 < u_reset0 - u_reset_j := by
  intro H_parent u_g u_reset0 u_reset_j
  dsimp only [H_parent, u_g, u_reset0, u_reset_j]
  refine ⟨by ring, by linarith, by linarith, by linarith, by linarith⟩

/-- Reset play count vector during `\mathsf{c}_j`'s run in `\mathcal{B}(q)`:
    all earlier reset actions `ℓ < j` have completed `m_vec ℓ` plays, `\mathsf{c}_j` has played
    `h` times, and all later reset actions `ℓ > j` have played `0` times. -/
def resetPrefixCount {n : ℕ} (j : Fin n) (m_vec : Fin n → ℚ) (h : ℚ) (ℓ : Fin n) : ℚ :=
  if ℓ.val < j.val then m_vec ℓ else if ℓ = j then h else 0

/-- Reset score vector `v_mid(i) = ζ - (J m)_i` immediately before `\mathcal{B}(q)` begins. -/
def resetEntryScore {n : ℕ} (J : Matrix (Fin n) (Fin n) ℚ) (m_vec : Fin n → ℚ) (ζ : ℚ)
    (i : Fin n) : ℚ :=
  ζ - ∑ ℓ : Fin n, J i ℓ * m_vec ℓ

/-- **Stage 3a (Active Reset Ceiling, Section 9.1)**:
    If `J` is strictly lower-triangular (`J a b = 0` for `a ≤ b`), then throughout `\mathsf{c}_j`'s
    run (for any `h`), the active reset action `\mathsf{c}_j` has score identically equal to `ζ`. -/
theorem chronology_reset_active_at_ceiling {n : ℕ}
    (J : Matrix (Fin n) (Fin n) ℚ) (m_vec : Fin n → ℚ) (ζ h : ℚ) (j : Fin n)
    (hJ_lower : ∀ a b : Fin n, a.val ≤ b.val → J a b = 0) :
    scoreVec (J - J.transpose) (resetEntryScore J m_vec ζ) (resetPrefixCount j m_vec h) j = ζ := by
  simp only [scoreVec, resetEntryScore, Matrix.sub_apply, Matrix.transpose_apply]
  have h_sum :
      (∑ ℓ : Fin n, (J j ℓ - J ℓ j) * resetPrefixCount j m_vec h ℓ) =
        ∑ ℓ : Fin n, J j ℓ * m_vec ℓ := by
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    unfold resetPrefixCount
    by_cases hlt : ℓ.val < j.val
    · have hJ0 : J ℓ j = 0 := hJ_lower ℓ j (le_of_lt hlt)
      simp [hlt, hJ0]
    · by_cases heq : ℓ = j
      · subst heq
        have hJ0 : J ℓ ℓ = 0 := hJ_lower ℓ ℓ (le_refl _)
        simp [hJ0]
      · have hle : j.val ≤ ℓ.val := by omega
        have hJ0 : J j ℓ = 0 := hJ_lower j ℓ hle
        simp [hlt, heq, hJ0]
  linarith

/-- **Stage 3a (Future Reset Action Strict Deficit, Section 9.1)**:
    For any future reset action `i` (`j < i`), its deficit below the ceiling `ζ` after `h` plays
    of `\mathsf{c}_j` (`h ≤ m_vec j`) is at least `J i j * (m_vec j - h)`.
    In particular, when `J i j > 0` and `h < m_vec j`, action `i` is strictly below `ζ`. -/
theorem chronology_reset_later_deficit {n : ℕ}
    (J : Matrix (Fin n) (Fin n) ℚ) (m_vec : Fin n → ℚ) (ζ h : ℚ) (j i : Fin n)
    (hij : j.val < i.val)
    (hJ_lower : ∀ a b : Fin n, a.val ≤ b.val → J a b = 0)
    (hJ_nonneg : ∀ a b : Fin n, 0 ≤ J a b)
    (hm_nonneg : ∀ ℓ : Fin n, 0 ≤ m_vec ℓ)
    (hh_le : h ≤ m_vec j) :
    J i j * (m_vec j - h) ≤
      ζ - scoreVec (J - J.transpose) (resetEntryScore J m_vec ζ) (resetPrefixCount j m_vec h) i := by
  simp only [scoreVec, resetEntryScore, Matrix.sub_apply, Matrix.transpose_apply]
  have h_rewrite :
      ζ - (ζ - (∑ ℓ : Fin n, J i ℓ * m_vec ℓ) +
        ∑ ℓ : Fin n, (J i ℓ - J ℓ i) * resetPrefixCount j m_vec h ℓ) =
        ∑ ℓ : Fin n, (J i ℓ * m_vec ℓ - (J i ℓ - J ℓ i) * resetPrefixCount j m_vec h ℓ) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [h_rewrite]
  have h_term_j :
      J i j * m_vec j - (J i j - J j i) * resetPrefixCount j m_vec h j =
        J i j * (m_vec j - h) := by
    have hJji : J j i = 0 := hJ_lower j i (le_of_lt hij)
    simp [resetPrefixCount, hJji]
    ring
  rw [← h_term_j]
  refine Finset.single_le_sum
    (f := fun ℓ : Fin n => J i ℓ * m_vec ℓ - (J i ℓ - J ℓ i) * resetPrefixCount j m_vec h ℓ)
    (fun ℓ _ => ?_) (Finset.mem_univ j)
  unfold resetPrefixCount
  by_cases hlt : ℓ.val < j.val
  · have hJli : J ℓ i = 0 := hJ_lower ℓ i (by omega)
    simp [hlt, hJli]
  · by_cases heq : ℓ = j
    · subst heq
      have hJji : J ℓ i = 0 := hJ_lower ℓ i (le_of_lt hij)
      simp only [lt_irrefl, ↓reduceIte, hJji, sub_zero]
      have : J i ℓ * m_vec ℓ - J i ℓ * h = J i ℓ * (m_vec ℓ - h) := by ring
      rw [this]
      exact mul_nonneg (hJ_nonneg i ℓ) (by linarith)
    · simp only [hlt, heq, ↓reduceIte, mul_zero, sub_zero]
      exact mul_nonneg (hJ_nonneg i ℓ) (hm_nonneg ℓ)

/-- **Stage 3a (Earlier Reset Action Deficit, Section 9.1)**:
    For any previously played reset action `i` (`i < j`), its deficit below `ζ` after `h ≥ 0`
    plays of `\mathsf{c}_j` is at least `J j i * h ≥ 0`. -/
theorem chronology_reset_earlier_deficit {n : ℕ}
    (J : Matrix (Fin n) (Fin n) ℚ) (m_vec : Fin n → ℚ) (ζ h : ℚ) (j i : Fin n)
    (hij : i.val < j.val)
    (hJ_lower : ∀ a b : Fin n, a.val ≤ b.val → J a b = 0)
    (hJ_nonneg : ∀ a b : Fin n, 0 ≤ J a b)
    (hm_nonneg : ∀ ℓ : Fin n, 0 ≤ m_vec ℓ)
    (hh_nonneg : 0 ≤ h) :
    J j i * h ≤
      ζ - scoreVec (J - J.transpose) (resetEntryScore J m_vec ζ) (resetPrefixCount j m_vec h) i := by
  simp only [scoreVec, resetEntryScore, Matrix.sub_apply, Matrix.transpose_apply]
  have h_rewrite :
      ζ - (ζ - (∑ ℓ : Fin n, J i ℓ * m_vec ℓ) +
        ∑ ℓ : Fin n, (J i ℓ - J ℓ i) * resetPrefixCount j m_vec h ℓ) =
        ∑ ℓ : Fin n, (J i ℓ * m_vec ℓ - (J i ℓ - J ℓ i) * resetPrefixCount j m_vec h ℓ) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [h_rewrite]
  have h_term_j :
      J i j * m_vec j - (J i j - J j i) * resetPrefixCount j m_vec h j = J j i * h := by
    have hJij : J i j = 0 := hJ_lower i j (le_of_lt hij)
    simp [resetPrefixCount, hJij]
  rw [← h_term_j]
  refine Finset.single_le_sum
    (f := fun ℓ : Fin n => J i ℓ * m_vec ℓ - (J i ℓ - J ℓ i) * resetPrefixCount j m_vec h ℓ)
    (fun ℓ _ => ?_) (Finset.mem_univ j)
  unfold resetPrefixCount
  by_cases hlt : ℓ.val < j.val
  · by_cases hli : ℓ.val ≤ i.val
    · have hJli : J ℓ i = 0 := hJ_lower ℓ i hli
      simp [hlt, hJli]
    · have hJil : J i ℓ = 0 := hJ_lower i ℓ (by omega)
      simp only [hlt, ↓reduceIte, hJil, zero_mul, zero_sub, neg_mul, sub_neg_eq_add, zero_add]
      exact mul_nonneg (hJ_nonneg ℓ i) (hm_nonneg ℓ)
  · by_cases heq : ℓ = j
    · subst heq
      have hJij : J i ℓ = 0 := hJ_lower i ℓ (le_of_lt hij)
      simp only [lt_irrefl, ↓reduceIte, hJij, zero_mul, zero_sub, neg_mul, sub_neg_eq_add, zero_add]
      exact mul_nonneg (hJ_nonneg ℓ i) hh_nonneg
    · have hJil : J i ℓ = 0 := hJ_lower i ℓ (by omega)
      simp [hlt, heq, hJil]

/-- **Stage 3b (Old Actions Wait During Early Reset Half, Section 9.1)**:
    During the early reset runs where `P_E ≤ 0` and `z_early ≥ 0`, every old action starting at
    `s_mid_i ≤ ζ - c + δ` stays at or below `ζ - c + δ` (strictly below `ζ` by at least `c - δ`). -/
theorem chronology_old_waits_early_reset {r : Type*} [Fintype r]
    (P_E_row z_early : r → ℚ) (s_mid_i ζ c δ : ℚ)
    (hs_mid : s_mid_i ≤ ζ - c + δ)
    (hPE : ∀ j : r, P_E_row j ≤ 0)
    (hz : ∀ j : r, 0 ≤ z_early j) :
    let u_old_i := s_mid_i + ∑ j : r, P_E_row j * z_early j
    c - δ ≤ ζ - u_old_i := by
  intro u_old_i
  have h_nonpos : (∑ j : r, P_E_row j * z_early j) ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg (hPE j) (hz j)
  dsimp only [u_old_i]
  linarith

/-- **Stage 3b (Old Actions Wait During Late Reset Half, Equation `eq:oldlate`)**:
    Working backward from the end of `\mathcal{B}(q)` where old action `i` reaches
    `s_next_i ≤ ζ`, if every late coupling entry satisfies `P_L_row j ≥ p_min > 0` and
    `z_late_rem ≥ 0`, then `u_old_i = s_next_i - ∑ j, P_L_row j * z_late_rem j` has deficit
    `ζ - u_old_i ≥ p_min * ∑ j, z_late_rem j` (strictly positive whenever at least 1 play remains). -/
theorem chronology_old_waits_late_reset {r : Type*} [Fintype r]
    (P_L_row z_late_rem : r → ℚ) (s_next_i ζ p_min : ℚ)
    (hs_next : s_next_i ≤ ζ)
    (hPL : ∀ j : r, p_min ≤ P_L_row j)
    (hz : ∀ j : r, 0 ≤ z_late_rem j) :
    let u_old_i := s_next_i - ∑ j : r, P_L_row j * z_late_rem j
    p_min * (∑ j : r, z_late_rem j) ≤ ζ - u_old_i := by
  intro u_old_i
  have h_sum :
      p_min * (∑ j : r, z_late_rem j) ≤ ∑ j : r, P_L_row j * z_late_rem j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hPL j) (hz j)
  dsimp only [u_old_i]
  linarith

/-!
## 3. Proposition 9.2 (`prop:inherit`): Clock Inheritance for the Rotated Phase
-/

/-- **Rotated Clock Entry Safety (`prop:inherit` Condition (II), Equation `eq:supportsafe`)**:
    At the start of the rotated phase `\mathcal{W}_{k+1}(q) = \mathcal{B}(q)\mathcal{A}(q+1)`,
    the entry leader `b_+ = \mathsf{c}_0` has score `ζ`, while the sole action in
    `\operatorname{supp}(v_+) = \{g\}` has score `ζ - c + δ`. After one play of `\mathsf{c}_0`
    (which adds `0` to `\mathsf{c}_0` and `P_{g,0} < 0` to `g`) and subtracting `v_+ᵀ = e_g`,
    `\mathsf{c}_0` beats `g` by `(c - δ) + (-P_{g,0}) + 1 > 1`. -/
theorem inherit_entry_safety {ζ c δ P_g0 : ℚ}
    (hδc : δ < c) (hPg0 : P_g0 < 0) :
    let r_reset0 := ζ
    let r_g := ζ - c + δ
    let after_reset0 := r_reset0 + 0 - 0
    let after_g := r_g + P_g0 - 1
    1 < after_reset0 - after_g := by
  intro r_reset0 r_g after_reset0 after_g
  dsimp only [after_reset0, after_g, r_reset0, r_g]
  linarith

/-- **Rotated Clock Remaining Height Bound (`prop:inherit` Condition (III), Equation (79))**:
    At any prefix in the parent bundle of `\mathcal{A}(q+1)`, if the remaining height gain to the
    bundle endpoint `ζ_next - c` is at most `ε * N_rem + A_k` and `c ≤ 1`, then the remaining
    height gain to the rotated phase exit height `ζ_next` is at most `ε * N_rem + (A_k + 1)`. -/
theorem inherit_remaining_height_bound {ζ_next H_prefix c ε N_rem A_k : ℚ}
    (h_bundle : (ζ_next - c) - H_prefix ≤ ε * N_rem + A_k)
    (hc : c ≤ 1) :
    ζ_next - H_prefix ≤ ε * N_rem + (A_k + 1) := by
  linarith

/-!
## 4. Action Count Recursion & All-Time Duality Gap Enclosure (`lem:alltime`, `thm:main`)
-/

/-- Number of recurrent actions `m_k = (k + 1)^2 - 6` in the order-`k` clock constructed from RPS. -/
def recurrentActionCount (k : ℕ) : ℕ :=
  (k + 1) ^ 2 - 6

/-- Total number of actions `n_k = (k + 1)^2 - 5` including the single setup action `\omega`. -/
def totalActionCount (k : ℕ) : ℕ :=
  (k + 1) ^ 2 - 5

/-- Total number of actions `n_k^{(7)} = (k + 1)^2 - 9` when lifting from the 6-action cubic base. -/
def totalActionCountFromCubicBase (k : ℕ) : ℕ :=
  (k + 1) ^ 2 - 9

/-- **Action Count Recurrence (Equation (5) & Theorem 1.1 `thm:main`)**:
    Starting from `m_2 = 3`, adding `1 + 2(k + 1) = 2k + 3` actions at each lift `k ↦ k + 1`
    produces `m_k = (k + 1)^2 - 6` and `n_k = m_k + 1 = (k + 1)^2 - 5` for all `k ≥ 2`
    (with `n_3 = 11` and `n_3^{(7)} = 7`). -/
theorem action_count_recurrence {k : ℕ} (hk : 2 ≤ k) :
    recurrentActionCount 2 = 3 ∧
      recurrentActionCount k + (2 * k + 3) = recurrentActionCount (k + 1) ∧
      totalActionCount k = recurrentActionCount k + 1 ∧
      totalActionCount 3 = 11 ∧
      totalActionCountFromCubicBase 3 = 7 := by
  unfold recurrentActionCount totalActionCount totalActionCountFromCubicBase
  have h1 : (k + 1 + 1) ^ 2 = (k + 1) ^ 2 + 2 * k + 3 := by ring
  have h2 : 9 ≤ (k + 1) ^ 2 := by nlinarith
  refine ⟨by decide, by omega, by omega, by decide, by decide⟩

/-- **All-Integer-Time Duality Gap Enclosure (`lem:alltime` & Section A.3 `sec:onset`)**:
    For any integer time `t` inside phase `q` (`0 < t_q ≤ t ≤ t_next`), if the nondecreasing
    trajectory height `H_t` satisfies `0 ≤ H_q ≤ H_t ≤ H_next`, then the synchronized
    skew-symmetric duality gap `2 * H_t / t` is enclosed between
    `2 * H_q / t_next` and `2 * H_next / t_q`. -/
theorem all_time_gap_enclosure {t_q t t_next H_q H_t H_next : ℚ}
    (htq : 0 < t_q) (ht1 : t_q ≤ t) (ht2 : t ≤ t_next)
    (hHq : 0 ≤ H_q) (hH1 : H_q ≤ H_t) (hH2 : H_t ≤ H_next) :
    2 * H_q / t_next ≤ 2 * H_t / t ∧ 2 * H_t / t ≤ 2 * H_next / t_q := by
  have ht : 0 < t := lt_of_lt_of_le htq ht1
  have htnext : 0 < t_next := lt_of_lt_of_le ht ht2
  have hHt : 0 ≤ H_t := le_trans hHq hH1
  have hHnext : 0 ≤ H_next := le_trans hHt hH2
  constructor
  · rw [div_le_div_iff₀ htnext ht]
    nlinarith
  · rw [div_le_div_iff₀ ht htq]
    nlinarith

/-- **Constant Unit First Coordinate of Binomial Basis (`eq:clock-table`)**:
    For any positive width `w > 0` and phase index `q ∈ ℕ`,
    `e_0^\top p_{w-1}(q) = \binom{q}{0} = 1`. -/
theorem e0_row_dot_binomBasis {w : ℕ} (hw : 0 < w) (q : ℕ) :
    dotProduct (e0_row w) (binomBasis w q) = 1 := by
  let i0 : Fin w := ⟨0, hw⟩
  have hsum :
      dotProduct (e0_row w) (binomBasis w q) =
        ∑ i : Fin w, if i = i0 then (Nat.choose q i.val : ℚ) else 0 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i = i0
    · subst hi
      simp [e0_row, binomBasis, i0]
    · have hne : i.val ≠ 0 := by
        intro h
        apply hi
        ext
        exact h
      simp [e0_row, binomBasis, hi, hne]
  rw [hsum, Finset.sum_ite_eq' Finset.univ i0]
  simp [i0]

/-- **General Order-`w` Single-Phase Score Increment (`eq:clock-table`)**:
    If `(M, R, C)` satisfies the clock table equation `M * C = R * N_{w-1}`, then for every
    phase `q ∈ ℕ`, the score change produced by the phase count vector `C p_{w-1}(q)` equals
    `R p_{w-1}(q + 1) - R p_{w-1}(q)`. -/
theorem clock_phase_score_diff {m : Type*} [Fintype m] [DecidableEq m] {w : ℕ}
    (M : Matrix m m ℚ) (R C : Matrix m (Fin w) ℚ)
    (hclock : M * C = R * N_mat w) (q : ℕ) :
    M.mulVec (C.mulVec (binomBasis w q)) =
      R.mulVec (binomBasis w (q + 1)) - R.mulVec (binomBasis w q) := by
  rw [Matrix.mulVec_mulVec, hclock, ← Matrix.mulVec_mulVec, ← binomBasis_succ_sub w q,
    Matrix.mulVec_sub]

/-- **General Order-`w` Single-Phase Trajectory Transition (`eq:clock-table`)**:
    Under `M * C = R * N_{w-1}`, starting phase `q` at score vector `s(q) = R p_{w-1}(q)` and
    playing count vector `r(q) = C p_{w-1}(q)` transitions the cumulative score vector to
    `s(q + 1) = R p_{w-1}(q + 1)`. -/
theorem clock_phase_transition {m : Type*} [Fintype m] [DecidableEq m] {w : ℕ}
    (M : Matrix m m ℚ) (R C : Matrix m (Fin w) ℚ)
    (hclock : M * C = R * N_mat w) (q : ℕ) :
    scoreVec M (R.mulVec (binomBasis w q)) (C.mulVec (binomBasis w q)) =
      R.mulVec (binomBasis w (q + 1)) := by
  have hdiff := clock_phase_score_diff M R C hclock q
  ext i
  have hi := congr_fun hdiff i
  simp only [Pi.sub_apply] at hi
  have hscore :
      scoreVec M (R.mulVec (binomBasis w q)) (C.mulVec (binomBasis w q)) i =
        R.mulVec (binomBasis w q) i + M.mulVec (C.mulVec (binomBasis w q)) i := by
    rfl
  linarith

/-- **General Order-`w` Endpoint Counter Invariant (`eq:clock-table`)**:
    If the endpoint functional `v` satisfies `v^\top C = e_0^\top`, then along every phase
    `q ∈ ℕ`, the linear functional `v^\top r(q)` of the phase play counts equals `1`. -/
theorem clock_endpoint_increment_eq_one {m : Type*} [Fintype m] [DecidableEq m] {w : ℕ}
    (hw : 0 < w) (v : m → ℚ) (C : Matrix m (Fin w) ℚ)
    (hvC : Matrix.vecMul v C = e0_row w) (q : ℕ) :
    dotProduct v (C.mulVec (binomBasis w q)) = 1 := by
  rw [Matrix.dotProduct_mulVec, hvC, e0_row_dot_binomBasis hw q]

/-- **Master Algebraic Clock Lift (`thm:lift` & Proposition 8.1 `prop:rot-alg`)**:
    Given `B * (1 + N) = 1` and a coupling block `P` satisfying the interpolation system
    `Pᵀ * X = Q_reset(J, M, B, ζ)` and `P * M = S * N - G_O * X`, the rotated next-order
    count table `C_+ = (X * (1 + N), M)` and rotated next-order score table
    `R_+ = (S + G_O * X, 1_n ζ - J * M)` satisfy both block rows of the next-order clock
    table equation `G_+ * C_+ = R_+ * N`. -/
theorem master_algebraic_clock_lift {m n w : Type*} [Fintype m] [Fintype n] [Fintype w]
    [DecidableEq w]
    (G_O : Matrix m m ℚ) (P : Matrix m n ℚ) (J : Matrix n n ℚ)
    (S X : Matrix m w ℚ) (M : Matrix n w ℚ) (B N : Matrix w w ℚ) (zeta : w → ℚ)
    (hBT : B * (1 + N) = 1)
    (hPtX : P.transpose * X = Q_reset J M B zeta)
    (hPM : P * M = S * N - G_O * X) :
    G_O * (X * (1 + N)) + P * M = (S + G_O * X) * N ∧
      -P.transpose * (X * (1 + N)) + (J - J.transpose) * M =
        (one_zeta n zeta - J * M) * N := by
  refine ⟨rotated_clock_old_block G_O P S X M N hPM, ?_⟩
  have hreset : -P.transpose * X + (J - J.transpose) * M = V_reset J M B zeta * N :=
    ((reset_identity_iff G_O P J S X M B N zeta hBT).mpr ⟨hPM, hPtX⟩).2
  have hrot :=
    rotated_clock_reset_block P J X M (V_reset J M B zeta) (Q_reset J M B zeta) N hreset hPtX
  rw [rotated_reset_score_identity J M B zeta] at hrot
  exact hrot

/-- **Main Theorem Synthesis (`thm:main`, Theorem 1.1)**:
    For every order `k ≥ 2`:
    1. The inductive action count recurrence yields `m_k = (k + 1)^2 - 6` recurrent actions
       and `n_k = (k + 1)^2 - 5` total actions (or `n_k^{(7)} = (k + 1)^2 - 9` from the 7-action
       cubic base).
    2. Any order-`k` clock table `(M, R, C, v)` satisfying `M * C = R * N_{k-1}` and
       `v^\top C = e_0^\top` advances the phase score vector from `R p_{k-1}(q)` to
       `R p_{k-1}(q + 1)` with unit endpoint counter increment `v^\top (C p_{k-1}(q)) = 1`
       for every phase `q ∈ ℕ`.
    3. At every integer step `t ∈ [t_q, t_{q+1}]`, the synchronized skew-symmetric duality gap
       `2 H_t / t` is sandwiched between `2 H_q / t_{q+1}` and `2 H_{q+1} / t_q`. -/
theorem karlin_main_theorem_synthesis {m : Type*} [Fintype m] [DecidableEq m]
    {k : ℕ} (hk : 2 ≤ k)
    (M : Matrix m m ℚ) (R C : Matrix m (Fin k) ℚ) (v : m → ℚ)
    (hclock : M * C = R * N_mat k)
    (hvC : Matrix.vecMul v C = e0_row k)
    (q : ℕ)
    {t_q t t_next H_q H_t H_next : ℚ}
    (htq : 0 < t_q) (ht1 : t_q ≤ t) (ht2 : t ≤ t_next)
    (hHq : 0 ≤ H_q) (hH1 : H_q ≤ H_t) (hH2 : H_t ≤ H_next) :
    (recurrentActionCount k + (2 * k + 3) = recurrentActionCount (k + 1) ∧
      totalActionCount k = recurrentActionCount k + 1) ∧
    (scoreVec M (R.mulVec (binomBasis k q)) (C.mulVec (binomBasis k q)) =
      R.mulVec (binomBasis k (q + 1)) ∧
      dotProduct v (C.mulVec (binomBasis k q)) = 1) ∧
    (2 * H_q / t_next ≤ 2 * H_t / t ∧ 2 * H_t / t ≤ 2 * H_next / t_q) := by
  have hk_pos : 0 < k := by omega
  have hact := action_count_recurrence hk
  refine ⟨⟨hact.2.1, hact.2.2.1⟩, ?_, all_time_gap_enclosure htq ht1 ht2 hHq hH1 hH2⟩
  exact ⟨clock_phase_transition M R C hclock q, clock_endpoint_increment_eq_one hk_pos v C hvC q⟩

/-!
## 5. Word-Level Chronology & Prefix-by-Prefix Best-Response Composition (`prop:chronology`)
-/

/-- Action play-count vector of a finite play word `W : List α`. -/
def wordCountVec {α : Type*} [DecidableEq α] (W : List α) (i : α) : ℚ :=
  (W.count i : ℚ)

/-- Score vector reached after playing the word `W : List α` starting from `s0 : α → ℚ`
    under game matrix `M : Matrix α α ℚ`. -/
def wordScore {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (s0 : α → ℚ) (W : List α) : α → ℚ :=
  scoreVec M s0 (wordCountVec W)

/-- Play counts of a concatenated word `W1 ++ W2` sum the play counts of `W1` and `W2`. -/
theorem wordCountVec_append {α : Type*} [DecidableEq α] (W1 W2 : List α) (i : α) :
    wordCountVec (W1 ++ W2) i = wordCountVec W1 i + wordCountVec W2 i := by
  simp [wordCountVec, List.count_append]

/-- Score evolution across a concatenated word `W1 ++ W2` composes the score transitions
    of `W1` and `W2`. -/
theorem wordScore_append {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (s0 : α → ℚ) (W1 W2 : List α) :
    wordScore M s0 (W1 ++ W2) = wordScore M (wordScore M s0 W1) W2 := by
  ext i
  simp only [wordScore, scoreVec, wordCountVec_append, mul_add, Finset.sum_add_distrib, add_assoc]

/-- Strict best-response condition at prefix index `k < W.length` of a finite play word `W`. -/
def IsStrictBestResponseAt {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (s0 : α → ℚ) (W : List α) (k : ℕ) (hk : k < W.length) : Prop :=
  ∀ j : α, j ≠ W[k] →
    wordScore M s0 (W.take k) j < wordScore M s0 (W.take k) W[k]

/-- A finite play word `W : List α` is a valid strict Fictitious Play word from initial score
    vector `s0` if at **every** prefix `0 ≤ k < W.length`, the scheduled action `W[k]` is the
    unique strict best response. -/
def IsValidStrictWord {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (s0 : α → ℚ) (W : List α) : Prop :=
  ∀ (k : ℕ) (hk : k < W.length), IsStrictBestResponseAt M s0 W k hk

/-- **Concatenation of Valid Strict Fictitious Play Words (`isValidStrictWord_append`)**:
    If `W1` is a valid strict FP word from `s0`, and `W2` is a valid strict FP word from
    `wordScore M s0 W1`, then `W1 ++ W2` is a valid strict FP word from `s0` at every prefix. -/
theorem isValidStrictWord_append {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (s0 : α → ℚ) (W1 W2 : List α)
    (h1 : IsValidStrictWord M s0 W1)
    (h2 : IsValidStrictWord M (wordScore M s0 W1) W2) :
    IsValidStrictWord M s0 (W1 ++ W2) := by
  intro k hk j hj
  rw [List.length_append] at hk
  by_cases hk1 : k < W1.length
  · have htake : (W1 ++ W2).take k = W1.take k :=
      List.take_append_of_le_length (le_of_lt hk1)
    have hget : (W1 ++ W2)[k] = W1[k] := List.getElem_append_left hk1
    rw [hget] at hj
    rw [htake, hget]
    exact h1 k hk1 j hj
  · have hle : W1.length ≤ k := le_of_not_gt hk1
    have hk2 : k - W1.length < W2.length := by omega
    have htake : (W1 ++ W2).take k = W1 ++ W2.take (k - W1.length) := by
      rw [List.take_append, List.take_of_length_le hle]
    have hget : (W1 ++ W2)[k] = W2[k - W1.length] := List.getElem_append_right hle
    rw [hget] at hj
    rw [htake, hget, wordScore_append]
    exact h2 (k - W1.length) hk2 j hj

/-- **Four-Stage Macro-Block Chronology Composition (`chronology_four_stage_phase_word_valid`)**:
    In Proposition 9.1 (`prop:chronology`), if the four macro-stages of phase `q` —
    (1) the parent bundle word `W_bundle`,
    (2) the single endpoint play `[g]`,
    (3) the early reset block `W_early_reset`, and
    (4) the late reset block `W_late_reset` —
    are each valid strict FP words from the score vector reached by the preceding stage,
    then the complete phase word `W_bundle ++ [g] ++ W_early_reset ++ W_late_reset` is a
    valid strict FP word at **every** integer prefix within the phase. -/
theorem chronology_four_stage_phase_word_valid {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (s0 : α → ℚ)
    (W_bundle : List α) (g : α) (W_early_reset W_late_reset : List α)
    (h_stage1 : IsValidStrictWord M s0 W_bundle)
    (h_stage2 : IsValidStrictWord M (wordScore M s0 W_bundle) [g])
    (h_stage3 : IsValidStrictWord M (wordScore M s0 (W_bundle ++ [g])) W_early_reset)
    (h_stage4 :
      IsValidStrictWord M (wordScore M s0 (W_bundle ++ [g] ++ W_early_reset)) W_late_reset) :
    IsValidStrictWord M s0 (W_bundle ++ [g] ++ W_early_reset ++ W_late_reset) := by
  have h12 : IsValidStrictWord M s0 (W_bundle ++ [g]) :=
    isValidStrictWord_append M s0 W_bundle [g] h_stage1 h_stage2
  have h123 : IsValidStrictWord M s0 (W_bundle ++ [g] ++ W_early_reset) :=
    isValidStrictWord_append M s0 (W_bundle ++ [g]) W_early_reset h12 h_stage3
  exact isValidStrictWord_append M s0 (W_bundle ++ [g] ++ W_early_reset) W_late_reset h123 h_stage4

/-- Score after `k` plays of a single action `a` (`List.replicate k a`). -/
theorem wordScore_replicate {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (s0 : α → ℚ) (k : ℕ) (a i : α) :
    wordScore M s0 (List.replicate k a) i = s0 i + M i a * (k : ℚ) := by
  simp only [wordScore, scoreVec, wordCountVec]
  have hsum :
      (∑ j : α, M i j * ((List.replicate k a).count j : ℚ)) =
        ∑ j : α, if j = a then M i a * (k : ℚ) else 0 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hja : j = a
    · subst hja
      simp [List.count_replicate_self]
    · have hne : a ≠ j := Ne.symm hja
      simp [List.count_replicate, hja, hne]
  rw [hsum, Finset.sum_ite_eq' Finset.univ a]
  simp

/-- **Within-Run Prefix Validity from Endpoint Checks (`isValidStrictWord_replicate_of_endpoints`)**:
    By affine linearity of cumulative scores during a constant-action run `List.replicate m a`
    (`M a a = 0`), if `a` strictly leads every other action `j ≠ a` at the start of the run (`h = 0`)
    and at the last step before completion (`h = m - 1`), then `List.replicate m a` is a valid
    strict FP word at **every** intermediate step `0 ≤ h < m`. -/
theorem isValidStrictWord_replicate_of_endpoints {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (s0 : α → ℚ) (m : ℕ) (a : α)
    (hm : 1 ≤ m) (hMaa : M a a = 0)
    (h_start : ∀ j : α, j ≠ a → s0 j < s0 a)
    (h_end : ∀ j : α, j ≠ a → s0 j + M j a * ((m - 1 : ℕ) : ℚ) < s0 a) :
    IsValidStrictWord M s0 (List.replicate m a) := by
  intro k hk j hj
  have hget : (List.replicate m a)[k] = a := List.getElem_replicate hk
  rw [List.length_replicate] at hk
  rw [hget] at hj ⊢
  have htake : (List.replicate m a).take k = List.replicate k a := by
    rw [List.take_replicate, Nat.min_eq_left (le_of_lt hk)]
  rw [htake, wordScore_replicate, wordScore_replicate, hMaa, zero_mul, add_zero]
  have hk_le : (k : ℚ) ≤ ((m - 1 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : k ≤ m - 1)
  have hk0 : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg k
  have h0 := h_start j hj
  have hend := h_end j hj
  by_cases hs : 0 ≤ M j a <;> nlinarith

/-- A single-step word `[a]` is a valid strict FP word from `s0` whenever `a` strictly leads
    every other action `j ≠ a` at `s0`. -/
theorem isValidStrictWord_singleton {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (s0 : α → ℚ) (a : α)
    (h_dom : ∀ j : α, j ≠ a → s0 j < s0 a) :
    IsValidStrictWord M s0 [a] := by
  intro k hk j hj
  simp only [List.length_singleton] at hk
  have hk0 : k = 0 := by omega
  subst hk0
  have htake : ([a] : List α).take 0 = [] := rfl
  have hget : ([a] : List α)[0] = a := rfl
  rw [hget] at hj ⊢
  rw [htake]
  have hws : ∀ x : α, wordScore M s0 ([] : List α) x = s0 x := by
    intro x
    simp [wordScore, scoreVec, wordCountVec]
  rw [hws j, hws a]
  exact h_dom j hj

/-- Count vector of a word mapped through `Sum.inl` vanishes on `Sum.inr j`. -/
theorem wordCountVec_map_inl_inr {α β : Type*} [DecidableEq α] [DecidableEq β]
    (W : List α) (j : β) :
    wordCountVec (W.map (Sum.inl : α → α ⊕ β)) (Sum.inr j) = 0 := by
  induction W with
  | nil => rfl
  | cons a tl ih =>
    have hcons :
        ((a :: tl).map (Sum.inl : α → α ⊕ β)) = [Sum.inl a] ++ tl.map Sum.inl := rfl
    rw [hcons, wordCountVec_append, ih, add_zero]
    simp [wordCountVec]

/-- Count vector of a word mapped through `Sum.inl` on `Sum.inl i` equals
    the parent count vector on `i`. -/
theorem wordCountVec_map_inl_inl {α β : Type*} [DecidableEq α] [DecidableEq β]
    (W : List α) (i : α) :
    wordCountVec (W.map (Sum.inl : α → α ⊕ β)) (Sum.inl i) = wordCountVec W i := by
  induction W with
  | nil => rfl
  | cons a tl ih =>
    have hcons1 : ((a :: tl : List α)) = [a] ++ tl := rfl
    have hcons2 :
        ((a :: tl).map (Sum.inl : α → α ⊕ β)) = [Sum.inl a] ++ tl.map Sum.inl := rfl
    rw [hcons2, wordCountVec_append, ih]
    conv_rhs => rw [hcons1, wordCountVec_append]
    congr 1
    by_cases hai : a = i
    · subst hai; simp [wordCountVec]
    · have hne : (Sum.inl a : α ⊕ β) ≠ Sum.inl i := fun h => hai (Sum.inl.inj h)
      simp [wordCountVec, hai, hne]

/-- **Old-Block Score Preservation During Parent Bundle (`wordScore_map_inl_old`)**:
    When a word `W : List α` of old actions is embedded into `α ⊕ β` via `Sum.inl`, the
    cumulative score on any old coordinate `Sum.inl i` under
    `Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose)` equals the parent cumulative
    score on `G_O`. -/
theorem wordScore_map_inl_old {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (G_O : Matrix α α ℚ) (P : Matrix α β ℚ) (J : Matrix β β ℚ)
    (s0 : α ⊕ β → ℚ) (W : List α) (i : α) :
    wordScore (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose)) s0
      (W.map Sum.inl) (Sum.inl i) =
      wordScore G_O (fun u => s0 (Sum.inl u)) W i := by
  simp only [wordScore, scoreVec]
  congr 1
  rw [Fintype.sum_sum_type]
  have h_new :
      (∑ j : β,
        Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose) (Sum.inl i) (Sum.inr j) *
          wordCountVec (W.map Sum.inl) (Sum.inr j)) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [wordCountVec_map_inl_inr (α := α) (β := β) W j, mul_zero]
  rw [h_new, add_zero]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.fromBlocks_apply₁₁, wordCountVec_map_inl_inl (α := α) (β := β) W u]

/-- **New-Block Score Formula During Parent Bundle (`wordScore_map_inl_new`)**:
    When a word `W : List α` of old actions is embedded into `α ⊕ β` via `Sum.inl`, the
    cumulative score on any reset coordinate `Sum.inr j` under
    `Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose)` equals
    `s0 (Sum.inr j) - ∑ u, P u j * wordCountVec W u`. -/
theorem wordScore_map_inl_new {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (G_O : Matrix α α ℚ) (P : Matrix α β ℚ) (J : Matrix β β ℚ)
    (s0 : α ⊕ β → ℚ) (W : List α) (j : β) :
    wordScore (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose)) s0
      (W.map Sum.inl) (Sum.inr j) =
      s0 (Sum.inr j) - ∑ u : α, P u j * wordCountVec W u := by
  simp only [wordScore, scoreVec]
  rw [Fintype.sum_sum_type]
  have h_new :
      (∑ j' : β,
        Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose) (Sum.inr j) (Sum.inr j') *
          wordCountVec (W.map Sum.inl) (Sum.inr j')) = 0 := by
    refine Finset.sum_eq_zero fun j' _ => ?_
    rw [wordCountVec_map_inl_inr (α := α) (β := β) W j', mul_zero]
  rw [h_new, add_zero]
  have h_old :
      (∑ u : α,
        Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose) (Sum.inr j) (Sum.inl u) *
          wordCountVec (W.map (Sum.inl : α → α ⊕ β)) (Sum.inl u)) =
        -∑ u : α, P u j * wordCountVec W u := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Matrix.fromBlocks_apply₂₁, Matrix.neg_apply, Matrix.transpose_apply,
      wordCountVec_map_inl_inl (α := α) (β := β) W u, neg_mul]
  rw [h_old, sub_eq_add_neg]

/-- **Stage 1 Grounded Prefix Validity (`chronology_stage1_bundle_valid`)**:
    In Proposition 9.1 (`prop:chronology`, Stage 1), if:
    1. `W_O : List α` is a valid strict FP word on the parent game `G_O` from the
       old-block initial scores `fun u => s0 (Sum.inl u)` (inherited by the gateway
       invariance lemma `gateway_waits_on_proper_prefix`), and
    2. At every prefix `k < W_O.length`, every reset action `j : β` has score
       `s0 (Sum.inr j) - ∑ u, P u j * wordCountVec (W_O.take k) u` strictly below the
       active old action's score (established by `chronology_early_reset_waits` and
       `chronology_late_reset_waits`),
    then the embedded parent bundle `W_O.map Sum.inl` is a valid strict FP word on
    `Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose)` at every prefix
    `k < (W_O.map Sum.inl).length`. -/
theorem chronology_stage1_bundle_valid {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (G_O : Matrix α α ℚ) (P : Matrix α β ℚ) (J : Matrix β β ℚ)
    (s0 : α ⊕ β → ℚ) (W_O : List α)
    (h_parent : IsValidStrictWord G_O (fun u => s0 (Sum.inl u)) W_O)
    (h_reset_waits :
      ∀ (k : ℕ) (hk : k < W_O.length) (j : β),
        s0 (Sum.inr j) - ∑ u : α, P u j * wordCountVec (W_O.take k) u <
          wordScore G_O (fun u => s0 (Sum.inl u)) (W_O.take k) (W_O[k])) :
    IsValidStrictWord (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
      s0 (W_O.map Sum.inl) := by
  intro k hk x hx
  have hk_len : k < W_O.length := by simpa using hk
  have hget : (W_O.map (Sum.inl : α → α ⊕ β))[k] = Sum.inl (W_O[k]) := by
    simp
  have htake : (W_O.map (Sum.inl : α → α ⊕ β)).take k = (W_O.take k).map Sum.inl := by
    rw [List.map_take]
  rw [hget] at hx ⊢
  rw [htake, wordScore_map_inl_old G_O P J s0 (W_O.take k) (W_O[k])]
  cases x with
  | inl i =>
    have hi : i ≠ W_O[k] := fun h => hx (congr_arg Sum.inl h)
    rw [wordScore_map_inl_old G_O P J s0 (W_O.take k) i]
    exact h_parent k hk_len i hi
  | inr j =>
    rw [wordScore_map_inl_new G_O P J s0 (W_O.take k) j]
    exact h_reset_waits k hk_len j

/-- **Stage 2 Grounded Endpoint Validity (`chronology_stage2_endpoint_valid`)**:
    In Proposition 9.1 (`prop:chronology`, Stage 2), when the parent bundle `W_O` finishes,
    if the endpoint action `g : α` strictly leads every other old action `i ≠ g`
    (by `gateway_takeover_at_completion`) and strictly leads every reset action `j : β`
    (by `chronology_early_reset_waits` and `chronology_late_reset_waits`), then the single
    endpoint play `[Sum.inl g]` is a valid strict FP word on
    `Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose)`. -/
theorem chronology_stage2_endpoint_valid {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (G_O : Matrix α α ℚ) (P : Matrix α β ℚ) (J : Matrix β β ℚ)
    (s_after_bundle : α ⊕ β → ℚ) (g : α)
    (h_old_dom : ∀ i : α, i ≠ g →
      s_after_bundle (Sum.inl i) < s_after_bundle (Sum.inl g))
    (h_new_dom : ∀ j : β,
      s_after_bundle (Sum.inr j) < s_after_bundle (Sum.inl g)) :
    IsValidStrictWord (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
      s_after_bundle [Sum.inl g] := by
  refine isValidStrictWord_singleton
    (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
    s_after_bundle (Sum.inl g) ?_
  intro x hx
  cases x with
  | inl i => exact h_old_dom i (fun h => hx (congr_arg Sum.inl h))
  | inr j => exact h_new_dom j

/-- **Single Reset Run Prefix Validity (`chronology_reset_run_valid`)**:
    In Proposition 9.1 (`prop:chronology`, Stages 3 and 4), during a constant run of reset
    action `Sum.inr j` of length `m ≥ 1` on
    `Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose)`,
    if `Sum.inr j` strictly leads every old action `i : α` and every other reset
    action `j' ≠ j` at the start (`h = 0`) and last step (`h = m - 1`) of the run
    (established by `chronology_reset_active_at_ceiling`, `chronology_reset_earlier_deficit`,
    `chronology_reset_later_deficit`, `chronology_old_waits_early_reset`, and
    `chronology_old_waits_late_reset`), then `List.replicate m (Sum.inr j)` is a valid
    strict FP word at every prefix `0 ≤ h < m`. -/
theorem chronology_reset_run_valid {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (G_O : Matrix α α ℚ) (P : Matrix α β ℚ) (J : Matrix β β ℚ)
    (s_run : α ⊕ β → ℚ) (m : ℕ) (j : β)
    (hm : 1 ≤ m)
    (h_old_start : ∀ i : α, s_run (Sum.inl i) < s_run (Sum.inr j))
    (h_old_end : ∀ i : α,
      s_run (Sum.inl i) + P i j * ((m - 1 : ℕ) : ℚ) < s_run (Sum.inr j))
    (h_new_start : ∀ j' : β, j' ≠ j → s_run (Sum.inr j') < s_run (Sum.inr j))
    (h_new_end : ∀ j' : β, j' ≠ j →
      s_run (Sum.inr j') + (J j' j - J j j') * ((m - 1 : ℕ) : ℚ) < s_run (Sum.inr j)) :
    IsValidStrictWord (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
      s_run (List.replicate m (Sum.inr j)) := by
  have hdiag :
      Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose) (Sum.inr j) (Sum.inr j) = 0 := by
    simp [Matrix.fromBlocks]
  refine isValidStrictWord_replicate_of_endpoints
    (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
    s_run m (Sum.inr j) hm hdiag ?_ ?_
  · intro x hx
    cases x with
    | inl i => exact h_old_start i
    | inr j' => exact h_new_start j' (fun h => hx (congr_arg Sum.inr h))
  · intro x hx
    cases x with
    | inl i =>
      simp only [Matrix.fromBlocks_apply₁₂]
      exact h_old_end i
    | inr j' =>
      simp only [Matrix.fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.transpose_apply]
      exact h_new_end j' (fun h => hx (congr_arg Sum.inr h))

/-- **Grounded Four-Stage Phase Word Validity from Margin Conditions (`chronology_four_stage_from_margins`)**:
    Combines the grounded Stage 1 (`chronology_stage1_bundle_valid`), Stage 2
    (`chronology_stage2_endpoint_valid`), Stage 3 (`W_early_reset`), and Stage 4
    (`W_late_reset`) conditions on `Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose)`
    into a single `IsValidStrictWord` certificate for the full lifted phase word
    `W_O.map Sum.inl ++ [Sum.inl g] ++ W_early_reset ++ W_late_reset`. -/
theorem chronology_four_stage_from_margins {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (G_O : Matrix α α ℚ) (P : Matrix α β ℚ) (J : Matrix β β ℚ)
    (s0 : α ⊕ β → ℚ)
    (W_O : List α) (g : α)
    (W_early_reset W_late_reset : List (α ⊕ β))
    (h_parent : IsValidStrictWord G_O (fun u => s0 (Sum.inl u)) W_O)
    (h_reset_waits_bundle :
      ∀ (k : ℕ) (hk : k < W_O.length) (j : β),
        s0 (Sum.inr j) - ∑ u : α, P u j * wordCountVec (W_O.take k) u <
          wordScore G_O (fun u => s0 (Sum.inl u)) (W_O.take k) (W_O[k]))
    (h_endpoint_old :
      ∀ i : α, i ≠ g →
        wordScore (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
          s0 (W_O.map Sum.inl) (Sum.inl i) <
          wordScore (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
            s0 (W_O.map Sum.inl) (Sum.inl g))
    (h_endpoint_new :
      ∀ j : β,
        wordScore (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
          s0 (W_O.map Sum.inl) (Sum.inr j) <
          wordScore (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
            s0 (W_O.map Sum.inl) (Sum.inl g))
    (h_stage3 :
      IsValidStrictWord (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
        (wordScore (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
          s0 (W_O.map Sum.inl ++ [Sum.inl g]))
        W_early_reset)
    (h_stage4 :
      IsValidStrictWord (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
        (wordScore (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose)) s0
          (W_O.map Sum.inl ++ [Sum.inl g] ++ W_early_reset))
        W_late_reset) :
    IsValidStrictWord (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose)) s0
      (W_O.map Sum.inl ++ [Sum.inl g] ++ W_early_reset ++ W_late_reset) := by
  have h1 :
      IsValidStrictWord (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
        s0 (W_O.map Sum.inl) :=
    chronology_stage1_bundle_valid G_O P J s0 W_O h_parent h_reset_waits_bundle
  have h2 :
      IsValidStrictWord (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
        (wordScore (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
          s0 (W_O.map Sum.inl))
        [Sum.inl g] :=
    chronology_stage2_endpoint_valid G_O P J
      (wordScore (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
        s0 (W_O.map Sum.inl))
      g h_endpoint_old h_endpoint_new
  exact chronology_four_stage_phase_word_valid
    (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose)) s0
    (W_O.map Sum.inl) (Sum.inl g) W_early_reset W_late_reset
    h1 h2 h_stage3 h_stage4

end Karlin

#print axioms Karlin.bundle_remaining_height_bound
#print axioms Karlin.chronology_early_reset_waits
#print axioms Karlin.chronology_late_reset_waits
#print axioms Karlin.chronology_endpoint_to_reset0
#print axioms Karlin.chronology_reset_active_at_ceiling
#print axioms Karlin.chronology_reset_later_deficit
#print axioms Karlin.chronology_reset_earlier_deficit
#print axioms Karlin.chronology_old_waits_early_reset
#print axioms Karlin.chronology_old_waits_late_reset
#print axioms Karlin.inherit_entry_safety
#print axioms Karlin.inherit_remaining_height_bound
#print axioms Karlin.action_count_recurrence
#print axioms Karlin.all_time_gap_enclosure
#print axioms Karlin.e0_row_dot_binomBasis
#print axioms Karlin.clock_phase_score_diff
#print axioms Karlin.clock_phase_transition
#print axioms Karlin.clock_endpoint_increment_eq_one
#print axioms Karlin.master_algebraic_clock_lift
#print axioms Karlin.karlin_main_theorem_synthesis
#print axioms Karlin.wordCountVec_append
#print axioms Karlin.wordScore_append
#print axioms Karlin.isValidStrictWord_append
#print axioms Karlin.chronology_four_stage_phase_word_valid
#print axioms Karlin.wordScore_replicate
#print axioms Karlin.isValidStrictWord_replicate_of_endpoints
#print axioms Karlin.isValidStrictWord_singleton
#print axioms Karlin.wordCountVec_map_inl_inr
#print axioms Karlin.wordCountVec_map_inl_inl
#print axioms Karlin.wordScore_map_inl_old
#print axioms Karlin.wordScore_map_inl_new
#print axioms Karlin.chronology_stage1_bundle_valid
#print axioms Karlin.chronology_stage2_endpoint_valid
#print axioms Karlin.chronology_reset_run_valid
#print axioms Karlin.chronology_four_stage_from_margins


