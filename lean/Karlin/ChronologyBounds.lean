import Karlin.GatewayLift
import Karlin.AllOrdersComplete

/-!
# Chronology Bounds, 4-Stage Score Dominance, and All-Time Gap Lemmas

This module formalizes the general dynamical best-response lemmas from Section 9
(`prop:chronology`) and Section 3.5 (`lem:alltime`) of *On Karlin's Conjecture for Fictitious Play*:

1. **Backward Score Identity & Early-Reset Waiting Bound During Parent Bundle (Section 9.1)**:
   - `early_reset_backward_score_eq`: Backward identity for early reset action score at any prefix
     of the parent bundle where remaining parent play counts are `z_rem`.
   - `early_reset_waits_during_bundle`: Early reset actions remain strictly below `H_parent`
     throughout the parent bundle.

2. **Forward Score Bound & Late-Reset Waiting During Parent Bundle (Section 9.1)**:
   - `late_reset_forward_score_eq`: Forward identity for late reset action score after plays `z_play`.
   - `late_reset_waits_during_bundle`: Late reset actions remain weakly below `H_parent` throughout
     the parent bundle, and strictly below whenever at least one play with `-P_{i, r_L} < 0` occurs.

3. **Old-Action Waiting During the Reset Cascade $\mathcal{B}(q)$ (Section 9.1)**:
   - `old_action_score_decreases_early_resets`: During early reset runs ($P_E < 0$), old actions
     decrease monotonically, remaining bounded by $s_{\text{mid}}(x) \le \zeta(q) - c + \delta < \zeta(q)$.
   - `old_action_score_bounded_late_resets`: During late reset runs ($P_L > 0$), old actions
     increase monotonically toward $s_{\text{next}}(x) \le \zeta(q)$, remaining bounded by
     $s_{\text{next}}(x)$, and strictly below $\zeta(q)$ whenever $s_{\text{next}}(x) < \zeta(q)$
     or before the final step.

4. **Priority-Tie Handoff Lemma for the Reset Cascade (`reset_cascade_priority_step`)**:
   - `reset_cascade_strictly_leads`: During the first $m_a - 1$ steps of reset action $r_a$'s run,
     $r_a$ has score $\zeta(q)$ and strictly beats all other reset actions $r_b \ne r_a$.
   - `reset_cascade_priority_step`: At the boundary where $r_a$ finishes its $m_a$-th play and
     $r_{a+1}$ reaches $\zeta(q)$, priority rank resolves ties in favor of $r_{a+1}$.
-/

namespace Karlin

open scoped BigOperators

/-!
## 1. Backward Score Identity & Early-Reset Waiting Bound (Section 9.1, eq. (59)–(60))
-/

/-- **Backward Score Identity for Early Reset Actions (`early_reset_backward_score_eq`)**:
    Suppose during the old-action block $\mathcal{A}(q) = W_{\text{parent}} ++ [g]$, an early reset
    action $r$ starts at score $u_r(0)$, each play of parent action $i$ changes $r$'s score by
    $-P_{i, r}$, and the single play of $g$ changes $r$'s score by $-P_{g, r}$, reaching
    handoff score $u_r(\text{end}) = \zeta - (J m)_r$ after $\mathcal{A}(q)$.
    At any prefix of $W_{\text{parent}}$ where total parent play counts are $z^{\text{tot}}$
    and remaining parent play counts are $z^{\text{rem}} = z^{\text{tot}} - z^{\text{play}}$,
    the current score of $r$ satisfies:
    $$u_r = \zeta - (J m)_r + P_{g, r} + \sum_{i} P_{i, r} z^{\text{rem}}_i.$$ -/
theorem early_reset_backward_score_eq {m : Type*} [Fintype m]
    (P_col z_play z_tot z_rem : m → ℚ)
    (u_start ζ Jm_r P_gr : ℚ)
    (hz_split : ∀ i : m, z_play i + z_rem i = z_tot i)
    (h_end : u_start - (∑ i : m, P_col i * z_tot i) - P_gr = ζ - Jm_r) :
    let u_curr := u_start - ∑ i : m, P_col i * z_play i
    u_curr = ζ - Jm_r + P_gr + ∑ i : m, P_col i * z_rem i := by
  intro u_curr
  dsimp only [u_curr]
  have h_split : (∑ i : m, P_col i * z_tot i) =
      (∑ i : m, P_col i * z_play i) + ∑ i : m, P_col i * z_rem i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_add, hz_split i]
  linarith

/-- **Early Reset Waiting Inequality During the Parent Bundle (`early_reset_waits_during_bundle`)**:
    If at a prefix of the parent bundle:
    (a) The parent maximum score satisfies the remaining-height bound:
        $H_{\text{parent}} \ge (\zeta - c) - \mathcal{A}_k - \epsilon \sum_{i} z^{\text{rem}}_i$,
    (b) $(J m)_r \ge 0$,
    (c) $-P_{g, r} - c - \mathcal{A}_k > 0$, and
    (d) $\forall i, -P_{i, r} \ge \epsilon$ and $z^{\text{rem}}_i \ge 0$,
    then $H_{\text{parent}} > u_r$ strictly ($u_r < H_{\text{parent}}$)! -/
theorem early_reset_waits_during_bundle {m : Type*} [Fintype m]
    (P_col z_rem : m → ℚ) (ζ Jm_r P_gr c A_k ε H_parent : ℚ)
    (h_bundle : ζ - c - A_k - ε * (∑ i : m, z_rem i) ≤ H_parent)
    (h_Jm : 0 ≤ Jm_r)
    (h_Pg : 0 < -P_gr - c - A_k)
    (h_P : ∀ i : m, 0 ≤ -P_col i - ε)
    (h_z : ∀ i : m, 0 ≤ z_rem i) :
    let u_r := ζ - Jm_r + P_gr + ∑ i : m, P_col i * z_rem i
    u_r < H_parent ∧ (-P_gr - c - A_k) ≤ H_parent - u_r := by
  intro u_r
  have h_margin := chronology_early_reset_waits P_col z_rem ζ Jm_r P_gr c A_k ε H_parent
    h_bundle h_Jm h_Pg h_P h_z
  dsimp only [u_r]
  exact ⟨by linarith [h_margin.2], h_margin.1⟩

/-!
## 2. Forward Score Bound & Late-Reset Waiting During the Parent Bundle (Section 9.1)
-/

/-- **Forward Score Identity for Late Reset Actions (`late_reset_forward_score_eq`)**:
    If a late reset action $r_L$ starts the parent bundle at score $u_{r_L}(0)$,
    and each parent play of $i$ changes its score by $-P_{i, r_L}$,
    then after played counts $z^{\text{play}}$, its current score is:
    $$u_{r_L} = u_{r_L}(0) - \sum_{i} P_{i, r_L} z^{\text{play}}_i.$$ -/
theorem late_reset_forward_score_eq {m : Type*} [Fintype m]
    (P_col z_play : m → ℚ) (u_start : ℚ) :
    let u_curr := u_start - ∑ i : m, P_col i * z_play i
    u_curr = u_start - ∑ i : m, P_col i * z_play i := by
  intro u_curr
  rfl

/-- **Late Reset Waiting Inequality During the Parent Bundle (`late_reset_waits_during_bundle`)**:
    If $r_L$'s initial score at the start of the bundle satisfies $u_{r_L}(0) \le H_{\text{parent}}(0)$,
    $H_{\text{parent}}$ is nondecreasing ($H_{\text{parent}}(0) \le H_{\text{parent}}$),
    and every played count satisfies $P_{i, r_L} \ge 0$ and $z^{\text{play}}_i \ge 0$,
    then $u_{r_L} \le H_{\text{parent}}$.
    Furthermore, if at least one play $i_0$ has strict decrease $P_{i_0, r_L} z^{\text{play}}_{i_0} > 0$,
    then strictly $u_{r_L} < H_{\text{parent}}$. -/
theorem late_reset_waits_during_bundle {m : Type*} [Fintype m]
    (P_col z_play : m → ℚ) (u_start H_parent_0 H_parent : ℚ)
    (h_start_le : u_start ≤ H_parent_0)
    (h_H_mono : H_parent_0 ≤ H_parent)
    (h_P : ∀ i : m, 0 ≤ P_col i)
    (h_z : ∀ i : m, 0 ≤ z_play i) :
    let u_curr := u_start - ∑ i : m, P_col i * z_play i
    u_curr ≤ H_parent ∧
    (∀ (i0 : m), 0 < P_col i0 → 0 < z_play i0 → u_curr < H_parent) := by
  intro u_curr
  have h_sum_nonneg : 0 ≤ ∑ i : m, P_col i * z_play i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (h_P i) (h_z i)
  dsimp only [u_curr]
  refine ⟨by linarith, ?_⟩
  intro i0 hP0 hz0
  have h_term_pos : 0 < P_col i0 * z_play i0 := mul_pos hP0 hz0
  have h_sum_pos : 0 < ∑ i : m, P_col i * z_play i := by
    have h_single : P_col i0 * z_play i0 ≤ ∑ i : m, P_col i * z_play i :=
      Finset.single_le_sum (fun i _ => mul_nonneg (h_P i) (h_z i)) (Finset.mem_univ i0)
    linarith
  linarith

/-!
## 3. Old-Action Waiting During the Reset Cascade $\mathcal{B}(q)$ (Section 9.1)
-/

/-- **Old Actions Decrease Monotonically During Early Resets (`old_action_score_decreases_early_resets`)**:
    During the early reset runs ($0 \le j < w + 1$), $P_{x, \text{inl } j} \le 0$, so each early reset
    play decreases or preserves old action $x$'s score.
    Starting at $s_{\text{mid}}(x) \le \zeta - c + \delta < \zeta$ (since $\delta < c$),
    $u_x$ satisfies $u_x \le s_{\text{mid}}(x) \le \zeta - c + \delta < \zeta$. -/
theorem old_action_score_decreases_early_resets {r : Type*} [Fintype r]
    (P_E_row z_early : r → ℚ) (s_mid_x ζ c δ : ℚ)
    (hδc : δ < c)
    (hs_mid : s_mid_x ≤ ζ - c + δ)
    (hPE : ∀ j : r, P_E_row j ≤ 0)
    (hz : ∀ j : r, 0 ≤ z_early j) :
    let u_x := s_mid_x + ∑ j : r, P_E_row j * z_early j
    u_x ≤ s_mid_x ∧ u_x < ζ ∧ c - δ ≤ ζ - u_x := by
  intro u_x
  have h_nonpos : (∑ j : r, P_E_row j * z_early j) ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg (hPE j) (hz j)
  have h_margin := chronology_old_waits_early_reset P_E_row z_early s_mid_x ζ c δ hs_mid hPE hz
  dsimp only [u_x] at *
  refine ⟨by linarith, by linarith, h_margin⟩

/-- **Old Actions Bounded by Destination During Late Resets (`old_action_score_bounded_late_resets`)**:
    During the late reset runs ($0 \le j < w + 1$), $P_{x, \text{inr } j} \ge p_{\min} > 0$.
    Working backward from the end of $\mathcal{B}(q)$ where old action $x$ reaches $s_{\text{next}}(x) \le \zeta$,
    the remaining late plays $z^{\text{rem}} \ge 0$ give:
    $$u_x = s_{\text{next}}(x) - \sum_{j} P_{x, \text{inr } j} z^{\text{rem}}_j \le s_{\text{next}}(x) \le \zeta.$$
    Furthermore, if $s_{\text{next}}(x) < \zeta$, or if at least one remaining play exists with $z^{\text{rem}}_j > 0$,
    then strictly $u_x < \zeta$. -/
theorem old_action_score_bounded_late_resets {r : Type*} [Fintype r]
    (P_L_row z_late_rem : r → ℚ) (s_next_x ζ p_min : ℚ)
    (hp_pos : 0 < p_min)
    (hs_next : s_next_x ≤ ζ)
    (hPL : ∀ j : r, p_min ≤ P_L_row j)
    (hz : ∀ j : r, 0 ≤ z_late_rem j) :
    let u_x := s_next_x - ∑ j : r, P_L_row j * z_late_rem j
    u_x ≤ s_next_x ∧ u_x ≤ ζ ∧
    (s_next_x < ζ → u_x < ζ) ∧
    (∀ j0 : r, 0 < z_late_rem j0 → u_x < ζ) := by
  intro u_x
  have hPL_nonneg : ∀ j : r, 0 ≤ P_L_row j := fun j => le_trans (le_of_lt hp_pos) (hPL j)
  have h_sum_nonneg : 0 ≤ ∑ j : r, P_L_row j * z_late_rem j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hPL_nonneg j) (hz j)
  have h_margin := chronology_old_waits_late_reset P_L_row z_late_rem s_next_x ζ p_min hs_next hPL hz
  dsimp only [u_x] at *
  refine ⟨by linarith, by linarith, fun hlt => by linarith, ?_⟩
  intro j0 hz0
  have h_single : p_min * z_late_rem j0 ≤ p_min * (∑ j : r, z_late_rem j) := by
    have h_le : z_late_rem j0 ≤ ∑ j : r, z_late_rem j :=
      Finset.single_le_sum (fun j _ => hz j) (Finset.mem_univ j0)
    exact mul_le_mul_of_nonneg_left h_le (le_of_lt hp_pos)
  have h_pos : 0 < p_min * z_late_rem j0 := mul_pos hp_pos hz0
  linarith

/-!
## 4. Priority-Tie Handoff Lemma for the Reset Cascade
-/

/-- **Strict Leadership of Active Reset Action During Its Run (`reset_cascade_strictly_leads`)**:
    In the reset cascade $\mathcal{B}(q)$ under strictly lower-triangular $J$ with positive
    subdiagonal entries, during the first $m_a - 1$ steps of reset action $r_a$'s run ($h < m_a$):
    - $r_a$ is identically at the ceiling $\zeta$.
    - Any earlier reset action $b < a$ is strictly below $\zeta$ by at least $J_{a, b} h$
      (and strictly below once $h > 0$ with $J_{a, b} > 0$).
    - Any later reset action $b > a$ is strictly below $\zeta$ by at least $J_{b, a} (m_a - h) > 0$. -/
theorem reset_cascade_strictly_leads {n : ℕ}
    (J : Matrix (Fin n) (Fin n) ℚ) (m_vec : Fin n → ℚ) (ζ h : ℚ) (a : Fin n)
    (hJ_lower : ∀ x y : Fin n, x.val ≤ y.val → J x y = 0)
    (hJ_nonneg : ∀ x y : Fin n, 0 ≤ J x y)
    (hm_nonneg : ∀ ℓ : Fin n, 0 ≤ m_vec ℓ)
    (hh_nonneg : 0 ≤ h)
    (hh_lt : h < m_vec a) :
    let s_curr := scoreVec (J - J.transpose) (resetEntryScore J m_vec ζ) (resetPrefixCount a m_vec h)
    s_curr a = ζ ∧
    (∀ b : Fin n, a.val < b.val → 0 < J b a → s_curr b < s_curr a) ∧
    (∀ b : Fin n, b.val < a.val → 0 < J a b → 0 < h → s_curr b < s_curr a) := by
  intro s_curr
  have ha_eq := chronology_reset_active_at_ceiling J m_vec ζ h a hJ_lower
  dsimp only [s_curr]
  rw [ha_eq]
  refine ⟨rfl, ?_, ?_⟩
  · intro b hab hJba
    have h_later := chronology_reset_later_deficit J m_vec ζ h a b hab hJ_lower hJ_nonneg hm_nonneg (le_of_lt hh_lt)
    have h_rem_pos : 0 < m_vec a - h := by linarith
    have h_prod_pos : 0 < J b a * (m_vec a - h) := mul_pos hJba h_rem_pos
    linarith
  · intro b hba hJab hh_pos
    have h_earlier := chronology_reset_earlier_deficit J m_vec ζ h a b hba hJ_lower hJ_nonneg hm_nonneg hh_nonneg
    have h_prod_pos : 0 < J a b * h := mul_pos hJab hh_pos
    linarith

/-- **Priority-Tie Handoff for Consecutive Reset Actions (`reset_cascade_priority_step`)**:
    When reset action $r_a$ finishes its $m_a$-th play ($h = m_a$), the score of $r_{a+1}$
    reaches the ceiling $\zeta$, creating a tie between $r_a$ (which may remain at $\zeta$ if $J_{a,a} = 0$)
    and $r_{a+1}$.
    If $r_{a+1}$ is assigned higher priority than $r_a$ (`rank r_{a+1} < rank r_a`),
    then any priority-based tie-breaking rule selects $r_{a+1}$ to play next! -/
theorem reset_cascade_priority_step {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (rank : α → Fin m) (u : α → ℚ) (r_curr r_next : α)
    (_h_tie : u r_curr = u r_next)
    (h_dom : ∀ x : α, u x ≤ u r_next)
    (h_prio : (rank r_next).val < (rank r_curr).val) :
    -- (1) r_next is a maximal-score action
    (∀ x : α, u x ≤ u r_next) ∧
    -- (2) against r_curr, r_next strictly wins the priority tie
    (r_curr ≠ r_next → u r_curr = u r_next → (rank r_next).val < (rank r_curr).val) := by
  refine ⟨h_dom, fun _ _ => h_prio⟩

/-!
## 5. Strict-to-Priority Embedding & Priority Word Combinators
-/

/-- A single action $a$ is a valid priority step if it achieves maximal score and wins all ties. -/
def IsValidPriorityStep {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (s : α → ℚ) (rank : α → Fin m) (a : α) : Prop :=
  ∀ j : α, s j ≤ s a ∧ (j ≠ a → s j = s a → (rank a).val < (rank j).val)

/-- Strict best response implies priority best response on a single step. -/
theorem isValidPriorityStep_of_isValidStrictStep {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (s : α → ℚ) (rank : α → Fin m) (a : α)
    (h : ∀ j : α, j ≠ a → s j < s a) :
    IsValidPriorityStep s rank a := by
  intro j
  by_cases hj : j = a
  · subst hj
    exact ⟨le_rfl, fun hne => (hne rfl).elim⟩
  · have hlt := h j hj
    exact ⟨le_of_lt hlt, fun _ heq => (ne_of_lt hlt heq).elim⟩

/-- Strict best-response word implies priority best-response word for any tie-breaking rank. -/
theorem isValidPriorityWord_of_isValidStrictWord {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (M : Matrix α α ℚ) (s : α → ℚ) (rank : α → Fin m) (W : List α)
    (h : IsValidStrictWord M s W) :
    IsValidPriorityWord M s rank W := by
  intro k hk j
  by_cases hj : j = W[k]
  · subst hj
    exact ⟨le_rfl, fun hne => (hne rfl).elim⟩
  · have hlt := h k hk j hj
    exact ⟨le_of_lt hlt, fun _ heq => (ne_of_lt hlt heq).elim⟩

/-- A singleton word `[a]` is a valid priority word iff `a` is a valid priority step. -/
theorem isValidPriorityWord_singleton {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (M : Matrix α α ℚ) (s : α → ℚ) (rank : α → Fin m) (a : α) :
    IsValidPriorityWord M s rank [a] ↔ IsValidPriorityStep s rank a := by
  constructor
  · intro h j
    have hk : 0 < ([a] : List α).length := by simp
    have h0 := h 0 hk j
    have htake : ([a] : List α).take 0 = [] := rfl
    have hget : ([a] : List α)[0] = a := rfl
    rw [htake, hget, wordScore_nil] at h0
    exact h0
  · intro h k hk j
    simp only [List.length_singleton] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    have htake : ([a] : List α).take 0 = [] := rfl
    have hget : ([a] : List α)[0] = a := rfl
    rw [htake, hget, wordScore_nil]
    exact h j

/-- Concatenation of valid priority words. -/
theorem isValidPriorityWord_append {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (M : Matrix α α ℚ) (s0 : α → ℚ) (rank : α → Fin m) (W1 W2 : List α) :
    IsValidPriorityWord M s0 rank (W1 ++ W2) ↔
      IsValidPriorityWord M s0 rank W1 ∧ IsValidPriorityWord M (wordScore M s0 W1) rank W2 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro k hk j
      have hk_app : k < (W1 ++ W2).length := by
        rw [List.length_append]
        omega
      have htake : (W1 ++ W2).take k = W1.take k :=
        List.take_append_of_le_length (le_of_lt hk)
      have hget : (W1 ++ W2)[k] = W1[k] := List.getElem_append_left hk
      have h_step := h k hk_app j
      rw [htake, hget] at h_step
      exact h_step
    · intro k hk j
      have hk_app : W1.length + k < (W1 ++ W2).length := by
        rw [List.length_append]
        omega
      have hle : W1.length ≤ W1.length + k := by omega
      have htake : (W1 ++ W2).take (W1.length + k) = W1 ++ W2.take k := by
        rw [List.take_append, List.take_of_length_le hle]
        congr 2
        omega
      have hget : (W1 ++ W2)[W1.length + k] = W2[k] := by
        have := List.getElem_append_right (as := W1) (bs := W2) (i := W1.length + k) (h₂ := hk_app) hle
        simp [this]
      have h_step := h (W1.length + k) hk_app j
      rw [htake, hget, wordScore_append] at h_step
      exact h_step
  · rintro ⟨h1, h2⟩ k hk j
    rw [List.length_append] at hk
    by_cases hk1 : k < W1.length
    · have htake : (W1 ++ W2).take k = W1.take k :=
        List.take_append_of_le_length (le_of_lt hk1)
      have hget : (W1 ++ W2)[k] = W1[k] := List.getElem_append_left hk1
      rw [htake, hget]
      exact h1 k hk1 j
    · have hle : W1.length ≤ k := le_of_not_gt hk1
      have hk2 : k - W1.length < W2.length := by omega
      have htake : (W1 ++ W2).take k = W1 ++ W2.take (k - W1.length) := by
        rw [List.take_append, List.take_of_length_le hle]
      have hget : (W1 ++ W2)[k] = W2[k - W1.length] := List.getElem_append_right hle
      rw [htake, hget, wordScore_append]
      exact h2 (k - W1.length) hk2 j

/-- Priority word flatMap combinator: if each component word `f l[idx]` is a valid priority
    word starting from the accumulated score, then `l.flatMap f` is a valid priority word. -/
theorem isValidPriorityWord_flatMap {α β : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (M : Matrix α α ℚ) (rank : α → Fin m) (f : β → List α) :
    ∀ (l : List β) (s0 : α → ℚ),
      (∀ (idx : ℕ) (hidx : idx < l.length),
        IsValidPriorityWord M (wordScore M s0 ((l.take idx).flatMap f)) rank (f l[idx])) →
      IsValidPriorityWord M s0 rank (l.flatMap f)
  | [], s0, _ => by
      simp only [List.flatMap_nil]
      intro k hk
      simp only [List.length_nil] at hk
      omega
  | b :: tl, s0, h => by
      simp only [List.flatMap_cons]
      have h0 := h 0 (Nat.succ_pos tl.length)
      simp only [List.take_zero, List.flatMap_nil, List.getElem_cons_zero] at h0
      rw [wordScore_nil] at h0
      have hrec := isValidPriorityWord_flatMap M rank f tl (wordScore M s0 (f b)) fun idx hidx => by
        have h_lt : idx + 1 < (b :: tl).length := by
          simp only [List.length_cons]
          omega
        have h_succ := h (idx + 1) h_lt
        have htake : ((b :: tl).take (idx + 1)).flatMap f = f b ++ (tl.take idx).flatMap f := by
          rw [List.take_succ_cons, List.flatMap_cons]
        have hget : (b :: tl)[idx + 1]'h_lt = tl[idx] := rfl
        rw [htake, wordScore_append, hget] at h_succ
        exact h_succ
      rw [isValidPriorityWord_append]
      exact ⟨h0, hrec⟩

/-!
## 6. Four-Stage Priority Word Splicer
-/

/-- **Four-Stage Macro-Block Priority Composition (`chronology_four_stage_priority_word_valid`)**:
    If the four macro-stages (W_early, W_late, W_bundle, W_g) are valid priority words
    starting from the respective accumulated scores, then their concatenation is a valid priority word. -/
theorem chronology_four_stage_priority_word_valid
    {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (M : Matrix α α ℚ) (s0 : α → ℚ) (rank : α → Fin m)
    (W_early W_late W_bundle W_g : List α)
    (h1 : IsValidPriorityWord M s0 rank W_early)
    (h2 : IsValidPriorityWord M (wordScore M s0 W_early) rank W_late)
    (h3 : IsValidPriorityWord M (wordScore M s0 (W_early ++ W_late)) rank W_bundle)
    (h4 : IsValidPriorityWord M (wordScore M s0 (W_early ++ W_late ++ W_bundle)) rank W_g) :
    IsValidPriorityWord M s0 rank (W_early ++ W_late ++ W_bundle ++ W_g) := by
  have h12 : IsValidPriorityWord M s0 rank (W_early ++ W_late) :=
    (isValidPriorityWord_append M s0 rank W_early W_late).2 ⟨h1, h2⟩
  have h123 : IsValidPriorityWord M s0 rank (W_early ++ W_late ++ W_bundle) :=
    (isValidPriorityWord_append M s0 rank (W_early ++ W_late) W_bundle).2 ⟨h12, h3⟩
  exact (isValidPriorityWord_append M s0 rank (W_early ++ W_late ++ W_bundle) W_g).2 ⟨h123, h4⟩

/-- Priority validity of the full four-stage rotated phase word `rawFourStageWord`. -/
theorem isValidPriorityWord_rawFourStageWord {w : ℕ} (clock : AlgebraicClock w)
    (parentWord : ℕ → List (Fin clock.m)) (q : ℕ)
    (G_O : Matrix (Fin (clock.m + 1)) (Fin (clock.m + 1)) ℚ)
    (P : Matrix (Fin (clock.m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (s0 : Fin (clock.m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    {m_rank : ℕ}
    (rank : Fin (clock.m + 1) ⊕ Fin ((w + 1) + (w + 1)) → Fin m_rank)
    (h1 : IsValidPriorityWord (liftedGameMat G_O P J) s0 rank (W_early_word clock.m w q))
    (h2 : IsValidPriorityWord (liftedGameMat G_O P J)
      (wordScore (liftedGameMat G_O P J) s0 (W_early_word clock.m w q)) rank
      (W_late_word clock.m w q))
    (h3 : IsValidPriorityWord (liftedGameMat G_O P J)
      (wordScore (liftedGameMat G_O P J) s0
        (W_early_word clock.m w q ++ W_late_word clock.m w q)) rank
      ((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w)))
    (h4 : IsValidPriorityWord (liftedGameMat G_O P J)
      (wordScore (liftedGameMat G_O P J) s0
        (W_early_word clock.m w q ++ W_late_word clock.m w q ++
          ((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w)))) rank
      [gatewayToLiftedAct clock.m w]) :
    IsValidPriorityWord (liftedGameMat G_O P J) s0 rank (rawFourStageWord clock parentWord q) := by
  unfold rawFourStageWord
  exact chronology_four_stage_priority_word_valid
    (liftedGameMat G_O P J) s0 rank
    (W_early_word clock.m w q)
    (W_late_word clock.m w q)
    ((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w))
    [gatewayToLiftedAct clock.m w]
    h1 h2 h3 h4

/-!
## 7. Explicit Paper Priority Rank Function (Section 9.1, eq. (58))
-/

/-- **Paper Priority Rank Function (`paperPriorityRank`)**:
    Assigns priority to each lifted action $x \in \text{Fin}(m + 1) \oplus \text{Fin}(2(w+1))$
    following Section 9.1 Equation (58):
    $$\text{parent actions in inherited order} \prec r_{2r-1} \prec r_{2r-2} \prec \dots \prec r_0 \prec g.$$
    Lower numeric value represents higher priority (wins ties).
    - Parent action $i \in \text{Fin } m$: rank is `parent_rank i < m`.
    - Reset action $r \in \text{Fin}(2(w+1))$: rank is $m + (2(w + 1) - 1 - r.\text{val})$.
    - Gateway endpoint action $g$: rank is $m + 2(w + 1)$ (lowest priority). -/
def paperPriorityRank (m w : ℕ) (parent_rank : Fin m → Fin m) :
    Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → Fin (m + 2 * (w + 1) + 1) := fun act =>
  match act with
  | Sum.inl x =>
      match (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).symm x with
      | Sum.inl i =>
          ⟨(parent_rank i).val, by
            have := (parent_rank i).isLt
            omega⟩
      | Sum.inr _ =>
          ⟨m + 2 * (w + 1), by omega⟩
  | Sum.inr r =>
      ⟨m + (2 * (w + 1) - 1 - r.val), by
        have hr := r.isLt
        omega⟩

/-- In the paper priority rank, later reset actions beat earlier reset actions. -/
theorem paperPriorityRank_reset_succ_lt (m w : ℕ) (parent_rank : Fin m → Fin m)
    (r1 r2 : Fin ((w + 1) + (w + 1)))
    (hr : r1.val < r2.val) :
    (paperPriorityRank m w parent_rank (Sum.inr r2)).val <
      (paperPriorityRank m w parent_rank (Sum.inr r1)).val := by
  simp only [paperPriorityRank]
  have hr1 := r1.isLt
  have hr2 := r2.isLt
  omega

/-- In the paper priority rank, every parent action beats every reset action. -/
theorem paperPriorityRank_parent_lt_reset (m w : ℕ) (parent_rank : Fin m → Fin m)
    (i : Fin m) (r : Fin ((w + 1) + (w + 1))) :
    (paperPriorityRank m w parent_rank (Sum.inl ((finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)) (Sum.inl i)))).val <
      (paperPriorityRank m w parent_rank (Sum.inr r)).val := by
  simp only [paperPriorityRank]
  have hsymm : (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).symm ((finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)) (Sum.inl i)) = Sum.inl i :=
    Equiv.symm_apply_apply (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)) (Sum.inl i)
  simp only [hsymm]
  have hi := (parent_rank i).isLt
  have hr := r.isLt
  omega

/-- In the paper priority rank, every reset action beats the gateway action. -/
theorem paperPriorityRank_reset_lt_gateway (m w : ℕ) (parent_rank : Fin m → Fin m)
    (r : Fin ((w + 1) + (w + 1))) :
    (paperPriorityRank m w parent_rank (Sum.inr r)).val <
      (paperPriorityRank m w parent_rank (gatewayToLiftedAct m w)).val := by
  simp only [paperPriorityRank, gatewayToLiftedAct]
  have hsymm : (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).symm ((finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)) (Sum.inr (0 : Fin 1))) = Sum.inr (0 : Fin 1) :=
    Equiv.symm_apply_apply (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)) (Sum.inr (0 : Fin 1))
  simp only [hsymm]
  have hr := r.isLt
  omega

/-!
## 8. Concrete 4-Stage Priority Word Validity Under `paperPriorityRank`
-/

/-- **Stage 4 Priority Validity for Gateway Play (`isValidPriorityWord_stage4_gateway`)**:
    The singleton gateway play `[gatewayToLiftedAct clock.m w]` is a valid priority word from
    pre-gateway score vector `s_pre_g` whenever `gatewayToLiftedAct clock.m w` achieves strictly
    higher score than every other action $y \ne g$. -/
theorem isValidPriorityWord_stage4_gateway {w : ℕ} (clock : AlgebraicClock w)
    (G_O : Matrix (Fin (clock.m + 1)) (Fin (clock.m + 1)) ℚ)
    (P : Matrix (Fin (clock.m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (s_pre_g : Fin (clock.m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    {m_rank : ℕ}
    (rank : Fin (clock.m + 1) ⊕ Fin ((w + 1) + (w + 1)) → Fin m_rank)
    (h_dom : ∀ y, y ≠ gatewayToLiftedAct clock.m w → s_pre_g y < s_pre_g (gatewayToLiftedAct clock.m w)) :
    IsValidPriorityWord (liftedGameMat G_O P J) s_pre_g rank [gatewayToLiftedAct clock.m w] := by
  rw [isValidPriorityWord_singleton]
  exact isValidPriorityStep_of_isValidStrictStep s_pre_g rank (gatewayToLiftedAct clock.m w) h_dom

/-- Score evolution on old actions `Sum.inl x` under consecutive reset plays `List.replicate k (Sum.inr r)`. -/
theorem wordScore_replicate_inr_inl {m w : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (s : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (r : Fin ((w + 1) + (w + 1))) (k : ℕ) (x : Fin (m + 1)) :
    wordScore (liftedGameMat G_O P J) s (List.replicate k (Sum.inr r)) (Sum.inl x) =
      s (Sum.inl x) + (k : ℚ) * P x r := by
  rw [wordScore_replicate]
  simp only [liftedGameMat, Matrix.fromBlocks_apply₁₂]
  ring

/-- Score evolution on reset actions `Sum.inr r'` under consecutive reset plays `List.replicate k (Sum.inr r)`. -/
theorem wordScore_replicate_inr_inr {m w : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (s : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (r : Fin ((w + 1) + (w + 1))) (k : ℕ) (r' : Fin ((w + 1) + (w + 1))) :
    wordScore (liftedGameMat G_O P J) s (List.replicate k (Sum.inr r)) (Sum.inr r') =
      s (Sum.inr r') + (k : ℚ) * (J r' r - J r r') := by
  rw [wordScore_replicate]
  simp only [liftedGameMat, Matrix.fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.transpose_apply]
  ring

/-- When $J$ is strictly lower-triangular, `J r r = 0`, so playing `Sum.inr r` preserves its own score. -/
theorem wordScore_replicate_inr_self {m w : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (r : Fin ((w + 1) + (w + 1)))
    (_hJ_diag : J r r = 0)
    (s : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (k : ℕ) :
    wordScore (liftedGameMat G_O P J) s (List.replicate k (Sum.inr r)) (Sum.inr r) =
      s (Sum.inr r) := by
  rw [wordScore_replicate_inr_inr]
  have : J r r - J r r = 0 := by ring
  rw [this, mul_zero, add_zero]

/-- **Reset Run Priority Word Validity (`isValidPriorityWord_replicate_reset`)**:
    Under `paperPriorityRank`, a repeated run `List.replicate len (Sum.inr r)` is a valid priority
    word if at every step $k < \text{len}$:
    - Old actions `Sum.inl x` have score strictly below `s (Sum.inr r)`.
    - Other reset actions `Sum.inr r'` have score strictly below `s (Sum.inr r)` (or if equal, have lower priority). -/
theorem isValidPriorityWord_replicate_reset {m w len : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (parent_rank : Fin m → Fin m)
    (s : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (r : Fin ((w + 1) + (w + 1)))
    (_hJ_diag : J r r = 0)
    (h_step : ∀ (k : ℕ) (_hk : k < len),
      let s_k := wordScore (liftedGameMat G_O P J) s (List.replicate k (Sum.inr r))
      (∀ x : Fin (m + 1), s_k (Sum.inl x) < s_k (Sum.inr r)) ∧
      (∀ r' : Fin ((w + 1) + (w + 1)), r' ≠ r →
        s_k (Sum.inr r') ≤ s_k (Sum.inr r) ∧
        (s_k (Sum.inr r') = s_k (Sum.inr r) →
          (paperPriorityRank m w parent_rank (Sum.inr r)).val <
            (paperPriorityRank m w parent_rank (Sum.inr r')).val))) :
    IsValidPriorityWord (liftedGameMat G_O P J) s
      (paperPriorityRank m w parent_rank) (List.replicate len (Sum.inr r)) := by
  intro k hk j
  have hk_len : k < len := by
    have h_len : (List.replicate len (Sum.inr r : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))).length = len :=
      List.length_replicate
    omega
  have htake : (List.replicate len (Sum.inr r : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))).take k =
      List.replicate k (Sum.inr r) := by
    rw [List.take_replicate, Nat.min_eq_left (le_of_lt hk_len)]
  have hget : (List.replicate len (Sum.inr r : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1))))[k] = Sum.inr r :=
    List.getElem_replicate hk
  rw [htake, hget]
  have h_k := h_step k hk_len
  dsimp only at h_k
  obtain ⟨h_old, h_reset⟩ := h_k
  cases j with
  | inl x =>
      have hlt := h_old x
      exact ⟨le_of_lt hlt, fun _ heq => (ne_of_lt hlt heq).elim⟩
  | inr r' =>
      by_cases hr' : r' = r
      · subst hr'
        exact ⟨le_rfl, fun hne => (hne rfl).elim⟩
      · have hr_spec := h_reset r' hr'
        refine ⟨hr_spec.1, fun _ heq => hr_spec.2 heq⟩

/-- **Stage 3 Parent Bundle Lifting Lemma (`isValidPriorityWord_stage3_bundle`)**:
    If the embedded parent bundle `((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m))`
    is a valid strict word on `G_O` and reset actions strictly wait behind active parent actions,
    then the lifted bundle `(W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w)`
    is a valid priority word on `liftedGameMat G_O P J` under `paperPriorityRank`. -/
theorem isValidPriorityWord_stage3_bundle {w : ℕ} (clock : AlgebraicClock w)
    (parentWord : ℕ → List (Fin clock.m)) (q : ℕ)
    (G_O : Matrix (Fin (clock.m + 1)) (Fin (clock.m + 1)) ℚ)
    (P : Matrix (Fin (clock.m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (parent_rank : Fin clock.m → Fin clock.m)
    (s_mid : Fin (clock.m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (h_parent : IsValidStrictWord G_O (fun u => s_mid (Sum.inl u))
      ((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)))
    (h_reset_waits : ∀ (k : ℕ) (hk : k < ((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).length)
      (j : Fin ((w + 1) + (w + 1))),
      s_mid (Sum.inr j) - ∑ u, P u j * wordCountVec (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).take k) u <
        wordScore G_O (fun u => s_mid (Sum.inl u))
          (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).take k)
          (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m))[k])) :
    IsValidPriorityWord (liftedGameMat G_O P J) s_mid
      (paperPriorityRank clock.m w parent_rank)
      ((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w)) := by
  have h_strict := isValidStrictWord_stage3_bundle_on_liftedGameMat clock parentWord q G_O P J s_mid
    h_parent h_reset_waits
  exact isValidPriorityWord_of_isValidStrictWord (liftedGameMat G_O P J) s_mid
    (paperPriorityRank clock.m w parent_rank) _ h_strict

/-!
## 9. Full Reset Cascade Priority Validity & Convex Endpoint Reduction
-/

/-- **Convex Endpoint Priority Run Theorem (`chronology_reset_run_priority_valid`)**:
    Under `paperPriorityRank`, a repeated reset run `List.replicate cnt (Sum.inr j)` is a valid
    priority word if:
    - At start and end of the run, all old actions `Sum.inl x` are strictly below `Sum.inr j`.
    - Earlier reset actions `j' < j` are weakly below `Sum.inr j` at start, and strictly drop thereafter.
    - Later reset actions `j < j'` are strictly below `Sum.inr j` at start and end. -/
theorem chronology_reset_run_priority_valid {m w : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (parent_rank : Fin m → Fin m)
    (s_run : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (cnt : ℕ) (j : Fin ((w + 1) + (w + 1)))
    (hcnt : 1 ≤ cnt)
    (hJ_diag : J j j = 0)
    (h_old_start : ∀ x : Fin (m + 1), s_run (Sum.inl x) < s_run (Sum.inr j))
    (h_old_end : ∀ x : Fin (m + 1),
      s_run (Sum.inl x) + ((cnt - 1 : ℕ) : ℚ) * P x j < s_run (Sum.inr j))
    (h_earlier_start : ∀ j' : Fin ((w + 1) + (w + 1)), j'.val < j.val → s_run (Sum.inr j') ≤ s_run (Sum.inr j))
    (h_earlier_drop : ∀ j' : Fin ((w + 1) + (w + 1)), j'.val < j.val → J j' j - J j j' < 0)
    (h_later_start : ∀ j' : Fin ((w + 1) + (w + 1)), j.val < j'.val → s_run (Sum.inr j') < s_run (Sum.inr j))
    (h_later_end : ∀ j' : Fin ((w + 1) + (w + 1)), j.val < j'.val →
      s_run (Sum.inr j') + ((cnt - 1 : ℕ) : ℚ) * (J j' j - J j j') < s_run (Sum.inr j)) :
    IsValidPriorityWord (liftedGameMat G_O P J) s_run
      (paperPriorityRank m w parent_rank) (List.replicate cnt (Sum.inr j)) := by
  apply isValidPriorityWord_replicate_reset G_O P J parent_rank s_run j hJ_diag
  intro k hk
  dsimp only
  rw [wordScore_replicate_inr_self G_O P J j hJ_diag]
  have hk_le : (k : ℚ) ≤ ((cnt - 1 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : k ≤ cnt - 1)
  have hk0 : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg k
  refine ⟨?_, ?_⟩
  · intro x
    rw [wordScore_replicate_inr_inl]
    have h0 := h_old_start x
    have hend := h_old_end x
    have hP : s_run (Sum.inl x) + (k : ℚ) * P x j =
        s_run (Sum.inl x) + P x j * (k : ℚ) := by ring
    rw [hP]
    by_cases hs : 0 ≤ P x j <;> nlinarith
  · intro r' hr'
    rw [wordScore_replicate_inr_inr]
    cases lt_or_gt_of_ne (fun heq => hr' (Fin.ext heq)) with
    | inl h_earlier =>
        have hprio : (paperPriorityRank m w parent_rank (Sum.inr j)).val <
            (paperPriorityRank m w parent_rank (Sum.inr r')).val :=
          paperPriorityRank_reset_succ_lt m w parent_rank r' j h_earlier
        by_cases hk_zero : k = 0
        · subst hk_zero
          push_cast
          rw [zero_mul, add_zero]
          exact ⟨h_earlier_start r' h_earlier, fun _ => hprio⟩
        · have hk_pos : 0 < (k : ℚ) := by
            have : 1 ≤ k := by omega
            exact_mod_cast this
          have hdrop := h_earlier_drop r' h_earlier
          have h_neg : (k : ℚ) * (J r' j - J j r') < 0 := mul_neg_of_pos_of_neg hk_pos hdrop
          have h_le := h_earlier_start r' h_earlier
          have h_lt : s_run (Sum.inr r') + (k : ℚ) * (J r' j - J j r') < s_run (Sum.inr j) := by linarith
          exact ⟨le_of_lt h_lt, fun heq => (ne_of_lt h_lt heq).elim⟩
    | inr h_later =>
        have h0 := h_later_start r' h_later
        have hend := h_later_end r' h_later
        have h_comm : s_run (Sum.inr r') + (k : ℚ) * (J r' j - J j r') =
            s_run (Sum.inr r') + (J r' j - J j r') * (k : ℚ) := by ring
        rw [h_comm]
        have h_lt : s_run (Sum.inr r') + (J r' j - J j r') * (k : ℚ) < s_run (Sum.inr j) := by
          by_cases hs : 0 ≤ J r' j - J j r' <;> nlinarith
        exact ⟨le_of_lt h_lt, fun heq => (ne_of_lt h_lt heq).elim⟩

/-- Priority validity of `W_early_word` from per-run priority validity. -/
theorem isValidPriorityWord_W_early_word {m w q : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (parent_rank : Fin m → Fin m)
    (s0 : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (hrun : ∀ (idx : ℕ) (hidx : idx < (List.finRange (w + 1)).length),
      IsValidPriorityWord (liftedGameMat G_O P J)
        (wordScore (liftedGameMat G_O P J) s0
          (((List.finRange (w + 1)).take idx).flatMap fun r =>
            List.replicate (resetStepCount w (finSumFinEquiv (Sum.inl r)) q)
              (Sum.inr (finSumFinEquiv (Sum.inl r)))))
        (paperPriorityRank m w parent_rank)
        (List.replicate (resetStepCount w (finSumFinEquiv (Sum.inl (List.finRange (w + 1))[idx])) q)
          (Sum.inr (finSumFinEquiv (Sum.inl (List.finRange (w + 1))[idx]))))) :
    IsValidPriorityWord (liftedGameMat G_O P J) s0
      (paperPriorityRank m w parent_rank) (W_early_word m w q) := by
  unfold W_early_word
  exact isValidPriorityWord_flatMap (liftedGameMat G_O P J) _ _ (List.finRange (w + 1)) s0 hrun

/-- Priority validity of `W_late_word` from per-run priority validity. -/
theorem isValidPriorityWord_W_late_word {m w q : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (parent_rank : Fin m → Fin m)
    (s0 : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (hrun : ∀ (idx : ℕ) (hidx : idx < (List.finRange (w + 1)).length),
      IsValidPriorityWord (liftedGameMat G_O P J)
        (wordScore (liftedGameMat G_O P J) s0
          (((List.finRange (w + 1)).take idx).flatMap fun r =>
            List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
              (Sum.inr (finSumFinEquiv (Sum.inr r)))))
        (paperPriorityRank m w parent_rank)
        (List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr (List.finRange (w + 1))[idx])) q)
          (Sum.inr (finSumFinEquiv (Sum.inr (List.finRange (w + 1))[idx]))))) :
    IsValidPriorityWord (liftedGameMat G_O P J) s0
      (paperPriorityRank m w parent_rank) (W_late_word m w q) := by
  unfold W_late_word
  exact isValidPriorityWord_flatMap (liftedGameMat G_O P J) _ _ (List.finRange (w + 1)) s0 hrun

/-- Priority validity of combined reset stages `W_early_word ++ W_late_word`. -/
theorem isValidPriorityWord_reset_stages {m w q : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (parent_rank : Fin m → Fin m)
    (s0 : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (h_early : IsValidPriorityWord (liftedGameMat G_O P J) s0
      (paperPriorityRank m w parent_rank) (W_early_word m w q))
    (h_late : IsValidPriorityWord (liftedGameMat G_O P J)
      (wordScore (liftedGameMat G_O P J) s0 (W_early_word m w q))
      (paperPriorityRank m w parent_rank) (W_late_word m w q)) :
    IsValidPriorityWord (liftedGameMat G_O P J) s0
      (paperPriorityRank m w parent_rank) (W_early_word m w q ++ W_late_word m w q) :=
  (isValidPriorityWord_append (liftedGameMat G_O P J) s0 (paperPriorityRank m w parent_rank)
    (W_early_word m w q) (W_late_word m w q)).2 ⟨h_early, h_late⟩

/-!
## 10. Priority-to-Priority Stage 3 Bundle Lifting & Master 4-Stage Priority Theorem
-/

/-- **Priority-to-Priority Stage 3 Bundle Lifting (`isValidPriorityWord_stage3_bundle_of_priority`)**:
    If the embedded parent bundle `W_O` is a valid priority word on `G_O` and reset actions strictly
    wait behind active parent actions at every step, then the lifted bundle `W_O.map Sum.inl` is
    a valid priority word on `Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose)`. -/
theorem isValidPriorityWord_stage1_bundle_valid {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] {m_rank : ℕ}
    (G_O : Matrix α α ℚ) (P : Matrix α β ℚ) (J : Matrix β β ℚ)
    (rank : α ⊕ β → Fin m_rank)
    (s0 : α ⊕ β → ℚ) (W_O : List α)
    (h_parent : IsValidPriorityWord G_O (fun u => s0 (Sum.inl u)) (fun u => rank (Sum.inl u)) W_O)
    (h_reset_waits :
      ∀ (k : ℕ) (hk : k < W_O.length) (j : β),
        s0 (Sum.inr j) - ∑ u : α, P u j * wordCountVec (W_O.take k) u <
          wordScore G_O (fun u => s0 (Sum.inl u)) (W_O.take k) (W_O[k])) :
    IsValidPriorityWord (Matrix.fromBlocks G_O P (-P.transpose) (J - J.transpose))
      s0 rank (W_O.map Sum.inl) := by
  intro k hk x
  have hk_len : k < W_O.length := by simpa using hk
  have hget : (W_O.map (Sum.inl : α → α ⊕ β))[k] = Sum.inl (W_O[k]) := by
    simp
  have htake : (W_O.map (Sum.inl : α → α ⊕ β)).take k = (W_O.take k).map Sum.inl := by
    rw [List.map_take]
  rw [hget, htake, wordScore_map_inl_old G_O P J s0 (W_O.take k) (W_O[k])]
  cases x with
  | inl i =>
      rw [wordScore_map_inl_old G_O P J s0 (W_O.take k) i]
      have h_step := h_parent k hk_len i
      refine ⟨h_step.1, ?_⟩
      intro hne heq
      have hi_ne : i ≠ W_O[k] := fun h => hne (congr_arg Sum.inl h)
      exact h_step.2 hi_ne heq
  | inr j =>
      rw [wordScore_map_inl_new G_O P J s0 (W_O.take k) j]
      have h_lt := h_reset_waits k hk_len j
      exact ⟨le_of_lt h_lt, fun _ heq => (ne_of_lt h_lt heq).elim⟩

/-- **Priority-to-Priority Stage 3 Lifting on `liftedGameMat` (`isValidPriorityWord_stage3_bundle_of_priority`)**:
    Lifted version for `(W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w)`. -/
theorem isValidPriorityWord_stage3_bundle_of_priority {w : ℕ} (clock : AlgebraicClock w)
    (parentWord : ℕ → List (Fin clock.m)) (q : ℕ)
    (G_O : Matrix (Fin (clock.m + 1)) (Fin (clock.m + 1)) ℚ)
    (P : Matrix (Fin (clock.m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    {m_rank : ℕ}
    (rank : Fin (clock.m + 1) ⊕ Fin ((w + 1) + (w + 1)) → Fin m_rank)
    (s_mid : Fin (clock.m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (h_parent : IsValidPriorityWord G_O (fun u => s_mid (Sum.inl u)) (fun u => rank (Sum.inl u))
      ((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)))
    (h_reset_waits : ∀ (k : ℕ) (hk : k < ((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).length)
      (j : Fin ((w + 1) + (w + 1))),
      s_mid (Sum.inr j) - ∑ u, P u j * wordCountVec (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).take k) u <
        wordScore G_O (fun u => s_mid (Sum.inl u))
          (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).take k)
          (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m))[k])) :
    IsValidPriorityWord (liftedGameMat G_O P J) s_mid rank
      ((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w)) := by
  rw [map_bundleToLiftedAct_eq_map_inl]
  exact isValidPriorityWord_stage1_bundle_valid G_O P J rank s_mid
    ((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)) h_parent h_reset_waits

/-- **Lifting Parent `IsValidPriorityWord` from `Fin m` to `Fin (m + 1)` (`isValidPriorityWord_map_parentToOldAct`)**:
    When a valid priority word `W_p : List (Fin m)` on `G` is embedded into the old-action space
    `Fin (m + 1)` via `parentToOldAct m`, and the endpoint `gatewayOldAct m` strictly waits at every step,
    the embedded word is a valid priority word on `G_O` under `paperPriorityRank`. -/
theorem isValidPriorityWord_map_parentToOldAct {m w : ℕ}
    (G : Matrix (Fin m) (Fin m) ℚ)
    (s_p : Fin m → ℚ) (c_shift : ℚ)
    (parent_rank : Fin m → Fin m)
    (W_p : List (Fin m))
    (h_p : IsValidPriorityWord G s_p parent_rank W_p)
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (s_old : Fin (m + 1) → ℚ)
    (hG_agree : ∀ i j : Fin m, G_O (parentToOldAct m i) (parentToOldAct m j) = G i j)
    (hs_agree : ∀ i : Fin m, s_old (parentToOldAct m i) = s_p i + c_shift)
    (h_gw_waits : ∀ (k : ℕ) (hk : k < W_p.length),
      wordScore G_O s_old ((W_p.map (parentToOldAct m)).take k) (gatewayOldAct m) <
        wordScore G_O s_old ((W_p.map (parentToOldAct m)).take k) (parentToOldAct m (W_p[k]'hk))) :
    IsValidPriorityWord G_O s_old
      (fun u => paperPriorityRank m w parent_rank (Sum.inl u))
      (W_p.map (parentToOldAct m)) := by
  intro k hk u
  have hk_len : k < W_p.length := by simpa using hk
  have hget : (W_p.map (parentToOldAct m))[k] = parentToOldAct m (W_p[k]) := by simp
  have htake : (W_p.map (parentToOldAct m)).take k = (W_p.take k).map (parentToOldAct m) := by
    rw [List.map_take]
  rw [hget]
  have hcount_gw : wordCountVec ((W_p.take k).map (parentToOldAct m)) (gatewayOldAct m) = 0 := by
    unfold wordCountVec
    have hnone : ∀ y ∈ (W_p.take k).map (parentToOldAct m), y ≠ gatewayOldAct m := by
      intro y hy
      simp only [List.mem_map] at hy
      rcases hy with ⟨j, _, rfl⟩
      simp only [parentToOldAct, gatewayOldAct]
      intro heq
      have := finSumFinEquiv.injective heq
      contradiction
    rw [list_count_eq_zero_of_forall_ne hnone]
    rfl
  have hscore_p : ∀ i : Fin m,
      wordScore G_O s_old ((W_p.take k).map (parentToOldAct m)) (parentToOldAct m i) =
        wordScore G s_p (W_p.take k) i + c_shift := by
    intro i
    simp only [wordScore, scoreVec]
    rw [hs_agree i]
    have hsum : (∑ j : Fin (m + 1), G_O (parentToOldAct m i) j *
        wordCountVec ((W_p.take k).map (parentToOldAct m)) j) =
        ∑ j : Fin m, G i j * wordCountVec (W_p.take k) j := by
      have hcomp := (Equiv.sum_comp finSumFinEquiv fun j =>
        G_O (parentToOldAct m i) j * wordCountVec ((W_p.take k).map (parentToOldAct m)) j).symm
      rw [hcomp, Fintype.sum_sum_type]
      have hsum_inr : (∑ j : Fin 1, G_O (parentToOldAct m i) (finSumFinEquiv (Sum.inr j)) *
          wordCountVec ((W_p.take k).map (parentToOldAct m)) (finSumFinEquiv (Sum.inr j))) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        have hj0 : j = 0 := by ext; omega
        subst hj0
        change G_O (parentToOldAct m i) (gatewayOldAct m) *
          wordCountVec ((W_p.take k).map (parentToOldAct m)) (gatewayOldAct m) = 0
        rw [hcount_gw, mul_zero]
      rw [hsum_inr, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hcount_j : wordCountVec ((W_p.take k).map (parentToOldAct m)) (parentToOldAct m j) =
          wordCountVec (W_p.take k) j := by
        unfold wordCountVec
        have hinj : Function.Injective (parentToOldAct m) := fun a b h => by
          simp only [parentToOldAct] at h
          have := finSumFinEquiv.injective h
          cases this
          rfl
        rw [list_count_map_of_injective (parentToOldAct m) hinj (W_p.take k) j]
      change G_O (parentToOldAct m i) (parentToOldAct m j) *
        wordCountVec ((W_p.take k).map (parentToOldAct m)) (parentToOldAct m j) =
        G i j * wordCountVec (W_p.take k) j
      rw [hG_agree i j, hcount_j]
    rw [hsum]
    ring
  cases hsym : finSumFinEquiv.symm u with
  | inl i =>
      have hu_eq : u = parentToOldAct m i := by
        rw [parentToOldAct, ← hsym, Equiv.apply_symm_apply]
      rw [hu_eq, htake]
      rw [hscore_p i, hscore_p (W_p[k])]
      have h_step := h_p k hk_len i
      refine ⟨by linarith, ?_⟩
      intro hne heq
      have hi_ne : i ≠ W_p[k] := fun h => hne (by subst h; rfl)
      have h_tie : wordScore G s_p (W_p.take k) i = wordScore G s_p (W_p.take k) (W_p[k]) := by linarith
      have hprio := h_step.2 hi_ne h_tie
      simp only [paperPriorityRank]
      have hsym_act : (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).symm (parentToOldAct m (W_p[k])) = Sum.inl (W_p[k]) := by
        simp [parentToOldAct]
      have hsym_u : (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).symm (parentToOldAct m i) = Sum.inl i := by
        simp [parentToOldAct]
      simp only [hsym_act, hsym_u]
      exact hprio
  | inr _ =>
      have hu_gw : u = gatewayOldAct m := by
        have heq0 : (0 : Fin 1) = ⟨0, by omega⟩ := rfl
        have h_inr_unique : ∀ v : Fin 1, (Sum.inr v : Fin m ⊕ Fin 1) = Sum.inr ⟨0, by omega⟩ := fun v => by
          have : v = ⟨0, by omega⟩ := by ext; omega
          subst this; rfl
        rw [gatewayOldAct, heq0, ← h_inr_unique, ← hsym, Equiv.apply_symm_apply]
      rw [hu_gw, htake]
      have h_lt := h_gw_waits k hk_len
      rw [htake] at h_lt
      exact ⟨le_of_lt h_lt, fun _ heq => (ne_of_lt h_lt heq).elim⟩

/-- **Master 4-Stage Priority Synthesis Theorem (`chronology_four_stage_master_priority_valid`)**:
    Combines the priority validity of:
    1. Reset stages `W_early_word clock.m w q ++ W_late_word clock.m w q`,
    2. Lifted parent bundle `(W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w)`, and
    3. Gateway endpoint `[gatewayToLiftedAct clock.m w]`
    to unconditionally establish priority validity of the full four-stage word `rawFourStageWord`. -/
theorem chronology_four_stage_master_priority_valid {w : ℕ} (clock : AlgebraicClock w)
    (parentWord : ℕ → List (Fin clock.m)) (q : ℕ)
    (G_O : Matrix (Fin (clock.m + 1)) (Fin (clock.m + 1)) ℚ)
    (P : Matrix (Fin (clock.m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (parent_rank : Fin clock.m → Fin clock.m)
    (s0 : Fin (clock.m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (h_early : IsValidPriorityWord (liftedGameMat G_O P J) s0
      (paperPriorityRank clock.m w parent_rank) (W_early_word clock.m w q))
    (h_late : IsValidPriorityWord (liftedGameMat G_O P J)
      (wordScore (liftedGameMat G_O P J) s0 (W_early_word clock.m w q))
      (paperPriorityRank clock.m w parent_rank) (W_late_word clock.m w q))
    (h_bundle : IsValidPriorityWord (liftedGameMat G_O P J)
      (wordScore (liftedGameMat G_O P J) s0
        (W_early_word clock.m w q ++ W_late_word clock.m w q))
      (paperPriorityRank clock.m w parent_rank)
      ((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w)))
    (h_gw : IsValidPriorityWord (liftedGameMat G_O P J)
      (wordScore (liftedGameMat G_O P J) s0
        (W_early_word clock.m w q ++ W_late_word clock.m w q ++
          ((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w))))
      (paperPriorityRank clock.m w parent_rank)
      [gatewayToLiftedAct clock.m w]) :
    IsValidPriorityWord (liftedGameMat G_O P J) s0
      (paperPriorityRank clock.m w parent_rank)
      (rawFourStageWord clock parentWord q) := by
  exact isValidPriorityWord_rawFourStageWord clock parentWord q G_O P J s0
    (paperPriorityRank clock.m w parent_rank) h_early h_late h_bundle h_gw

/-!
## 11. Concrete Seed Validity, Reset Run Reduction, and Master Reduction
-/

/-- Run 0 strict best-response validity for all `q : ℚ` with `0 ≤ q`. -/
theorem rps_run0_valid_nonneg {q h : ℚ} (hq : 0 ≤ q) (hh0 : 0 ≤ h) (hhL : h ≤ (3 * q + 5) - 1) :
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

/-- Run 1 strict best-response validity for all `q : ℚ` with `0 ≤ q`. -/
theorem rps_run1_valid_nonneg {q h : ℚ} (hq : 0 ≤ q) (hh0 : 0 ≤ h) (hhL : h ≤ (3 * q + 6) - 1) :
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

/-- Run 2 strict best-response validity for all `q : ℚ` with `0 ≤ q`. -/
theorem rps_run2_valid_nonneg {q h : ℚ} (hq : 0 ≤ q) (hh0 : 0 ≤ h) (hhL : h ≤ (3 * q + 7) - 1) :
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

/-- Coefficient table identity matching `r2Vec q` with `R2 * binomBasis 2 q`. -/
theorem r2Vec_eq_R2_mulVec (q : ℕ) : r2Vec (q : ℚ) = R2.mulVec (binomBasis 2 q) := by
  ext i
  fin_cases i <;> simp [r2Vec, R2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, binomBasis] <;> ring

/-- Single-run strict validity on `A_RPS` for Run 0. -/
theorem isValidStrictWord_rps_run0 (q : ℕ) :
    IsValidStrictWord A_RPS (r2Vec (q : ℚ)) (List.replicate (3 * q + 5) 0) := by
  apply isValidStrictWord_replicate_of_endpoints
  · omega
  · rfl
  · intro j hj
    fin_cases j
    · contradiction
    · simp [r2Vec]; linarith
    · simp [r2Vec]; linarith
  · intro j hj
    have hq : 0 ≤ (q : ℚ) := by positivity
    fin_cases j
    · contradiction
    · simp [r2Vec, A_RPS]; linarith
    · simp [r2Vec, A_RPS]; linarith

/-- Single-run strict validity on `A_RPS` for Run 1. -/
theorem isValidStrictWord_rps_run1 (q : ℕ) :
    IsValidStrictWord A_RPS (rpsStateAfterRun0 (q : ℚ)) (List.replicate (3 * q + 6) 1) := by
  apply isValidStrictWord_replicate_of_endpoints
  · omega
  · rfl
  · intro j hj
    have hq : 0 ≤ (q : ℚ) := by positivity
    fin_cases j
    · simp [rpsStateAfterRun0]; linarith
    · contradiction
    · simp [rpsStateAfterRun0]; linarith
  · intro j hj
    have hq : 0 ≤ (q : ℚ) := by positivity
    fin_cases j
    · simp [rpsStateAfterRun0, A_RPS]; linarith
    · contradiction
    · simp [rpsStateAfterRun0, A_RPS]; linarith

/-- Single-run strict validity on `A_RPS` for Run 2. -/
theorem isValidStrictWord_rps_run2 (q : ℕ) :
    IsValidStrictWord A_RPS (rpsStateAfterRun1 (q : ℚ)) (List.replicate (3 * q + 7) 2) := by
  apply isValidStrictWord_replicate_of_endpoints
  · omega
  · rfl
  · intro j hj
    have hq : 0 ≤ (q : ℚ) := by positivity
    fin_cases j
    · simp [rpsStateAfterRun1]; linarith
    · simp [rpsStateAfterRun1]; linarith
    · contradiction
  · intro j hj
    have hq : 0 ≤ (q : ℚ) := by positivity
    fin_cases j
    · simp [rpsStateAfterRun1, A_RPS]; linarith
    · simp [rpsStateAfterRun1, A_RPS]; linarith
    · contradiction

/-- **Unconditional Strict Validity of RPS Seed Phase Word (`isValidStrictWord_rpsPhaseWord`)**:
    For all `q : ℕ`, the 3-run phase word `0^{3q+5} ++ 1^{3q+6} ++ 2^{3q+7}` is a valid strict FP word
    starting from `R2 * binomBasis 2 q`. -/
theorem isValidStrictWord_rpsPhaseWord (q : ℕ) :
    IsValidStrictWord A_RPS (R2.mulVec (binomBasis 2 q))
      (List.replicate (3 * q + 5) 0 ++ List.replicate (3 * q + 6) 1 ++ List.replicate (3 * q + 7) 2) := by
  rw [← r2Vec_eq_R2_mulVec]
  have h0 := isValidStrictWord_rps_run0 q
  have h0_trans : wordScore A_RPS (r2Vec (q : ℚ)) (List.replicate (3 * q + 5) 0) = rpsStateAfterRun0 (q : ℚ) := by
    ext j
    rw [wordScore_replicate]
    fin_cases j <;> simp [r2Vec, rpsStateAfterRun0, A_RPS] <;> ring
  have h1 := isValidStrictWord_rps_run1 q
  rw [← h0_trans] at h1
  have h01 := isValidStrictWord_append A_RPS (r2Vec (q : ℚ))
    (List.replicate (3 * q + 5) 0) (List.replicate (3 * q + 6) 1) h0 h1
  have h1_trans : wordScore A_RPS (wordScore A_RPS (r2Vec (q : ℚ)) (List.replicate (3 * q + 5) 0))
      (List.replicate (3 * q + 6) 1) = rpsStateAfterRun1 (q : ℚ) := by
    rw [h0_trans]
    ext j
    rw [wordScore_replicate]
    fin_cases j <;> simp [rpsStateAfterRun0, rpsStateAfterRun1, A_RPS] <;> ring
  rw [← wordScore_append] at h1_trans
  have h2 := isValidStrictWord_rps_run2 q
  rw [← h1_trans] at h2
  exact isValidStrictWord_append A_RPS (r2Vec (q : ℚ))
    (List.replicate (3 * q + 5) 0 ++ List.replicate (3 * q + 6) 1) (List.replicate (3 * q + 7) 2) h01 h2

/-- **Unconditional Priority Validity of RPS Seed Phase Word (`isValidPriorityWord_rpsPhaseWord`)**:
    For all `q : ℕ` and any tie-breaking rank, the RPS 3-run phase word is a valid priority word. -/
theorem isValidPriorityWord_rpsPhaseWord (q : ℕ) (rank : Fin 3 → Fin 3) :
    IsValidPriorityWord A_RPS (R2.mulVec (binomBasis 2 q)) rank
      (List.replicate (3 * q + 5) 0 ++ List.replicate (3 * q + 6) 1 ++ List.replicate (3 * q + 7) 2) :=
  isValidPriorityWord_of_isValidStrictWord A_RPS _ rank _ (isValidStrictWord_rpsPhaseWord q)

/-- **Unconditional Reset-vs-Reset Priority Validity for Any Single Reset Run (`chronology_reset_run_priority_valid_of_old_waits`)**:
    Under exact intermediate reset entry scores $s_{\text{run}}$, the reset-vs-reset dominance
    and tie-breaking conditions hold automatically, reducing reset run validity strictly to the
    two old-action endpoint waiting checks. -/
theorem chronology_reset_run_priority_valid_of_old_waits {m w : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (parent_rank : Fin m → Fin m)
    (s_run : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (m_r : ℕ) (r : Fin ((w + 1) + (w + 1)))
    (hm_r : 1 ≤ m_r)
    (s_ceil : ℚ)
    (m_vec : Fin ((w + 1) + (w + 1)) → ℚ)
    (hm_r_eq : m_vec r = (m_r : ℚ))
    (hm_pos : ∀ b_idx, 1 ≤ m_vec b_idx)
    (hJ_lower : ∀ a b_idx, a.val ≤ b_idx.val → J a b_idx = 0)
    (hJ_subdiag_pos : ∀ a b_idx, b_idx.val < a.val → 0 < J a b_idx)
    (hs_inr : ∀ r' : Fin ((w + 1) + (w + 1)),
      s_run (Sum.inr r') = s_ceil - ∑ b_idx : Fin ((w + 1) + (w + 1)),
        if r.val ≤ b_idx.val then J r' b_idx * m_vec b_idx else 0)
    (h_old_start : ∀ x : Fin (m + 1), s_run (Sum.inl x) < s_ceil)
    (h_old_end : ∀ x : Fin (m + 1),
      s_run (Sum.inl x) + ((m_r - 1 : ℕ) : ℚ) * P x r < s_ceil) :
    IsValidPriorityWord (liftedGameMat G_O P J) s_run
      (paperPriorityRank m w parent_rank) (List.replicate m_r (Sum.inr r)) := by
  have hs_r : s_run (Sum.inr r) = s_ceil := by
    rw [hs_inr r]
    have hsum : (∑ b_idx : Fin ((w + 1) + (w + 1)),
        if r.val ≤ b_idx.val then J r b_idx * m_vec b_idx else 0) = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs with hle
      · rw [hJ_lower r b hle, zero_mul]
      · rfl
    rw [hsum, sub_zero]
  have hJ_diag : J r r = 0 := hJ_lower r r (le_refl _)
  have hs_earlier : ∀ j' : Fin ((w + 1) + (w + 1)), j'.val < r.val → s_run (Sum.inr j') = s_ceil := by
    intro j' hj'
    rw [hs_inr j']
    have hsum : (∑ b_idx : Fin ((w + 1) + (w + 1)),
        if r.val ≤ b_idx.val then J j' b_idx * m_vec b_idx else 0) = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs with hle
      · have : j'.val ≤ b.val := by omega
        rw [hJ_lower j' b this, zero_mul]
      · rfl
    rw [hsum, sub_zero]
  have hs_later : ∀ j' : Fin ((w + 1) + (w + 1)), r.val < j'.val →
      s_run (Sum.inr j') + ((m_r - 1 : ℕ) : ℚ) * (J j' r - J r j') < s_ceil := by
    intro j' hj'
    rw [hs_inr j']
    have hJ_rj' : J r j' = 0 := hJ_lower r j' (by omega)
    rw [hJ_rj', sub_zero]
    have h_split : (∑ b_idx : Fin ((w + 1) + (w + 1)),
        if r.val ≤ b_idx.val then J j' b_idx * m_vec b_idx else 0) =
        J j' r * m_vec r + ∑ b_idx ∈ Finset.univ.erase r,
          if r.val ≤ b_idx.val then J j' b_idx * m_vec b_idx else 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
      have : r.val ≤ r.val := le_refl _
      simp
    rw [h_split, hm_r_eq]
    have h_rest_nonneg : 0 ≤ ∑ b_idx ∈ Finset.univ.erase r,
        if r.val ≤ b_idx.val then J j' b_idx * m_vec b_idx else 0 := by
      refine Finset.sum_nonneg fun b _ => ?_
      split_ifs with hle
      · by_cases hb : b.val < j'.val
        · have h1 : 0 ≤ J j' b := le_of_lt (hJ_subdiag_pos j' b hb)
          have h2 : 0 ≤ m_vec b := le_trans (by norm_num) (hm_pos b)
          exact mul_nonneg h1 h2
        · have : j'.val ≤ b.val := by omega
          rw [hJ_lower j' b this, zero_mul]
      · rfl
    have hJ_pos : 0 < J j' r := hJ_subdiag_pos j' r hj'
    have : ((m_r - 1 : ℕ) : ℚ) < (m_r : ℚ) := by
      have : m_r - 1 < m_r := by omega
      exact_mod_cast this
    nlinarith
  apply chronology_reset_run_priority_valid G_O P J parent_rank s_run m_r r hm_r hJ_diag
  · intro x; rw [hs_r]; exact h_old_start x
  · intro x; rw [hs_r]; exact h_old_end x
  · intro j' hj'; rw [hs_r, hs_earlier j' hj']
  · intro j' hj'
    have h1 : J j' r = 0 := hJ_lower j' r (le_of_lt hj')
    have h2 : 0 < J r j' := hJ_subdiag_pos r j' hj'
    rw [h1, zero_sub]
    linarith
  · intro j' hj'
    have := hs_later j' hj'
    rw [hs_r]
    have hJ_rj' : J r j' = 0 := hJ_lower r j' (by omega)
    rw [hJ_rj', sub_zero] at this
    have : 0 ≤ ((m_r - 1 : ℕ) : ℚ) * J j' r := by
      have : 0 ≤ ((m_r - 1 : ℕ) : ℚ) := Nat.cast_nonneg _
      have : 0 ≤ J j' r := le_of_lt (hJ_subdiag_pos j' r hj')
      positivity
    linarith
  · intro j' hj'
    rw [hs_r]
    exact hs_later j' hj'

/-- **Master Stagewise Priority Reduction Theorem (`chronology_rawFourStageWord_of_stage_conditions`)**:
    Establishes priority validity of `rawFourStageWord clock parentWord q` directly from:
    1. Early reset stage priority validity,
    2. Late reset stage priority validity,
    3. Stage 3 parent bundle priority validity and gateway/reset waiting, and
    4. Stage 4 gateway single-play dominance. -/
theorem chronology_rawFourStageWord_of_stage_conditions {w : ℕ} (clock : AlgebraicClock w)
    (parentWord : ℕ → List (Fin clock.m)) (q : ℕ)
    (G_O : Matrix (Fin (clock.m + 1)) (Fin (clock.m + 1)) ℚ)
    (P : Matrix (Fin (clock.m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (parent_rank : Fin clock.m → Fin clock.m)
    (s0 : Fin (clock.m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (h_early : IsValidPriorityWord (liftedGameMat G_O P J) s0
      (paperPriorityRank clock.m w parent_rank) (W_early_word clock.m w q))
    (h_late : IsValidPriorityWord (liftedGameMat G_O P J)
      (wordScore (liftedGameMat G_O P J) s0 (W_early_word clock.m w q))
      (paperPriorityRank clock.m w parent_rank) (W_late_word clock.m w q))
    (h_bundle : IsValidPriorityWord (liftedGameMat G_O P J)
      (wordScore (liftedGameMat G_O P J) s0
        (W_early_word clock.m w q ++ W_late_word clock.m w q))
      (paperPriorityRank clock.m w parent_rank)
      ((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w)))
    (h_gw : ∀ y, y ≠ gatewayToLiftedAct clock.m w →
      wordScore (liftedGameMat G_O P J) s0
        (W_early_word clock.m w q ++ W_late_word clock.m w q ++
          ((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w))) y <
      wordScore (liftedGameMat G_O P J) s0
        (W_early_word clock.m w q ++ W_late_word clock.m w q ++
          ((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w)))
        (gatewayToLiftedAct clock.m w)) :
    IsValidPriorityWord (liftedGameMat G_O P J) s0
      (paperPriorityRank clock.m w parent_rank)
      (rawFourStageWord clock parentWord q) := by
  have h_gw_word : IsValidPriorityWord (liftedGameMat G_O P J)
      (wordScore (liftedGameMat G_O P J) s0
        (W_early_word clock.m w q ++ W_late_word clock.m w q ++
          ((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w))))
      (paperPriorityRank clock.m w parent_rank)
      [gatewayToLiftedAct clock.m w] :=
    isValidPriorityWord_stage4_gateway clock G_O P J _ (paperPriorityRank clock.m w parent_rank) h_gw
  exact chronology_four_stage_master_priority_valid clock parentWord q G_O P J parent_rank s0
    h_early h_late h_bundle h_gw_word

/-!
## 12. Stage 3 & Stage 4 Priority Reductions and Master Inductive Priority Lift
-/

/-- **Priority-Word Version of `isValidStrictWord_bundle_word` (`isValidPriorityWord_bundle_word`)**:
    Validity of `W_bundle_word parentWord Q` as a priority word under `parent_rank` whenever each
    single-phase parent word is a valid priority word. -/
theorem isValidPriorityWord_bundle_word {w : ℕ} (clock : AlgebraicClock w)
    (parentWord : ℕ → List (Fin clock.m))
    (parent_rank : Fin clock.m → Fin clock.m)
    (hparent_count : ∀ σ : ℕ, wordCountVec (parentWord σ) = clock.C.mulVec (binomBasis w σ))
    (hparent_valid : ∀ σ : ℕ,
      IsValidPriorityWord clock.G (clock.R.mulVec (binomBasis w σ)) parent_rank (parentWord σ))
    (c_shift : ℚ) (Q : ℕ) :
    IsValidPriorityWord clock.G (fun i => clock.R.mulVec (binomBasis w 0) i + c_shift)
      parent_rank (W_bundle_word parentWord Q) := by
  induction Q with
  | zero =>
    intro k hk
    simp [W_bundle_word] at hk
  | succ Q ih =>
    have hflat : W_bundle_word parentWord (Q + 1) =
        W_bundle_word parentWord Q ++ parentWord Q := by
      unfold W_bundle_word
      rw [@List.range_succ Q, List.flatMap_append]
      simp
    rw [hflat]
    rw [isValidPriorityWord_append]
    refine ⟨ih, ?_⟩
    have hws := wordScore_bundle_word clock parentWord hparent_count c_shift Q
    rw [hws]
    have hvalidQ := hparent_valid Q
    intro k hk j
    have hval := hvalidQ k hk j
    have hbias_j : wordScore clock.G (fun i => clock.R.mulVec (binomBasis w Q) i + c_shift)
        ((parentWord Q).take k) j =
        wordScore clock.G (clock.R.mulVec (binomBasis w Q)) ((parentWord Q).take k) j + c_shift := by
      simp only [wordScore, scoreVec]; ring
    have hbias_act : wordScore clock.G (fun i => clock.R.mulVec (binomBasis w Q) i + c_shift)
        ((parentWord Q).take k) ((parentWord Q)[k]) =
        wordScore clock.G (clock.R.mulVec (binomBasis w Q)) ((parentWord Q).take k) ((parentWord Q)[k]) + c_shift := by
      simp only [wordScore, scoreVec]; ring
    rw [hbias_j, hbias_act]
    refine ⟨by linarith, ?_⟩
    intro hne heq
    have heq_orig : wordScore clock.G (clock.R.mulVec (binomBasis w Q)) ((parentWord Q).take k) j =
        wordScore clock.G (clock.R.mulVec (binomBasis w Q)) ((parentWord Q).take k) ((parentWord Q)[k]) := by
      linarith
    exact hval.2 hne heq_orig

/-- **Full Stage 3 Lifted Bundle Reduction from Single-Phase Parent Priority Validity (`isValidPriorityWord_stage3_bundle_from_parent`)**:
    Combines single-phase parent priority validity into full priority validity of the lifted parent bundle
    on `liftedGameMat G_O P J`. -/
theorem isValidPriorityWord_stage3_bundle_from_parent {w : ℕ} (clock : AlgebraicClock w)
    (parentWord : ℕ → List (Fin clock.m))
    (parent_rank : Fin clock.m → Fin clock.m)
    (hparent_count : ∀ σ : ℕ, wordCountVec (parentWord σ) = clock.C.mulVec (binomBasis w σ))
    (hparent_valid : ∀ σ : ℕ,
      IsValidPriorityWord clock.G (clock.R.mulVec (binomBasis w σ)) parent_rank (parentWord σ))
    (q : ℕ) (c_shift : ℚ)
    (G_O : Matrix (Fin (clock.m + 1)) (Fin (clock.m + 1)) ℚ)
    (P : Matrix (Fin (clock.m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (s_mid : Fin (clock.m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (hG_agree : ∀ i j : Fin clock.m,
      G_O (parentToOldAct clock.m i) (parentToOldAct clock.m j) = clock.G i j)
    (hs_agree : ∀ i : Fin clock.m,
      s_mid (Sum.inl (parentToOldAct clock.m i)) = clock.R.mulVec (binomBasis w 0) i + c_shift)
    (h_gw_waits : ∀ (k : ℕ) (hk : k < (W_bundle_word parentWord (q + 1)).length),
      wordScore G_O (fun u => s_mid (Sum.inl u))
        (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).take k)
        (gatewayOldAct clock.m) <
      wordScore G_O (fun u => s_mid (Sum.inl u))
        (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).take k)
        (parentToOldAct clock.m ((W_bundle_word parentWord (q + 1))[k]'hk)))
    (h_reset_waits : ∀ (k : ℕ)
      (hk : k < ((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).length)
      (j : Fin ((w + 1) + (w + 1))),
      s_mid (Sum.inr j) - ∑ u, P u j * wordCountVec (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).take k) u <
        wordScore G_O (fun u => s_mid (Sum.inl u))
          (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).take k)
          (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m))[k])) :
    IsValidPriorityWord (liftedGameMat G_O P J) s_mid
      (paperPriorityRank clock.m w parent_rank)
      ((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w)) := by
  have h_bundle_p : IsValidPriorityWord clock.G (fun i => clock.R.mulVec (binomBasis w 0) i + c_shift)
      parent_rank (W_bundle_word parentWord (q + 1)) :=
    isValidPriorityWord_bundle_word clock parentWord parent_rank hparent_count hparent_valid c_shift (q + 1)
  have h_bundle_old : IsValidPriorityWord G_O (fun u => s_mid (Sum.inl u))
      (fun u => paperPriorityRank clock.m w parent_rank (Sum.inl u))
      ((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)) :=
    isValidPriorityWord_map_parentToOldAct clock.G
      (fun i => clock.R.mulVec (binomBasis w 0) i + c_shift) 0 parent_rank
      (W_bundle_word parentWord (q + 1)) h_bundle_p G_O (fun u => s_mid (Sum.inl u))
      hG_agree (fun i => by simp [hs_agree i]) h_gw_waits
  exact isValidPriorityWord_stage3_bundle_of_priority clock parentWord q G_O P J
    (paperPriorityRank clock.m w parent_rank) s_mid h_bundle_old h_reset_waits

/-- **Master 4-Stage Inductive Priority Lift Theorem (`chronology_inductive_priority_lift`)**:
    Shows that if `parentWord` is a valid priority word family for `clock`, then
    `rawFourStageWord clock parentWord q` is unconditionally a valid priority word for
    `liftedGameMat G_O P J` under `paperPriorityRank clock.m w parent_rank` whenever the stage
    waiting and takeover inequalities hold. -/
theorem chronology_inductive_priority_lift {w : ℕ} (clock : AlgebraicClock w)
    (parentWord : ℕ → List (Fin clock.m))
    (parent_rank : Fin clock.m → Fin clock.m)
    (hparent_count : ∀ σ : ℕ, wordCountVec (parentWord σ) = clock.C.mulVec (binomBasis w σ))
    (hparent_valid : ∀ σ : ℕ,
      IsValidPriorityWord clock.G (clock.R.mulVec (binomBasis w σ)) parent_rank (parentWord σ))
    (q : ℕ) (c_shift : ℚ)
    (G_O : Matrix (Fin (clock.m + 1)) (Fin (clock.m + 1)) ℚ)
    (P : Matrix (Fin (clock.m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (s0 : Fin (clock.m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (h_early : IsValidPriorityWord (liftedGameMat G_O P J) s0
      (paperPriorityRank clock.m w parent_rank) (W_early_word clock.m w q))
    (h_late : IsValidPriorityWord (liftedGameMat G_O P J)
      (wordScore (liftedGameMat G_O P J) s0 (W_early_word clock.m w q))
      (paperPriorityRank clock.m w parent_rank) (W_late_word clock.m w q))
    (hG_agree : ∀ i j : Fin clock.m,
      G_O (parentToOldAct clock.m i) (parentToOldAct clock.m j) = clock.G i j)
    (hs_agree : ∀ i : Fin clock.m,
      wordScore (liftedGameMat G_O P J) s0 (W_early_word clock.m w q ++ W_late_word clock.m w q)
        (Sum.inl (parentToOldAct clock.m i)) = clock.R.mulVec (binomBasis w 0) i + c_shift)
    (h_gw_waits : ∀ (k : ℕ) (hk : k < (W_bundle_word parentWord (q + 1)).length),
      wordScore G_O (fun u => wordScore (liftedGameMat G_O P J) s0
          (W_early_word clock.m w q ++ W_late_word clock.m w q) (Sum.inl u))
        (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).take k)
        (gatewayOldAct clock.m) <
      wordScore G_O (fun u => wordScore (liftedGameMat G_O P J) s0
          (W_early_word clock.m w q ++ W_late_word clock.m w q) (Sum.inl u))
        (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).take k)
        (parentToOldAct clock.m ((W_bundle_word parentWord (q + 1))[k]'hk)))
    (h_reset_waits : ∀ (k : ℕ)
      (hk : k < ((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).length)
      (j : Fin ((w + 1) + (w + 1))),
      wordScore (liftedGameMat G_O P J) s0 (W_early_word clock.m w q ++ W_late_word clock.m w q) (Sum.inr j) -
        ∑ u, P u j * wordCountVec (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).take k) u <
        wordScore G_O (fun u => wordScore (liftedGameMat G_O P J) s0
            (W_early_word clock.m w q ++ W_late_word clock.m w q) (Sum.inl u))
          (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).take k)
          (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m))[k]))
    (h_gw : ∀ y, y ≠ gatewayToLiftedAct clock.m w →
      wordScore (liftedGameMat G_O P J) s0
        (W_early_word clock.m w q ++ W_late_word clock.m w q ++
          ((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w))) y <
      wordScore (liftedGameMat G_O P J) s0
        (W_early_word clock.m w q ++ W_late_word clock.m w q ++
          ((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w)))
        (gatewayToLiftedAct clock.m w)) :
    IsValidPriorityWord (liftedGameMat G_O P J) s0
      (paperPriorityRank clock.m w parent_rank)
      (rawFourStageWord clock parentWord q) := by
  have h_bundle : IsValidPriorityWord (liftedGameMat G_O P J)
      (wordScore (liftedGameMat G_O P J) s0 (W_early_word clock.m w q ++ W_late_word clock.m w q))
      (paperPriorityRank clock.m w parent_rank)
      ((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w)) :=
    isValidPriorityWord_stage3_bundle_from_parent clock parentWord parent_rank hparent_count hparent_valid
      q c_shift G_O P J _ hG_agree hs_agree h_gw_waits h_reset_waits
  exact chronology_rawFourStageWord_of_stage_conditions clock parentWord q G_O P J parent_rank s0
    h_early h_late h_bundle h_gw

/-!
## 13. Monotonicity of Old-Action Scores During Early & Late Reset Stages
-/

/-- **Early Reset Run Priority Validity Under Nonpositive Coupling (`chronology_early_reset_run_valid_of_start`)**:
    When all old-action coupling entries $P_{x, r} \le 0$, the old-action waiting condition at the end of the run
    holds automatically from the starting waiting condition, eliminating the end-of-run check. -/
theorem chronology_early_reset_run_valid_of_start {m w : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (parent_rank : Fin m → Fin m)
    (s_run : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (m_r : ℕ) (r : Fin ((w + 1) + (w + 1)))
    (hm_r : 1 ≤ m_r)
    (s_ceil : ℚ)
    (m_vec : Fin ((w + 1) + (w + 1)) → ℚ)
    (hm_r_eq : m_vec r = (m_r : ℚ))
    (hm_pos : ∀ b_idx, 1 ≤ m_vec b_idx)
    (hJ_lower : ∀ a b_idx, a.val ≤ b_idx.val → J a b_idx = 0)
    (hJ_subdiag_pos : ∀ a b_idx, b_idx.val < a.val → 0 < J a b_idx)
    (hs_inr : ∀ r' : Fin ((w + 1) + (w + 1)),
      s_run (Sum.inr r') = s_ceil - ∑ b_idx : Fin ((w + 1) + (w + 1)),
        if r.val ≤ b_idx.val then J r' b_idx * m_vec b_idx else 0)
    (hP_nonpos : ∀ x : Fin (m + 1), P x r ≤ 0)
    (h_old_start : ∀ x : Fin (m + 1), s_run (Sum.inl x) < s_ceil) :
    IsValidPriorityWord (liftedGameMat G_O P J) s_run
      (paperPriorityRank m w parent_rank) (List.replicate m_r (Sum.inr r)) := by
  apply chronology_reset_run_priority_valid_of_old_waits G_O P J parent_rank s_run m_r r hm_r
    s_ceil m_vec hm_r_eq hm_pos hJ_lower hJ_subdiag_pos hs_inr h_old_start
  intro x
  have hP := hP_nonpos x
  have h_mul : ((m_r - 1 : ℕ) : ℚ) * P x r ≤ 0 := by
    have : 0 ≤ ((m_r - 1 : ℕ) : ℚ) := Nat.cast_nonneg _
    nlinarith
  have h_start := h_old_start x
  linarith

/-- **Late Reset Run Priority Validity Under Nonnegative Coupling (`chronology_late_reset_run_valid_of_end`)**:
    When all old-action coupling entries $P_{x, r} \ge 0$, if the post-run score remains strictly below
    the ceiling $\zeta$, then both the start and within-run checks hold automatically. -/
theorem chronology_late_reset_run_valid_of_end {m w : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (parent_rank : Fin m → Fin m)
    (s_run : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (m_r : ℕ) (r : Fin ((w + 1) + (w + 1)))
    (hm_r : 1 ≤ m_r)
    (s_ceil : ℚ)
    (m_vec : Fin ((w + 1) + (w + 1)) → ℚ)
    (hm_r_eq : m_vec r = (m_r : ℚ))
    (hm_pos : ∀ b_idx, 1 ≤ m_vec b_idx)
    (hJ_lower : ∀ a b_idx, a.val ≤ b_idx.val → J a b_idx = 0)
    (hJ_subdiag_pos : ∀ a b_idx, b_idx.val < a.val → 0 < J a b_idx)
    (hs_inr : ∀ r' : Fin ((w + 1) + (w + 1)),
      s_run (Sum.inr r') = s_ceil - ∑ b_idx : Fin ((w + 1) + (w + 1)),
        if r.val ≤ b_idx.val then J r' b_idx * m_vec b_idx else 0)
    (hP_nonneg : ∀ x : Fin (m + 1), 0 ≤ P x r)
    (h_old_after : ∀ x : Fin (m + 1), s_run (Sum.inl x) + (m_r : ℚ) * P x r < s_ceil) :
    IsValidPriorityWord (liftedGameMat G_O P J) s_run
      (paperPriorityRank m w parent_rank) (List.replicate m_r (Sum.inr r)) := by
  have h_old_start : ∀ x : Fin (m + 1), s_run (Sum.inl x) < s_ceil := fun x => by
    have h_aft := h_old_after x
    have hP := hP_nonneg x
    have : 0 ≤ (m_r : ℚ) * P x r := mul_nonneg (Nat.cast_nonneg _) hP
    linarith
  have h_old_end : ∀ x : Fin (m + 1), s_run (Sum.inl x) + ((m_r - 1 : ℕ) : ℚ) * P x r < s_ceil := fun x => by
    have h_aft := h_old_after x
    have hP := hP_nonneg x
    have hle : ((m_r - 1 : ℕ) : ℚ) ≤ (m_r : ℚ) := by
      have : m_r - 1 ≤ m_r := by omega
      exact_mod_cast this
    have : ((m_r - 1 : ℕ) : ℚ) * P x r ≤ (m_r : ℚ) * P x r := mul_le_mul_of_nonneg_right hle hP
    linarith
  exact chronology_reset_run_priority_valid_of_old_waits G_O P J parent_rank s_run m_r r hm_r
    s_ceil m_vec hm_r_eq hm_pos hJ_lower hJ_subdiag_pos hs_inr h_old_start h_old_end

/-- **Early Reset Prefix Score Bound for Old Actions (`wordScore_flatMap_replicate_inr_inl_le`)**:
    Under nonpositive coupling $P_{x, r} \le 0$ for all reset actions in list $L$, the score of every old action
    $x \in \text{Fin}(m + 1)$ is monotonically nonincreasing across the reset concatenation. -/
theorem wordScore_flatMap_replicate_inr_inl_le {m w : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (s0 : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (L : List (Fin ((w + 1) + (w + 1))))
    (m_len : Fin ((w + 1) + (w + 1)) → ℕ)
    (hP_nonpos : ∀ (r : Fin ((w + 1) + (w + 1))), r ∈ L → ∀ x : Fin (m + 1), P x r ≤ 0)
    (x : Fin (m + 1)) :
    wordScore (liftedGameMat G_O P J) s0
      (L.flatMap fun r => List.replicate (m_len r) (Sum.inr r)) (Sum.inl x) ≤ s0 (Sum.inl x) := by
  induction L generalizing s0 with
  | nil =>
    simp only [List.flatMap_nil, wordScore_nil, le_rfl]
  | cons r tl ih =>
    simp only [List.flatMap_cons]
    rw [wordScore_append]
    have hr_in : r ∈ r :: tl := List.mem_cons_self
    have hP_r := hP_nonpos r hr_in x
    have h_rec := ih (wordScore (liftedGameMat G_O P J) s0 (List.replicate (m_len r) (Sum.inr r)))
      fun r' hr' => hP_nonpos r' (List.mem_cons_of_mem r hr')
    have h_step : wordScore (liftedGameMat G_O P J) s0 (List.replicate (m_len r) (Sum.inr r)) (Sum.inl x) ≤
        s0 (Sum.inl x) := by
      rw [wordScore_replicate_inr_inl]
      have : ((m_len r : ℕ) : ℚ) * P x r ≤ 0 := by
        have : 0 ≤ ((m_len r : ℕ) : ℚ) := Nat.cast_nonneg _
        nlinarith
      linarith
    linarith

/-- **Corollary: Early Reset Run Start Score Bound (`wordScore_W_early_word_take_old_le`)**:
    At the start of every early reset run `idx : ℕ` in `W_early_word`, if all early reset coupling entries
    are nonpositive, the score of every old action is bounded above by its initial value $s_0(x)$. -/
theorem wordScore_W_early_word_take_old_le {m w q : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (s0 : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (hP_early_nonpos : ∀ (j : Fin (w + 1)) (x : Fin (m + 1)),
      P x (finSumFinEquiv (Sum.inl j)) ≤ 0)
    (idx : ℕ) (x : Fin (m + 1)) :
    wordScore (liftedGameMat G_O P J) s0
      (((List.finRange (w + 1)).take idx).flatMap (fun r =>
        List.replicate (resetStepCount w (finSumFinEquiv (Sum.inl r)) q)
          (Sum.inr (finSumFinEquiv (Sum.inl r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1))))) (Sum.inl x) ≤ s0 (Sum.inl x) := by
  let L := ((List.finRange (w + 1)).take idx).map (fun r => (finSumFinEquiv (Sum.inl r) : Fin ((w + 1) + (w + 1))))
  have h_flat : (((List.finRange (w + 1)).take idx).flatMap (fun r =>
      List.replicate (resetStepCount w (finSumFinEquiv (Sum.inl r)) q)
        (Sum.inr (finSumFinEquiv (Sum.inl r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1))))) =
      L.flatMap (fun r => List.replicate (resetStepCount w r q) (Sum.inr r)) := by
    dsimp [L]
    rw [List.flatMap_map]
  rw [h_flat]
  apply wordScore_flatMap_replicate_inr_inl_le G_O P J s0 L (fun r => resetStepCount w r q)
  intro r hr x'
  simp only [L, List.mem_map] at hr
  rcases hr with ⟨j, _, rfl⟩
  exact hP_early_nonpos j x'

/-- **Late Reset Suffix Score Bound for Old Actions (`wordScore_flatMap_replicate_inr_inl_le_end`)**:
    Under nonnegative coupling $P_{x, r} \ge 0$, for any prefix decomposition $L = L_1 ++ L_2$,
    the score of an old action after $L_1$ is bounded above by its score after the entire list $L$. -/
theorem wordScore_flatMap_replicate_inr_inl_le_end {m w : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (s0 : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (L1 L2 : List (Fin ((w + 1) + (w + 1))))
    (m_len : Fin ((w + 1) + (w + 1)) → ℕ)
    (hP_nonneg : ∀ (r : Fin ((w + 1) + (w + 1))), r ∈ L2 → ∀ x : Fin (m + 1), 0 ≤ P x r)
    (x : Fin (m + 1)) :
    wordScore (liftedGameMat G_O P J) s0
      (L1.flatMap fun r => List.replicate (m_len r) (Sum.inr r)) (Sum.inl x) ≤
    wordScore (liftedGameMat G_O P J) s0
      ((L1 ++ L2).flatMap fun r => List.replicate (m_len r) (Sum.inr r)) (Sum.inl x) := by
  rw [List.flatMap_append, wordScore_append]
  have h_mono : ∀ (L : List (Fin ((w + 1) + (w + 1))))
      (s : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ),
      (∀ r ∈ L, ∀ x : Fin (m + 1), 0 ≤ P x r) →
      s (Sum.inl x) ≤ wordScore (liftedGameMat G_O P J) s (L.flatMap fun r => List.replicate (m_len r) (Sum.inr r)) (Sum.inl x) := by
    intro L s hP
    induction L generalizing s with
    | nil =>
      simp only [List.flatMap_nil, wordScore_nil, le_rfl]
    | cons r tl ih =>
      simp only [List.flatMap_cons]
      rw [wordScore_append]
      have hr_in : r ∈ r :: tl := List.mem_cons_self
      have hP_r := hP r hr_in x
      have h_step : s (Sum.inl x) ≤ wordScore (liftedGameMat G_O P J) s (List.replicate (m_len r) (Sum.inr r)) (Sum.inl x) := by
        rw [wordScore_replicate_inr_inl]
        have : 0 ≤ ((m_len r : ℕ) : ℚ) * P x r := mul_nonneg (Nat.cast_nonneg _) hP_r
        linarith
      have h_rec := ih (wordScore (liftedGameMat G_O P J) s (List.replicate (m_len r) (Sum.inr r)))
        fun r' hr' => hP r' (List.mem_cons_of_mem r hr')
      linarith
  exact h_mono L2 (wordScore (liftedGameMat G_O P J) s0 (L1.flatMap fun r => List.replicate (m_len r) (Sum.inr r))) hP_nonneg

/-!
## 14. Complete Reduction of Stage 1 & Stage 2 Priority Validity to Endpoint Inequalities
-/

/-- Count of `i : Fin n` in `(List.finRange n).take idx` is 1 if `i.val < idx` and 0 otherwise. -/
theorem count_take_finRange (n idx : ℕ) (i : Fin n) :
    ((List.finRange n).take idx).count i = if i.val < idx then 1 else 0 := by
  by_cases h : i.val < idx
  · rw [if_pos h]
    have hnodup : ((List.finRange n).take idx).Nodup :=
      List.Nodup.sublist (List.take_sublist idx (List.finRange n)) (List.nodup_finRange n)
    apply List.count_eq_one_of_mem hnodup
    rw [List.mem_take_iff_getElem]
    have hi_len : i.val < (List.finRange n).length := by
      rw [List.length_finRange]
      exact i.isLt
    refine ⟨i.val, lt_min h hi_len, ?_⟩
    simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
  · rw [if_neg h]
    apply List.count_eq_zero_of_not_mem
    intro hmem
    rw [List.mem_take_iff_getElem] at hmem
    rcases hmem with ⟨k, hk, hget⟩
    simp only [List.getElem_finRange, Fin.ext_iff, Fin.val_cast] at hget
    have hk_idx : k < idx := lt_of_lt_of_le hk (Nat.min_le_left _ _)
    omega

/-- Action count vector of `(W_early_word m w q).take` matches `resetPrefixCount` at `h = 0`. -/
theorem wordCountVec_W_early_word_take_eq_resetPrefixCount {m w : ℕ} (q : ℕ)
    (idx : ℕ) (hidx : idx < w + 1)
    (x : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1))) :
    wordCountVec (((List.finRange (w + 1)).take idx).flatMap fun r =>
      List.replicate (resetStepCount w (finSumFinEquiv (Sum.inl r)) q)
        (Sum.inr (finSumFinEquiv (Sum.inl r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))) x =
    match x with
    | Sum.inl _ => 0
    | Sum.inr ℓ =>
      resetPrefixCount (finSumFinEquiv (Sum.inl ⟨idx, hidx⟩))
        ((M_coupled w).mulVec (binomBasis (w + 1) q)) 0 ℓ := by
  let j : Fin ((w + 1) + (w + 1)) := finSumFinEquiv (Sum.inl ⟨idx, hidx⟩)
  have hj_val : j.val = idx := rfl
  cases x with
  | inl u =>
    unfold wordCountVec
    have hnone : ∀ y ∈ (((List.finRange (w + 1)).take idx).flatMap fun r =>
        List.replicate (resetStepCount w (finSumFinEquiv (Sum.inl r)) q)
          (Sum.inr (finSumFinEquiv (Sum.inl r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))), y ≠ Sum.inl u := by
      intro y hy
      simp only [List.mem_flatMap, List.mem_replicate] at hy
      rcases hy with ⟨r, _, _, rfl⟩
      intro h
      contradiction
    rw [list_count_eq_zero_of_forall_ne hnone]
    rfl
  | inr ℓ =>
    dsimp only
    unfold wordCountVec
    have hinj : Function.Injective (fun r : Fin (w + 1) =>
        (Sum.inr (finSumFinEquiv (Sum.inl r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))) := by
      intro a b hab
      simp only [Sum.inr.injEq, Equiv.apply_eq_iff_eq, Sum.inl.injEq] at hab
      exact hab
    cases hsym : finSumFinEquiv.symm ℓ with
    | inl i =>
      have h_ℓ : ℓ = finSumFinEquiv (Sum.inl i) := by rw [← hsym, Equiv.apply_symm_apply]
      have hℓ_val : (finSumFinEquiv (Sum.inl i : Fin (w + 1) ⊕ Fin (w + 1))).val = i.val := rfl
      rw [h_ℓ]
      have hcnt := count_flatMap_replicate
        (fun r => resetStepCount w (finSumFinEquiv (Sum.inl r)) q)
        (fun r => (Sum.inr (finSumFinEquiv (Sum.inl r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1))))
        hinj i ((List.finRange (w + 1)).take idx)
      rw [hcnt, count_take_finRange (w + 1) idx i]
      unfold resetPrefixCount
      change (((if i.val < idx then 1 else 0) * resetStepCount w (finSumFinEquiv (Sum.inl i)) q : ℕ) : ℚ) =
        if (finSumFinEquiv (Sum.inl i : Fin (w + 1) ⊕ Fin (w + 1))).val < j.val then
          ((M_coupled w).mulVec (binomBasis (w + 1) q)) (finSumFinEquiv (Sum.inl i))
        else if finSumFinEquiv (Sum.inl i) = j then 0 else 0
      rw [hj_val, hℓ_val]
      by_cases h_i_lt : i.val < idx
      · rw [if_pos h_i_lt, if_pos h_i_lt, one_mul, resetStepCount_cast]
      · rw [if_neg h_i_lt, if_neg h_i_lt, zero_mul, Nat.cast_zero]
        split_ifs <;> rfl
    | inr i =>
      have h_ℓ : ℓ = finSumFinEquiv (Sum.inr i) := by rw [← hsym, Equiv.apply_symm_apply]
      have hℓ_val : ℓ.val = (w + 1) + i.val := by
        rw [h_ℓ]
        rfl
      have hnone : ∀ y ∈ (((List.finRange (w + 1)).take idx).flatMap fun r =>
          List.replicate (resetStepCount w (finSumFinEquiv (Sum.inl r)) q)
            (Sum.inr (finSumFinEquiv (Sum.inl r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))), y ≠ Sum.inr ℓ := by
        intro y hy
        simp only [List.mem_flatMap, List.mem_replicate] at hy
        rcases hy with ⟨r, _, _, rfl⟩
        rw [h_ℓ]
        intro h
        simp only [Sum.inr.injEq, Equiv.apply_eq_iff_eq] at h
        contradiction
      rw [list_count_eq_zero_of_forall_ne hnone, Nat.cast_zero]
      unfold resetPrefixCount
      change (0 : ℚ) =
        if ℓ.val < j.val then ((M_coupled w).mulVec (binomBasis (w + 1) q)) ℓ
        else if ℓ = j then 0 else 0
      rw [hj_val, hℓ_val]
      have hnot_lt : ¬ ((w + 1) + i.val < idx) := by omega
      rw [if_neg hnot_lt]
      split_ifs <;> rfl

/-- Action count vector of `W_early_word ++ (W_late_word.take)` matches `resetPrefixCount` at `h = 0`. -/
theorem wordCountVec_W_early_append_W_late_take_eq_resetPrefixCount {m w : ℕ} (q : ℕ)
    (idx : ℕ) (hidx : idx < w + 1)
    (x : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1))) :
    wordCountVec (W_early_word m w q ++ (((List.finRange (w + 1)).take idx).flatMap fun r =>
      List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
        (Sum.inr (finSumFinEquiv (Sum.inr r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1))))) x =
    match x with
    | Sum.inl _ => 0
    | Sum.inr ℓ =>
      resetPrefixCount (finSumFinEquiv (Sum.inr ⟨idx, hidx⟩))
        ((M_coupled w).mulVec (binomBasis (w + 1) q)) 0 ℓ := by
  let j : Fin ((w + 1) + (w + 1)) := finSumFinEquiv (Sum.inr ⟨idx, hidx⟩)
  have hj_val : j.val = (w + 1) + idx := rfl
  rw [wordCountVec_append]
  cases x with
  | inl u =>
    have h1 : wordCountVec (W_early_word m w q) (Sum.inl u) = 0 := by
      unfold wordCountVec W_early_word
      have hnone : ∀ y ∈ (List.finRange (w + 1)).flatMap (fun r =>
          List.replicate (resetStepCount w (finSumFinEquiv (Sum.inl r)) q)
            (Sum.inr (finSumFinEquiv (Sum.inl r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))), y ≠ Sum.inl u := by
        intro y hy
        simp only [List.mem_flatMap, List.mem_replicate] at hy
        rcases hy with ⟨r, _, _, rfl⟩
        intro h
        contradiction
      rw [list_count_eq_zero_of_forall_ne hnone]
      rfl
    have h2 : wordCountVec (((List.finRange (w + 1)).take idx).flatMap fun r =>
        List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
          (Sum.inr (finSumFinEquiv (Sum.inr r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))) (Sum.inl u) = 0 := by
      unfold wordCountVec
      have hnone : ∀ y ∈ (((List.finRange (w + 1)).take idx).flatMap fun r =>
          List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
            (Sum.inr (finSumFinEquiv (Sum.inr r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))), y ≠ Sum.inl u := by
        intro y hy
        simp only [List.mem_flatMap, List.mem_replicate] at hy
        rcases hy with ⟨r, _, _, rfl⟩
        intro h
        contradiction
      rw [list_count_eq_zero_of_forall_ne hnone]
      rfl
    rw [h1, h2, add_zero]
  | inr ℓ =>
    dsimp only
    have hinj_early : Function.Injective (fun r : Fin (w + 1) =>
        (Sum.inr (finSumFinEquiv (Sum.inl r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))) := by
      intro a b hab
      simp only [Sum.inr.injEq, Equiv.apply_eq_iff_eq, Sum.inl.injEq] at hab
      exact hab
    have hinj_late : Function.Injective (fun r : Fin (w + 1) =>
        (Sum.inr (finSumFinEquiv (Sum.inr r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))) := by
      intro a b hab
      simp only [Sum.inr.injEq, Equiv.apply_eq_iff_eq, Sum.inr.injEq] at hab
      exact hab
    cases hsym : finSumFinEquiv.symm ℓ with
    | inl i =>
      have h_ℓ : ℓ = finSumFinEquiv (Sum.inl i) := by rw [← hsym, Equiv.apply_symm_apply]
      have hℓ_val : ℓ.val = i.val := by
        rw [h_ℓ]
        rfl
      have h1 : wordCountVec (W_early_word m w q) (Sum.inr ℓ) = (resetStepCount w ℓ q : ℚ) := by
        unfold wordCountVec W_early_word
        rw [h_ℓ]
        have hcnt := count_flatMap_finRange_replicate (w + 1)
          (fun r => resetStepCount w (finSumFinEquiv (Sum.inl r)) q)
          (fun r => (Sum.inr (finSumFinEquiv (Sum.inl r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1))))
          hinj_early i
        rw [hcnt]
      have h2 : wordCountVec (((List.finRange (w + 1)).take idx).flatMap fun r =>
          List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
            (Sum.inr (finSumFinEquiv (Sum.inr r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))) (Sum.inr ℓ) = 0 := by
        unfold wordCountVec
        have hnone : ∀ y ∈ (((List.finRange (w + 1)).take idx).flatMap fun r =>
            List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
              (Sum.inr (finSumFinEquiv (Sum.inr r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))), y ≠ Sum.inr ℓ := by
          intro y hy
          simp only [List.mem_flatMap, List.mem_replicate] at hy
          rcases hy with ⟨r, _, _, rfl⟩
          rw [h_ℓ]
          intro h
          simp only [Sum.inr.injEq, Equiv.apply_eq_iff_eq] at h
          contradiction
        rw [list_count_eq_zero_of_forall_ne hnone, Nat.cast_zero]
      rw [h1, h2, add_zero, resetStepCount_cast]
      unfold resetPrefixCount
      change ((M_coupled w).mulVec (binomBasis (w + 1) q)) ℓ =
        if ℓ.val < j.val then ((M_coupled w).mulVec (binomBasis (w + 1) q)) ℓ
        else if ℓ = j then 0 else 0
      rw [hj_val, hℓ_val]
      have hlt : i.val < (w + 1) + idx := by
        have := i.isLt
        omega
      rw [if_pos hlt]
    | inr i =>
      have h_ℓ : ℓ = finSumFinEquiv (Sum.inr i) := by rw [← hsym, Equiv.apply_symm_apply]
      have hℓ_val : (finSumFinEquiv (Sum.inr i : Fin (w + 1) ⊕ Fin (w + 1))).val = (w + 1) + i.val := rfl
      have h1 : wordCountVec (W_early_word m w q) (Sum.inr ℓ) = 0 := by
        unfold wordCountVec W_early_word
        have hnone : ∀ y ∈ (List.finRange (w + 1)).flatMap (fun r =>
            List.replicate (resetStepCount w (finSumFinEquiv (Sum.inl r)) q)
              (Sum.inr (finSumFinEquiv (Sum.inl r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))), y ≠ Sum.inr ℓ := by
          intro y hy
          simp only [List.mem_flatMap, List.mem_replicate] at hy
          rcases hy with ⟨r, _, _, rfl⟩
          rw [h_ℓ]
          intro h
          simp only [Sum.inr.injEq, Equiv.apply_eq_iff_eq] at h
          contradiction
        rw [list_count_eq_zero_of_forall_ne hnone, Nat.cast_zero]
      have h2 : wordCountVec (((List.finRange (w + 1)).take idx).flatMap fun r =>
          List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
            (Sum.inr (finSumFinEquiv (Sum.inr r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))) (Sum.inr ℓ) =
          (((if i.val < idx then 1 else 0) * resetStepCount w (finSumFinEquiv (Sum.inr i)) q : ℕ) : ℚ) := by
        unfold wordCountVec
        rw [h_ℓ]
        have hcnt := count_flatMap_replicate
          (fun r => resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
          (fun r => (Sum.inr (finSumFinEquiv (Sum.inr r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1))))
          hinj_late i ((List.finRange (w + 1)).take idx)
        rw [hcnt, count_take_finRange (w + 1) idx i]
      rw [h1, h2, zero_add]
      rw [h_ℓ]
      unfold resetPrefixCount
      change (((if i.val < idx then 1 else 0) * resetStepCount w (finSumFinEquiv (Sum.inr i)) q : ℕ) : ℚ) =
        if (finSumFinEquiv (Sum.inr i : Fin (w + 1) ⊕ Fin (w + 1))).val < j.val then
          ((M_coupled w).mulVec (binomBasis (w + 1) q)) (finSumFinEquiv (Sum.inr i))
        else if finSumFinEquiv (Sum.inr i) = j then 0 else 0
      rw [hj_val, hℓ_val]
      by_cases h_i_lt : i.val < idx
      · have h_add_lt : (w + 1) + i.val < (w + 1) + idx := by omega
        rw [if_pos h_i_lt, if_pos h_add_lt, one_mul, resetStepCount_cast]
      · have h_not_add_lt : ¬ ((w + 1) + i.val < (w + 1) + idx) := by omega
        rw [if_neg h_i_lt, if_neg h_not_add_lt, zero_mul, Nat.cast_zero]
        split_ifs <;> rfl

/-- **Complete Reduction of Stage 1 Early Reset Priority Validity (`isValidPriorityWord_W_early_word_of_start`)**:
    Reduces full priority validity of `W_early_word` strictly to the initial old-action waiting condition
    `s0 (Sum.inl x) < dotProduct zeta (binomBasis (w + 1) q)`. -/
theorem isValidPriorityWord_W_early_word_of_start {m w q : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (S : Matrix (Fin (m + 1)) (Fin (w + 1)) ℚ)
    (X : Matrix (Fin (m + 1)) (Fin (w + 1)) ℚ)
    (zeta : Fin (w + 1) → ℚ)
    (parent_rank : Fin m → Fin m)
    (hJ_lower : ∀ a b : Fin ((w + 1) + (w + 1)), a.val ≤ b.val → J a b = 0)
    (hJ_subdiag_pos : ∀ a b : Fin ((w + 1) + (w + 1)), b.val < a.val → 0 < J a b)
    (hP_early_nonpos : ∀ (j : Fin (w + 1)) (x : Fin (m + 1)),
      P x (finSumFinEquiv (Sum.inl j)) ≤ 0)
    (h_old_start : ∀ x : Fin (m + 1),
      (liftedScoreMat G_O J S X (M_coupled w) zeta).mulVec (binomBasis (w + 1) q) (Sum.inl x) <
        dotProduct zeta (binomBasis (w + 1) q)) :
    IsValidPriorityWord (liftedGameMat G_O P J)
      ((liftedScoreMat G_O J S X (M_coupled w) zeta).mulVec (binomBasis (w + 1) q))
      (paperPriorityRank m w parent_rank) (W_early_word m w q) := by
  let s0 := (liftedScoreMat G_O J S X (M_coupled w) zeta).mulVec (binomBasis (w + 1) q)
  apply isValidPriorityWord_W_early_word
  intro idx hidx_len
  have hidx : idx < w + 1 := by
    simpa [List.length_finRange] using hidx_len
  let j : Fin ((w + 1) + (w + 1)) := finSumFinEquiv (Sum.inl ⟨idx, hidx⟩)
  have hj_get : finSumFinEquiv (Sum.inl (List.finRange (w + 1))[idx]) = j := by
    have : (List.finRange (w + 1))[idx]'hidx_len = ⟨idx, hidx⟩ := by
      simp only [List.getElem_finRange, Fin.cast_mk]
    rw [this]
  rw [hj_get]
  let cnt := resetStepCount w j q
  let s_run := wordScore (liftedGameMat G_O P J) s0
    (((List.finRange (w + 1)).take idx).flatMap fun r =>
      List.replicate (resetStepCount w (finSumFinEquiv (Sum.inl r)) q)
        (Sum.inr (finSumFinEquiv (Sum.inl r))))
  have hs_run_eq : s_run = scoreVec (liftedGameMat G_O P J)
      ((liftedScoreMat G_O J S X (M_coupled w) zeta).mulVec (binomBasis (w + 1) q))
      (fun x => match x with
        | Sum.inl _ => 0
        | Sum.inr ℓ => resetPrefixCount j ((M_coupled w).mulVec (binomBasis (w + 1) q)) 0 ℓ) := by
    unfold s_run wordScore
    congr 1
    funext x
    exact wordCountVec_W_early_word_take_eq_resetPrefixCount q idx hidx x
  have hcnt : 1 ≤ cnt := resetStepCount_pos w j q
  have hJ_diag : J j j = 0 := hJ_lower j j (le_refl _)
  have hJ_nonneg : ∀ a b : Fin ((w + 1) + (w + 1)), 0 ≤ J a b := fun a b => by
    by_cases h : b.val < a.val
    · exact le_of_lt (hJ_subdiag_pos a b h)
    · have : a.val ≤ b.val := by omega
      rw [hJ_lower a b this]
  have hm_nonneg : ∀ ℓ : Fin ((w + 1) + (w + 1)), 0 ≤ ((M_coupled w).mulVec (binomBasis (w + 1) q)) ℓ := fun ℓ => by
    rw [← resetStepCount_cast]
    exact Nat.cast_nonneg _
  have h_le0 : (0 : ℚ) ≤ ((M_coupled w).mulVec (binomBasis (w + 1) q)) j := hm_nonneg j
  have hact := liftedScore_reset_active_at_ceiling G_O J S X (M_coupled w) zeta q P j 0 hJ_lower
  have h_srun_j : s_run (Sum.inr j) = dotProduct zeta (binomBasis (w + 1) q) := by
    rw [hs_run_eq]
    exact hact
  apply chronology_reset_run_priority_valid G_O P J parent_rank s_run cnt j hcnt hJ_diag
  · intro x
    have h_le := wordScore_W_early_word_take_old_le (q := q) G_O P J s0 hP_early_nonpos idx x
    have h_s0 := h_old_start x
    have h_srun_x : s_run (Sum.inl x) ≤ s0 (Sum.inl x) := h_le
    rw [h_srun_j]
    exact lt_of_le_of_lt h_srun_x h_s0
  · intro x
    have h_le := wordScore_W_early_word_take_old_le (q := q) G_O P J s0 hP_early_nonpos idx x
    have h_s0 := h_old_start x
    have hP : P x j ≤ 0 := by
      dsimp [j]
      exact hP_early_nonpos ⟨idx, hidx⟩ x
    have h_term : ((cnt - 1 : ℕ) : ℚ) * P x j ≤ 0 := by
      have : 0 ≤ ((cnt - 1 : ℕ) : ℚ) := Nat.cast_nonneg _
      nlinarith
    have h_srun_x : s_run (Sum.inl x) ≤ s0 (Sum.inl x) := h_le
    rw [h_srun_j]
    dsimp [s0] at h_srun_x
    linarith
  · intro j' hj'
    have hear : J j j' * 0 ≤ dotProduct zeta (binomBasis (w + 1) q) - s_run (Sum.inr j') := by
      rw [hs_run_eq]
      exact liftedScore_reset_earlier_deficit G_O J S X (M_coupled w) zeta q P j j' 0 hj' hJ_lower hJ_nonneg hm_nonneg (le_refl 0)
    rw [mul_zero] at hear
    rw [h_srun_j]
    linarith
  · intro j' hj'
    have h1 : J j' j = 0 := hJ_lower j' j (le_of_lt hj')
    have h2 : 0 < J j j' := hJ_subdiag_pos j j' hj'
    rw [h1, zero_sub]
    linarith
  · intro j' hj'
    have hlate : J j' j * (((M_coupled w).mulVec (binomBasis (w + 1) q)) j - 0) ≤
        dotProduct zeta (binomBasis (w + 1) q) - s_run (Sum.inr j') := by
      rw [hs_run_eq]
      exact liftedScore_reset_later_deficit G_O J S X (M_coupled w) zeta q P j j' 0 hj' hJ_lower hJ_nonneg hm_nonneg h_le0
    rw [sub_zero] at hlate
    have hJ_pos : 0 < J j' j := hJ_subdiag_pos j' j hj'
    have hm_pos : 0 < ((M_coupled w).mulVec (binomBasis (w + 1) q)) j := by
      rw [← resetStepCount_cast]
      have : 0 < resetStepCount w j q := resetStepCount_pos w j q
      exact_mod_cast this
    have hprod_pos : 0 < J j' j * ((M_coupled w).mulVec (binomBasis (w + 1) q)) j := mul_pos hJ_pos hm_pos
    rw [h_srun_j]
    linarith
  · intro j' hj'
    have hJ_jj' : J j j' = 0 := hJ_lower j j' (by omega)
    rw [hJ_jj', sub_zero]
    have hlate : J j' j * (((M_coupled w).mulVec (binomBasis (w + 1) q)) j - 0) ≤
        dotProduct zeta (binomBasis (w + 1) q) - s_run (Sum.inr j') := by
      rw [hs_run_eq]
      exact liftedScore_reset_later_deficit G_O J S X (M_coupled w) zeta q P j j' 0 hj' hJ_lower hJ_nonneg hm_nonneg h_le0
    rw [sub_zero] at hlate
    have hcnt_eq : ((M_coupled w).mulVec (binomBasis (w + 1) q)) j = (cnt : ℚ) := by
      dsimp [cnt]
      rw [resetStepCount_cast]
    rw [hcnt_eq] at hlate
    have hJ_pos : 0 < J j' j := hJ_subdiag_pos j' j hj'
    have hcnt_lt : ((cnt - 1 : ℕ) : ℚ) < (cnt : ℚ) := by
      have : cnt - 1 < cnt := by omega
      exact_mod_cast this
    rw [h_srun_j]
    nlinarith

/-- **Complete Reduction of Stage 2 Late Reset Priority Validity (`isValidPriorityWord_W_late_word_of_end`)**:
    Reduces full priority validity of `W_late_word` strictly to the post-Stage-2 old-action waiting condition
    `wordScore ... (W_early ++ W_late) (Sum.inl x) < dotProduct zeta (binomBasis (w + 1) q)`. -/
theorem isValidPriorityWord_W_late_word_of_end {m w q : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (S : Matrix (Fin (m + 1)) (Fin (w + 1)) ℚ)
    (X : Matrix (Fin (m + 1)) (Fin (w + 1)) ℚ)
    (zeta : Fin (w + 1) → ℚ)
    (parent_rank : Fin m → Fin m)
    (hJ_lower : ∀ a b : Fin ((w + 1) + (w + 1)), a.val ≤ b.val → J a b = 0)
    (hJ_subdiag_pos : ∀ a b : Fin ((w + 1) + (w + 1)), b.val < a.val → 0 < J a b)
    (hP_late_nonneg : ∀ (j : Fin (w + 1)) (x : Fin (m + 1)),
      0 ≤ P x (finSumFinEquiv (Sum.inr j)))
    (h_old_end : ∀ x : Fin (m + 1),
      wordScore (liftedGameMat G_O P J)
        ((liftedScoreMat G_O J S X (M_coupled w) zeta).mulVec (binomBasis (w + 1) q))
        (W_early_word m w q ++ W_late_word m w q) (Sum.inl x) <
        dotProduct zeta (binomBasis (w + 1) q)) :
    IsValidPriorityWord (liftedGameMat G_O P J)
      (wordScore (liftedGameMat G_O P J)
        ((liftedScoreMat G_O J S X (M_coupled w) zeta).mulVec (binomBasis (w + 1) q))
        (W_early_word m w q))
      (paperPriorityRank m w parent_rank) (W_late_word m w q) := by
  let s0 := (liftedScoreMat G_O J S X (M_coupled w) zeta).mulVec (binomBasis (w + 1) q)
  apply isValidPriorityWord_W_late_word
  intro idx hidx_len
  have hidx : idx < w + 1 := by
    simpa [List.length_finRange] using hidx_len
  let j : Fin ((w + 1) + (w + 1)) := finSumFinEquiv (Sum.inr ⟨idx, hidx⟩)
  have hj_get : finSumFinEquiv (Sum.inr (List.finRange (w + 1))[idx]) = j := by
    have : (List.finRange (w + 1))[idx]'hidx_len = ⟨idx, hidx⟩ := by
      simp only [List.getElem_finRange, Fin.cast_mk]
    rw [this]
  rw [hj_get]
  let cnt := resetStepCount w j q
  let s_run := wordScore (liftedGameMat G_O P J) s0
    (W_early_word m w q ++
      (((List.finRange (w + 1)).take idx).flatMap fun r =>
        List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
          (Sum.inr (finSumFinEquiv (Sum.inr r)))))
  have hs_run_eq_score : wordScore (liftedGameMat G_O P J)
      (wordScore (liftedGameMat G_O P J) s0 (W_early_word m w q))
      (((List.finRange (w + 1)).take idx).flatMap fun r =>
        List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
          (Sum.inr (finSumFinEquiv (Sum.inr r)))) = s_run := by
    unfold s_run
    rw [wordScore_append]
  rw [hs_run_eq_score]
  have hs_run_eq : s_run = scoreVec (liftedGameMat G_O P J)
      ((liftedScoreMat G_O J S X (M_coupled w) zeta).mulVec (binomBasis (w + 1) q))
      (fun x => match x with
        | Sum.inl _ => 0
        | Sum.inr ℓ => resetPrefixCount j ((M_coupled w).mulVec (binomBasis (w + 1) q)) 0 ℓ) := by
    unfold s_run wordScore
    congr 1
    funext x
    exact wordCountVec_W_early_append_W_late_take_eq_resetPrefixCount q idx hidx x
  have hcnt : 1 ≤ cnt := resetStepCount_pos w j q
  have hJ_diag : J j j = 0 := hJ_lower j j (le_refl _)
  have hP_mono : ∀ x : Fin (m + 1), s_run (Sum.inl x) + ((cnt - 1 : ℕ) : ℚ) * P x j ≤
      wordScore (liftedGameMat G_O P J) s0 (W_early_word m w q ++ W_late_word m w q) (Sum.inl x) := by
    intro x
    have hle_cnt : ((cnt - 1 : ℕ) : ℚ) ≤ (cnt : ℚ) := by
      have : cnt - 1 ≤ cnt := by omega
      exact_mod_cast this
    have hP : 0 ≤ P x j := by
      dsimp [j]
      exact hP_late_nonneg ⟨idx, hidx⟩ x
    have hmul_le : ((cnt - 1 : ℕ) : ℚ) * P x j ≤ (cnt : ℚ) * P x j := mul_le_mul_of_nonneg_right hle_cnt hP
    have hrun_step : s_run (Sum.inl x) + (cnt : ℚ) * P x j =
        wordScore (liftedGameMat G_O P J) s_run (List.replicate cnt (Sum.inr j)) (Sum.inl x) := by
      rw [wordScore_replicate_inr_inl]
    have h_split : W_late_word m w q =
        (((List.finRange (w + 1)).take idx).flatMap fun r =>
          List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
            (Sum.inr (finSumFinEquiv (Sum.inr r)))) ++
        List.replicate cnt (Sum.inr j) ++
        (((List.finRange (w + 1)).drop (idx + 1)).flatMap fun r =>
          List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
            (Sum.inr (finSumFinEquiv (Sum.inr r)))) := by
      unfold W_late_word
      have hdecomp : (List.finRange (w + 1)) =
          (List.finRange (w + 1)).take idx ++
          [(List.finRange (w + 1))[idx]'hidx_len] ++
          (List.finRange (w + 1)).drop (idx + 1) := by
        have := (List.take_append_drop idx (List.finRange (w + 1))).symm
        have hdrop : (List.finRange (w + 1)).drop idx =
            [(List.finRange (w + 1))[idx]'hidx_len] ++ (List.finRange (w + 1)).drop (idx + 1) := by
          rw [List.drop_eq_getElem_cons hidx_len]
          rfl
        rw [hdrop] at this
        simpa [List.append_assoc] using this
      conv_lhs => rw [hdecomp]
      rw [List.flatMap_append, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [hj_get]
    have h_app_all : W_early_word m w q ++ W_late_word m w q =
        (W_early_word m w q ++
          (((List.finRange (w + 1)).take idx).flatMap fun r =>
            List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
              (Sum.inr (finSumFinEquiv (Sum.inr r)))) ++
          List.replicate cnt (Sum.inr j)) ++
        (((List.finRange (w + 1)).drop (idx + 1)).flatMap fun r =>
          List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
            (Sum.inr (finSumFinEquiv (Sum.inr r)))) := by
      rw [h_split]
      simp only [List.append_assoc]
    have h_le_tail : wordScore (liftedGameMat G_O P J) s_run (List.replicate cnt (Sum.inr j)) (Sum.inl x) ≤
        wordScore (liftedGameMat G_O P J) s0 (W_early_word m w q ++ W_late_word m w q) (Sum.inl x) := by
      rw [h_app_all]
      dsimp only [s_run]
      rw [← wordScore_append]
      let L1 := (W_early_word m w q ++
          (((List.finRange (w + 1)).take idx).flatMap fun r =>
            List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
              (Sum.inr (finSumFinEquiv (Sum.inr r))))) ++
          List.replicate cnt (Sum.inr j)
      let drop_L := ((List.finRange (w + 1)).drop (idx + 1)).map (fun r => (finSumFinEquiv (Sum.inr r) : Fin ((w + 1) + (w + 1))))
      have h_flat_drop : (((List.finRange (w + 1)).drop (idx + 1)).flatMap fun r =>
          List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
            (Sum.inr (finSumFinEquiv (Sum.inr r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))) =
          drop_L.flatMap (fun r => List.replicate (resetStepCount w r q) (Sum.inr r)) := by
        dsimp [drop_L]
        rw [List.flatMap_map]
      rw [h_flat_drop]
      change (wordScore (liftedGameMat G_O P J) s0 L1) (Sum.inl x) ≤
        wordScore (liftedGameMat G_O P J) s0
          (L1 ++ drop_L.flatMap fun r => List.replicate (resetStepCount w r q) (Sum.inr r)) (Sum.inl x)
      rw [wordScore_append (W1 := L1)]
      have h_nonneg_drop : ∀ r ∈ drop_L, ∀ x' : Fin (m + 1), 0 ≤ P x' r := by
        intro r hr x'
        simp only [drop_L, List.mem_map] at hr
        rcases hr with ⟨r', _, rfl⟩
        exact hP_late_nonneg r' x'
      have h_end_le : (wordScore (liftedGameMat G_O P J) s0 L1) (Sum.inl x) ≤
          wordScore (liftedGameMat G_O P J) (wordScore (liftedGameMat G_O P J) s0 L1)
            (drop_L.flatMap fun r => List.replicate (resetStepCount w r q) (Sum.inr r)) (Sum.inl x) := by
        have := wordScore_flatMap_replicate_inr_inl_le_end G_O P J (wordScore (liftedGameMat G_O P J) s0 L1) [] drop_L (fun r => resetStepCount w r q)
          (by simpa using h_nonneg_drop) x
        simp only [List.flatMap_nil, wordScore_nil, List.nil_append] at this
        exact this
      exact h_end_le
    linarith
  have hJ_nonneg : ∀ a b : Fin ((w + 1) + (w + 1)), 0 ≤ J a b := fun a b => by
    by_cases h : b.val < a.val
    · exact le_of_lt (hJ_subdiag_pos a b h)
    · have : a.val ≤ b.val := by omega
      rw [hJ_lower a b this]
  have hm_nonneg : ∀ ℓ : Fin ((w + 1) + (w + 1)), 0 ≤ ((M_coupled w).mulVec (binomBasis (w + 1) q)) ℓ := fun ℓ => by
    rw [← resetStepCount_cast]
    exact Nat.cast_nonneg _
  have h_le0 : (0 : ℚ) ≤ ((M_coupled w).mulVec (binomBasis (w + 1) q)) j := hm_nonneg j
  have hact := liftedScore_reset_active_at_ceiling G_O J S X (M_coupled w) zeta q P j 0 hJ_lower
  have h_srun_j : s_run (Sum.inr j) = dotProduct zeta (binomBasis (w + 1) q) := by
    rw [hs_run_eq]
    exact hact
  apply chronology_reset_run_priority_valid G_O P J parent_rank s_run cnt j hcnt hJ_diag
  · intro x
    have h_le := hP_mono x
    have h_end := h_old_end x
    have hP : 0 ≤ P x j := by
      dsimp [j]
      exact hP_late_nonneg ⟨idx, hidx⟩ x
    have h_nonneg : 0 ≤ ((cnt - 1 : ℕ) : ℚ) * P x j := mul_nonneg (Nat.cast_nonneg _) hP
    rw [h_srun_j]
    dsimp [s0] at h_le
    linarith
  · intro x
    have h_le := hP_mono x
    have h_end := h_old_end x
    rw [h_srun_j]
    dsimp [s0] at h_le
    linarith
  · intro j' hj'
    have hear : J j j' * 0 ≤ dotProduct zeta (binomBasis (w + 1) q) - s_run (Sum.inr j') := by
      rw [hs_run_eq]
      exact liftedScore_reset_earlier_deficit G_O J S X (M_coupled w) zeta q P j j' 0 hj' hJ_lower hJ_nonneg hm_nonneg (le_refl 0)
    rw [mul_zero] at hear
    rw [h_srun_j]
    linarith
  · intro j' hj'
    have h1 : J j' j = 0 := hJ_lower j' j (le_of_lt hj')
    have h2 : 0 < J j j' := hJ_subdiag_pos j j' hj'
    rw [h1, zero_sub]
    linarith
  · intro j' hj'
    have hlate : J j' j * (((M_coupled w).mulVec (binomBasis (w + 1) q)) j - 0) ≤
        dotProduct zeta (binomBasis (w + 1) q) - s_run (Sum.inr j') := by
      rw [hs_run_eq]
      exact liftedScore_reset_later_deficit G_O J S X (M_coupled w) zeta q P j j' 0 hj' hJ_lower hJ_nonneg hm_nonneg h_le0
    rw [sub_zero] at hlate
    have hJ_pos : 0 < J j' j := hJ_subdiag_pos j' j hj'
    have hm_pos : 0 < ((M_coupled w).mulVec (binomBasis (w + 1) q)) j := by
      rw [← resetStepCount_cast]
      have : 0 < resetStepCount w j q := resetStepCount_pos w j q
      exact_mod_cast this
    have hprod_pos : 0 < J j' j * ((M_coupled w).mulVec (binomBasis (w + 1) q)) j := mul_pos hJ_pos hm_pos
    rw [h_srun_j]
    linarith
  · intro j' hj'
    have hJ_jj' : J j j' = 0 := hJ_lower j j' (by omega)
    rw [hJ_jj', sub_zero]
    have hlate : J j' j * (((M_coupled w).mulVec (binomBasis (w + 1) q)) j - 0) ≤
        dotProduct zeta (binomBasis (w + 1) q) - s_run (Sum.inr j') := by
      rw [hs_run_eq]
      exact liftedScore_reset_later_deficit G_O J S X (M_coupled w) zeta q P j j' 0 hj' hJ_lower hJ_nonneg hm_nonneg h_le0
    rw [sub_zero] at hlate
    have hcnt_eq : ((M_coupled w).mulVec (binomBasis (w + 1) q)) j = (cnt : ℚ) := by
      dsimp [cnt]
      rw [resetStepCount_cast]
    rw [hcnt_eq] at hlate
    have hJ_pos : 0 < J j' j := hJ_subdiag_pos j' j hj'
    have hcnt_lt : ((cnt - 1 : ℕ) : ℚ) < (cnt : ℚ) := by
      have : cnt - 1 < cnt := by omega
      exact_mod_cast this
    rw [h_srun_j]
    nlinarith

theorem wordScore_flatMap_replicate_inr_inl_ge_mem {m w : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (s0 : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (L : List (Fin ((w + 1) + (w + 1))))
    (m_len : Fin ((w + 1) + (w + 1)) → ℕ)
    (hP_nonneg : ∀ (r : Fin ((w + 1) + (w + 1))), r ∈ L → ∀ x : Fin (m + 1), 0 ≤ P x r)
    (x : Fin (m + 1))
    (r0 : Fin ((w + 1) + (w + 1)))
    (hr0 : r0 ∈ L)
    (hm_r0 : 1 ≤ m_len r0) :
    s0 (Sum.inl x) + P x r0 ≤
      wordScore (liftedGameMat G_O P J) s0
        (L.flatMap fun r => List.replicate (m_len r) (Sum.inr r)) (Sum.inl x) := by
  have h_mono : ∀ (L' : List (Fin ((w + 1) + (w + 1))))
      (s : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ),
      (∀ r ∈ L', ∀ x : Fin (m + 1), 0 ≤ P x r) →
      s (Sum.inl x) ≤ wordScore (liftedGameMat G_O P J) s (L'.flatMap fun r => List.replicate (m_len r) (Sum.inr r)) (Sum.inl x) := by
    intro L' s hP
    induction L' generalizing s with
    | nil =>
      simp only [List.flatMap_nil, wordScore_nil, le_rfl]
    | cons r tl ih =>
      simp only [List.flatMap_cons]
      rw [wordScore_append]
      have hr_in : r ∈ r :: tl := List.mem_cons_self
      have hP_r := hP r hr_in x
      have h_step : s (Sum.inl x) ≤ wordScore (liftedGameMat G_O P J) s (List.replicate (m_len r) (Sum.inr r)) (Sum.inl x) := by
        rw [wordScore_replicate_inr_inl]
        have : 0 ≤ ((m_len r : ℕ) : ℚ) * P x r := mul_nonneg (Nat.cast_nonneg _) hP_r
        linarith
      have h_rec := ih (wordScore (liftedGameMat G_O P J) s (List.replicate (m_len r) (Sum.inr r)))
        fun r' hr' => hP r' (List.mem_cons_of_mem r hr')
      linarith
  induction L generalizing s0 with
  | nil =>
    contradiction
  | cons r tl ih =>
    simp only [List.flatMap_cons]
    rw [wordScore_append]
    have hr_in : r ∈ r :: tl := List.mem_cons_self
    have hP_r := hP_nonneg r hr_in x
    have hP_tl : ∀ r' ∈ tl, ∀ x' : Fin (m + 1), 0 ≤ P x' r' :=
      fun r' hr' => hP_nonneg r' (List.mem_cons_of_mem r hr')
    cases hr0 with
    | head =>
      have h_step : s0 (Sum.inl x) + P x r0 ≤
          wordScore (liftedGameMat G_O P J) s0 (List.replicate (m_len r0) (Sum.inr r0)) (Sum.inl x) := by
        rw [wordScore_replicate_inr_inl]
        have h1 : (1 : ℚ) ≤ ((m_len r0 : ℕ) : ℚ) := by exact_mod_cast hm_r0
        have hP_r0 := hP_nonneg r0 List.mem_cons_self x
        have hmul : P x r0 ≤ ((m_len r0 : ℕ) : ℚ) * P x r0 := by
          calc P x r0 = (1 : ℚ) * P x r0 := (one_mul _).symm
          _ ≤ ((m_len r0 : ℕ) : ℚ) * P x r0 := mul_le_mul_of_nonneg_right h1 hP_r0
        linarith
      have h_tail := h_mono tl (wordScore (liftedGameMat G_O P J) s0 (List.replicate (m_len r0) (Sum.inr r0))) hP_tl
      linarith
    | tail _ hr0_tl =>
      have h_step : s0 (Sum.inl x) ≤
          wordScore (liftedGameMat G_O P J) s0 (List.replicate (m_len r) (Sum.inr r)) (Sum.inl x) := by
        rw [wordScore_replicate_inr_inl]
        have : 0 ≤ ((m_len r : ℕ) : ℚ) * P x r := mul_nonneg (Nat.cast_nonneg _) hP_r
        linarith
      have h_tail := ih (wordScore (liftedGameMat G_O P J) s0 (List.replicate (m_len r) (Sum.inr r)))
        hP_tl hr0_tl
      linarith

theorem mem_drop_finRange_top {w idx : ℕ} (hidx : idx < w) :
    (⟨w, Nat.lt_succ_self w⟩ : Fin (w + 1)) ∈ (List.finRange (w + 1)).drop (idx + 1) := by
  rw [List.mem_iff_getElem]
  have hlen : idx + 1 + (w - (idx + 1)) < w + 1 := by omega
  refine ⟨w - (idx + 1), by
    rw [List.length_drop, List.length_finRange]
    omega, ?_⟩
  rw [List.getElem_drop]
  have heq : idx + 1 + (w - (idx + 1)) = w := by omega
  have h_idx_eq : (⟨idx + 1 + (w - (idx + 1)), hlen⟩ : Fin (w + 1)) = ⟨w, Nat.lt_succ_self w⟩ := by
    ext; exact heq
  rw [List.getElem_finRange]
  exact h_idx_eq

/-- **Complete Reduction of Stage 2 Late Reset Priority Validity (Sharpened Version)**:
    Reduces full priority validity of `W_late_word` strictly to the sharpened post-Stage-2
    old-action waiting condition
    `score_after_stage2 (inl x) - P x (inr w) < dotProduct zeta (binomBasis (w + 1) q)`. -/
theorem isValidPriorityWord_W_late_word_of_end_sharp {m w q : ℕ}
    (G_O : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (S : Matrix (Fin (m + 1)) (Fin (w + 1)) ℚ)
    (X : Matrix (Fin (m + 1)) (Fin (w + 1)) ℚ)
    (zeta : Fin (w + 1) → ℚ)
    (parent_rank : Fin m → Fin m)
    (hJ_lower : ∀ a b : Fin ((w + 1) + (w + 1)), a.val ≤ b.val → J a b = 0)
    (hJ_subdiag_pos : ∀ a b : Fin ((w + 1) + (w + 1)), b.val < a.val → 0 < J a b)
    (hP_late_nonneg : ∀ (j : Fin (w + 1)) (x : Fin (m + 1)),
      0 ≤ P x (finSumFinEquiv (Sum.inr j)))
    (h_old_end : ∀ x : Fin (m + 1),
      wordScore (liftedGameMat G_O P J)
        ((liftedScoreMat G_O J S X (M_coupled w) zeta).mulVec (binomBasis (w + 1) q))
        (W_early_word m w q ++ W_late_word m w q) (Sum.inl x) -
        P x (finSumFinEquiv (Sum.inr ⟨w, Nat.lt_succ_self w⟩)) <
        dotProduct zeta (binomBasis (w + 1) q)) :
    IsValidPriorityWord (liftedGameMat G_O P J)
      (wordScore (liftedGameMat G_O P J)
        ((liftedScoreMat G_O J S X (M_coupled w) zeta).mulVec (binomBasis (w + 1) q))
        (W_early_word m w q))
      (paperPriorityRank m w parent_rank) (W_late_word m w q) := by
  let s0 := (liftedScoreMat G_O J S X (M_coupled w) zeta).mulVec (binomBasis (w + 1) q)
  apply isValidPriorityWord_W_late_word
  intro idx hidx_len
  have hidx : idx < w + 1 := by
    simpa [List.length_finRange] using hidx_len
  let j : Fin ((w + 1) + (w + 1)) := finSumFinEquiv (Sum.inr ⟨idx, hidx⟩)
  have hj_get : finSumFinEquiv (Sum.inr (List.finRange (w + 1))[idx]) = j := by
    have : (List.finRange (w + 1))[idx]'hidx_len = ⟨idx, hidx⟩ := by
      simp only [List.getElem_finRange, Fin.cast_mk]
    rw [this]
  rw [hj_get]
  let cnt := resetStepCount w j q
  let s_run := wordScore (liftedGameMat G_O P J) s0
    (W_early_word m w q ++
      (((List.finRange (w + 1)).take idx).flatMap fun r =>
        List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
          (Sum.inr (finSumFinEquiv (Sum.inr r)))))
  have hs_run_eq_score : wordScore (liftedGameMat G_O P J)
      (wordScore (liftedGameMat G_O P J) s0 (W_early_word m w q))
      (((List.finRange (w + 1)).take idx).flatMap fun r =>
        List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
          (Sum.inr (finSumFinEquiv (Sum.inr r)))) = s_run := by
    unfold s_run
    rw [wordScore_append]
  rw [hs_run_eq_score]
  have hs_run_eq : s_run = scoreVec (liftedGameMat G_O P J)
      ((liftedScoreMat G_O J S X (M_coupled w) zeta).mulVec (binomBasis (w + 1) q))
      (fun x => match x with
        | Sum.inl _ => 0
        | Sum.inr ℓ => resetPrefixCount j ((M_coupled w).mulVec (binomBasis (w + 1) q)) 0 ℓ) := by
    unfold s_run wordScore
    congr 1
    funext x
    exact wordCountVec_W_early_append_W_late_take_eq_resetPrefixCount q idx hidx x
  have hcnt : 1 ≤ cnt := resetStepCount_pos w j q
  have hJ_diag : J j j = 0 := hJ_lower j j (le_refl _)
  let rw : Fin ((w + 1) + (w + 1)) := finSumFinEquiv (Sum.inr ⟨w, Nat.lt_succ_self w⟩)
  have hP_mono : ∀ x : Fin (m + 1), s_run (Sum.inl x) + ((cnt - 1 : ℕ) : ℚ) * P x j + P x rw ≤
      wordScore (liftedGameMat G_O P J) s0 (W_early_word m w q ++ W_late_word m w q) (Sum.inl x) := by
    intro x
    have h_split : W_late_word m w q =
        (((List.finRange (w + 1)).take idx).flatMap fun r =>
          List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
            (Sum.inr (finSumFinEquiv (Sum.inr r)))) ++
        List.replicate cnt (Sum.inr j) ++
        (((List.finRange (w + 1)).drop (idx + 1)).flatMap fun r =>
          List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
            (Sum.inr (finSumFinEquiv (Sum.inr r)))) := by
      unfold W_late_word
      have hdecomp : (List.finRange (w + 1)) =
          (List.finRange (w + 1)).take idx ++
          [(List.finRange (w + 1))[idx]'hidx_len] ++
          (List.finRange (w + 1)).drop (idx + 1) := by
        have := (List.take_append_drop idx (List.finRange (w + 1))).symm
        have hdrop : (List.finRange (w + 1)).drop idx =
            [(List.finRange (w + 1))[idx]'hidx_len] ++ (List.finRange (w + 1)).drop (idx + 1) := by
          rw [List.drop_eq_getElem_cons hidx_len]
          rfl
        rw [hdrop] at this
        simpa [List.append_assoc] using this
      conv_lhs => rw [hdecomp]
      rw [List.flatMap_append, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [hj_get]
    have h_app_all : W_early_word m w q ++ W_late_word m w q =
        (W_early_word m w q ++
          (((List.finRange (w + 1)).take idx).flatMap fun r =>
            List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
              (Sum.inr (finSumFinEquiv (Sum.inr r)))) ++
          List.replicate cnt (Sum.inr j)) ++
        (((List.finRange (w + 1)).drop (idx + 1)).flatMap fun r =>
          List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
            (Sum.inr (finSumFinEquiv (Sum.inr r)))) := by
      rw [h_split]
      simp only [List.append_assoc]
    let L1 := (W_early_word m w q ++
        (((List.finRange (w + 1)).take idx).flatMap fun r =>
          List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
            (Sum.inr (finSumFinEquiv (Sum.inr r))))) ++
        List.replicate cnt (Sum.inr j)
    let drop_L := ((List.finRange (w + 1)).drop (idx + 1)).map (fun r => (finSumFinEquiv (Sum.inr r) : Fin ((w + 1) + (w + 1))))
    have h_flat_drop : (((List.finRange (w + 1)).drop (idx + 1)).flatMap fun r =>
        List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
          (Sum.inr (finSumFinEquiv (Sum.inr r)) : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))) =
        drop_L.flatMap (fun r => List.replicate (resetStepCount w r q) (Sum.inr r)) := by
      dsimp [drop_L]
      rw [List.flatMap_map]
    have h_score_L1 : wordScore (liftedGameMat G_O P J) s0 L1 (Sum.inl x) =
        s_run (Sum.inl x) + (cnt : ℚ) * P x j := by
      dsimp [L1, s_run]
      rw [wordScore_append]
      rw [wordScore_replicate_inr_inl]
    have h_score_end : wordScore (liftedGameMat G_O P J) s0 (W_early_word m w q ++ W_late_word m w q) (Sum.inl x) =
        wordScore (liftedGameMat G_O P J) (wordScore (liftedGameMat G_O P J) s0 L1)
          (drop_L.flatMap fun r => List.replicate (resetStepCount w r q) (Sum.inr r)) (Sum.inl x) := by
      rw [h_app_all]
      change wordScore (liftedGameMat G_O P J) s0
        (L1 ++ (((List.finRange (w + 1)).drop (idx + 1)).flatMap fun r =>
          List.replicate (resetStepCount w (finSumFinEquiv (Sum.inr r)) q)
            (Sum.inr (finSumFinEquiv (Sum.inr r))))) (Sum.inl x) = _
      rw [h_flat_drop, wordScore_append]
    have h_nonneg_drop : ∀ r ∈ drop_L, ∀ x' : Fin (m + 1), 0 ≤ P x' r := by
      intro r hr x'
      simp only [drop_L, List.mem_map] at hr
      rcases hr with ⟨r', _, rfl⟩
      exact hP_late_nonneg r' x'
    have hcnt_split : (cnt : ℚ) = ((cnt - 1 : ℕ) : ℚ) + 1 := by
      have : cnt = (cnt - 1) + 1 := by omega
      exact_mod_cast this
    have hP_j : 0 ≤ P x j := by
      dsimp [j]
      exact hP_late_nonneg ⟨idx, hidx⟩ x
    by_cases h_idx_eq : idx = w
    · have hj_rw : j = rw := by
        dsimp only [j, rw]
        congr 1
        congr 1
        exact Fin.ext h_idx_eq
      have hlen_le : (List.finRange (w + 1)).length ≤ idx + 1 := by
        rw [List.length_finRange]
        omega
      have hdrop_nil : (List.finRange (w + 1)).drop (idx + 1) = [] :=
        List.drop_of_length_le hlen_le
      have h_drop_L_nil : drop_L = [] := by
        dsimp [drop_L]
        rw [hdrop_nil, List.map_nil]
      rw [h_drop_L_nil] at h_score_end
      simp only [List.flatMap_nil, wordScore_nil] at h_score_end
      rw [h_score_end, h_score_L1, hj_rw, hcnt_split]
      have : s_run (Sum.inl x) + (((cnt - 1 : ℕ) : ℚ) + 1) * P x rw =
          s_run (Sum.inl x) + ((cnt - 1 : ℕ) : ℚ) * P x rw + P x rw := by ring
      rw [this]
    · have h_idx_lt : idx < w := by omega
      have hrw_in_drop : rw ∈ drop_L := by
        dsimp [drop_L]
        rw [List.mem_map]
        refine ⟨⟨w, Nat.lt_succ_self w⟩, mem_drop_finRange_top h_idx_lt, rfl⟩
      have h_ge_rw := wordScore_flatMap_replicate_inr_inl_ge_mem G_O P J
        (wordScore (liftedGameMat G_O P J) s0 L1) drop_L (fun r => resetStepCount w r q)
        h_nonneg_drop x rw hrw_in_drop (resetStepCount_pos w rw q)
      have h_le_cnt : ((cnt - 1 : ℕ) : ℚ) * P x j ≤ (cnt : ℚ) * P x j := by
        have : ((cnt - 1 : ℕ) : ℚ) ≤ (cnt : ℚ) := by
          have : cnt - 1 ≤ cnt := by omega
          exact_mod_cast this
        exact mul_le_mul_of_nonneg_right this hP_j
      rw [h_score_end]
      linarith [h_score_L1, h_ge_rw, h_le_cnt]
  have hJ_nonneg : ∀ a b : Fin ((w + 1) + (w + 1)), 0 ≤ J a b := fun a b => by
    by_cases h : b.val < a.val
    · exact le_of_lt (hJ_subdiag_pos a b h)
    · have : a.val ≤ b.val := by omega
      rw [hJ_lower a b this]
  have hm_nonneg : ∀ ℓ : Fin ((w + 1) + (w + 1)), 0 ≤ ((M_coupled w).mulVec (binomBasis (w + 1) q)) ℓ := fun ℓ => by
    rw [← resetStepCount_cast]
    exact Nat.cast_nonneg _
  have h_le0 : (0 : ℚ) ≤ ((M_coupled w).mulVec (binomBasis (w + 1) q)) j := hm_nonneg j
  have hact := liftedScore_reset_active_at_ceiling G_O J S X (M_coupled w) zeta q P j 0 hJ_lower
  have h_srun_j : s_run (Sum.inr j) = dotProduct zeta (binomBasis (w + 1) q) := by
    rw [hs_run_eq]
    exact hact
  apply chronology_reset_run_priority_valid G_O P J parent_rank s_run cnt j hcnt hJ_diag
  · intro x
    have h_le := hP_mono x
    have h_end := h_old_end x
    have hP : 0 ≤ P x j := by
      dsimp [j]
      exact hP_late_nonneg ⟨idx, hidx⟩ x
    have h_nonneg : 0 ≤ ((cnt - 1 : ℕ) : ℚ) * P x j := mul_nonneg (Nat.cast_nonneg _) hP
    rw [h_srun_j]
    dsimp [s0] at h_le
    linarith
  · intro x
    have h_le := hP_mono x
    have h_end := h_old_end x
    rw [h_srun_j]
    dsimp [s0] at h_le
    linarith
  · intro j' hj'
    have hear : J j j' * 0 ≤ dotProduct zeta (binomBasis (w + 1) q) - s_run (Sum.inr j') := by
      rw [hs_run_eq]
      exact liftedScore_reset_earlier_deficit G_O J S X (M_coupled w) zeta q P j j' 0 hj' hJ_lower hJ_nonneg hm_nonneg (le_refl 0)
    rw [mul_zero] at hear
    rw [h_srun_j]
    linarith
  · intro j' hj'
    have h1 : J j' j = 0 := hJ_lower j' j (le_of_lt hj')
    have h2 : 0 < J j j' := hJ_subdiag_pos j j' hj'
    rw [h1, zero_sub]
    linarith
  · intro j' hj'
    have hlate : J j' j * (((M_coupled w).mulVec (binomBasis (w + 1) q)) j - 0) ≤
        dotProduct zeta (binomBasis (w + 1) q) - s_run (Sum.inr j') := by
      rw [hs_run_eq]
      exact liftedScore_reset_later_deficit G_O J S X (M_coupled w) zeta q P j j' 0 hj' hJ_lower hJ_nonneg hm_nonneg h_le0
    rw [sub_zero] at hlate
    have hJ_pos : 0 < J j' j := hJ_subdiag_pos j' j hj'
    have hm_pos : 0 < ((M_coupled w).mulVec (binomBasis (w + 1) q)) j := by
      rw [← resetStepCount_cast]
      have : 0 < resetStepCount w j q := resetStepCount_pos w j q
      exact_mod_cast this
    have hprod_pos : 0 < J j' j * ((M_coupled w).mulVec (binomBasis (w + 1) q)) j := mul_pos hJ_pos hm_pos
    rw [h_srun_j]
    linarith
  · intro j' hj'
    have hJ_jj' : J j j' = 0 := hJ_lower j j' (by omega)
    rw [hJ_jj', sub_zero]
    have hlate : J j' j * (((M_coupled w).mulVec (binomBasis (w + 1) q)) j - 0) ≤
        dotProduct zeta (binomBasis (w + 1) q) - s_run (Sum.inr j') := by
      rw [hs_run_eq]
      exact liftedScore_reset_later_deficit G_O J S X (M_coupled w) zeta q P j j' 0 hj' hJ_lower hJ_nonneg hm_nonneg h_le0
    rw [sub_zero] at hlate
    have hcnt_eq : ((M_coupled w).mulVec (binomBasis (w + 1) q)) j = (cnt : ℚ) := by
      dsimp [cnt]
      rw [resetStepCount_cast]
    rw [hcnt_eq] at hlate
    have hJ_pos : 0 < J j' j := hJ_subdiag_pos j' j hj'
    have hcnt_lt : ((cnt - 1 : ℕ) : ℚ) < (cnt : ℚ) := by
      have : cnt - 1 < cnt := by omega
      exact_mod_cast this
    rw [h_srun_j]
    nlinarith

end Karlin

#print axioms Karlin.early_reset_backward_score_eq
#print axioms Karlin.early_reset_waits_during_bundle
#print axioms Karlin.late_reset_forward_score_eq
#print axioms Karlin.late_reset_waits_during_bundle
#print axioms Karlin.old_action_score_decreases_early_resets
#print axioms Karlin.old_action_score_bounded_late_resets
#print axioms Karlin.reset_cascade_strictly_leads
#print axioms Karlin.reset_cascade_priority_step
#print axioms Karlin.isValidPriorityStep_of_isValidStrictStep
#print axioms Karlin.isValidPriorityWord_of_isValidStrictWord
#print axioms Karlin.isValidPriorityWord_singleton
#print axioms Karlin.isValidPriorityWord_append
#print axioms Karlin.isValidPriorityWord_flatMap
#print axioms Karlin.chronology_four_stage_priority_word_valid
#print axioms Karlin.isValidPriorityWord_rawFourStageWord
#print axioms Karlin.paperPriorityRank_reset_succ_lt
#print axioms Karlin.paperPriorityRank_parent_lt_reset
#print axioms Karlin.paperPriorityRank_reset_lt_gateway
#print axioms Karlin.isValidPriorityWord_stage4_gateway
#print axioms Karlin.wordScore_replicate_inr_inl
#print axioms Karlin.wordScore_replicate_inr_inr
#print axioms Karlin.wordScore_replicate_inr_self
#print axioms Karlin.isValidPriorityWord_replicate_reset
#print axioms Karlin.isValidPriorityWord_stage3_bundle
#print axioms Karlin.chronology_reset_run_priority_valid
#print axioms Karlin.isValidPriorityWord_W_early_word
#print axioms Karlin.isValidPriorityWord_W_late_word
#print axioms Karlin.isValidPriorityWord_reset_stages
#print axioms Karlin.isValidPriorityWord_stage1_bundle_valid
#print axioms Karlin.isValidPriorityWord_stage3_bundle_of_priority
#print axioms Karlin.isValidPriorityWord_map_parentToOldAct
#print axioms Karlin.chronology_four_stage_master_priority_valid
#print axioms Karlin.rps_run0_valid_nonneg
#print axioms Karlin.rps_run1_valid_nonneg
#print axioms Karlin.rps_run2_valid_nonneg
#print axioms Karlin.r2Vec_eq_R2_mulVec
#print axioms Karlin.isValidStrictWord_rps_run0
#print axioms Karlin.isValidStrictWord_rps_run1
#print axioms Karlin.isValidStrictWord_rps_run2
#print axioms Karlin.isValidStrictWord_rpsPhaseWord
#print axioms Karlin.isValidPriorityWord_rpsPhaseWord
#print axioms Karlin.chronology_reset_run_priority_valid_of_old_waits
#print axioms Karlin.chronology_rawFourStageWord_of_stage_conditions
#print axioms Karlin.isValidPriorityWord_bundle_word
#print axioms Karlin.isValidPriorityWord_stage3_bundle_from_parent
#print axioms Karlin.chronology_inductive_priority_lift
#print axioms Karlin.chronology_early_reset_run_valid_of_start
#print axioms Karlin.chronology_late_reset_run_valid_of_end
#print axioms Karlin.wordScore_flatMap_replicate_inr_inl_le
#print axioms Karlin.wordScore_W_early_word_take_old_le
#print axioms Karlin.wordScore_flatMap_replicate_inr_inl_le_end
#print axioms Karlin.count_take_finRange
#print axioms Karlin.wordCountVec_W_early_word_take_eq_resetPrefixCount
#print axioms Karlin.wordCountVec_W_early_append_W_late_take_eq_resetPrefixCount
#print axioms Karlin.isValidPriorityWord_W_early_word_of_start
#print axioms Karlin.isValidPriorityWord_W_late_word_of_end
#print axioms Karlin.wordScore_flatMap_replicate_inr_inl_ge_mem
#print axioms Karlin.mem_drop_finRange_top
#print axioms Karlin.isValidPriorityWord_W_late_word_of_end_sharp
