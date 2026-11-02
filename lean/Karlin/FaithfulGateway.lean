import Karlin.FaithfulClock

/-! The endpoint action on the actual consecutive parent window.  All score and
priority claims refer to its literal word; no realized-clock assumptions enter. -/

namespace Karlin.FaithfulGateway

open scoped BigOperators
open FaithfulClock FaithfulWindow

variable {k : ℕ} (P : Clock k)

abbrev Act := Fin P.m ⊕ Fin 1

def game : Matrix (Act P) (Act P) ℚ :=
  Matrix.fromBlocks P.A (fun i _ => -(P.A P.b i + P.v i))
    (fun _ j => P.A P.b j + P.v j) 0

def initial (a n : ℕ) (h delta : ℚ) : Act P → ℚ :=
  Sum.elim (fun i => P.entry a i + h)
    (fun _ => P.entry a P.b + h - n + delta)

def priority : Act P → Fin (P.m + 1) :=
  Sum.elim (fun i => (P.rank i).castSucc) (fun _ => Fin.last P.m)

def oldWord (a n : ℕ) : List (Act P) :=
  (consecutiveWord P.word a n).map Sum.inl ++ [Sum.inr 0]

theorem game_skew : IsSkewSymmetric (game P) := by
  intro x y
  cases x <;> cases y <;> simp [game, Matrix.fromBlocks]
  exact P.skew _ _

/-- The sum-indexed game is exactly the paper's finite-indexed old game. -/
theorem game_eq_paper (x y : Act P) :
    game P x y = AdjoinLeaderEndpointG P.A P.b P.v
      (finSumFinEquiv x) (finSumFinEquiv y) := by
  cases x <;> cases y <;> simp [game, AdjoinLeaderEndpointG]

theorem parent_score (a n : ℕ) (h delta : ℚ) (W : List (Fin P.m)) (i : Fin P.m) :
    wordScore (game P) (initial P a n h delta) (W.map Sum.inl) (Sum.inl i) =
      wordScore P.A (P.entry a) W i + h := by
  simp only [wordScore, scoreVec, Fintype.sum_sum_type,
    wordCountVec_map_inl_inl, wordCountVec_map_inl_inr, mul_zero, Finset.sum_const_zero,
    add_zero, game, Matrix.fromBlocks_apply₁₁, initial, Sum.elim_inl]
  ring

theorem gateway_score (a n : ℕ) (h delta : ℚ) (W : List (Fin P.m)) :
    wordScore (game P) (initial P a n h delta) (W.map Sum.inl) (Sum.inr 0) =
      wordScore P.A (P.entry a) W P.b + h - n + delta +
        dotProduct P.v (wordCountVec W) := by
  simp only [wordScore, scoreVec, Fintype.sum_sum_type,
    wordCountVec_map_inl_inl, wordCountVec_map_inl_inr, mul_zero, Finset.sum_const_zero,
    add_zero, game, Matrix.fromBlocks_apply₂₁, initial, Sum.elim_inr]
  simp only [add_mul, Finset.sum_add_distrib, dotProduct]
  ring

/-- Exact equation (gatewaygap), allowing negative parent counter entries. -/
theorem gateway_gap (a : ℕ) (ha : P.Q ≤ a) (n r : ℕ) (h delta : ℚ) :
    wordScore (game P) (initial P a n h delta)
        (((consecutiveWord P.word a n).take r).map Sum.inl) (Sum.inr 0) -
      wordScore (game P) (initial P a n h delta)
        (((consecutiveWord P.word a n).take r).map Sum.inl) (Sum.inl P.b) =
      delta - dotProduct P.v (wordCountVec ((consecutiveWord P.word a n).drop r)) := by
  rw [gateway_score, parent_score]
  have hc := dotCount_take_add_drop P.v (consecutiveWord P.word a n) r
  rw [P.consecutive_counter a ha n] at hc
  linarith

/-- At every proper parent prefix, the actual scheduled parent defeats g by the
fixed margin delta0-delta. Parent b need not remain a maximizer. -/
theorem gateway_waits (a : ℕ) (ha : P.Q ≤ a) (n r : ℕ)
    (hr : r < (consecutiveWord P.word a n).length) (h delta : ℚ) :
    wordScore (game P) (initial P a n h delta)
        (((consecutiveWord P.word a n).take r).map Sum.inl) (Sum.inr 0) ≤
      wordScore (game P) (initial P a n h delta)
        (((consecutiveWord P.word a n).take r).map Sum.inl)
        (Sum.inl ((consecutiveWord P.word a n)[r])) - (P.delta0 - delta) := by
  have hv := (consecutiveWord_valid_score P.A P.rank P.word P.entry P.Q
    P.valid P.phase_transition a ha n).1
  have hh := height_eq P.b
    (wordScore P.A (P.entry a) ((consecutiveWord P.word a n).take r))
    ((consecutiveWord P.word a n)[r]) (fun j => (hv r hr j).1)
  have hm := P.consecutive_marker a ha n r hr
  rw [hh] at hm
  have hg := gateway_gap P a ha n r h delta
  rw [parent_score] at hg ⊢
  linarith

theorem parent_word_valid (a : ℕ) (ha : P.Q ≤ a) (n : ℕ) (h delta : ℚ)
    (hd : delta < P.delta0) :
    IsValidPriorityWord (game P) (initial P a n h delta) (priority P)
      ((consecutiveWord P.word a n).map Sum.inl) := by
  have hv := (consecutiveWord_valid_score P.A P.rank P.word P.entry P.Q
    P.valid P.phase_transition a ha n).1
  intro r hr x
  have hr' : r < (consecutiveWord P.word a n).length := by simpa using hr
  rw [← List.map_take, List.getElem_map]
  cases x with
  | inl i =>
      rw [parent_score, parent_score]
      have hi := hv r hr' i
      refine ⟨by linarith [hi.1], ?_⟩
      intro hne heq
      have hni : i ≠ (consecutiveWord P.word a n)[r] := fun h => hne (congrArg Sum.inl h)
      exact hi.2 hni (by linarith)
  | inr i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      have hw := gateway_waits P a ha n r hr' h delta
      refine ⟨by linarith, ?_⟩
      intro _ heq
      linarith

theorem endpoint_gateway_wins (a : ℕ) (ha : P.Q ≤ a) (n : ℕ) (h delta : ℚ)
    (hd : 0 < delta) (i : Fin P.m) :
    wordScore (game P) (initial P a n h delta)
        ((consecutiveWord P.word a n).map Sum.inl) (Sum.inl i) <
      wordScore (game P) (initial P a n h delta)
        ((consecutiveWord P.word a n).map Sum.inl) (Sum.inr 0) := by
  have he := (consecutiveWord_valid_score P.A P.rank P.word P.entry P.Q
    P.valid P.phase_transition a ha n).2
  have hh := le_height P.b (P.entry (a + n)) i
  rw [P.entry_height (a + n) (by omega)] at hh
  rw [parent_score, gateway_score, he, P.consecutive_counter a ha n]
  linarith

/-- The old word consists of precisely the parent interval followed by one g. -/
theorem oldWord_valid (a : ℕ) (ha : P.Q ≤ a) (n : ℕ) (h delta : ℚ)
    (hd0 : 0 < delta) (hd : delta < P.delta0) :
    IsValidPriorityWord (game P) (initial P a n h delta) (priority P) (oldWord P a n) := by
  apply (isValidPriorityWord_append _ _ _ _ _).2
  refine ⟨parent_word_valid P a ha n h delta hd, ?_⟩
  apply (isValidPriorityWord_singleton _ _ _ _).2
  apply isValidPriorityStep_of_isValidStrictStep
  intro x hx
  cases x with
  | inl i => exact endpoint_gateway_wins P a ha n h delta hd0 i
  | inr i => exact (hx (congrArg Sum.inr (Subsingleton.elim i 0))).elim

theorem after_gateway_parent_score (a : ℕ) (ha : P.Q ≤ a) (n : ℕ)
    (h delta : ℚ) (i : Fin P.m) :
    wordScore (game P) (initial P a n h delta) (oldWord P a n) (Sum.inl i) =
      P.entry (a + n) i + P.A i P.b - P.v i + h := by
  have he := (consecutiveWord_valid_score P.A P.rank P.word P.entry P.Q
    P.valid P.phase_transition a ha n).2
  rw [oldWord, wordScore_append, wordScore_singleton, parent_score, he]
  have hs := P.skew P.b i
  simp only [game, Matrix.fromBlocks_apply₁₂]
  linarith

theorem after_gateway_score (a : ℕ) (ha : P.Q ≤ a) (n : ℕ) (h delta : ℚ) :
    wordScore (game P) (initial P a n h delta) (oldWord P a n) (Sum.inr 0) =
      P.entry (a + n) P.b + h + delta := by
  have he := (consecutiveWord_valid_score P.A P.rank P.word P.entry P.Q
    P.valid P.phase_transition a ha n).2
  rw [oldWord, wordScore_append, wordScore_singleton, gateway_score, he,
    P.consecutive_counter a ha n]
  simp [game, Matrix.fromBlocks_apply₂₂]
  ring

/-- Post-gateway parent leadership follows from the two initial parent plays and
support safety. No sign restriction on the counter is imposed. -/
theorem after_gateway_parent_max (a : ℕ) (ha : P.Q ≤ a) (n : ℕ) (h delta : ℚ) :
    (∀ i : Fin P.m,
      wordScore (game P) (initial P a n h delta) (oldWord P a n) (Sum.inl i) ≤
        P.entry (a + n) P.b + h) ∧
    wordScore (game P) (initial P a n h delta) (oldWord P a n) (Sum.inl P.b) =
        P.entry (a + n) P.b + h := by
  have hq : P.Q ≤ a + n := by omega
  constructor
  · intro i
    rw [after_gateway_parent_score P a ha n h delta i]
    by_cases hv : P.v i = 0
    · have hl := P.second_entry_leader (a + n) hq i
      rw [hv]
      linarith
    · have hs := P.support_safe (a + n) hq i hv
      rw [skew_diag_zero P.skew, P.counter_entry] at hs
      change P.entry (a + n) i + P.A i P.b - P.v i <
        P.entry (a + n) P.b + 0 - 0 at hs
      linarith
  · rw [after_gateway_parent_score P a ha n h delta P.b, skew_diag_zero P.skew, P.counter_entry]
    ring

theorem oldWord_parent_count (a n : ℕ) (i : Fin P.m) :
    wordCountVec (oldWord P a n) (Sum.inl i) =
      wordCountVec (consecutiveWord P.word a n) i := by
  rw [oldWord, wordCountVec_append, wordCountVec_map_inl_inl]
  simp [wordCountVec]

theorem oldWord_gateway_count (a n : ℕ) :
    wordCountVec (oldWord P a n) (Sum.inr 0) = 1 := by
  rw [oldWord, wordCountVec_append, wordCountVec_map_inl_inr]
  simp [wordCountVec]

end Karlin.FaithfulGateway
