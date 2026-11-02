import Karlin.FaithfulGateway
import Karlin.FaithfulGrowth

/-! Reset waiting during the literal parent window and endpoint action. -/

namespace Karlin.FaithfulWaiting

open scoped BigOperators
open FaithfulClock FaithfulWindow

variable {k nR : ℕ} (P : Clock k)

abbrev Old := FaithfulGateway.Act P
abbrev Act := Old P ⊕ Fin nR

def parentStage (W : List (Fin P.m)) : List (Act (nR := nR) P) :=
  (W.map (Sum.inl : Fin P.m → Old P)).map Sum.inl

theorem old_score (C : Matrix (Old P) (Fin nR) ℚ) (J : Matrix (Fin nR) (Fin nR) ℚ)
    (s0 : Act (nR := nR) P → ℚ) (a n : ℕ) (h delta : ℚ)
    (hs : ∀ x, s0 (Sum.inl x) = FaithfulGateway.initial P a n h delta x)
    (W : List (Old P)) (i : Old P) :
    wordScore (liftedGameMat (FaithfulGateway.game P) C J) s0 (W.map Sum.inl) (Sum.inl i) =
      wordScore (FaithfulGateway.game P) (FaithfulGateway.initial P a n h delta) W i := by
  unfold liftedGameMat
  rw [wordScore_map_inl_old]
  congr 1
  exact funext hs

theorem parent_score (C : Matrix (Old P) (Fin nR) ℚ) (J : Matrix (Fin nR) (Fin nR) ℚ)
    (s0 : Act (nR := nR) P → ℚ) (a n : ℕ) (h delta : ℚ)
    (hs : ∀ x, s0 (Sum.inl x) = FaithfulGateway.initial P a n h delta x)
    (W : List (Fin P.m)) (i : Fin P.m) :
    wordScore (liftedGameMat (FaithfulGateway.game P) C J) s0 (parentStage P W) (Sum.inl (Sum.inl i)) =
      wordScore P.A (P.entry a) W i + h := by
  rw [parentStage, old_score P C J s0 a n h delta hs, FaithfulGateway.parent_score]

theorem reset_forward (C : Matrix (Old P) (Fin nR) ℚ) (J : Matrix (Fin nR) (Fin nR) ℚ)
    (s0 : Act (nR := nR) P → ℚ) (W : List (Fin P.m)) (j : Fin nR) :
    wordScore (liftedGameMat (FaithfulGateway.game P) C J) s0 (parentStage P W) (Sum.inr j) =
      s0 (Sum.inr j) - ∑ i : Fin P.m, C (Sum.inl i) j * wordCountVec W i := by
  rw [parentStage]
  unfold liftedGameMat
  rw [wordScore_map_inl_new]
  simp [Fintype.sum_sum_type, wordCountVec_map_inl_inl, wordCountVec_map_inl_inr]

theorem coupling_oldWord_count (C : Matrix (Old P) (Fin nR) ℚ) (a n : ℕ) (j : Fin nR) :
    (∑ x : Old P, C x j * wordCountVec (FaithfulGateway.oldWord P a n) x) =
      C (Sum.inr 0) j + ∑ i : Fin P.m, C (Sum.inl i) j *
        wordCountVec (consecutiveWord P.word a n) i := by
  simp only [FaithfulGateway.oldWord, wordCountVec_append, Fintype.sum_sum_type,
    wordCountVec_map_inl_inl, wordCountVec_map_inl_inr]
  simp [wordCountVec, List.count_singleton, add_comm]

/-- Actual interpolation data, via P-transpose times the exact old-word table,
imply the reset initial score used in the backward waiting calculation. -/
theorem reset_initial_of_count_table {w : ℕ}
    (C : Matrix (Old P) (Fin nR) ℚ) (X : Matrix (Old P) (Fin w) ℚ) (v : Fin w → ℚ)
    (a n : ℕ) (zeta : ℚ) (Jm initialReset : Fin nR → ℚ)
    (hcount : wordCountVec (FaithfulGateway.oldWord P a n) = X.mulVec v)
    (hinit : ∀ j, initialReset j = zeta - Jm j + (C.transpose * X).mulVec v j) :
    ∀ j, initialReset j = zeta - Jm j + C (Sum.inr 0) j +
      ∑ i : Fin P.m, C (Sum.inl i) j * wordCountVec (consecutiveWord P.word a n) i := by
  intro j
  rw [hinit j, ← Matrix.mulVec_mulVec, ← hcount]
  change zeta - Jm j + (∑ x : Old P, C x j * wordCountVec (FaithfulGateway.oldWord P a n) x) = _
  rw [coupling_oldWord_count]
  ring

theorem reset_backward (C : Matrix (Old P) (Fin nR) ℚ) (J : Matrix (Fin nR) (Fin nR) ℚ)
    (s0 : Act (nR := nR) P → ℚ) (a n : ℕ) (zeta : ℚ) (Jm : Fin nR → ℚ)
    (hinit : ∀ j, s0 (Sum.inr j) = zeta - Jm j + C (Sum.inr 0) j +
      ∑ i : Fin P.m, C (Sum.inl i) j * wordCountVec (consecutiveWord P.word a n) i)
    (r : ℕ) (j : Fin nR) :
    wordScore (liftedGameMat (FaithfulGateway.game P) C J) s0
        (parentStage P ((consecutiveWord P.word a n).take r)) (Sum.inr j) =
      zeta - Jm j + C (Sum.inr 0) j + ∑ i : Fin P.m, C (Sum.inl i) j *
        wordCountVec ((consecutiveWord P.word a n).drop r) i := by
  rw [reset_forward, hinit j]
  have hs : (∑ i : Fin P.m, C (Sum.inl i) j * wordCountVec (consecutiveWord P.word a n) i) =
      (∑ i : Fin P.m, C (Sum.inl i) j * wordCountVec ((consecutiveWord P.word a n).take r) i) +
      ∑ i : Fin P.m, C (Sum.inl i) j * wordCountVec ((consecutiveWord P.word a n).drop r) i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_add, wordCountVec_take_add_drop]
  linarith

/-- The fixed-A bundle bound gives a strict early-reset waiting margin at every
parent prefix, including the complete parent word immediately before g. -/
theorem early_waits (C : Matrix (Old P) (Fin nR) ℚ) (J : Matrix (Fin nR) (Fin nR) ℚ)
    (s0 : Act (nR := nR) P → ℚ) (a n : ℕ) (h zeta c eps : ℚ) (Jm : Fin nR → ℚ)
    (heps : 0 < eps) (ha : FaithfulGrowth.Clock.bundleThreshold P eps ≤ a)
    (hend : P.entry (a + n) P.b + h = zeta - c)
    (hinit : ∀ j, s0 (Sum.inr j) = zeta - Jm j + C (Sum.inr 0) j +
      ∑ i : Fin P.m, C (Sum.inl i) j * wordCountVec (consecutiveWord P.word a n) i)
    (j : Fin nR) (hJm : 0 ≤ Jm j) (hreserve : 0 < -C (Sum.inr 0) j - c - P.Arem)
    (hC : ∀ i, 0 ≤ -C (Sum.inl i) j - eps)
    (r : ℕ) (hr : r ≤ (consecutiveWord P.word a n).length) :
    wordScore (liftedGameMat (FaithfulGateway.game P) C J) s0
        (parentStage P ((consecutiveWord P.word a n).take r)) (Sum.inr j) <
      height P.b (wordScore P.A (P.entry a) ((consecutiveWord P.word a n).take r)) + h := by
  have hQ : P.Q ≤ a :=
    (P.threshold_onset eps heps).trans ((le_max_left _ _).trans ha)
  have hsuf := FaithfulGrowth.Clock.consecutive_suffix P heps a n r ha hr
  rw [P.entry_height (a + n) (by omega)] at hsuf
  have hbound : zeta - c - P.Arem - eps *
      (∑ i : Fin P.m, wordCountVec ((consecutiveWord P.word a n).drop r) i) ≤
      height P.b (wordScore P.A (P.entry a) ((consecutiveWord P.word a n).take r)) + h := by
    rw [← list_length_eq_sum_wordCountVec, List.length_drop]
    linarith
  have he := early_reset_waits_during_bundle (fun i => C (Sum.inl i) j)
    (wordCountVec ((consecutiveWord P.word a n).drop r)) zeta (Jm j) (C (Sum.inr 0) j)
    c P.Arem eps (height P.b (wordScore P.A (P.entry a) ((consecutiveWord P.word a n).take r)) + h)
    hbound hJm hreserve hC (fun i => Nat.cast_nonneg _)
  rw [reset_backward P C J s0 a n zeta Jm hinit]
  exact he.1

/-- Positive coupling only decreases a late reset while the parent maximum is
nondecreasing. Empty-prefix ties are intentionally retained for parent priority. -/
theorem late_waits (C : Matrix (Old P) (Fin nR) ℚ) (J : Matrix (Fin nR) (Fin nR) ℚ)
    (s0 : Act (nR := nR) P → ℚ) (a n : ℕ) (h : ℚ) (ha : P.Q ≤ a)
    (j : Fin nR) (hstart : s0 (Sum.inr j) ≤ P.entry a P.b + h)
    (hC : ∀ i, 0 ≤ C (Sum.inl i) j)
    (r : ℕ) (hr : r ≤ (consecutiveWord P.word a n).length) :
    wordScore (liftedGameMat (FaithfulGateway.game P) C J) s0
        (parentStage P ((consecutiveWord P.word a n).take r)) (Sum.inr j) ≤
      height P.b (wordScore P.A (P.entry a) ((consecutiveWord P.word a n).take r)) + h := by
  have hv := (consecutiveWord_valid_score P.A P.rank P.word P.entry P.Q
    P.valid P.phase_transition a ha n).1
  have hm := height_prefix_ge P.b P.A P.skew (P.entry a) P.rank _ hv r hr
  rw [P.entry_height a ha] at hm
  have hw := late_reset_waits_during_bundle (fun i => C (Sum.inl i) j)
    (wordCountVec ((consecutiveWord P.word a n).take r)) (s0 (Sum.inr j))
    (P.entry a P.b + h)
    (height P.b (wordScore P.A (P.entry a) ((consecutiveWord P.word a n).take r)) + h)
    hstart (by linarith) hC (fun i => Nat.cast_nonneg _)
  rw [reset_forward]
  exact hw.1

theorem parentStage_valid {nRank : ℕ}
    (C : Matrix (Old P) (Fin nR) ℚ) (J : Matrix (Fin nR) (Fin nR) ℚ)
    (s0 : Act (nR := nR) P → ℚ) (rank : Act (nR := nR) P → Fin nRank)
    (a n : ℕ) (h delta : ℚ) (ha : P.Q ≤ a) (hd : delta < P.delta0)
    (hs : ∀ x, s0 (Sum.inl x) = FaithfulGateway.initial P a n h delta x)
    (hparent : ∀ i j, (P.rank i).val < (P.rank j).val →
      (rank (Sum.inl (Sum.inl i))).val < (rank (Sum.inl (Sum.inl j))).val)
    (hpriority : ∀ i j, (rank (Sum.inl (Sum.inl i))).val < (rank (Sum.inr j)).val)
    (hwait : ∀ r, r ≤ (consecutiveWord P.word a n).length → ∀ j,
      wordScore (liftedGameMat (FaithfulGateway.game P) C J) s0
        (parentStage P ((consecutiveWord P.word a n).take r)) (Sum.inr j) ≤
      height P.b (wordScore P.A (P.entry a) ((consecutiveWord P.word a n).take r)) + h) :
    IsValidPriorityWord (liftedGameMat (FaithfulGateway.game P) C J) s0 rank
      (parentStage P (consecutiveWord P.word a n)) := by
  let W := consecutiveWord P.word a n
  have hv := (consecutiveWord_valid_score P.A P.rank P.word P.entry P.Q
    P.valid P.phase_transition a ha n).1
  intro r hr x
  have hr' : r < W.length := by simpa [parentStage, W] using hr
  have ht : (parentStage (nR := nR) P W).take r = parentStage P (W.take r) := by
    simp only [parentStage, List.map_take]
  have hg : (parentStage (nR := nR) P W)[r] = Sum.inl (Sum.inl W[r]) := by
    simp [parentStage]
  change wordScore _ _ ((parentStage P W).take r) x ≤
    wordScore _ _ ((parentStage P W).take r) (parentStage P W)[r] ∧ _
  rw [ht, hg]
  cases x with
  | inl x =>
    cases x with
    | inl i =>
      rw [parent_score P C J s0 a n h delta hs, parent_score P C J s0 a n h delta hs]
      have hi := hv r hr' i
      refine ⟨by linarith [hi.1], ?_⟩
      intro hne heq
      apply hparent
      apply hi.2
      · intro he; exact hne (congrArg (fun z => Sum.inl (Sum.inl z)) he)
      · linarith
    | inr i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      have hsco := old_score P C J s0 a n h delta hs (W.take r |>.map Sum.inl) (Sum.inr 0)
      have hw := FaithfulGateway.gateway_waits P a ha n r hr' h delta
      rw [FaithfulGateway.parent_score] at hw
      change wordScore _ _ (parentStage P (W.take r)) (Sum.inl (Sum.inr 0)) = _ at hsco
      rw [hsco, parent_score P C J s0 a n h delta hs]
      refine ⟨by linarith, ?_⟩
      intro _ heq
      linarith
  | inr j =>
    have hw := hwait r hr'.le j
    have hh := height_eq P.b (wordScore P.A (P.entry a) (W.take r)) W[r]
      (fun i => (hv r hr' i).1)
    rw [hh] at hw
    rw [parent_score P C J s0 a n h delta hs]
    exact ⟨hw, fun _ _ => hpriority _ j⟩

/-- A gateway is handled as a separate strict step; it need not outrank resets.
The parent-over-reset ordering is used only during the actual parent word. -/
theorem oldWord_valid_of_waits {nRank : ℕ}
    (C : Matrix (Old P) (Fin nR) ℚ) (J : Matrix (Fin nR) (Fin nR) ℚ)
    (s0 : Act (nR := nR) P → ℚ) (rank : Act (nR := nR) P → Fin nRank)
    (a n : ℕ) (h delta : ℚ) (ha : P.Q ≤ a) (hd0 : 0 < delta) (hd : delta < P.delta0)
    (hs : ∀ x, s0 (Sum.inl x) = FaithfulGateway.initial P a n h delta x)
    (hparent : ∀ i j, (P.rank i).val < (P.rank j).val →
      (rank (Sum.inl (Sum.inl i))).val < (rank (Sum.inl (Sum.inl j))).val)
    (hpriority : ∀ i j, (rank (Sum.inl (Sum.inl i))).val < (rank (Sum.inr j)).val)
    (hwait : ∀ r, r ≤ (consecutiveWord P.word a n).length → ∀ j,
      wordScore (liftedGameMat (FaithfulGateway.game P) C J) s0
        (parentStage P ((consecutiveWord P.word a n).take r)) (Sum.inr j) ≤
      height P.b (wordScore P.A (P.entry a) ((consecutiveWord P.word a n).take r)) + h) :
    IsValidPriorityWord (liftedGameMat (FaithfulGateway.game P) C J) s0 rank
      ((FaithfulGateway.oldWord P a n).map Sum.inl) := by
  let W := consecutiveWord P.word a n
  have he := (consecutiveWord_valid_score P.A P.rank P.word P.entry P.Q
    P.valid P.phase_transition a ha n).2
  have hg : wordScore (liftedGameMat (FaithfulGateway.game P) C J) s0
      (parentStage P W) (Sum.inl (Sum.inr 0)) = P.entry (a + n) P.b + h + delta := by
    rw [parentStage, old_score P C J s0 a n h delta hs, FaithfulGateway.gateway_score,
      he, P.consecutive_counter a ha n]
    ring
  rw [FaithfulGateway.oldWord, List.map_append, List.map_singleton]
  apply (isValidPriorityWord_append _ _ _ _ _).2
  refine ⟨parentStage_valid P C J s0 rank a n h delta ha hd hs hparent hpriority hwait, ?_⟩
  apply (isValidPriorityWord_singleton _ _ _ _).2
  apply isValidPriorityStep_of_isValidStrictStep
  intro x hx
  cases x with
  | inl x =>
    cases x with
    | inl i =>
      have hp := le_height P.b (P.entry (a + n)) i
      rw [P.entry_height (a + n) (by omega)] at hp
      change wordScore _ _ (parentStage P W) _ < wordScore _ _ (parentStage P W) _
      rw [parent_score P C J s0 a n h delta hs, he, hg]
      linarith
    | inr i => exact (hx (congrArg (fun j => Sum.inl (Sum.inr j)) (Subsingleton.elim i 0))).elim
  | inr j =>
    have hw := hwait W.length le_rfl j
    rw [List.take_length, he, P.entry_height (a + n) (by omega)] at hw
    change wordScore _ _ (parentStage P W) _ < wordScore _ _ (parentStage P W) _
    rw [hg]
    linarith

/-- The complete old word in the full lifted game, from literal clock suffix,
coupling reserves, initial reset data and prescribed priority. All waiting
inequalities are derived; none is an all-prefix hypothesis of this theorem. -/
theorem oldWord_valid_from_data {nRank : ℕ}
    (C : Matrix (Old P) (Fin nR) ℚ) (J : Matrix (Fin nR) (Fin nR) ℚ)
    (s0 : Act (nR := nR) P → ℚ) (rank : Act (nR := nR) P → Fin nRank)
    (a n split : ℕ) (h delta zeta c eps : ℚ) (Jm : Fin nR → ℚ)
    (heps : 0 < eps) (ha : FaithfulGrowth.Clock.bundleThreshold P eps ≤ a)
    (hd0 : 0 < delta) (hd : delta < P.delta0)
    (hs : ∀ x, s0 (Sum.inl x) = FaithfulGateway.initial P a n h delta x)
    (hend : P.entry (a + n) P.b + h = zeta - c)
    (hinit : ∀ j, s0 (Sum.inr j) = zeta - Jm j + C (Sum.inr 0) j +
      ∑ i : Fin P.m, C (Sum.inl i) j * wordCountVec (consecutiveWord P.word a n) i)
    (hJm : ∀ j, j.val < split → 0 ≤ Jm j)
    (hreserve : ∀ j, j.val < split → 0 < -C (Sum.inr 0) j - c - P.Arem)
    (hearly : ∀ j, j.val < split → ∀ i, 0 ≤ -C (Sum.inl i) j - eps)
    (hlateStart : ∀ j, split ≤ j.val → s0 (Sum.inr j) ≤ P.entry a P.b + h)
    (hlate : ∀ j, split ≤ j.val → ∀ i, 0 ≤ C (Sum.inl i) j)
    (hparent : ∀ i j, (P.rank i).val < (P.rank j).val →
      (rank (Sum.inl (Sum.inl i))).val < (rank (Sum.inl (Sum.inl j))).val)
    (hpriority : ∀ i j, (rank (Sum.inl (Sum.inl i))).val < (rank (Sum.inr j)).val) :
    IsValidPriorityWord (liftedGameMat (FaithfulGateway.game P) C J) s0 rank
      ((FaithfulGateway.oldWord P a n).map Sum.inl) := by
  have hQ : P.Q ≤ a :=
    (P.threshold_onset eps heps).trans ((le_max_left _ _).trans ha)
  apply oldWord_valid_of_waits P C J s0 rank a n h delta hQ hd0 hd hs hparent hpriority
  intro r hr j
  by_cases hj : j.val < split
  · exact (early_waits P C J s0 a n h zeta c eps Jm heps ha hend hinit j
      (hJm j hj) (hreserve j hj) (hearly j hj) r hr).le
  · exact late_waits P C J s0 a n h hQ j (hlateStart j (by omega))
      (hlate j (by omega)) r hr

end Karlin.FaithfulWaiting
