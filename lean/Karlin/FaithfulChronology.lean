import Karlin.FaithfulClock

/-!
# The actual reset cascade

The reset word uses arbitrary natural run lengths. Its intermediate scores use
all earlier reset plays, including their effect on previously played resets.
Only the scalar old-action inequalities at run endpoints remain hypotheses.
-/

namespace Karlin.FaithfulChronology

open scoped BigOperators

def resetPrefix {m n : ℕ} (count : Fin n → ℕ) (idx : ℕ) : List (Fin m ⊕ Fin n) :=
  ((List.finRange n).take idx).flatMap (fun j => List.replicate (count j) (Sum.inr j))

def resetWord {m n : ℕ} (count : Fin n → ℕ) : List (Fin m ⊕ Fin n) :=
  (List.finRange n).flatMap (fun j => List.replicate (count j) (Sum.inr j))

theorem count_reset_list_inl {m n : ℕ} (count : Fin n → ℕ) (l : List (Fin n))
    (i : Fin m) :
    wordCountVec (l.flatMap (fun j => List.replicate (count j) (Sum.inr j : Fin m ⊕ Fin n)))
      (Sum.inl i) = 0 := by
  induction l with
  | nil => simp [wordCountVec]
  | cons j l ih =>
      rw [List.flatMap_cons, wordCountVec_append, ih, add_zero]
      simp [wordCountVec, List.count_replicate]

theorem resetPrefix_count_inl {m n : ℕ} (count : Fin n → ℕ) (idx : ℕ) (i : Fin m) :
    wordCountVec (resetPrefix (m := m) count idx) (Sum.inl i) = 0 := by
  exact count_reset_list_inl count ((List.finRange n).take idx) i

theorem resetPrefix_count_inr {m n : ℕ} (count : Fin n → ℕ) (idx : ℕ) (i : Fin n) :
    wordCountVec (resetPrefix (m := m) count idx) (Sum.inr i) =
      if i.val < idx then (count i : ℚ) else 0 := by
  unfold wordCountVec resetPrefix
  rw [count_flatMap_replicate count (Sum.inr : Fin n → Fin m ⊕ Fin n)
    (fun _ _ h => Sum.inr.inj h), count_take_finRange]
  split_ifs <;> simp

theorem resetWord_count_inr {m n : ℕ} (count : Fin n → ℕ) (i : Fin n) :
    wordCountVec (resetWord (m := m) count) (Sum.inr i) = (count i : ℚ) := by
  unfold wordCountVec resetWord
  rw [count_flatMap_finRange_replicate n count (Sum.inr : Fin n → Fin m ⊕ Fin n)
    (fun _ _ h => Sum.inr.inj h)]

theorem resetWord_count {m n : ℕ} (count : Fin n → ℕ) :
    wordCountVec (resetWord (m := m) count) = Sum.elim (fun _ => 0) (fun j => (count j : ℚ)) := by
  funext i
  cases i with
  | inl i => exact count_reset_list_inl count (List.finRange n) i
  | inr i => exact resetWord_count_inr count i

/-- The first reset supplies the two initial leader plays required by Clock. -/
theorem resetWord_begins_twice {m n : ℕ} (hn : 0 < n) (count : Fin n → ℕ)
    (hcount : 2 ≤ count ⟨0, hn⟩) :
    ∃ tail, resetWord (m := m) count =
      Sum.inr ⟨0, hn⟩ :: Sum.inr ⟨0, hn⟩ :: tail := by
  cases n with
  | zero => omega
  | succ n =>
      change 2 ≤ count 0 at hcount
      refine ⟨List.replicate (count 0 - 2) (Sum.inr 0) ++
        ((List.finRange n).map Fin.succ).flatMap
          (fun j => List.replicate (count j) (Sum.inr j)), ?_⟩
      have hc : count 0 = (count 0 - 2) + 1 + 1 := by omega
      have hrep : List.replicate (count 0) (Sum.inr (0 : Fin (n + 1)) : Fin m ⊕ Fin (n + 1)) =
          Sum.inr 0 :: Sum.inr 0 :: List.replicate (count 0 - 2) (Sum.inr 0) := by
        conv_lhs => rw [hc]
        simp only [List.replicate_succ]
      rw [resetWord, List.finRange_succ, List.flatMap_cons, hrep]
      rfl

def oldPrefixScore {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℚ)
    (s0 : Fin m ⊕ Fin n → ℚ) (count : Fin n → ℕ) (j : Fin n) (i : Fin m) : ℚ :=
  s0 (Sum.inl i) + ∑ ell : Fin n, P i ell * (if ell.val < j.val then (count ell : ℚ) else 0)

theorem resetPrefix_score_old {m n : ℕ}
    (G : Matrix (Fin m) (Fin m) ℚ) (P : Matrix (Fin m) (Fin n) ℚ)
    (J : Matrix (Fin n) (Fin n) ℚ) (s0 : Fin m ⊕ Fin n → ℚ)
    (count : Fin n → ℕ) (j : Fin n) (i : Fin m) :
    wordScore (liftedGameMat G P J) s0 (resetPrefix count j.val) (Sum.inl i) =
      oldPrefixScore P s0 count j i := by
  simp [wordScore, scoreVec, Fintype.sum_sum_type, resetPrefix_count_inl,
    resetPrefix_count_inr, liftedGameMat, oldPrefixScore]

theorem resetPrefix_score_reset {m n : ℕ}
    (G : Matrix (Fin m) (Fin m) ℚ) (P : Matrix (Fin m) (Fin n) ℚ)
    (J : Matrix (Fin n) (Fin n) ℚ) (s0 : Fin m ⊕ Fin n → ℚ)
    (count : Fin n → ℕ) (zeta : ℚ)
    (hs0 : ∀ i, s0 (Sum.inr i) = resetEntryScore J (fun j => (count j : ℚ)) zeta i)
    (j i : Fin n) :
    wordScore (liftedGameMat G P J) s0 (resetPrefix count j.val) (Sum.inr i) =
      scoreVec (J - J.transpose) (resetEntryScore J (fun a => (count a : ℚ)) zeta)
        (resetPrefixCount j (fun a => (count a : ℚ)) 0) i := by
  simp only [wordScore, scoreVec, Fintype.sum_sum_type, resetPrefix_count_inl,
    resetPrefix_count_inr, mul_zero, Finset.sum_const_zero, zero_add,
    liftedGameMat, Matrix.fromBlocks_apply₂₂, hs0]
  congr 1
  apply Finset.sum_congr rfl
  intro ell _
  simp [resetPrefixCount]

theorem reset_score_affine {n : ℕ} (J : Matrix (Fin n) (Fin n) ℚ)
    (count : Fin n → ℚ) (zeta h : ℚ) (j i : Fin n) :
    scoreVec (J - J.transpose) (resetEntryScore J count zeta) (resetPrefixCount j count h) i =
      scoreVec (J - J.transpose) (resetEntryScore J count zeta) (resetPrefixCount j count 0) i +
        h * (J i j - J j i) := by
  have hc (ell : Fin n) : resetPrefixCount j count h ell =
      resetPrefixCount j count 0 ell + if ell = j then h else 0 := by
    by_cases he : ell = j
    · subst ell; simp [resetPrefixCount]
    · simp [resetPrefixCount, he]
  simp only [scoreVec, hc, Matrix.sub_apply, Matrix.transpose_apply, mul_add,
    Finset.sum_add_distrib]
  simp [mul_ite, Finset.sum_ite_eq', mul_comm, add_assoc]

/-- During an early run, every earlier increment and the current increment
are nonpositive. Only the actual old score at the start of the cascade is used. -/
theorem old_waits_early {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℚ)
    (s0 : Fin m ⊕ Fin n → ℚ) (count : Fin n → ℕ) (split : ℕ)
    (i : Fin m) (j : Fin n) (h zeta : ℚ) (hj : j.val < split) (hh : 0 ≤ h)
    (hP : ∀ ell, ell.val < split → P i ell ≤ 0)
    (hstart : s0 (Sum.inl i) < zeta) :
    oldPrefixScore P s0 count j i + h * P i j < zeta := by
  have hsum : (∑ ell : Fin n, P i ell *
      (if ell.val < j.val then (count ell : ℚ) else 0)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro ell _
    split_ifs with hell
    · exact mul_nonpos_of_nonpos_of_nonneg (hP ell (by omega)) (Nat.cast_nonneg _)
    · simp
  have hcur : h * P i j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hh (hP j hj)
  unfold oldPrefixScore
  linarith

/-- During a late run, the exact future state bounds the current old score.
The positive unplayed part of the active reset alone supplies strictness. -/
theorem old_waits_late {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℚ)
    (s0 : Fin m ⊕ Fin n → ℚ) (count : Fin n → ℕ) (split : ℕ)
    (i : Fin m) (j : Fin n) (h zeta next : ℚ) (hj : split ≤ j.val)
    (hh : h < (count j : ℚ))
    (hP : ∀ ell, split ≤ ell.val → 0 < P i ell)
    (hnext : next = s0 (Sum.inl i) + ∑ ell, P i ell * (count ell : ℚ))
    (hnext_le : next ≤ zeta) :
    oldPrefixScore P s0 count j i + h * P i j < zeta := by
  let tail : ℚ := ∑ ell : Fin n,
    if j.val ≤ ell.val then P i ell * (count ell : ℚ) else 0
  have hsplit : next = oldPrefixScore P s0 count j i + tail := by
    rw [hnext]
    unfold oldPrefixScore tail
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro ell _
    by_cases hell : ell.val < j.val
    · simp [hell, show ¬ j.val ≤ ell.val by omega]
    · simp [hell, show j.val ≤ ell.val by omega]
  have htail : P i j * (count j : ℚ) ≤ tail := by
    have hnonneg : ∀ ell ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ (if j.val ≤ ell.val then P i ell * (count ell : ℚ) else 0) := by
      intro ell _
      split_ifs with hell
      · exact mul_nonneg (hP ell (by omega)).le (Nat.cast_nonneg _)
      · exact le_rfl
    have h := Finset.single_le_sum hnonneg (Finset.mem_univ j)
    simpa only [le_refl, if_true, tail] using h
  have hcur : h * P i j < P i j * (count j : ℚ) := by
    have := mul_lt_mul_of_pos_right hh (hP j hj)
    simpa [mul_comm] using this
  linarith

/-- Full validity of the actual reset word from its two old-score endpoint tests.
Earlier resets may tie at the start of a run; reverse reset priority resolves it.
No suffix-only formula for previously played reset scores is assumed. -/
theorem resetWord_valid {m w : ℕ}
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (rank : Fin m → Fin m)
    (s0 : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (count : Fin ((w + 1) + (w + 1)) → ℕ) (zeta : ℚ)
    (hcount : ∀ j, 1 ≤ count j)
    (hJlower : ∀ a b, a.val ≤ b.val → J a b = 0)
    (hJpos : ∀ a b, b.val < a.val → 0 < J a b)
    (hs0 : ∀ i, s0 (Sum.inr i) = resetEntryScore J (fun j => (count j : ℚ)) zeta i)
    (hold_start : ∀ j i, oldPrefixScore P s0 count j i < zeta)
    (hold_last : ∀ j i, oldPrefixScore P s0 count j i +
      ((count j - 1 : ℕ) : ℚ) * P i j < zeta) :
    IsValidPriorityWord (liftedGameMat G P J) s0 (paperPriorityRank m w rank) (resetWord count) := by
  have hJnonneg : ∀ a b, 0 ≤ J a b := by
    intro a b
    by_cases hab : a.val ≤ b.val
    · rw [hJlower a b hab]
    · exact le_of_lt (hJpos a b (by omega))
  have hcntnonneg : ∀ j, 0 ≤ (count j : ℚ) := fun j => Nat.cast_nonneg _
  apply isValidPriorityWord_flatMap (liftedGameMat G P J) (paperPriorityRank m w rank)
    (fun j => List.replicate (count j) (Sum.inr j)) (List.finRange _) s0
  intro idx hidx
  have hidx' : idx < (w + 1) + (w + 1) := by simpa using hidx
  let j : Fin ((w + 1) + (w + 1)) := ⟨idx, hidx'⟩
  let sr := wordScore (liftedGameMat G P J) s0 (resetPrefix count idx)
  have hsr (i) : sr (Sum.inr i) =
      scoreVec (J - J.transpose) (resetEntryScore J (fun a => (count a : ℚ)) zeta)
        (resetPrefixCount j (fun a => (count a : ℚ)) 0) i :=
    resetPrefix_score_reset G P J s0 count zeta hs0 j i
  have hactive : sr (Sum.inr j) = zeta := by
    rw [hsr]
    exact chronology_reset_active_at_ceiling J _ zeta 0 j hJlower
  have hold (i) : sr (Sum.inl i) = oldPrefixScore P s0 count j i :=
    resetPrefix_score_old G P J s0 count j i
  have hresult : IsValidPriorityWord (liftedGameMat G P J) sr
      (paperPriorityRank m w rank) (List.replicate (count j) (Sum.inr j)) := by
    apply chronology_reset_run_priority_valid G P J rank sr (count j) j (hcount j)
      (hJlower j j le_rfl)
    · intro i; rw [hold, hactive]; exact hold_start j i
    · intro i; rw [hold, hactive]; exact hold_last j i
    · intro i hij
      rw [hactive, hsr]
      have he := chronology_reset_earlier_deficit J (fun a => (count a : ℚ)) zeta 0 j i
        hij hJlower hJnonneg hcntnonneg le_rfl
      linarith
    · intro i hij
      rw [hJlower i j (by omega), zero_sub]
      exact neg_neg_of_pos (hJpos j i hij)
    · intro i hij
      rw [hactive, hsr]
      have hd := chronology_reset_later_deficit J (fun a => (count a : ℚ)) zeta 0 j i
        hij hJlower hJnonneg hcntnonneg (hcntnonneg j)
      have hc : 0 < (count j : ℚ) := by exact_mod_cast (hcount j)
      have hp := mul_pos (hJpos i j hij) hc
      linarith
    · intro i hij
      rw [hactive, hsr, ← reset_score_affine]
      have hcl : ((count j - 1 : ℕ) : ℚ) < (count j : ℚ) := by
        exact_mod_cast (by have := hcount j; omega : count j - 1 < count j)
      have hd := chronology_reset_later_deficit J (fun a => (count a : ℚ)) zeta
        ((count j - 1 : ℕ) : ℚ) j i hij hJlower hJnonneg hcntnonneg hcl.le
      have hp := mul_pos (hJpos i j hij) (sub_pos.mpr hcl)
      linarith
  simpa only [sr, resetPrefix, j, List.getElem_finRange, Fin.cast_mk] using hresult

/-- The paper's coupling signs and two exact boundary states imply the entire
reset chronology. Counts and matrix are fixed for the actual word. The endpoint
upper bound may be weak; every proper late offset is made strict by the positive
remaining active-reset count. -/
theorem resetWord_valid_of_signs {m w : ℕ}
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (rank : Fin m → Fin m)
    (s0 : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (count : Fin ((w + 1) + (w + 1)) → ℕ) (zeta : ℚ)
    (nextOld : Fin (m + 1) → ℚ)
    (hcount : ∀ j, 2 ≤ count j)
    (hJlower : ∀ a b, a.val ≤ b.val → J a b = 0)
    (hJpos : ∀ a b, b.val < a.val → 0 < J a b)
    (hs0 : ∀ i, s0 (Sum.inr i) = resetEntryScore J (fun j => (count j : ℚ)) zeta i)
    (hstart : ∀ i, s0 (Sum.inl i) < zeta)
    (hnext : ∀ i, nextOld i = s0 (Sum.inl i) + ∑ ell, P i ell * (count ell : ℚ))
    (hnext_le : ∀ i, nextOld i ≤ zeta)
    (hPearly : ∀ i ell, ell.val < w + 1 → P i ell ≤ 0)
    (hPlate : ∀ i ell, w + 1 ≤ ell.val → 0 < P i ell) :
    IsValidPriorityWord (liftedGameMat G P J) s0 (paperPriorityRank m w rank)
      (resetWord count) := by
  apply resetWord_valid G P J rank s0 count zeta (fun j => by have := hcount j; omega)
    hJlower hJpos hs0
  · intro j i
    by_cases hj : j.val < w + 1
    · simpa using old_waits_early P s0 count (w + 1) i j 0 zeta hj le_rfl (hPearly i) (hstart i)
    · have hh : (0 : ℚ) < count j := by exact_mod_cast (by have := hcount j; omega : 0 < count j)
      simpa using old_waits_late P s0 count (w + 1) i j 0 zeta (nextOld i)
        (by omega) hh (hPlate i) (hnext i) (hnext_le i)
  · intro j i
    by_cases hj : j.val < w + 1
    · exact old_waits_early P s0 count (w + 1) i j ((count j - 1 : ℕ) : ℚ) zeta hj
        (Nat.cast_nonneg _) (hPearly i) (hstart i)
    · have hh : ((count j - 1 : ℕ) : ℚ) < count j := by
        exact_mod_cast (by have := hcount j; omega : count j - 1 < count j)
      exact old_waits_late P s0 count (w + 1) i j ((count j - 1 : ℕ) : ℚ) zeta (nextOld i)
        (by omega) hh (hPlate i) (hnext i) (hnext_le i)

/-- Compose an already validated old word with the literal reset cascade.
The remaining old/reset obligations are scalar endpoint inequalities, not a
premise that the reset word already follows the process. -/
theorem old_then_reset_valid {m w : ℕ}
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (P : Matrix (Fin (m + 1)) (Fin ((w + 1) + (w + 1))) ℚ)
    (J : Matrix (Fin ((w + 1) + (w + 1))) (Fin ((w + 1) + (w + 1))) ℚ)
    (rank : Fin m → Fin m)
    (s0 : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (old : List (Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1))))
    (count : Fin ((w + 1) + (w + 1)) → ℕ) (zeta : ℚ)
    (hold : IsValidPriorityWord (liftedGameMat G P J) s0 (paperPriorityRank m w rank) old)
    (hcount : ∀ j, 1 ≤ count j)
    (hJlower : ∀ a b, a.val ≤ b.val → J a b = 0)
    (hJpos : ∀ a b, b.val < a.val → 0 < J a b)
    (hs0 : ∀ i, wordScore (liftedGameMat G P J) s0 old (Sum.inr i) =
      resetEntryScore J (fun j => (count j : ℚ)) zeta i)
    (hold_start : ∀ j i,
      oldPrefixScore P (wordScore (liftedGameMat G P J) s0 old) count j i < zeta)
    (hold_last : ∀ j i,
      oldPrefixScore P (wordScore (liftedGameMat G P J) s0 old) count j i +
        ((count j - 1 : ℕ) : ℚ) * P i j < zeta) :
    IsValidPriorityWord (liftedGameMat G P J) s0 (paperPriorityRank m w rank)
      (old ++ resetWord count) := by
  apply (isValidPriorityWord_append _ _ _ _ _).2
  exact ⟨hold, resetWord_valid G P J rank _ count zeta hcount hJlower hJpos hs0 hold_start hold_last⟩

/-- Change the phase origin from A(q)B(q) to B(q)A(q+1), using the same words,
same game, same priority, and the actual state after A(q). No trajectory is
replaced when the phase boundary is rotated. -/
theorem rotate_compatible_words {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (G : Matrix α α ℚ) (rank : α → Fin m) (s : ℕ → α → ℚ)
    (old reset : ℕ → List α) (Q : ℕ)
    (hvalid : ∀ q, Q ≤ q → IsValidPriorityWord G (s q) rank (old q ++ reset q))
    (hnext : ∀ q, Q ≤ q → wordScore G (s q) (old q ++ reset q) = s (q + 1))
    (q : ℕ) (hq : Q ≤ q) :
    IsValidPriorityWord G (wordScore G (s q) (old q)) rank (reset q ++ old (q + 1)) ∧
      wordScore G (wordScore G (s q) (old q)) (reset q ++ old (q + 1)) =
        wordScore G (s (q + 1)) (old (q + 1)) := by
  have hc := (isValidPriorityWord_append G (s q) rank (old q) (reset q)).1 (hvalid q hq)
  have hn := (isValidPriorityWord_append G (s (q + 1)) rank (old (q + 1)) (reset (q + 1))).1
    (hvalid (q + 1) (by omega))
  have ht : wordScore G (wordScore G (s q) (old q)) (reset q) = s (q + 1) := by
    rw [← wordScore_append]
    exact hnext q hq
  constructor
  · apply (isValidPriorityWord_append _ _ _ _ _).2
    exact ⟨hc.2, by rw [ht]; exact hn.1⟩
  · rw [wordScore_append, ht]

end Karlin.FaithfulChronology
