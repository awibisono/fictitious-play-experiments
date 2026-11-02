import Karlin.PaperProof

/-!
# Consecutive and dyadic words for the v15 construction

All results here use one fixed parent word family, score table and priority.
The interval begins at an arbitrary admissible phase; no initial segment is replayed.
This module is a component of the construction, not a completed lift theorem.
-/

namespace Karlin.FaithfulWindow

open scoped BigOperators

/-- The words at exactly the phases `a, ..., a+n-1`, in that order. -/
def consecutiveWord {α : Type*} (W : ℕ → List α) (a : ℕ) : ℕ → List α
  | 0 => []
  | n + 1 => consecutiveWord W a n ++ W (a + n)

theorem consecutiveWord_eq_flatMap {α : Type*} (W : ℕ → List α) (a n : ℕ) :
    consecutiveWord W a n = (List.range n).flatMap (fun j => W (a + j)) := by
  induction n with
  | zero => simp [consecutiveWord]
  | succ n ih => simp [consecutiveWord, List.range_succ, ih]

theorem consecutiveWord_length {α : Type*} (W : ℕ → List α) (a n : ℕ) :
    (consecutiveWord W a n).length = ∑ j ∈ Finset.range n, (W (a + j)).length := by
  induction n with
  | zero => simp [consecutiveWord]
  | succ n ih => simp [consecutiveWord, ih, Finset.sum_range_succ]

theorem consecutiveWord_count {α : Type*} [DecidableEq α]
    (W : ℕ → List α) (a n : ℕ) (i : α) :
    wordCountVec (consecutiveWord W a n) i =
      ∑ j ∈ Finset.range n, wordCountVec (W (a + j)) i := by
  induction n with
  | zero => simp [consecutiveWord, wordCountVec]
  | succ n ih => simp [consecutiveWord, wordCountVec_append, ih, Finset.sum_range_succ]

theorem consecutiveWord_count_Ico {α : Type*} [DecidableEq α]
    (W : ℕ → List α) (a n : ℕ) (i : α) :
    wordCountVec (consecutiveWord W a n) i =
      ∑ j ∈ Finset.Ico a (a + n), wordCountVec (W j) i := by
  rw [Finset.sum_Ico_eq_sum_range]
  simpa using consecutiveWord_count W a n i

theorem dotCount_append {α : Type*} [Fintype α] [DecidableEq α]
    (v : α → ℚ) (U V : List α) :
    dotProduct v (wordCountVec (U ++ V)) =
      dotProduct v (wordCountVec U) + dotProduct v (wordCountVec V) := by
  simp [dotProduct, wordCountVec_append, mul_add, Finset.sum_add_distrib]

theorem dotCount_take_add_drop {α : Type*} [Fintype α] [DecidableEq α]
    (v : α → ℚ) (W : List α) (r : ℕ) :
    dotProduct v (wordCountVec (W.take r)) + dotProduct v (wordCountVec (W.drop r)) =
      dotProduct v (wordCountVec W) := by
  rw [← dotCount_append, List.take_append_drop]

theorem wordScore_singleton {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℚ) (s : α → ℚ) (a i : α) :
    wordScore A s [a] i = s i + A i a := by
  simp [wordScore, scoreVec, wordCountVec, List.count_singleton]

/-- A compatible interval inherits both validity and its exact endpoint from the
same parent phase family. The starting phase alone must exceed the parent onset. -/
theorem consecutiveWord_valid_score {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} (A : Matrix α α ℚ) (rank : α → Fin m) (W : ℕ → List α)
    (s : ℕ → α → ℚ) (Q : ℕ)
    (hvalid : ∀ q, Q ≤ q → IsValidPriorityWord A (s q) rank (W q))
    (hnext : ∀ q, Q ≤ q → wordScore A (s q) (W q) = s (q + 1))
    (a : ℕ) (ha : Q ≤ a) (n : ℕ) :
    IsValidPriorityWord A (s a) rank (consecutiveWord W a n) ∧
      wordScore A (s a) (consecutiveWord W a n) = s (a + n) := by
  induction n with
  | zero =>
      constructor
      · intro r hr
        simp [consecutiveWord] at hr
      · simp [consecutiveWord, wordScore_nil]
  | succ n ih =>
      have hq : Q ≤ a + n := by omega
      constructor
      · apply (isValidPriorityWord_append A (s a) rank _ _).2
        exact ⟨ih.1, by simpa [ih.2] using hvalid (a + n) hq⟩
      · change wordScore A (s a) (consecutiveWord W a n ++ W (a + n)) = _
        rw [wordScore_append, ih.2, hnext (a + n) hq]
        congr 1

/-- The literal moving window of v15: phases `[tau*q, 2*tau*q)`. -/
def dyadicWord {α : Type*} (W : ℕ → List α) (tau q : ℕ) : List α :=
  consecutiveWord W (tau * q) (tau * q)

theorem dyadicWord_valid_score {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} (A : Matrix α α ℚ) (rank : α → Fin m) (W : ℕ → List α)
    (s : ℕ → α → ℚ) (Q : ℕ)
    (hvalid : ∀ q, Q ≤ q → IsValidPriorityWord A (s q) rank (W q))
    (hnext : ∀ q, Q ≤ q → wordScore A (s q) (W q) = s (q + 1))
    (tau q : ℕ) (hq : Q ≤ tau * q) :
    IsValidPriorityWord A (s (tau * q)) rank (dyadicWord W tau q) ∧
      wordScore A (s (tau * q)) (dyadicWord W tau q) = s (2 * tau * q) := by
  have h := consecutiveWord_valid_score A rank W s Q hvalid hnext (tau * q) hq (tau * q)
  have he : tau * q + tau * q = 2 * tau * q := by ring
  simpa [dyadicWord, he] using h

/-- Every proper prefix is completed phases followed by one proper phase prefix. -/
theorem consecutiveWord_prefix {α : Type*} (W : ℕ → List α) (a n r : ℕ)
    (hr : r < (consecutiveWord W a n).length) :
    ∃ j < n, ∃ u < (W (a + j)).length,
      r = (consecutiveWord W a j).length + u ∧
      (consecutiveWord W a n).take r =
        consecutiveWord W a j ++ (W (a + j)).take u := by
  induction n with
  | zero => simp [consecutiveWord] at hr
  | succ n ih =>
      by_cases hsmall : r < (consecutiveWord W a n).length
      · obtain ⟨j, hj, u, hu, hlen, htake⟩ := ih hsmall
        refine ⟨j, by omega, u, hu, hlen, ?_⟩
        change (consecutiveWord W a n ++ W (a + n)).take r = _
        rw [List.take_append_of_le_length hsmall.le, htake]
      · have hle : (consecutiveWord W a n).length ≤ r := by omega
        refine ⟨n, by omega, r - (consecutiveWord W a n).length, ?_, by omega, ?_⟩
        · simp only [consecutiveWord, List.length_append] at hr
          omega
        · change (consecutiveWord W a n ++ W (a + n)).take r = _
          rw [List.take_append, List.take_of_length_le hle]

/-- The actual moving-window word has the paper's transferred count table. -/
theorem dyadicWord_count_table {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} (C : Matrix α (Fin k) ℚ) (W : ℕ → List α) (Q : ℕ)
    (hcount : ∀ q, Q ≤ q → wordCountVec (W q) = C.mulVec (binomBasis k q))
    (tau q : ℕ) (hq : Q ≤ tau * q) :
    wordCountVec (dyadicWord W tau q) =
      (C * F_tau_mat k tau).mulVec (binomBasis (k + 1) q) := by
  have he : tau * q + tau * q = 2 * tau * q := by ring
  have hb : (F_tau_mat k tau).mulVec (binomBasis (k + 1) q) =
      ∑ j ∈ Finset.Ico (tau * q) (2 * tau * q), binomBasis k j := by
    ext i
    simpa only [Finset.sum_apply] using F_tau_mat_mulVec_binomBasis k tau q i
  rw [← Matrix.mulVec_mulVec, hb, Matrix.mulVec_sum]
  ext i
  rw [dyadicWord, consecutiveWord_count_Ico, he]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  exact congr_fun (hcount j (hq.trans (Finset.mem_Ico.mp hj).1)) i

/-- The single additive suffix constant is charged only to the current partial
phase. Subsequent full phases use the separate vanishing gain/length estimate.
The functional `height` will be the maximum score in the faithful clock. -/
theorem consecutiveWord_suffix {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℚ) (W : ℕ → List α) (s : ℕ → α → ℚ)
    (height : (α → ℚ) → ℚ) (Q : ℕ) (eps Arem : ℚ) (hArem : 0 ≤ Arem)
    (hnext : ∀ q, Q ≤ q → wordScore A (s q) (W q) = s (q + 1))
    (hlocal : ∀ q, Q ≤ q → ∀ r, r ≤ (W q).length →
      height (s (q + 1)) - height (wordScore A (s q) ((W q).take r)) ≤
        eps * ((W q).length - r : ℕ) + Arem)
    (hwhole : ∀ q, Q ≤ q → height (s (q + 1)) - height (s q) ≤
      eps * (W q).length)
    (a : ℕ) (ha : Q ≤ a) (n r : ℕ) (hr : r ≤ (consecutiveWord W a n).length) :
    height (s (a + n)) -
        height (wordScore A (s a) ((consecutiveWord W a n).take r)) ≤
      eps * ((consecutiveWord W a n).length - r : ℕ) + Arem := by
  have hend : ∀ n, wordScore A (s a) (consecutiveWord W a n) = s (a + n) := by
    intro n
    induction n with
    | zero => simp [consecutiveWord, wordScore_nil]
    | succ n ih =>
        change wordScore A (s a) (consecutiveWord W a n ++ W (a + n)) = _
        rw [wordScore_append, ih, hnext (a + n) (by omega)]
        congr 1
  induction n with
  | zero => simpa [consecutiveWord, wordScore_nil] using hArem
  | succ n ih =>
      have hq : Q ≤ a + n := by omega
      change r ≤ (consecutiveWord W a n ++ W (a + n)).length at hr
      by_cases hsmall : r ≤ (consecutiveWord W a n).length
      · have hprev := ih hsmall
        have hlast := hwhole (a + n) hq
        have hlen : (consecutiveWord W a (n + 1)).length - r =
            ((consecutiveWord W a n).length - r) + (W (a + n)).length := by
          simp only [consecutiveWord, List.length_append]
          omega
        change height (s (a + n + 1)) -
          height (wordScore A (s a) ((consecutiveWord W a n ++ W (a + n)).take r)) ≤ _
        rw [List.take_append_of_le_length hsmall, hlen, Nat.cast_add]
        linarith
      · have hle : (consecutiveWord W a n).length ≤ r := by omega
        have hu : r - (consecutiveWord W a n).length ≤ (W (a + n)).length := by
          rw [List.length_append] at hr
          omega
        have hp := hlocal (a + n) hq (r - (consecutiveWord W a n).length) hu
        have hlen : (consecutiveWord W a (n + 1)).length - r =
            (W (a + n)).length - (r - (consecutiveWord W a n).length) := by
          simp only [consecutiveWord, List.length_append]
          omega
        change height (s (a + n + 1)) -
          height (wordScore A (s a) ((consecutiveWord W a n ++ W (a + n)).take r)) ≤ _
        rw [List.take_append, List.take_of_length_le hle, wordScore_append, hend n, hlen]
        exact hp

end Karlin.FaithfulWindow
