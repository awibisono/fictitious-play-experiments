import Karlin.FaithfulReindex

/-! Packaging the earned clock fields on an arbitrary finite action type.
This changes only action labels; matrices, words, thresholds and constants are
transported verbatim. Every raw clock field must be supplied by its construction.
-/
namespace Karlin.FaithfulClockPackage
open scoped BigOperators Matrix
open FaithfulClock FaithfulReindex

set_option maxHeartbeats 800000

def rationalCounts {α : Type*} {k : ℕ} (C : Matrix α (Fin k) ℤ) : Matrix α (Fin k) ℚ :=
  fun i j => (C i j : ℚ)

structure Raw (k m : ℕ) (α : Type*) [Fintype α] [DecidableEq α] where
  order_ge_two : 2 ≤ k
  A : Matrix α α ℚ
  skew : IsSkewSymmetric A
  rank : α ≃ Fin m
  R : Matrix α (Fin k) ℚ
  C : Matrix α (Fin k) ℤ
  b : α
  v : α → ℚ
  Q : ℕ
  onset_pos : 1 ≤ Q
  word : ℕ → List α
  delta0 : ℚ
  marker_pos : 0 < delta0
  Arem : ℚ
  remainder_nonneg : 0 ≤ Arem
  threshold : ℚ → ℕ
  threshold_onset : ∀ eps, 0 < eps → Q ≤ threshold eps
  clock_eq : A * (rationalCounts C) = R * N_mat k
  full_column_rank : Function.Injective (fun x : Fin k → ℚ =>
    (rationalCounts C).mulVec x)
  leading_height : 0 < R b ⟨k-1, by omega⟩
  valid : ∀ q, Q ≤ q → IsValidPriorityWord A (R.mulVec (binomBasis k q)) rank (word q)
  counts : ∀ q, Q ≤ q → wordCountVec (word q) =
    (rationalCounts C).mulVec (binomBasis k q)
  begins_twice : ∀ q, Q ≤ q → ∃ tail, word q = b :: b :: tail
  counter_entry : v b = 0
  counter_table : Matrix.vecMul v (rationalCounts C) = e0_row k
  marker : ∀ q, Q ≤ q → ∀ r, r < (word q).length →
    delta0 ≤ Finset.univ.sup' ⟨b, Finset.mem_univ b⟩
      (wordScore A (R.mulVec (binomBasis k q)) ((word q).take r)) -
      wordScore A (R.mulVec (binomBasis k q)) ((word q).take r) b +
      dotProduct v (wordCountVec ((word q).drop r))
  support_safe : ∀ q, Q ≤ q → ∀ i, v i ≠ 0 →
    R.mulVec (binomBasis k q) i + A i b - v i <
      R.mulVec (binomBasis k q) b + A b b - v b
  suffix : ∀ eps, 0 < eps → ∀ q, threshold eps ≤ q →
    ∀ r, r ≤ (word q).length →
      Finset.univ.sup' ⟨b, Finset.mem_univ b⟩ (R.mulVec (binomBasis k (q+1))) -
      Finset.univ.sup' ⟨b, Finset.mem_univ b⟩
        (wordScore A (R.mulVec (binomBasis k q)) ((word q).take r)) ≤
      eps * ((word q).length - r : ℕ) + Arem

namespace Raw
variable {k m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable (D : Raw k m α) (e : α ≃ Fin m)

omit [Fintype α] in
theorem mapped_wordCount (W : List α) : wordCountVec (W.map e) = vec e (wordCountVec W) := by
  funext i
  exact wordCountVec_map_equiv e W i

theorem mapped_take_score (q r : ℕ) :
    wordScore (matrix e e D.A) ((rows e D.R).mulVec (binomBasis k q))
      (((D.word q).map e).take r) =
    vec e (wordScore D.A (D.R.mulVec (binomBasis k q)) ((D.word q).take r)) := by
  rw [← List.map_take, rows_mulVec, wordScore_eq]

/-- The exact same earned data, with a conventional Fin action index. -/
def toClock : Clock k where
  order_ge_two := D.order_ge_two
  m := m
  A := matrix e e D.A
  skew := FaithfulReindex.skew e D.skew
  rank := e.symm.trans D.rank
  R := rows e D.R
  C := rows e D.C
  b := e D.b
  v := vec e D.v
  Q := D.Q
  onset_pos := D.onset_pos
  word := fun q => (D.word q).map e
  delta0 := D.delta0
  marker_pos := D.marker_pos
  Arem := D.Arem
  remainder_nonneg := D.remainder_nonneg
  threshold := D.threshold
  threshold_onset := D.threshold_onset
  clock_eq := FaithfulReindex.clock_equation e D.A _ D.R _ D.clock_eq
  full_column_rank := FaithfulReindex.rows_full_column_rank e _ D.full_column_rank
  leading_height := by simpa only [rows_apply, Equiv.symm_apply_apply] using D.leading_height
  valid := by
    intro q hq
    exact FaithfulReindex.priority_valid e D.A _ D.rank (D.word q) (D.valid q hq)
  counts := by
    intro q hq
    exact FaithfulReindex.counts e _ _ _ (D.counts q hq)
  begins_twice := by
    intro q hq
    obtain ⟨tail, ht⟩ := D.begins_twice q hq
    exact ⟨tail.map e, by simp only [ht, List.map_cons]⟩
  counter_entry := by simpa only [vec_apply, Equiv.symm_apply_apply] using D.counter_entry
  counter_table := by
    change Matrix.vecMul (vec e D.v) (rows e (fun i j => (D.C i j : ℚ))) = _
    rw [vecMul_rows]
    exact D.counter_table
  marker := by
    intro q hq r hr
    rw [mapped_take_score, height_to_fin, ← List.map_drop, mapped_wordCount,
      dotProduct_vec]
    simp only [vec_apply, Equiv.symm_apply_apply]
    exact D.marker q hq r (by simpa only [List.length_map] using hr)
  support_safe := by
    intro q hq i hi
    simpa only [rows_mulVec, vec_apply, matrix_apply, Equiv.symm_apply_apply] using
      D.support_safe q hq (e.symm i) hi
  suffix := by
    intro eps heps q hq r hr
    rw [mapped_take_score, rows_mulVec, height_to_fin, height_to_fin, List.length_map]
    exact D.suffix eps heps q hq r (by simpa only [List.length_map] using hr)

@[simp] theorem toClock_A : (D.toClock e).A = matrix e e D.A := rfl
@[simp] theorem toClock_R : (D.toClock e).R = rows e D.R := rfl
@[simp] theorem toClock_C : (D.toClock e).C = rows e D.C := rfl
@[simp] theorem toClock_word (q : ℕ) : (D.toClock e).word q = (D.word q).map e := rfl
@[simp] theorem toClock_Arem : (D.toClock e).Arem = D.Arem := rfl
@[simp] theorem toClock_threshold : (D.toClock e).threshold = D.threshold := rfl

#print axioms toClock
end Raw
end Karlin.FaithfulClockPackage
