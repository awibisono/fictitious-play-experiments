import Karlin.FaithfulNextClockAssembly

/-! The literal reset cascade has constant maximum score, including its entry,
every intermediate play, and its complete endpoint. The actual parameter and
chronology theorems discharge all signs, counts, and validity assumptions. -/
namespace Karlin.FaithfulResetPlateau
open scoped BigOperators Matrix
open FaithfulClock FaithfulInheritance FaithfulAdmissible
open FaithfulController FaithfulNextClock FaithfulNextClock.Lift
open FaithfulNextClockAssembly
set_option maxHeartbeats 800000

/-- A valid skew-game word with equal endpoint maxima has a constant maximum
at every prefix. Both the empty prefix and complete word are included. -/
theorem prefix_height_eq_of_endpoints {α : Type*} [Fintype α] [DecidableEq α]
    {rnk : ℕ} (b : α) (G : Matrix α α ℚ) (hG : IsSkewSymmetric G)
    (s : α → ℚ) (rank : α → Fin rnk) (W : List α)
    (hW : IsValidPriorityWord G s rank W) (z : ℚ)
    (hstart : scoreHeight b s = z) (hend : scoreHeight b (wordScore G s W) = z)
    (r : ℕ) (hr : r ≤ W.length) :
    scoreHeight b (wordScore G s (W.take r)) = z := by
  have hl := scoreHeight_prefix_ge b G hG s rank W hW r hr
  rw [hstart] at hl
  have hsplit : IsValidPriorityWord G s rank (W.take r ++ W.drop r) := by
    simpa only [List.take_append_drop] using hW
  have htail := ((isValidPriorityWord_append G s rank (W.take r) (W.drop r)).mp hsplit).2
  have hu := scoreHeight_prefix_ge b G hG (wordScore G s (W.take r)) rank
    (W.drop r) htail (W.drop r).length le_rfl
  simp only [List.take_length, ← wordScore_append, List.take_append_drop, hend] at hu
  exact le_antisymm hu hl

variable {k : ℕ} {P : Clock k} (A : Admissible P)

/-- The literal final reset in the prescribed chronological order. -/
def lastReset : Res (k := k) := ⟨(k + 1) + (k + 1) - 1, by omega⟩

theorem last_column_zero (T1 T2 : ℕ) (j : Res (k := k)) :
    J A T1 T2 j (lastReset (k := k)) = 0 := by
  apply Lift.J_lower
  have := j.isLt
  simp only [lastReset, Fin.val_mk]
  omega

/-- At the complete reset endpoint, every score is at most the reset height. -/
theorem reset_endpoint_le (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) (i : Act (P := P)) :
    entryScore A T1 T2 (q + 1) i ≤ dotProduct (zeta A T1) (binomBasis (k + 1) q) := by
  cases i with
  | inl i => exact old_end_le A T1 T2 q hv hq i
  | inr j =>
    change (V_reset (J A T1 T2) (countRat A T1 T2) (B_mat (k + 1)) (zeta A T1)).mulVec
      (binomBasis (k + 1) (q + 1)) j ≤ _
    rw [FaithfulChronologyAlgebra.V_reset_eval_succ]
    apply sub_le_self
    change 0 ≤ ∑ i : Res (k := k), J A T1 T2 i j *
      (countRat A T1 T2).mulVec (binomBasis (k + 1) q) i
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (J_nonnegative A T1 T2 hv i j)
    rw [← count_cast_outer A T1 T2 q hv hq i]
    exact Nat.cast_nonneg _

/-- The last reset attains the unchanged height at the complete endpoint. -/
theorem reset_endpoint_attains (T1 T2 q : ℕ) :
    entryScore A T1 T2 (q + 1) (Sum.inr (lastReset (k := k))) =
      dotProduct (zeta A T1) (binomBasis (k + 1) q) := by
  change (V_reset (J A T1 T2) (countRat A T1 T2) (B_mat (k + 1)) (zeta A T1)).mulVec
    (binomBasis (k + 1) (q + 1)) (lastReset (k := k)) = _
  rw [FaithfulChronologyAlgebra.V_reset_eval_succ]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    last_column_zero, zero_mul, Finset.sum_const_zero, sub_zero]

theorem reset_endpoint_height (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) :
    scoreHeight base (wordScore (game A T1 T2) (rotatedScore A T1 T2 q)
      (reset A T1 T2 q)) = dotProduct (zeta A T1) (binomBasis (k + 1) q) := by
  rw [post_reset A T1 T2 q hv hq]
  rw [← reset_endpoint_attains A T1 T2 q]
  apply scoreHeight_eq
  intro i
  rw [reset_endpoint_attains]
  exact reset_endpoint_le A T1 T2 q hv hq i

/-- Proposition reset chronology's literal plateau, on the actual synthesized
game and reset word, with the whole range 0 <= r <= reset.length. -/
theorem reset_prefix_height (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) (r : ℕ) (hr : r ≤ (reset A T1 T2 q).length) :
    scoreHeight base (wordScore (game A T1 T2) (rotatedScore A T1 T2 q)
      ((reset A T1 T2 q).take r)) = dotProduct (zeta A T1) (binomBasis (k + 1) q) := by
  apply prefix_height_eq_of_endpoints base (game A T1 T2) (game_skew A T1 T2)
    (rotatedScore A T1 T2 q) (rank (P := P)) (reset A T1 T2 q)
    (reset_valid A T1 T2 q hv hq) _ _ (reset_endpoint_height A T1 T2 q hv hq) r hr
  exact entry_height A T1 T2 q hv hq

/-- The same plateau located inside the complete rotated word. -/
theorem rotated_reset_prefix_height (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) (r : ℕ) (hr : r ≤ (reset A T1 T2 q).length) :
    scoreHeight base (wordScore (game A T1 T2) (rotatedScore A T1 T2 q)
      ((word A T1 T2 q).take r)) = dotProduct (zeta A T1) (binomBasis (k + 1) q) := by
  simp only [reset] at hr
  rw [Lift.word, rotatedWord, List.take_append_of_le_length hr]
  exact reset_prefix_height A T1 T2 q hv hq r hr

/-- The unrotated old-then-reset trajectory has the same plateau after the old
stage, including the instant before its first reset play and its final state. -/
theorem raw_reset_prefix_height (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) (r : ℕ) (hr : r ≤ (reset A T1 T2 q).length) :
    scoreHeight base (wordScore (game A T1 T2) (entryScore A T1 T2 q)
      ((old A q).map Sum.inl ++ (reset A T1 T2 q).take r)) =
      dotProduct (zeta A T1) (binomBasis (k + 1) q) := by
  rw [wordScore_append, post_old A T1 T2 q hv hq]
  exact reset_prefix_height A T1 T2 q hv hq r hr

/-- The plateau in the conventional finite action labels of the constructed
next Clock, on precisely its own game, entry state, and phase word. -/
theorem nextClock_reset_prefix_height (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) (r : ℕ) (hr : r ≤ (reset A T1 T2 q).length) :
    FaithfulClock.height (nextClock A T1 T2 hv).b
      (wordScore (nextClock A T1 T2 hv).A ((nextClock A T1 T2 hv).entry q)
        (((nextClock A T1 T2 hv).word q).take r)) =
      dotProduct (zeta A T1) (binomBasis (k + 1) q) := by
  have hs := FaithfulClockPackage.Raw.mapped_take_score
    (nextRaw A T1 T2 hv) finSumFinEquiv q r
  change wordScore (nextClock A T1 T2 hv).A ((nextClock A T1 T2 hv).entry q)
    (((nextClock A T1 T2 hv).word q).take r) =
      FaithfulReindex.vec finSumFinEquiv
        (wordScore (game A T1 T2) (rotatedScore A T1 T2 q)
          ((word A T1 T2 q).take r)) at hs
  rw [hs, nextClock_b]
  exact (FaithfulReindex.height_to_fin finSumFinEquiv (base (P := P))
    (wordScore (game A T1 T2) (rotatedScore A T1 T2 q)
      ((word A T1 T2 q).take r))).trans
    (rotated_reset_prefix_height A T1 T2 q hv hq r hr)

/-- Specialization to the completely selected parameters. No reset sign,
compatibility, validity, or scale obligation remains as an external premise. -/
theorem chosen_reset_prefix_height (q : ℕ)
    (hq : outerOnset A (firstScale A) (secondScale A (firstScale A)) ≤ q)
    (r : ℕ)
    (hr : r ≤ (reset A (firstScale A) (secondScale A (firstScale A)) q).length) :
    scoreHeight base
      (wordScore (game A (firstScale A) (secondScale A (firstScale A)))
        (rotatedScore A (firstScale A) (secondScale A (firstScale A)) q)
        ((reset A (firstScale A) (secondScale A (firstScale A)) q).take r)) =
      dotProduct (zeta A (firstScale A)) (binomBasis (k + 1) q) :=
  reset_prefix_height A _ _ q (chosen_valid A) hq r hr

#print axioms reset_prefix_height
#print axioms rotated_reset_prefix_height
#print axioms raw_reset_prefix_height
#print axioms nextClock_reset_prefix_height
#print axioms chosen_reset_prefix_height
end Karlin.FaithfulResetPlateau
