import Karlin.AllOrdersComplete

namespace Karlin

/-- A zero-row endpoint cannot take over after a strict word ending in another action. -/
theorem zero_row_cannot_takeover_after_strict_word
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (s : α → ℚ) (V : List α) (a g : α)
    (hdiag : M a a = 0) (hzero : ∀ i, M g i = 0) (hag : a ≠ g)
    (hvalid : IsValidStrictWord M s (V ++ [a])) :
    wordScore M s (V ++ [a]) g < wordScore M s (V ++ [a]) a := by
  have hk : V.length < (V ++ [a]).length := by simp
  have hget : (V ++ [a])[V.length] = a := by simp
  have hne : g ≠ (V ++ [a])[V.length] := by rw [hget]; exact Ne.symm hag
  have hlast := hvalid V.length hk g hne
  have htake : (V ++ [a]).take V.length = V := by simp
  change wordScore M s ((V ++ [a]).take V.length) g <
    wordScore M s ((V ++ [a]).take V.length) (V ++ [a])[V.length] at hlast
  rw [htake, hget] at hlast
  have hstep : ∀ i, wordScore M s (V ++ [a]) i = wordScore M s V i + M i a := by
    intro i
    rw [wordScore_append, wordScore_singleton_eq_scoreVec_runCount, scoreVec_runCount]
    simp [scoreVec]
  rw [hstep g, hstep a, hzero a, hdiag, add_zero, add_zero]
  exact hlast

/-- The algebraic endpoint currently adjoined to a clock has zero interactions with old actions. -/
theorem adjoined_endpoint_row_zero {k : ℕ} (fc : FullRankClock k)
    (i : Fin (fc.clock.m + 1)) :
    fc.clock.adjoinEndpoint.G (finSumFinEquiv (Sum.inr (0 : Fin 1))) i = 0 := by
  simp

/-- Specialization to the designated endpoint in the current algebraic family. -/
theorem adjoined_endpoint_cannot_takeover {k : ℕ} (fc : FullRankClock k)
    (s : Fin (fc.clock.m + 1) → ℚ) (V : List (Fin (fc.clock.m + 1)))
    (a : Fin (fc.clock.m + 1))
    (ha : a ≠ finSumFinEquiv (Sum.inr (0 : Fin 1)))
    (hvalid : IsValidStrictWord fc.clock.adjoinEndpoint.G s (V ++ [a])) :
    wordScore fc.clock.adjoinEndpoint.G s (V ++ [a])
        (finSumFinEquiv (Sum.inr (0 : Fin 1))) <
      wordScore fc.clock.adjoinEndpoint.G s (V ++ [a]) a := by
  exact zero_row_cannot_takeover_after_strict_word fc.clock.adjoinEndpoint.G s V a _
    (skew_diag_zero fc.clock.adjoinEndpoint.hskew a)
    (adjoined_endpoint_row_zero fc) ha hvalid

end Karlin

#print axioms Karlin.zero_row_cannot_takeover_after_strict_word
#print axioms Karlin.adjoined_endpoint_row_zero
#print axioms Karlin.adjoined_endpoint_cannot_takeover
