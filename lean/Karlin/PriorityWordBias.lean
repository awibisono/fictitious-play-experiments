import Karlin.ChronologyAndMain

namespace Karlin
open scoped BigOperators

/-- Weak best responses with a fixed priority rank resolving every tie. -/
def IsValidPriorityWord {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (M : Matrix α α ℚ) (s : α → ℚ) (rank : α → Fin m) (W : List α) : Prop :=
  ∀ (k : ℕ) (hk : k < W.length) (j : α),
    wordScore M s (W.take k) j ≤ wordScore M s (W.take k) W[k] ∧
    (j ≠ W[k] → wordScore M s (W.take k) j = wordScore M s (W.take k) W[k] →
      (rank W[k]).val < (rank j).val)

/-- A fixed vector added to the initial score remains the same fixed vector after any word. -/
theorem wordScore_add_bias {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (s β : α → ℚ) (W : List α) (i : α) :
    wordScore M (fun j => s j + β j) W i = wordScore M s W i + β i := by
  simp only [wordScore, scoreVec]
  ring

/-- One denominator for the initial scores and payoff entries works for every finite word. -/
theorem wordScore_on_integer_grid {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (s : α → ℚ) (D : ℚ)
    (hM : ∀ i j, ∃ z : ℤ, D * M i j = z)
    (hs : ∀ i, ∃ z : ℤ, D * s i = z) (W : List α) (i : α) :
    ∃ z : ℤ, D * wordScore M s W i = z := by
  classical
  choose z hz using hM
  obtain ⟨b, hb⟩ := hs i
  refine ⟨b + ∑ j : α, z i j * (W.count j : ℤ), ?_⟩
  simp only [wordScore, scoreVec, wordCountVec, mul_add, Finset.mul_sum, ← mul_assoc]
  simp only [hb, hz, Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

/-- Strict inequalities on a common integer grid have a uniform positive gap. -/
theorem integer_grid_strict_gap {D ui uj : ℚ} (hD : 0 < D)
    (hi : ∃ z : ℤ, D * ui = z) (hj : ∃ z : ℤ, D * uj = z) (hlt : uj < ui) :
    1 / D ≤ ui - uj := by
  obtain ⟨zi, hi⟩ := hi
  obtain ⟨zj, hj⟩ := hj
  have hq : (zj : ℚ) < (zi : ℚ) := by nlinarith [mul_lt_mul_of_pos_left hlt hD]
  have hz : zj + 1 ≤ zi := Int.add_one_le_iff.mpr (by exact_mod_cast hq)
  have hzq : (zj : ℚ) + 1 ≤ (zi : ℚ) := by exact_mod_cast hz
  apply (div_le_iff₀ hD).2
  nlinarith

/-- A single rational priority bias makes the whole word strict, not just its endpoints. -/
theorem priority_word_bias_strict {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (M : Matrix α α ℚ) (s : α → ℚ) (rank : α → Fin m) (W : List α)
    (hm : 0 < m) (D : ℚ) (hD : 0 < D)
    (hM : ∀ i j, ∃ z : ℤ, D * M i j = z)
    (hs : ∀ i, ∃ z : ℤ, D * s i = z)
    (hW : IsValidPriorityWord M s rank W) :
    IsValidStrictWord M
      (fun i => s i + tieRemovalBias (m : ℚ) D ((rank i).val : ℚ)) W := by
  intro k hk j hj
  rw [wordScore_add_bias, wordScore_add_bias]
  have hmQ : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℚ) < 1 / (4 * (m : ℚ) * D) := by positivity
  obtain ⟨hle, htie⟩ := hW k hk j
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hgap := integer_grid_strict_gap hD
      (wordScore_on_integer_grid M s D hM hs (W.take k) W[k])
      (wordScore_on_integer_grid M s D hM hs (W.take k) j) hlt
    have hi0 : (0 : ℚ) ≤ (rank W[k]).val := Nat.cast_nonneg _
    have hj0 : (0 : ℚ) ≤ (rank j).val := Nat.cast_nonneg _
    have hi1 : ((rank W[k]).val : ℚ) ≤ (m : ℚ) - 1 := by
      have := (rank W[k]).isLt
      have : ((rank W[k]).val : ℚ) + 1 ≤ (m : ℚ) := by exact_mod_cast this
      linarith
    have hj1 : ((rank j).val : ℚ) ≤ (m : ℚ) - 1 := by
      have := (rank j).isLt
      have : ((rank j).val : ℚ) + 1 ≤ (m : ℚ) := by exact_mod_cast this
      linarith
    have := tieRemoval_strict_preserved hmQ hD hi0 hi1 hj0 hj1 hgap
    linarith
  · have hr : (1 : ℚ) ≤ ((rank j).val : ℚ) - ((rank W[k]).val : ℚ) := by
      have := htie hj heq
      have : ((rank W[k]).val : ℚ) + 1 ≤ ((rank j).val : ℚ) := by exact_mod_cast this
      linarith
    have := tieRemoval_tie_broken hmQ hD heq.symm hr
    linarith

/-- The same bias preserves exact phase-to-phase score transitions. -/
theorem word_transition_add_bias {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (s sNext β : α → ℚ) (W : List α)
    (h : wordScore M s W = sNext) :
    wordScore M (fun i => s i + β i) W = fun i => sNext i + β i := by
  funext i
  rw [wordScore_add_bias, h]

/-- One fixed bias works for every phase, with grid integrality required only at phase zero. -/
theorem priority_phase_family_bias_strict {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (M : Matrix α α ℚ) (s : ℕ → α → ℚ) (rank : α → Fin m) (W : ℕ → List α)
    (hm : 0 < m) (D : ℚ) (hD : 0 < D)
    (hM : ∀ i j, ∃ z : ℤ, D * M i j = z)
    (hs0 : ∀ i, ∃ z : ℤ, D * s 0 i = z)
    (htransition : ∀ p, wordScore M (s p) (W p) = s (p + 1))
    (hpriority : ∀ p, IsValidPriorityWord M (s p) rank (W p)) :
    (∀ p, IsValidStrictWord M
      (fun i => s p i + tieRemovalBias (m : ℚ) D ((rank i).val : ℚ)) (W p)) ∧
    (∀ p, wordScore M
      (fun i => s p i + tieRemovalBias (m : ℚ) D ((rank i).val : ℚ)) (W p) =
      fun i => s (p + 1) i + tieRemovalBias (m : ℚ) D ((rank i).val : ℚ)) := by
  have hgrid : ∀ p i, ∃ z : ℤ, D * s p i = z := by
    intro p
    induction p with
    | zero => exact hs0
    | succ p ih =>
      intro i
      rw [← htransition p]
      exact wordScore_on_integer_grid M (s p) D hM ih (W p) i
  exact ⟨fun p => priority_word_bias_strict M (s p) rank (W p) hm D hD hM
      (hgrid p) (hpriority p),
    fun p => word_transition_add_bias M (s p) (s (p + 1))
      (fun i => tieRemovalBias (m : ℚ) D ((rank i).val : ℚ)) (W p) (htransition p)⟩

end Karlin

#print axioms Karlin.wordScore_add_bias
#print axioms Karlin.wordScore_on_integer_grid
#print axioms Karlin.integer_grid_strict_gap
#print axioms Karlin.priority_word_bias_strict
#print axioms Karlin.word_transition_add_bias
#print axioms Karlin.priority_phase_family_bias_strict
