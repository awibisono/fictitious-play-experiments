import Karlin.FaithfulReindex
import Karlin.UnrolledTrajectory
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exact finite action relabeling of a fictitious-play game

All statements concern the given matrix and play sequences. Cumulative
scores start at zero, strictness starts at time one, and empirical payoffs
retain division by t. No Clock or final-family theorem is assumed.
-/
namespace Karlin.FaithfulGameReindex
open scoped BigOperators
open FaithfulReindex

variable {α β : Type*}

theorem skew_iff (e : α ≃ β) (M : Matrix α α ℚ) :
    IsSkewSymmetric (matrix e e M) ↔ IsSkewSymmetric M := by
  constructor
  · intro h i j
    simpa [matrix] using h (e i) (e j)
  · exact FaithfulReindex.skew e

/-- Relabeling preserves a payoff normalization bound without changing it. -/
theorem entry_bound_iff (e : α ≃ β) (M : Matrix α α ℚ) (B : ℚ) :
    (∀ i j, |matrix e e M i j| ≤ B) ↔ (∀ i j, |M i j| ≤ B) := by
  constructor
  · intro h i j
    simpa [matrix] using h (e i) (e j)
  · intro h i j
    exact h (e.symm i) (e.symm j)

@[simp] theorem cumScore_reindex (e : α ≃ β) (M : Matrix α α ℚ)
    (a : ℕ → α) (t : ℕ) (i : β) :
    cumScore (matrix e e M) (e ∘ a) t i = cumScore M a t (e.symm i) := by
  simp [cumScore, matrix, Function.comp_apply]

@[simp] theorem rowCumPayoff_reindex (e : α ≃ β) (M : Matrix α α ℚ)
    (a : ℕ → α) (t : ℕ) (i : β) :
    rowCumPayoff (matrix e e M) (e ∘ a) t i = rowCumPayoff M a t (e.symm i) := by
  simp [rowCumPayoff, matrix, Function.comp_apply]

@[simp] theorem colCumLoss_reindex (e : α ≃ β) (M : Matrix α α ℚ)
    (a : ℕ → α) (t : ℕ) (i : β) :
    colCumLoss (matrix e e M) (e ∘ a) t i = colCumLoss M a t (e.symm i) := by
  simp [colCumLoss, matrix, Function.comp_apply]

@[simp] theorem colCumPayoff_reindex (e : α ≃ β) (M : Matrix α α ℚ)
    (a : ℕ → α) (t : ℕ) (i : β) :
    colCumPayoff (matrix e e M) (e ∘ a) t i = colCumPayoff M a t (e.symm i) := by
  simp [colCumPayoff, matrix, Function.comp_apply]

theorem strictFP_iff (e : α ≃ β) (M : Matrix α α ℚ) (a : ℕ → α) :
    IsStrictFPTrajectory (matrix e e M) (e ∘ a) ↔ IsStrictFPTrajectory M a := by
  constructor
  · intro h t ht i hi
    have hne : e i ≠ (e ∘ a) t := fun he => hi (e.injective he)
    simpa using h t ht (e i) hne
  · intro h t ht i hi
    have hne : e.symm i ≠ a t := by
      intro he
      apply hi
      simpa [Function.comp_apply] using congrArg e he
    simpa [Function.comp_apply] using h t ht (e.symm i) hne

theorem strictTwoPlayerFP_iff (e : α ≃ β) (M : Matrix α α ℚ) (a b : ℕ → α) :
    IsStrictTwoPlayerFPTrajectory (matrix e e M) (e ∘ a) (e ∘ b) ↔
      IsStrictTwoPlayerFPTrajectory M a b := by
  constructor
  · intro h t ht
    constructor
    · intro i hi
      have hne : e i ≠ (e ∘ a) t := fun he => hi (e.injective he)
      simpa using (h t ht).1 (e i) hne
    · intro j hj
      have hne : e j ≠ (e ∘ b) t := fun he => hj (e.injective he)
      simpa using (h t ht).2 (e j) hne
  · intro h t ht
    constructor
    · intro i hi
      have hne : e.symm i ≠ a t := by
        intro he
        apply hi
        simpa [Function.comp_apply] using congrArg e he
      simpa [Function.comp_apply] using (h t ht).1 (e.symm i) hne
    · intro j hj
      have hne : e.symm j ≠ b t := by
        intro he
        apply hj
        simpa [Function.comp_apply] using congrArg e he
      simpa [Function.comp_apply] using (h t ht).2 (e.symm j) hne

theorem weakTwoPlayerFP_iff (e : α ≃ β) (M : Matrix α α ℚ) (a b : ℕ → α) :
    IsWeakTwoPlayerFPTrajectory (matrix e e M) (e ∘ a) (e ∘ b) ↔
      IsWeakTwoPlayerFPTrajectory M a b := by
  constructor
  · intro h t ht
    exact ⟨fun i => by simpa using (h t ht).1 (e i),
      fun j => by simpa using (h t ht).2 (e j)⟩
  · intro h t ht
    exact ⟨fun i => by simpa [Function.comp_apply] using (h t ht).1 (e.symm i),
      fun j => by simpa [Function.comp_apply] using (h t ht).2 (e.symm j)⟩

@[simp] theorem initial_action_iff (e : α ≃ β) (a : ℕ → α) (i : α) :
    (e ∘ a) 0 = e i ↔ a 0 = i := e.injective.eq_iff

@[simp] theorem stepDualityGap_reindex (e : α ≃ β) (M : Matrix α α ℚ)
    (a : ℕ → α) (t : ℕ) :
    stepDualityGap (matrix e e M) (e ∘ a) t = stepDualityGap M a t := by
  simp [stepDualityGap, Function.comp_apply]

@[simp] theorem empiricalStrategy_reindex [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (a : ℕ → α) (t : ℕ) (i : β) :
    empiricalStrategy (e ∘ a) t i = empiricalStrategy a t (e.symm i) := by
  simp only [empiricalStrategy, Function.comp_apply, Equiv.apply_eq_iff_eq_symm_apply]

@[simp] theorem empiricalRowPayoff_reindex [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (M : Matrix α α ℚ)
    (a : ℕ → α) (t : ℕ) (i : β) :
    empiricalRowPayoff (matrix e e M) (e ∘ a) t i = empiricalRowPayoff M a t (e.symm i) := by
  rw [empiricalRowPayoff_eq_cumScore_div, empiricalRowPayoff_eq_cumScore_div,
    cumScore_reindex]

@[simp] theorem empiricalColPayoff_reindex [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (M : Matrix α α ℚ)
    (a : ℕ → α) (t : ℕ) (i : β) :
    empiricalColPayoff (matrix e e M) (e ∘ a) t i = empiricalColPayoff M a t (e.symm i) := by
  rw [empiricalColPayoff_eq_colCumLoss_div, empiricalColPayoff_eq_colCumLoss_div,
    colCumLoss_reindex]

theorem maximum_reindex [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) (f : α → ℚ) :
    Finset.univ.sup' Finset.univ_nonempty (fun i => f (e.symm i)) =
      Finset.univ.sup' Finset.univ_nonempty f := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun i _ => Finset.le_sup' f (Finset.mem_univ (e.symm i)))
  · apply Finset.sup'_le _ _
    intro i _
    simpa using (Finset.le_sup' (fun j => f (e.symm j)) (Finset.mem_univ (e i)))

theorem minimum_reindex [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) (f : α → ℚ) :
    Finset.univ.inf' Finset.univ_nonempty (fun i => f (e.symm i)) =
      Finset.univ.inf' Finset.univ_nonempty f := by
  apply le_antisymm
  · apply Finset.le_inf' _ _
    intro i _
    simpa using (Finset.inf'_le (fun j => f (e.symm j)) (Finset.mem_univ (e i)))
  · exact Finset.le_inf' _ _ (fun i _ => Finset.inf'_le f (Finset.mem_univ (e.symm i)))

/-- Exact standard empirical saddle-point gap, preserving its division by t.
No skew symmetry, synchronized play, or trajectory premise is needed. -/
@[simp] theorem standardDualityGap_reindex [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) (M : Matrix α α ℚ) (a b : ℕ → α) (t : ℕ) :
    standardDualityGap (matrix e e M) (e ∘ a) (e ∘ b) t = standardDualityGap M a b t := by
  unfold standardDualityGap
  simp only [empiricalRowPayoff_reindex, empiricalColPayoff_reindex,
    maximum_reindex, minimum_reindex]

/-- The same common prescribed initial action fixes every weak simultaneous
trajectory after relabeling whenever the source trajectory is strict. -/
theorem unique_weak_trajectory (e : α ≃ β) {M : Matrix α α ℚ}
    (hM : IsSkewSymmetric M) {a : ℕ → α} (ha : IsStrictFPTrajectory M a)
    {rowPlay colPlay : ℕ → β}
    (hweak : IsWeakTwoPlayerFPTrajectory (matrix e e M) rowPlay colPlay)
    (hrow : rowPlay 0 = e (a 0)) (hcol : colPlay 0 = e (a 0)) (t : ℕ) :
    rowPlay t = e (a t) ∧ colPlay t = e (a t) :=
  unique_two_player_fp_trajectory (FaithfulReindex.skew e hM)
    ((strictFP_iff e M a).mpr ha) hweak hrow hcol t

/-- Setup action goes to 0; recurrent action i goes to i+1. -/
def optionFinEquiv (n : ℕ) : Option (Fin n) ≃ Fin (n + 1) := (finSuccEquiv n).symm

@[simp] theorem optionFinEquiv_none (n : ℕ) : optionFinEquiv n none = 0 := by
  simp [optionFinEquiv]

@[simp] theorem optionFinEquiv_some {n : ℕ} (i : Fin n) :
    optionFinEquiv n (some i) = i.succ := by simp [optionFinEquiv]

def finGame {n : ℕ} (M : Matrix (Option (Fin n)) (Option (Fin n)) ℚ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := matrix (optionFinEquiv n) (optionFinEquiv n) M

def finPlay {n : ℕ} (a : ℕ → Option (Fin n)) : ℕ → Fin (n + 1) := optionFinEquiv n ∘ a

theorem finGame_skew {n : ℕ} {M : Matrix (Option (Fin n)) (Option (Fin n)) ℚ}
    (hM : IsSkewSymmetric M) : IsSkewSymmetric (finGame M) :=
  FaithfulReindex.skew (optionFinEquiv n) hM

theorem finGame_strict_iff {n : ℕ} (M : Matrix (Option (Fin n)) (Option (Fin n)) ℚ)
    (a : ℕ → Option (Fin n)) : IsStrictFPTrajectory (finGame M) (finPlay a) ↔
      IsStrictFPTrajectory M a := strictFP_iff (optionFinEquiv n) M a

theorem finGame_strictTwoPlayer_iff {n : ℕ}
    (M : Matrix (Option (Fin n)) (Option (Fin n)) ℚ) (a b : ℕ → Option (Fin n)) :
    IsStrictTwoPlayerFPTrajectory (finGame M) (finPlay a) (finPlay b) ↔
      IsStrictTwoPlayerFPTrajectory M a b := strictTwoPlayerFP_iff (optionFinEquiv n) M a b

theorem finGame_weakTwoPlayer_iff {n : ℕ}
    (M : Matrix (Option (Fin n)) (Option (Fin n)) ℚ) (a b : ℕ → Option (Fin n)) :
    IsWeakTwoPlayerFPTrajectory (finGame M) (finPlay a) (finPlay b) ↔
      IsWeakTwoPlayerFPTrajectory M a b := weakTwoPlayerFP_iff (optionFinEquiv n) M a b

theorem finGame_gap {n : ℕ} (M : Matrix (Option (Fin n)) (Option (Fin n)) ℚ)
    (a b : ℕ → Option (Fin n)) (t : ℕ) :
    standardDualityGap (finGame M) (finPlay a) (finPlay b) t = standardDualityGap M a b t :=
  standardDualityGap_reindex (optionFinEquiv n) M a b t

theorem finPlay_initial {n : ℕ} (a : ℕ → Option (Fin n)) (ha : a 0 = none) :
    finPlay a 0 = 0 := by simp [finPlay, Function.comp_apply, ha]

end Karlin.FaithfulGameReindex
