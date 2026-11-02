import Karlin.FaithfulParameters

/-! The literal v15 least grid denominator and minimum-based setup shift. -/
namespace Karlin.FaithfulBiasSetup

variable {m : ℕ}

def gridData (M : Matrix (Fin m) (Fin m) ℚ) (s : Fin m → ℚ) :
    Sum (Fin m × Fin m) (Fin m) → ℚ
  | .inl p => M p.1 p.2
  | .inr i => s i

def gridDenominator (M : Matrix (Fin m) (Fin m) ℚ) (s : Fin m → ℚ) : ℕ :=
  FaithfulParameters.heightMultiplier (gridData M s)

theorem gridDenominator_pos (M : Matrix (Fin m) (Fin m) ℚ) (s : Fin m → ℚ) :
    0 < gridDenominator M s := FaithfulParameters.heightMultiplier_pos _

theorem grid_matrix (M : Matrix (Fin m) (Fin m) ℚ) (s : Fin m → ℚ) (i j : Fin m) :
    ∃ z : ℤ, (gridDenominator M s : ℚ) * M i j = z :=
  ⟨FaithfulParameters.clearedHeight (gridData M s) (.inl (i,j)),
    (FaithfulParameters.clearedHeight_cast (gridData M s) (.inl (i,j))).symm⟩

theorem grid_vector (M : Matrix (Fin m) (Fin m) ℚ) (s : Fin m → ℚ) (i : Fin m) :
    ∃ z : ℤ, (gridDenominator M s : ℚ) * s i = z :=
  ⟨FaithfulParameters.clearedHeight (gridData M s) (.inr i),
    (FaithfulParameters.clearedHeight_cast (gridData M s) (.inr i)).symm⟩

theorem gridDenominator_minimal (M : Matrix (Fin m) (Fin m) ℚ) (s : Fin m → ℚ)
    (n : ℕ) (hn : 0 < n)
    (hM : ∀ i j, ∃ z : ℤ, (n : ℚ) * M i j = z)
    (hs : ∀ i, ∃ z : ℤ, (n : ℚ) * s i = z) : gridDenominator M s ≤ n := by
  apply FaithfulParameters.heightMultiplier_minimal _ _ hn
  intro x
  cases x with
  | inl p => obtain ⟨z,hz⟩ := hM p.1 p.2; exact ⟨z,hz.symm⟩
  | inr i => obtain ⟨z,hz⟩ := hs i; exact ⟨z,hz.symm⟩

def shift (b : Fin m) (s : Fin m → ℚ) : ℚ :=
  1 - Finset.univ.inf' ⟨b, Finset.mem_univ b⟩ s

theorem one_le_shift (b : Fin m) (s : Fin m → ℚ) (i : Fin m) :
    1 ≤ s i + shift b s := by
  have h := Finset.inf'_le s (Finset.mem_univ i)
  unfold shift
  linarith

end Karlin.FaithfulBiasSetup
