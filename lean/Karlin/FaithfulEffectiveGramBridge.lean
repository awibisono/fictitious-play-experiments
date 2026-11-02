import Karlin.FaithfulEffectiveGram
import Karlin.FaithfulResetEquations

/-! Compiler bridges for the existing logical Gram-section API. These are
proved equalities, not unsafe implementations or new inverse assumptions. -/
namespace Karlin.FaithfulEffectiveGramBridge

def canonicalLX {m w : Type*} [Fintype m] [Fintype w]
    [DecidableEq m] [DecidableEq w] (X : Matrix m w ℚ) : Matrix m w ℚ :=
  FaithfulEffectiveGram.gramLX X

@[csimp] theorem canonicalLX_csimp :
    @FaithfulResetEquations.canonicalLX = @canonicalLX := by
  funext m w _ _ _ _ X
  exact (FaithfulEffectiveGram.gramLX_eq X).symm

def leftInverseLX {k : ℕ} (P : FaithfulClock.Clock k) (tau : ℕ) :=
  canonicalLX (FaithfulTables.X P tau)

@[csimp] theorem leftInverseLX_csimp :
    @FaithfulResetEquations.leftInverseLX = @leftInverseLX := by
  funext k P tau
  exact (FaithfulEffectiveGram.gramLX_eq (FaithfulTables.X P tau)).symm

/-- An ordinary executable caller may retain the original mathematical API. -/
def throughOriginalAPI {m w : Type*} [Fintype m] [Fintype w]
    [DecidableEq m] [DecidableEq w] (X : Matrix m w ℚ) : Matrix m w ℚ :=
  FaithfulResetEquations.canonicalLX X

def throughOriginalClockAPI {k : ℕ} (P : FaithfulClock.Clock k) (tau : ℕ) :=
  FaithfulResetEquations.leftInverseLX P tau

end Karlin.FaithfulEffectiveGramBridge
