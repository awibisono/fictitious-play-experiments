import Karlin.FaithfulMain
import Karlin.FaithfulEffectiveGramBridge
import Karlin.FaithfulScaleEffective
import Mathlib.Util.CompileInductive

/-!
Executable closure of the literal v15 lift. The numerical replacements below
are proved equal to the prescribed definitions. `compile_def%` only copies an
existing definition's identical body and proves the replacement by reflexivity;
it cannot supply an algorithm for a genuinely noncomputable dependency.
-/
namespace Karlin.FaithfulEffectiveLift
open scoped Matrix
open FaithfulClock FaithfulAdmissible

/-- Exact rational implementation of the prescribed target inverse. -/
def target {k : ℕ} (chi : Fin k → ℚ) (tau : ℕ) (c H : ℚ) : Fin k → ℚ :=
  Matrix.vecMul (fun i => FaithfulNextTables.targetRhs chi tau c H i.succ)
    (FaithfulEffectiveGram.inverse (FaithfulTables.Fblock k tau))

@[csimp] theorem target_csimp : @FaithfulNextTables.target = @target := by
  funext k chi tau c H
  simp only [target, FaithfulNextTables.target, FaithfulEffectiveGram.inverse_eq]

/-- The exact prospective scale from executable rational coefficient lists. -/
def nextScale {o : Type*} [Fintype o] (k : ℕ) (hk : 2 ≤ k + 1)
    (Smid X : Matrix o (Fin (k + 1)) ℚ) (zeta zeta0 ellStar : Fin (k + 1) → ℚ)
    (T1 lam : ℚ) (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) : ℕ :=
  FaithfulScaleEffective.computedScale (k + 1) hk
    (FaithfulNextTables.fixedMoment k Smid X zeta zeta0 ellStar T1 lam E)
    (FaithfulNextTables.fixedLength k X zeta0 ellStar T1 lam) zeta (1 / 2)

@[csimp] theorem nextScale_csimp : @FaithfulNextTables.nextScale = @nextScale := by
  funext o _ k hk Smid X zeta zeta0 ellStar T1 lam E
  exact (FaithfulScaleEffective.computedScale_spec_all (k + 1) hk _ _ _ _).symm

/-- The same prescribed integer correction, including a possible zero pivot. -/
def nextCorrection {o : Type*} [Fintype o] (k : ℕ) (hk : 2 ≤ k + 1)
    (Smid X : Matrix o (Fin (k + 1)) ℚ) (zeta zeta0 ellStar : Fin (k + 1) → ℚ)
    (T1 lam : ℚ) (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) : Fin (k + 2) → ℤ :=
  FaithfulScaleEffective.computedCorrection (k + 1) hk
    (FaithfulNextTables.fixedMoment k Smid X zeta zeta0 ellStar T1 lam E)
    (FaithfulNextTables.fixedLength k X zeta0 ellStar T1 lam) zeta (1 / 2)

@[csimp] theorem nextCorrection_csimp :
    @FaithfulNextTables.nextCorrection = @nextCorrection := by
  funext o _ k hk Smid X zeta zeta0 ellStar T1 lam E
  exact (FaithfulScaleEffective.computedCorrection_spec_all (k + 1) hk _ _ _ _).symm

-- Identical-body recompilation; every generated equality is reflexive.
compile_def% FaithfulGain.correctedMoment
compile_def% FaithfulGain.AdmissibleGain.momentTable
compile_def% FaithfulSynthesis.cross
compile_def% FaithfulSynthesis.coupling
compile_def% FaithfulResetEquations.actualCoupling
compile_def% FaithfulResetEquations.actualGame
compile_def% FaithfulNextClock.Lift.coupling
compile_def% FaithfulNextClock.Lift.J
compile_def% FaithfulNextClock.Lift.game
compile_def% FaithfulNextClock.Lift.entryTable
compile_def% FaithfulNextClock.Lift.scoreTable
compile_def% FaithfulNextClockAssembly.entryScore
compile_def% FaithfulNextClockAssembly.rotatedScore
compile_def% FaithfulNextClockAssembly.nextRaw
compile_def% FaithfulNextClockAssembly.nextClock

compile_def% FaithfulNextTables.nextTarget
compile_def% FaithfulNextTables.prescribedT2
compile_def% FaithfulNextTables.prescribedWeights
compile_def% FaithfulController.nextScale
compile_def% FaithfulController.secondScale
compile_def% FaithfulController.nextWeights
compile_def% FaithfulController.chosenOnset
compile_def% FaithfulLift.nextClock
compile_def% FaithfulLift.nextTableMatch
compile_def% FaithfulNextAdmissible.admissible
compile_def% FaithfulLift.nextAdmissible
compile_def% FaithfulFamily.iterate
compile_def% FaithfulFamily.atOrder
compile_def% FaithfulMain.step
compile_def% FaithfulMain.bundle
compile_def% FaithfulMain.clock
compile_def% FaithfulMain.admissible
compile_def% FaithfulMain.matrix
compile_def% FaithfulMain.trajectory

/-- Ordinary compiled callers of the full, proof-carrying original APIs. -/
def liftClock {k : ℕ} {P : Clock k} (A : Admissible P) : Clock (k + 1) :=
  FaithfulLift.nextClock A

def liftAdmissible {k : ℕ} {P : Clock k} (A : Admissible P) : Admissible (liftClock A) :=
  FaithfulLift.nextAdmissible A

def familyClock (k : ℕ) (hk : 2 ≤ k) : Clock k := FaithfulMain.clock k hk

def familyAdmissible (k : ℕ) (hk : 2 ≤ k) : Admissible (familyClock k hk) :=
  FaithfulMain.admissible k hk

def familyMatrix (k : ℕ) (hk : 2 ≤ k) := FaithfulMain.matrix k hk

def familyTrajectory (k : ℕ) (hk : 2 ≤ k) := FaithfulMain.trajectory k hk

def familyThreshold (k : ℕ) (hk : 2 ≤ k) (eps : ℚ) : ℕ :=
  (familyClock k hk).threshold eps

/-- A compiled transformation of a supplied parent program and its verified
admissibility data. The type `Bundle` itself does not assert computability of
arbitrary inhabitants; this particular constructor has executable Lean code. -/
def liftBundle (k : ℕ) (B : FaithfulFamily.Bundle k) : FaithfulFamily.Bundle (k + 1) :=
  FaithfulMain.step k B

/-- The actual proof-carrying family program, closed from the executable RPS
seed under the compiled lift. Proof fields are erased during execution. -/
def familyBundle (k : ℕ) (hk : 2 ≤ k) : FaithfulFamily.Bundle k :=
  FaithfulMain.bundle k hk

def familyWord (k : ℕ) (hk : 2 ≤ k) (q : ℕ) : List (Fin (familyClock k hk).m) :=
  (familyBundle k hk).clock.word q

theorem liftBundle_eq (k : ℕ) (B : FaithfulFamily.Bundle k) :
    liftBundle k B = FaithfulMain.step k B := rfl

theorem familyBundle_eq (k : ℕ) (hk : 2 ≤ k) :
    familyBundle k hk = FaithfulMain.bundle k hk := rfl

theorem familyWord_eq (k : ℕ) (hk : 2 ≤ k) (q : ℕ) :
    familyWord k hk q = (FaithfulMain.clock k hk).word q := rfl

theorem familyThreshold_eq (k : ℕ) (hk : 2 ≤ k) (eps : ℚ) :
    familyThreshold k hk eps = (FaithfulMain.clock k hk).threshold eps := rfl

theorem familyMatrix_eq (k : ℕ) (hk : 2 ≤ k) :
    familyMatrix k hk = FaithfulMain.matrix k hk := rfl

theorem familyTrajectory_eq (k : ℕ) (hk : 2 ≤ k) :
    familyTrajectory k hk = FaithfulMain.trajectory k hk := rfl

/-- The executable threshold certifies the actual inherited every-prefix
suffix inequality, with the same fixed remainder stored in the clock. -/
theorem familySuffix (k : ℕ) (hk : 2 ≤ k) (eps : ℚ) (heps : 0 < eps)
    (q : ℕ) (hq : familyThreshold k hk eps ≤ q)
    (r : ℕ) (hr : r ≤ (familyWord k hk q).length) :
    let P := familyClock k hk
    height P.b (P.entry (q + 1)) -
      height P.b (wordScore P.A (P.entry q) ((familyWord k hk q).take r)) ≤
        eps * ((familyWord k hk q).length - r : ℕ) + P.Arem :=
  (familyClock k hk).suffix eps heps q hq r hr

end Karlin.FaithfulEffectiveLift
