import Karlin.FaithfulNextClockAssembly
import Karlin.FaithfulSeed

/-!
# Executable inherited suffix thresholds

Only finite rational coefficient rows and natural bounds enter the program.
The parent threshold at the supplied epsilon is an explicit natural input.
Noncomputable Polynomial values are confined to the correctness proof; no
polynomial or asymptotic witness is selected by the executable definition.
-/
namespace Karlin.FaithfulEffectiveThreshold
open scoped BigOperators Matrix
open FaithfulClock FaithfulGrowth

/-- All coefficient data are fixed before epsilon. The parent rule's value
is supplied separately, so the executable program has only finite inputs. -/
structure Data (k : ℕ) where
  parentOnset : ℕ
  outerOnset : ℕ
  scale : ℕ
  parentLength : Fin k → ℚ
  parentGain : Fin k → ℚ
  resetLength : Fin (k + 1) → ℚ
  resetGain : Fin (k + 1) → ℚ

def program {k : ℕ} (d : Data k) (parentAtEpsilon : ℕ) (eps : ℚ) : ℕ :=
  max d.outerOnset
    (max (rowDominationThreshold d.resetLength d.resetGain k eps)
      ⌈((max parentAtEpsilon
        (max d.parentOnset (rowDominationThreshold d.parentLength d.parentGain (k - 1) eps)) : ℕ) : ℚ) /
          (d.scale : ℚ)⌉₊)

theorem program_onset {k : ℕ} (d : Data k) (parentAtEpsilon : ℕ) (eps : ℚ) :
    d.outerOnset ≤ program d parentAtEpsilon eps := le_max_left _ _

/-- The executable coefficient program dominates the lower-degree row. Its
premises concern finitely many rational entries, never a chosen polynomial. -/
theorem coefficient_domination {n d : ℕ} (hd : 0 < d) (c g : Fin n → ℚ)
    (hc : ∀ j, d < j.val → c j = 0)
    (hg : ∀ j, d - 1 < j.val → g j = 0)
    (hL : 0 < rowCoeff c d) {eps : ℚ} (heps : 0 < eps)
    {q : ℕ} (hq : rowDominationThreshold c g d eps ≤ q) :
    (∑ j, g j * (Nat.choose q j.val : ℚ)) ≤
      eps * (∑ j, c j * (Nat.choose q j.val : ℚ)) := by
  have h := polynomial_domination (rowPoly c) (rowPoly g) hd
    (rowPoly_natDegree_le_of_vanishing c hc) (rowPoly_natDegree_le_of_vanishing g hg)
    (by simpa only [rowCoeff_eq] using hL) heps
    (by simpa only [rowDominationThreshold_eq] using hq)
  simpa only [rowPoly_eval_nat] using h

/-- The actual parent's finite rational tables, with no epsilon argument. -/
def fromClock {k : ℕ} (P : Clock k) (tau Qout : ℕ) (c H : ℚ) : Data k where
  parentOnset := P.Q
  outerOnset := Qout
  scale := tau
  parentLength := FaithfulGrowth.Clock.totalCountCoeff P
  parentGain := FaithfulGrowth.Clock.heightGainCoeff P
  resetLength := FaithfulInheritance.nextOldLengthRow P tau
  resetGain := FaithfulInheritance.resetGainRow P tau c H

def clockThreshold {k : ℕ} (P : Clock k) (tau Qout : ℕ) (c H eps : ℚ) : ℕ :=
  program (fromClock P tau Qout c H) (P.threshold eps) eps

/-- This executable implementation is exactly the existing inherited rule. -/
theorem clockThreshold_eq {k : ℕ} (P : Clock k) (tau Qout : ℕ) (c H eps : ℚ) :
    clockThreshold P tau Qout c H eps =
      FaithfulInheritance.inheritedThreshold P tau Qout c H eps := by
  unfold clockThreshold program fromClock FaithfulInheritance.inheritedThreshold
    FaithfulInheritance.resetPrefixThreshold FaithfulGrowth.Clock.bundleThreshold
    FaithfulGrowth.Clock.wholePhaseThreshold
  rfl

theorem clockThreshold_onset {k : ℕ} (P : Clock k) (tau Qout : ℕ) (c H eps : ℚ) :
    Qout ≤ clockThreshold P tau Qout c H eps :=
  program_onset (fromClock P tau Qout c H) (P.threshold eps) eps

/-- The seed's epsilon-rule is genuinely executable and constant. -/
def seedThreshold (_eps : ℚ) : ℕ := 1

theorem seedThreshold_eq (eps : ℚ) : seedThreshold eps = FaithfulSeed.rpsClock.threshold eps := rfl

theorem seed_suffix (eps : ℚ) (heps : 0 < eps) (q : ℕ) (hq : seedThreshold eps ≤ q)
    (r : ℕ) (hr : r ≤ (FaithfulSeed.rpsClock.word q).length) :
    height FaithfulSeed.rpsClock.b (FaithfulSeed.rpsClock.entry (q + 1)) -
      height FaithfulSeed.rpsClock.b
        (wordScore FaithfulSeed.rpsClock.A (FaithfulSeed.rpsClock.entry q)
          ((FaithfulSeed.rpsClock.word q).take r)) ≤
      eps * ((FaithfulSeed.rpsClock.word q).length - r : ℕ) + FaithfulSeed.rpsClock.Arem :=
  FaithfulSeed.rpsClock.suffix eps heps q hq r hr

namespace Actual
open FaithfulAdmissible FaithfulParameters.AdmissibleParameters
open FaithfulNextClock FaithfulNextClock.Lift FaithfulNextClockAssembly
variable {k : ℕ} {P : Clock k} (A : Admissible P)

def threshold (T1 T2 : ℕ) (eps : ℚ) : ℕ :=
  clockThreshold P A.tau (FaithfulController.outerOnset A T1 T2)
    (FaithfulGain.AdmissibleGain.selectedGain A (lam A) T1) (baseline P) eps

theorem threshold_eq (T1 T2 : ℕ) (eps : ℚ) : threshold A T1 T2 eps =
    FaithfulNextClockAssembly.threshold A T1 T2 eps := by
  unfold threshold FaithfulNextClockAssembly.threshold
  exact clockThreshold_eq _ _ _ _ _ _

/-- The computed rule proves the actual same-word, every-prefix suffix
estimate. ValidParameters is the existing finite game-construction input;
no inherited suffix or unspecified growth onset is assumed. -/
theorem suffix (T1 T2 : ℕ) (hv : FaithfulController.ValidParameters A T1 T2)
    (eps : ℚ) (heps : 0 < eps) (q : ℕ) (hq : threshold A T1 T2 eps ≤ q)
    (r : ℕ) (hr : r ≤ (word A T1 T2 q).length) :
    FaithfulInheritance.scoreHeight base (rotatedScore A T1 T2 (q + 1)) -
      FaithfulInheritance.scoreHeight base
        (wordScore (game A T1 T2) (rotatedScore A T1 T2 q) ((word A T1 T2 q).take r)) ≤
      eps * ((word A T1 T2 q).length - r : ℕ) + (P.Arem + 1) :=
  FaithfulNextClockAssembly.suffix A T1 T2 hv eps heps q
    (by rwa [← threshold_eq A T1 T2 eps]) r hr

end Actual
end Karlin.FaithfulEffectiveThreshold
