import Karlin.FaithfulV15
open Karlin Karlin.FaithfulClock Karlin.FaithfulEffectiveContract
open scoped BigOperators Matrix

-- Paper's effective obligation for each existing closed clock, with no realizer
-- supplied by the caller. The same code handles every positive rational code.
theorem certified_rps (k : ℕ) (hk : 2 ≤ k) :
    ∃ code : ℕ, ∀ input : ℕ, 0 < decodeRat input →
      UniversalProgram.runCode code input =
        Part.some ((FaithfulMain.clock k hk).threshold (decodeRat input)) :=
  universal_clock_program (universalRpsFamily k hk)

theorem certified_seven (k : ℕ) (hk : 3 ≤ k) :
    ∃ code : ℕ, ∀ input : ℕ, 0 < decodeRat input →
      UniversalProgram.runCode code input =
        Part.some ((FaithfulSevenFamily.clock k hk).threshold (decodeRat input)) :=
  universal_clock_program (universalSevenFamily k hk)

-- Includes the SAME suffix inequality; no new clock or threshold witness.
theorem certified_rps_suffix (k : ℕ) (hk : 2 ≤ k) :
    let P := FaithfulMain.clock k hk
    ∃ code : ℕ, ∀ input : ℕ, 0 < decodeRat input →
      (∃ fuel, UniversalProgram.executeCode code fuel input = some (P.threshold (decodeRat input))) ∧
      ∀ q : ℕ, P.threshold (decodeRat input) ≤ q →
        ∀ r : ℕ, r ≤ (P.word q).length →
          height P.b (P.entry (q+1)) -
            height P.b (wordScore P.A (P.entry q) ((P.word q).take r)) ≤
              decodeRat input * ((P.word q).length-r : ℕ) + P.Arem :=
  universal_clock_contract (universalRpsFamily k hk)

-- This quantifier order admits any universally computable parent threshold;
-- its only correctness/termination premise is on positive rational inputs.
theorem generic_parent {k : ℕ} {P : Clock k} (A : FaithfulAdmissible.Admissible P)
    (c : Nat.Partrec.Code)
    (hc : ∀ eps : ℚ, 0 < eps → c.eval (encodeRat eps) = Part.some (P.threshold eps)) :
    ∃ code : ℕ, ∀ input : ℕ, 0 < decodeRat input →
      UniversalProgram.runCode code input = Part.some
        ((FaithfulLift.nextClock A).threshold (decodeRat input)) :=
  universal_clock_program (universalLift A (UniversalThresholdRealizer.ofCode c hc))

-- Explicit nonvacuous positive rational input: every certificate computes at 1.
example {k : ℕ} {P : Clock k} (E : UniversalThresholdRealizer P) :
    UniversalProgram.runCode E.code (encodeRat 1) = Part.some (P.threshold 1) := by
  simpa only [decode_encode_rat] using E.runCode_correct (encodeRat 1) (by simp)

-- These witness equalities are definitional; no replacement clock is selected.
example {k : ℕ} {P : Clock k} (A : FaithfulAdmissible.Admissible P)
    (E : UniversalThresholdRealizer P) :
    UniversalThresholdRealizer (FaithfulLift.nextClock A) := universalLift A E
example (k : ℕ) (hk : 0 < k) :
    FaithfulPaperCokernel.paperDividedPowerKernelBasis k hk =
      FaithfulCokernel.dividedPowerKernelBasis k :=
  FaithfulPaperCokernel.paperBasis_eq_existing k hk
example (k : ℕ) (hk : 0 < k) :
    FaithfulPaperCokernel.paperBinomialKernelBasis k hk =
      FaithfulCokernel.binomialKernelBasis k :=
  FaithfulPaperCokernel.paperBinomialBasis_eq_existing k hk

#print axioms certified_rps
#print axioms certified_seven
#print axioms certified_rps_suffix
#print axioms generic_parent

-- New independent tests of signed/noncanonical rational encodings and bounded
-- universal leaves. Use small codes; no large decoder performance claim.
#eval (decodeRat (Nat.pair (encodeInt (-2)) 4),
  decodeRat (Nat.pair (encodeInt 5) 0), decodeRat (encodeRat (3/7)))
def projectionProgram : UniversalProgram := .machine (Encodable.encode Nat.Partrec.Code.left)
#eval (projectionProgram.execute 0 (encodeRat (1/2)),
  projectionProgram.execute 200 (encodeRat (1/2)),
  projectionProgram.execute 200 (Nat.pair (encodeInt 2) 4))
#eval (execute (rpsFamily 2 (by decide)).code (encodeRat (1/25)),
  (universalSevenFamily 3 (by decide)).program.execute 0 (encodeRat (1/100)))
