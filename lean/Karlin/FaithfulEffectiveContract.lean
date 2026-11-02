import Karlin.FaithfulEffectiveThreshold
import Karlin.FaithfulSevenFamily
import Mathlib.Logic.Encodable.Basic
import Mathlib.Computability.PartrecCode

/-!
# Finite and universal program contracts for the suffix threshold

A raw `Clock` need not have a computable threshold. The first companion
certifies a finite arithmetic VM specialized to the delivered families.
`UniversalThresholdRealizer` then admits every partial-recursive parent
program through the genuine `Nat.Partrec.Code.eval` interpreter. Its bounded
interpreter has soundness and completeness, with termination proved for every
positive rational input. No syntax constructor accepts a function or oracle.

Both compilers compute the *existing* threshold; neither changes the clock,
selected parameters, matrices, words, or family witnesses. Their ordinary
family definitions use the proved-equal implementations in `FaithfulEffectiveLift`.
Arithmetic instruction counts and universal interpreter fuel are not bit
complexity or practical extraction-performance claims. We do not claim a
separate translation theorem for the uniform order-to-code compiler into a
universal Turing-machine model.
-/
set_option maxHeartbeats 2000000

namespace Karlin.FaithfulEffectiveContract
open FaithfulClock FaithfulAdmissible

/-- Even codes are nonnegative; odd codes encode negative successors. -/
def encodeInt : ℤ → ℕ
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

def decodeInt (n : ℕ) : ℤ :=
  if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)

@[simp] theorem decode_encode_int (z : ℤ) : decodeInt (encodeInt z) = z := by
  cases z <;> simp [encodeInt, decodeInt]
  omega

/-- Rational codes pair a signed numerator code with a natural denominator.
A zero denominator decodes to zero, so every input code has defined meaning. -/
def encodeRat (q : ℚ) : ℕ := Nat.pair (encodeInt q.num) q.den

def decodeRat (n : ℕ) : ℚ :=
  (decodeInt (Nat.unpair n).1 : ℚ) / ((Nat.unpair n).2 : ℚ)

@[simp] theorem decode_encode_rat (q : ℚ) : decodeRat (encodeRat q) = q := by
  simp [decodeRat, encodeRat, Rat.num_div_den]

/-- Opcodes: 0=input, 1=constant, 2=multiply, 3=divide, 4=maximum,
5=natural ceiling. Unknown instructions leave the stack unchanged. -/
def instruction (op data : ℕ) : ℕ := Nat.pair op data
abbrev Program := List ℕ

def tick (token : ℕ) (eps : ℚ) (stack : List ℚ) : List ℚ :=
  match (Nat.unpair token).1, stack with
  | 0, s => eps :: s
  | 1, s => decodeRat (Nat.unpair token).2 :: s
  | 2, y :: x :: s => x * y :: s
  | 3, y :: x :: s => x / y :: s
  | 4, y :: x :: s => max x y :: s
  | 5, x :: s => (⌈x⌉₊ : ℚ) :: s
  | _, s => s

/-- Structural recursion on the finite instruction list is the machine's
termination argument, independently of input and intermediate values. -/
def run : Program → ℚ → List ℚ → List ℚ
  | [], _, s => s
  | t :: p, eps, s => run p eps (tick t eps s)

@[simp] theorem run_append (p q : Program) (eps : ℚ) (s : List ℚ) :
    run (p ++ q) eps s = run q eps (run p eps s) := by
  induction p generalizing s with
  | nil => rfl
  | cons t p ih => simpa only [List.cons_append, run] using ih (tick t eps s)

/-- Natural-number program encoding with the standard executable list decoder. -/
def encodeProgram (p : Program) : ℕ := Encodable.encode p

def execute (programCode inputCode : ℕ) : Option ℕ := do
  let p ← Encodable.decode (α := Program) programCode
  return ⌈(run p (decodeRat inputCode) []).headD 0⌉₊

@[simp] theorem execute_encode (p : Program) (input : ℕ) :
    execute (encodeProgram p) input =
      some ⌈(run p (decodeRat input) []).headD 0⌉₊ := by
  simp [execute, encodeProgram]

/-- The uniform bound counts arithmetic instructions, not bit operations. -/
def runFuel : ℕ → Program → ℚ → List ℚ → Option (List ℚ)
  | _, [], _, s => some s
  | 0, _ :: _, _, _ => none
  | fuel + 1, t :: p, eps, s => runFuel fuel p eps (tick t eps s)

theorem runFuel_complete (p : Program) (eps : ℚ) (s : List ℚ) :
    runFuel p.length p eps s = some (run p eps s) := by
  induction p generalizing s with
  | nil => rfl
  | cons t p ih => simpa only [List.length_cons, runFuel, run] using ih (tick t eps s)

/-- Stack semantics robust under composition with other finite programs. -/
def Computes (p : Program) (f : ℚ → ℚ) : Prop :=
  ∀ eps s, run p eps s = f eps :: s

def input : Program := [instruction 0 0]
def constant (q : ℚ) : Program := [instruction 1 (encodeRat q)]
def multiply (p q : Program) : Program := p ++ q ++ [instruction 2 0]
def divide (p q : Program) : Program := p ++ q ++ [instruction 3 0]
def maximum (p q : Program) : Program := p ++ q ++ [instruction 4 0]
def ceiling (p : Program) : Program := p ++ [instruction 5 0]

@[simp] theorem input_computes : Computes input id := by
  intro eps s
  simp [input, instruction, run, tick]

@[simp] theorem constant_computes (q : ℚ) : Computes (constant q) (fun _ => q) := by
  intro eps s
  simp [constant, instruction, run, tick]

theorem multiply_computes {p q : Program} {f g : ℚ → ℚ}
    (hp : Computes p f) (hq : Computes q g) :
    Computes (multiply p q) (fun eps => f eps * g eps) := by
  intro eps s
  simp [multiply, run_append, hp eps, hq eps, instruction, run, tick]

theorem divide_computes {p q : Program} {f g : ℚ → ℚ}
    (hp : Computes p f) (hq : Computes q g) :
    Computes (divide p q) (fun eps => f eps / g eps) := by
  intro eps s
  simp [divide, run_append, hp eps, hq eps, instruction, run, tick]

theorem maximum_computes {p q : Program} {f g : ℚ → ℚ}
    (hp : Computes p f) (hq : Computes q g) :
    Computes (maximum p q) (fun eps => max (f eps) (g eps)) := by
  intro eps s
  simp [maximum, run_append, hp eps, hq eps, instruction, run, tick]

theorem ceiling_computes {p : Program} {f : ℚ → ℚ} (hp : Computes p f) :
    Computes (ceiling p) (fun eps => (⌈f eps⌉₊ : ℚ)) := by
  intro eps s
  simp [ceiling, run_append, hp eps, instruction, run, tick]

/-- The data field is finite syntax. Its proof certifies the original threshold
on all positive rational inputs, exactly the domain of the clock contract. -/
structure ThresholdRealizer {k : ℕ} (P : Clock k) where
  program : Program
  computes : ∀ eps : ℚ, 0 < eps → ∀ s : List ℚ,
    run program eps s = (P.threshold eps : ℚ) :: s

namespace ThresholdRealizer
variable {k : ℕ} {P : Clock k} (E : ThresholdRealizer P)
def code : ℕ := encodeProgram E.program

theorem terminates (input : ℕ) :
    ∃ s, runFuel E.program.length E.program (decodeRat input) [] = some s :=
  ⟨run E.program (decodeRat input) [], runFuel_complete _ _ _⟩

theorem terminates_correct (input : ℕ) (h : 0 < decodeRat input) :
    runFuel E.program.length E.program (decodeRat input) [] =
      some [(P.threshold (decodeRat input) : ℚ)] := by
  rw [runFuel_complete, E.computes _ h]

/-- Correct for every positive rational code, including noncanonical encodings. -/
theorem correct (input : ℕ) (h : 0 < decodeRat input) :
    execute E.code input = some (P.threshold (decodeRat input)) := by
  rw [code, execute_encode, E.computes _ h]
  simp

theorem positive_input (input : ℕ) (h : 0 < decodeRat input) :
    execute E.code input = some (P.threshold (decodeRat input)) := E.correct input h

theorem rational_input (eps : ℚ) (heps : 0 < eps) :
    execute E.code (encodeRat eps) = some (P.threshold eps) := by
  simpa using E.correct (encodeRat eps) (by simpa using heps)
end ThresholdRealizer

/-- Compilation of the coefficient domination rule: all coefficients are
finite rational literals, and epsilon is the sole runtime input. -/
def rowProgram {n : ℕ} (c g : Fin n → ℚ) (d : ℕ) : Program :=
  maximum (constant 1)
    (maximum (constant (⌈2 * FaithfulGrowth.rowCoeffMass c d /
      FaithfulGrowth.rowCoeff c d⌉₊ : ℚ))
      (ceiling (divide (constant (2 * FaithfulGrowth.rowCoeffMass g d))
        (multiply input (constant (FaithfulGrowth.rowCoeff c d))))))

theorem rowProgram_computes {n : ℕ} (c g : Fin n → ℚ) (d : ℕ) :
    Computes (rowProgram c g d)
      (fun eps => (FaithfulGrowth.rowDominationThreshold c g d eps : ℚ)) := by
  have h := maximum_computes (constant_computes 1)
    (maximum_computes (constant_computes
      (⌈2 * FaithfulGrowth.rowCoeffMass c d / FaithfulGrowth.rowCoeff c d⌉₊ : ℚ))
      (ceiling_computes (divide_computes
        (constant_computes (2 * FaithfulGrowth.rowCoeffMass g d))
        (multiply_computes input_computes (constant_computes (FaithfulGrowth.rowCoeff c d))))))
  simpa only [rowProgram, FaithfulGrowth.rowDominationThreshold, Nat.cast_max,
    Nat.cast_one, id_eq] using h

/-- Compile precisely `EffectiveThreshold.program`, with a finite parent
program. The parent code is inlined once; no oracle is introduced. -/
def compile {k : ℕ} (d : FaithfulEffectiveThreshold.Data k) (parent : Program) : Program :=
  maximum (constant d.outerOnset)
    (maximum (rowProgram d.resetLength d.resetGain k)
      (ceiling (divide
        (maximum parent (maximum (constant d.parentOnset)
          (rowProgram d.parentLength d.parentGain (k - 1))))
        (constant d.scale))))

theorem compile_computes {k : ℕ} (d : FaithfulEffectiveThreshold.Data k)
    {parent : Program} {f : ℚ → ℕ}
    (hp : Computes parent (fun eps => (f eps : ℚ))) :
    Computes (compile d parent)
      (fun eps => (FaithfulEffectiveThreshold.program d (f eps) eps : ℚ)) := by
  have h := maximum_computes (constant_computes (d.outerOnset : ℚ))
    (maximum_computes (rowProgram_computes d.resetLength d.resetGain k)
      (ceiling_computes (divide_computes
        (maximum_computes hp (maximum_computes (constant_computes (d.parentOnset : ℚ))
          (rowProgram_computes d.parentLength d.parentGain (k - 1))))
        (constant_computes (d.scale : ℚ)))))
  simpa only [compile, FaithfulEffectiveThreshold.program, Nat.cast_max] using h

theorem compile_run {k : ℕ} (d : FaithfulEffectiveThreshold.Data k)
    (parent : Program) (eps : ℚ) (v : ℕ)
    (hp : ∀ s, run parent eps s = (v : ℚ) :: s) (s : List ℚ) :
    run (compile d parent) eps s =
      (FaithfulEffectiveThreshold.program d v eps : ℚ) :: s := by
  simp [compile, maximum, ceiling, divide, run_append, instruction, run, tick,
    hp, rowProgram_computes d.resetLength d.resetGain k eps,
    rowProgram_computes d.parentLength d.parentGain (k - 1) eps,
    FaithfulEffectiveThreshold.program, Nat.cast_max, constant]

/-- The RPS threshold is realized by the one-instruction constant program. -/
def rps : ThresholdRealizer FaithfulSeed.rpsClock where
  program := constant 1
  computes := by
    intro eps _ s
    simpa only [FaithfulSeed.rpsClock] using constant_computes 1 eps s

/-- The essential seven-action seed also has a finite arithmetic realizer. -/
def seven : ThresholdRealizer FaithfulSevenSeed.sevenClock where
  program := maximum (constant 20) (ceiling (divide (constant 1) input))
  computes := by
    intro eps _ s
    have h := maximum_computes (constant_computes 20)
      (ceiling_computes (divide_computes (constant_computes 1) input_computes))
    simpa only [FaithfulSevenSeed.sevenClock, FaithfulSevenSuffix.threshold,
      Nat.cast_max, Nat.cast_ofNat, id_eq] using h eps s

/-- Specialization of the finite compiler to the actual lift data. -/
def lift {k : ℕ} {P : Clock k} (A : Admissible P) (E : ThresholdRealizer P) :
    ThresholdRealizer (FaithfulEffectiveLift.liftClock A) where
  program := compile
    (FaithfulEffectiveThreshold.fromClock P A.tau
      (FaithfulController.outerOnset A (FaithfulController.firstScale A)
        (FaithfulController.secondScale A (FaithfulController.firstScale A)))
      (FaithfulGain.AdmissibleGain.selectedGain A
        (FaithfulParameters.AdmissibleParameters.lam A) (FaithfulController.firstScale A))
      (FaithfulAdmissible.baseline P)) E.program
  computes := by
    intro eps heps s
    rw [compile_run _ _ _ _ (E.computes eps heps)]
    apply congrArg (fun x : ℚ => x :: s)
    exact congrArg (fun n : ℕ => (n : ℚ))
      (FaithfulEffectiveThreshold.Actual.threshold_eq A _ _ eps)

/-- Closure of the finite arithmetic fragment under the same lift.
For arbitrary partial-recursive parent programs, see `lift_every_partrec_parent`. -/
theorem actual_lift_preserves {k : ℕ} {P : Clock k} (A : Admissible P)
    (E : ThresholdRealizer P) (eps : ℚ) (heps : 0 < eps) :
    execute (lift A E).code (encodeRat eps) =
      some ((FaithfulLift.nextClock A).threshold eps) :=
  (lift A E).rational_input eps heps

/-- Uniform executable compilation along the RPS family, preserving the same
recursive bundle at every order. This is stronger than choosing a separate
program nonconstructively for each fixed order. -/
def rpsIterate : (n : ℕ) →
    ThresholdRealizer (FaithfulFamily.iterate FaithfulMain.step n).clock
  | 0 => rps
  | n + 1 => lift (FaithfulFamily.iterate FaithfulMain.step n).data (rpsIterate n)

/-- Uniform executable compilation along the smaller, seven-action family. -/
def sevenIterate : (n : ℕ) → ThresholdRealizer (FaithfulSevenFamily.iterate n).clock
  | 0 => seven
  | n + 1 => lift (FaithfulSevenFamily.iterate n).data (sevenIterate n)

def transportRealizer {a b : ℕ} (h : a = b) (B : FaithfulFamily.Bundle a)
    (E : ThresholdRealizer B.clock) : ThresholdRealizer (h ▸ B).clock := by
  cases h
  exact E

/-- The exact clock used by the unconditional main theorem. -/
def rpsFamily (k : ℕ) (hk : 2 ≤ k) : ThresholdRealizer (FaithfulMain.clock k hk) :=
  transportRealizer (show k - 2 + 2 = k by omega)
    (FaithfulFamily.iterate FaithfulMain.step (k - 2)) (rpsIterate (k - 2))

/-- The exact clock used by the unconditional smaller-family theorem. -/
def sevenFamily (k : ℕ) (hk : 3 ≤ k) : ThresholdRealizer (FaithfulSevenFamily.clock k hk) :=
  transportRealizer (show k - 3 + 3 = k by omega)
    (FaithfulSevenFamily.iterate (k - 3)) (sevenIterate (k - 3))

/-- Exact equality with the already delivered threshold implementation. -/
theorem rpsFamily_correct (k : ℕ) (hk : 2 ≤ k) (eps : ℚ) (heps : 0 < eps) :
    execute (rpsFamily k hk).code (encodeRat eps) =
      some (FaithfulEffectiveLift.familyThreshold k hk eps) :=
  (rpsFamily k hk).rational_input eps heps

theorem sevenFamily_correct (k : ℕ) (hk : 3 ≤ k) (eps : ℚ) (heps : 0 < eps) :
    execute (sevenFamily k hk).code (encodeRat eps) =
      some (FaithfulSevenFamily.threshold k hk eps) :=
  (sevenFamily k hk).rational_input eps heps

/-- One finite compiled program and a uniform instruction bound are fixed
before *all* positive epsilon inputs, with the original suffix inequality. -/
theorem clock_contract {k : ℕ} {P : Clock k} (E : ThresholdRealizer P) :
    ∃ (code fuel : ℕ), ∀ input : ℕ, 0 < decodeRat input →
      execute code input = some (P.threshold (decodeRat input)) ∧
      runFuel fuel E.program (decodeRat input) [] =
        some [(P.threshold (decodeRat input) : ℚ)] ∧
      ∀ q : ℕ, P.threshold (decodeRat input) ≤ q →
        ∀ r : ℕ, r ≤ (P.word q).length →
          height P.b (P.entry (q + 1)) -
            height P.b (wordScore P.A (P.entry q) ((P.word q).take r)) ≤
              decodeRat input * ((P.word q).length - r : ℕ) + P.Arem := by
  refine ⟨E.code, E.program.length, ?_⟩
  intro input hpos
  exact ⟨E.correct input hpos, E.terminates_correct input hpos, P.suffix (decodeRat input) hpos⟩

#print axioms actual_lift_preserves
#print axioms rpsFamily_correct
#print axioms sevenFamily_correct
#print axioms clock_contract

/-! ## Universal parent programs

The earlier VM is an efficient-to-describe arithmetic fragment, not a claim
that every computable threshold is expressible using only those instructions.
The following finite syntax includes a genuine universal partial-recursive
code leaf. It therefore places no arithmetic-language restriction on a parent
threshold. `Code.evaln` supplies an actual bounded interpreter, and completeness
connects termination of that interpreter to the partial semantics.
-/

/-- A finite first-order program tree. All leaves contain natural codes or
finite instruction lists. No constructor accepts a function or oracle. -/
inductive UniversalProgram where
  | machine : ℕ → UniversalProgram
  | arithmetic : Program → UniversalProgram
  | binary : ℕ → UniversalProgram → UniversalProgram → UniversalProgram
  | round : UniversalProgram → UniversalProgram

namespace UniversalProgram

/-- A computable serialization into the existing finite code-tree datatype.
These tags encode syntax; only `machine` leaves are run as universal codes. -/
def toCodeTree : UniversalProgram → Nat.Partrec.Code
  | .machine c => .pair .zero (Nat.Partrec.Code.ofNatCode c)
  | .arithmetic p => .pair .succ (Nat.Partrec.Code.ofNatCode (encodeProgram p))
  | .binary op p q =>
      .pair (.pair .left (Nat.Partrec.Code.ofNatCode op)) (.pair (toCodeTree p) (toCodeTree q))
  | .round p => .pair .right (toCodeTree p)

/-- Structural parser for that serialization, rejecting malformed trees. -/
def fromCodeTree : Nat.Partrec.Code → Option UniversalProgram
  | .pair .zero c => some (.machine c.encodeCode)
  | .pair .succ c => (Encodable.decode (α := Program) c.encodeCode).map .arithmetic
  | .pair (.pair .left c) (.pair p q) => do
      let p' ← fromCodeTree p
      let q' ← fromCodeTree q
      return .binary c.encodeCode p' q'
  | .pair .right p => (fromCodeTree p).map .round
  | _ => none

@[simp] theorem from_toCodeTree (p : UniversalProgram) :
    fromCodeTree (toCodeTree p) = some p := by
  induction p <;> simp [toCodeTree, fromCodeTree,
    ← Nat.Partrec.Code.encodeCode_eq, ← Nat.Partrec.Code.ofNatCode_eq, encodeProgram, *]

/-- The entire program, not merely its universal leaves, has a natural code. -/
def encode (p : UniversalProgram) : ℕ := Encodable.encode (toCodeTree p)
def decode (code : ℕ) : Option UniversalProgram :=
  fromCodeTree (Nat.Partrec.Code.ofNatCode code)

@[simp] theorem decode_encode (p : UniversalProgram) : decode (encode p) = some p := by
  simp [decode, encode, ← Nat.Partrec.Code.ofNatCode_eq]

/-- Binary opcodes are multiplication, division, and maximum. -/
def operation (op : ℕ) (x y : ℚ) : ℚ :=
  if op = 0 then x * y else if op = 1 then x / y else max x y

/-- Universal leaves receive precisely the signed-numerator/denominator code
of epsilon. Their evaluation may diverge, as a universal interpreter must. -/
def eval : UniversalProgram → ℚ → Part ℚ
  | .machine c, eps => ((Nat.Partrec.Code.ofNatCode c).eval (encodeRat eps)).map
      (fun n : ℕ => (n : ℚ))
  | .arithmetic p, eps => Part.some ((run p eps []).headD 0)
  | .binary op p q, eps => (eval p eps).bind fun x =>
      (eval q eps).map (operation op x)
  | .round p, eps => (eval p eps).map (fun x => (⌈x⌉₊ : ℚ))

/-- A computable bounded interpreter. Fuel bounds every universal leaf's
`Code.evaln` computation; the remaining tree and arithmetic blocks are finite.
This is not a bit-complexity bound and has no uniform bound over epsilon. -/
def evaln : UniversalProgram → ℕ → ℚ → Option ℚ
  | .machine c, fuel, eps => ((Nat.Partrec.Code.ofNatCode c).evaln fuel (encodeRat eps)).map
      (fun n : ℕ => (n : ℚ))
  | .arithmetic p, _, eps => some ((run p eps []).headD 0)
  | .binary op p q, fuel, eps => (evaln p fuel eps).bind fun x =>
      (evaln q fuel eps).map (operation op x)
  | .round p, fuel, eps => (evaln p fuel eps).map (fun x => (⌈x⌉₊ : ℚ))

theorem evaln_mono (p : UniversalProgram) {a b : ℕ} (hab : a ≤ b)
    {eps x : ℚ} (h : evaln p a eps = some x) : evaln p b eps = some x := by
  induction p generalizing x with
  | machine c =>
    simp only [evaln, Option.map_eq_some_iff] at h ⊢
    obtain ⟨n, hn, rfl⟩ := h
    exact ⟨n, Nat.Partrec.Code.evaln_mono hab hn, rfl⟩
  | arithmetic p => exact h
  | binary op p q ihp ihq =>
    simp only [evaln, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨u, hu, v, hv, rfl⟩ := h
    exact ⟨u, ihp hu, v, ihq hv, rfl⟩
  | round p ih =>
    simp only [evaln, Option.map_eq_some_iff] at h ⊢
    obtain ⟨u, hu, rfl⟩ := h
    exact ⟨u, ih hu, rfl⟩

theorem evaln_sound (p : UniversalProgram) {fuel : ℕ} {eps x : ℚ}
    (h : evaln p fuel eps = some x) : x ∈ eval p eps := by
  induction p generalizing x with
  | machine c =>
    simp only [evaln, Option.map_eq_some_iff] at h
    simp only [eval, Part.mem_map_iff]
    obtain ⟨n, hn, rfl⟩ := h
    exact ⟨n, Nat.Partrec.Code.evaln_sound hn, rfl⟩
  | arithmetic p =>
    simpa only [evaln, Option.some.injEq, eq_comm, eval, Part.mem_some_iff] using h
  | binary op p q ihp ihq =>
    simp only [evaln, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    simp only [eval, Part.mem_bind_iff, Part.mem_map_iff]
    obtain ⟨u, hu, v, hv, rfl⟩ := h
    exact ⟨u, ihp hu, v, ihq hv, rfl⟩
  | round p ih =>
    simp only [evaln, Option.map_eq_some_iff] at h
    simp only [eval, Part.mem_map_iff]
    obtain ⟨u, hu, rfl⟩ := h
    exact ⟨u, ih hu, rfl⟩

theorem evaln_complete (p : UniversalProgram) {eps x : ℚ} :
    x ∈ eval p eps ↔ ∃ fuel, evaln p fuel eps = some x := by
  refine ⟨?_, fun ⟨fuel, h⟩ => evaln_sound p h⟩
  intro h
  induction p generalizing x with
  | machine c =>
    simp only [eval, Part.mem_map_iff] at h
    obtain ⟨n, hn, rfl⟩ := h
    obtain ⟨fuel, hf⟩ := Nat.Partrec.Code.evaln_complete.mp hn
    change Nat.Partrec.Code.evaln fuel (Nat.Partrec.Code.ofNatCode c) (encodeRat eps) = some n at hf
    exact ⟨fuel, by simp only [evaln, hf, Option.map_some]⟩
  | arithmetic p =>
    simp only [eval, Part.mem_some_iff] at h
    exact ⟨0, by simp only [evaln, h]⟩
  | binary op p q ihp ihq =>
    simp only [eval, Part.mem_bind_iff, Part.mem_map_iff] at h
    obtain ⟨u, hu, v, hv, rfl⟩ := h
    obtain ⟨a, ha⟩ := ihp hu
    obtain ⟨b, hb⟩ := ihq hv
    refine ⟨max a b, ?_⟩
    simp only [evaln, evaln_mono p (le_max_left a b) ha,
      evaln_mono q (le_max_right a b) hb, Option.bind_some, Option.map_some]
  | round p ih =>
    simp only [eval, Part.mem_map_iff] at h
    obtain ⟨u, hu, rfl⟩ := h
    obtain ⟨fuel, hf⟩ := ih hu
    exact ⟨fuel, by simp only [evaln, hf, Option.map_some]⟩

@[simp] theorem machine_eval (c : Nat.Partrec.Code) (eps : ℚ) :
    eval (.machine (Encodable.encode c)) eps =
      (c.eval (encodeRat eps)).map (fun n : ℕ => (n : ℚ)) := by
  simp [eval, ← Nat.Partrec.Code.ofNatCode_eq]

/-- Every partial-recursive natural-input program is represented by a single
universal leaf. This explicitly removes the arithmetic-fragment restriction. -/
theorem represents_every_partrec {f : ℕ → Part ℕ} (hf : Nat.Partrec f) :
    ∃ p : UniversalProgram, ∀ eps : ℚ,
      eval p eps = (f (encodeRat eps)).map (fun n : ℕ => (n : ℚ)) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  exact ⟨.machine (Encodable.encode c), fun eps => by rw [machine_eval, hc]⟩

/-- The same inherited coefficient formula, now with a universal parent
expression. The universal subprogram is an actual syntax subtree. -/
def compile {k : ℕ} (d : FaithfulEffectiveThreshold.Data k)
    (parent : UniversalProgram) : UniversalProgram :=
  .binary 2 (.arithmetic (constant d.outerOnset))
    (.binary 2 (.arithmetic (rowProgram d.resetLength d.resetGain k))
      (.round (.binary 1
        (.binary 2 parent (.binary 2 (.arithmetic (constant d.parentOnset))
          (.arithmetic (rowProgram d.parentLength d.parentGain (k - 1)))))
        (.arithmetic (constant d.scale)))))

theorem compile_eval {k : ℕ} (d : FaithfulEffectiveThreshold.Data k)
    (parent : UniversalProgram) (eps : ℚ) (v : ℕ)
    (hp : eval parent eps = Part.some (v : ℚ)) :
    eval (compile d parent) eps =
      Part.some (FaithfulEffectiveThreshold.program d v eps : ℚ) := by
  simp [compile, eval, hp, operation, constant_computes _ eps [],
    rowProgram_computes d.resetLength d.resetGain k eps [],
    rowProgram_computes d.parentLength d.parentGain (k - 1) eps [],
    FaithfulEffectiveThreshold.program, Nat.cast_max]

/-- Observable natural output of the bounded interpreter. -/
def execute (p : UniversalProgram) (fuel inputCode : ℕ) : Option ℕ :=
  (evaln p fuel (decodeRat inputCode)).map Nat.ceil

/-- Parse and execute a natural-number program code. -/
def executeCode (code fuel inputCode : ℕ) : Option ℕ :=
  (decode code).bind (fun p => p.execute fuel inputCode)

@[simp] theorem executeCode_encode (p : UniversalProgram) (fuel input : ℕ) :
    executeCode (encode p) fuel input = p.execute fuel input := by
  simp [executeCode]

/-- The actual unbounded algorithm enumerates fuel, returning the first
successful bounded run. No halting bound is supplied by an oracle or caller. -/
def runCode (code input : ℕ) : Part ℕ :=
  Nat.rfindOpt (fun fuel => executeCode code fuel input)

end UniversalProgram

/-- Effective threshold in a language containing every partial-recursive
parent program, with correctness and termination required only for eps > 0. -/
structure UniversalThresholdRealizer {k : ℕ} (P : Clock k) where
  program : UniversalProgram
  computes : ∀ eps : ℚ, 0 < eps →
    program.eval eps = Part.some (P.threshold eps : ℚ)

namespace UniversalThresholdRealizer
variable {k : ℕ} {P : Clock k}

/-- The explicit natural serialization of a certified universal program. -/
def code (E : UniversalThresholdRealizer P) : ℕ := E.program.encode

/-- Embed the earlier finite VM without changing its instructions or output. -/
def ofArithmetic (E : ThresholdRealizer P) : UniversalThresholdRealizer P where
  program := .arithmetic E.program
  computes := by
    intro eps heps
    simp [UniversalProgram.eval, E.computes eps heps []]

/-- Accept an arbitrary universal parent code. This is the paper's computable
threshold hypothesis on positive encoded rational inputs, with no restriction
to arithmetic formulas and no termination assumption on other inputs. -/
def ofCode (c : Nat.Partrec.Code)
    (hc : ∀ eps : ℚ, 0 < eps → c.eval (encodeRat eps) = Part.some (P.threshold eps)) :
    UniversalThresholdRealizer P where
  program := .machine (Encodable.encode c)
  computes := by
    intro eps heps
    simp [UniversalProgram.machine_eval, hc eps heps]

/-- Every partial-recursive realizer on rational codes is admitted. -/
theorem accepts_every_partrec (f : ℕ → Part ℕ) (hf : Nat.Partrec f)
    (hc : ∀ eps : ℚ, 0 < eps → f (encodeRat eps) = Part.some (P.threshold eps)) :
    Nonempty (UniversalThresholdRealizer P) := by
  obtain ⟨c, hcode⟩ := Nat.Partrec.Code.exists_code.mp hf
  exact ⟨ofCode c (fun eps heps => by rw [hcode]; exact hc eps heps)⟩

/-- Positive-input termination yields an actual bounded interpreter run.
Fuel is allowed to depend on epsilon, as it must for arbitrary algorithms. -/
theorem terminates_correct (E : UniversalThresholdRealizer P) (input : ℕ)
    (h : 0 < decodeRat input) :
    ∃ fuel, E.program.execute fuel input = some (P.threshold (decodeRat input)) := by
  have hm : (P.threshold (decodeRat input) : ℚ) ∈ E.program.eval (decodeRat input) := by
    rw [E.computes _ h]
    exact Part.mem_some _
  obtain ⟨fuel, hf⟩ := E.program.evaln_complete.mp hm
  exact ⟨fuel, by simp [UniversalProgram.execute, hf]⟩

/-- Termination and exact output after decoding the *whole* natural program. -/
theorem encoded_terminates_correct (E : UniversalThresholdRealizer P) (input : ℕ)
    (h : 0 < decodeRat input) :
    ∃ fuel, UniversalProgram.executeCode E.code fuel input =
      some (P.threshold (decodeRat input)) := by
  simpa only [code, UniversalProgram.executeCode_encode] using E.terminates_correct input h

/-- Every terminating bounded run has the certified output; a small fuel
value can only time out, never return an incorrect threshold. -/
theorem result_unique (E : UniversalThresholdRealizer P) (input fuel n : ℕ)
    (h : 0 < decodeRat input) (hr : E.program.execute fuel input = some n) :
    n = P.threshold (decodeRat input) := by
  obtain ⟨x, hx, hn⟩ := Option.map_eq_some_iff.mp hr
  have hm := E.program.evaln_sound hx
  rw [E.computes _ h, Part.mem_some_iff] at hm
  simpa [hm] using hn.symm

/-- The fuel-search algorithm terminates with the original threshold on every
positive input; the existential fuel certificate is not an algorithmic oracle. -/
theorem runCode_correct (E : UniversalThresholdRealizer P) (input : ℕ)
    (h : 0 < decodeRat input) :
    UniversalProgram.runCode E.code input = Part.some (P.threshold (decodeRat input)) := by
  obtain ⟨fuel, hf⟩ := E.encoded_terminates_correct input h
  have hd : (UniversalProgram.runCode E.code input).Dom :=
    Nat.rfindOpt_dom.mpr ⟨fuel, P.threshold (decodeRat input), hf⟩
  have hm := Part.get_mem hd
  obtain ⟨fuel', hf'⟩ := Nat.rfindOpt_spec hm
  have he := E.result_unique input fuel' _ h (by
    simpa only [code, UniversalProgram.executeCode_encode] using hf')
  exact Part.eq_some_iff.mpr (he ▸ hm)

end UniversalThresholdRealizer

/-- Generic computational lift accepting a universally encoded parent.
The selected scales, coefficients, and resulting threshold remain unchanged. -/
def universalLift {k : ℕ} {P : Clock k} (A : Admissible P)
    (E : UniversalThresholdRealizer P) :
    UniversalThresholdRealizer (FaithfulEffectiveLift.liftClock A) where
  program := UniversalProgram.compile
    (FaithfulEffectiveThreshold.fromClock P A.tau
      (FaithfulController.outerOnset A (FaithfulController.firstScale A)
        (FaithfulController.secondScale A (FaithfulController.firstScale A)))
      (FaithfulGain.AdmissibleGain.selectedGain A
        (FaithfulParameters.AdmissibleParameters.lam A) (FaithfulController.firstScale A))
      (FaithfulAdmissible.baseline P)) E.program
  computes := by
    intro eps heps
    rw [UniversalProgram.compile_eval _ _ _ _ (E.computes eps heps)]
    apply congrArg Part.some
    exact congrArg (fun n : ℕ => (n : ℚ))
      (FaithfulEffectiveThreshold.Actual.threshold_eq A _ _ eps)

/-- An arbitrary universally computable positive-input parent threshold
remains computable after the actual lift, in the same construction. -/
theorem universal_actual_lift_preserves {k : ℕ} {P : Clock k} (A : Admissible P)
    (E : UniversalThresholdRealizer P) (input : ℕ) (h : 0 < decodeRat input) :
    ∃ fuel, (universalLift A E).program.execute fuel input =
      some ((FaithfulLift.nextClock A).threshold (decodeRat input)) :=
  (universalLift A E).terminates_correct input h

/-- The generic-lift theorem specializes directly to *any* partial-recursive
realizer of the parent's threshold; no arithmetic-representability premise. -/
theorem lift_every_partrec_parent {k : ℕ} {P : Clock k} (A : Admissible P)
    (f : ℕ → Part ℕ) (hf : Nat.Partrec f)
    (hc : ∀ eps : ℚ, 0 < eps → f (encodeRat eps) = Part.some (P.threshold eps)) :
    Nonempty (UniversalThresholdRealizer (FaithfulLift.nextClock A)) := by
  obtain ⟨E⟩ := UniversalThresholdRealizer.accepts_every_partrec f hf hc
  exact ⟨universalLift A E⟩

/-- Paper-shaped uniform program selection: a single finite program is fixed
before all positive epsilon inputs. This accepts any partial-recursive parent
threshold and computes the original actual-lift threshold on every such input. -/
theorem lift_every_partrec_parent_contract {k : ℕ} {P : Clock k} (A : Admissible P)
    (f : ℕ → Part ℕ) (hf : Nat.Partrec f)
    (hc : ∀ eps : ℚ, 0 < eps → f (encodeRat eps) = Part.some (P.threshold eps)) :
    ∃ code : ℕ, ∀ input : ℕ, 0 < decodeRat input →
      ∃ fuel, UniversalProgram.executeCode code fuel input =
        some ((FaithfulLift.nextClock A).threshold (decodeRat input)) := by
  obtain ⟨E⟩ := lift_every_partrec_parent A f hf hc
  exact ⟨E.code, fun input h => E.encoded_terminates_correct input h⟩

/-- A complete encoded program, including its own fuel search, for the actual
lift of any partial-recursively realized positive-input parent threshold. -/
theorem lift_every_partrec_parent_program {k : ℕ} {P : Clock k} (A : Admissible P)
    (f : ℕ → Part ℕ) (hf : Nat.Partrec f)
    (hc : ∀ eps : ℚ, 0 < eps → f (encodeRat eps) = Part.some (P.threshold eps)) :
    ∃ code : ℕ, ∀ input : ℕ, 0 < decodeRat input →
      UniversalProgram.runCode code input =
        Part.some ((FaithfulLift.nextClock A).threshold (decodeRat input)) := by
  obtain ⟨E⟩ := lift_every_partrec_parent A f hf hc
  exact ⟨E.code, fun input h => E.runCode_correct input h⟩

/-- The exact existing RPS family, embedded without changing its program. -/
def universalRpsFamily (k : ℕ) (hk : 2 ≤ k) :
    UniversalThresholdRealizer (FaithfulMain.clock k hk) :=
  UniversalThresholdRealizer.ofArithmetic (rpsFamily k hk)

/-- The exact existing smaller family, embedded without changing its program. -/
def universalSevenFamily (k : ℕ) (hk : 3 ≤ k) :
    UniversalThresholdRealizer (FaithfulSevenFamily.clock k hk) :=
  UniversalThresholdRealizer.ofArithmetic (sevenFamily k hk)

theorem universal_rpsFamily_correct (k : ℕ) (hk : 2 ≤ k) (eps : ℚ) (heps : 0 < eps) :
    ∃ fuel, (universalRpsFamily k hk).program.execute fuel (encodeRat eps) =
      some (FaithfulEffectiveLift.familyThreshold k hk eps) := by
  simpa using (universalRpsFamily k hk).terminates_correct (encodeRat eps) (by simpa using heps)

theorem universal_sevenFamily_correct (k : ℕ) (hk : 3 ≤ k) (eps : ℚ) (heps : 0 < eps) :
    ∃ fuel, (universalSevenFamily k hk).program.execute fuel (encodeRat eps) =
      some (FaithfulSevenFamily.threshold k hk eps) := by
  simpa using (universalSevenFamily k hk).terminates_correct (encodeRat eps) (by simpa using heps)

/-- The program is fixed before every positive input. Each such input has a
finite terminating computation and certifies all suffix prefixes. -/
theorem universal_clock_contract {k : ℕ} {P : Clock k} (E : UniversalThresholdRealizer P) :
    ∃ code : ℕ, ∀ input : ℕ, 0 < decodeRat input →
      (∃ fuel, UniversalProgram.executeCode code fuel input = some (P.threshold (decodeRat input))) ∧
      ∀ q : ℕ, P.threshold (decodeRat input) ≤ q →
        ∀ r : ℕ, r ≤ (P.word q).length →
          height P.b (P.entry (q + 1)) -
            height P.b (wordScore P.A (P.entry q) ((P.word q).take r)) ≤
              decodeRat input * ((P.word q).length - r : ℕ) + P.Arem := by
  refine ⟨E.code, ?_⟩
  intro input hpos
  exact ⟨E.encoded_terminates_correct input hpos, P.suffix (decodeRat input) hpos⟩

/-- Program selection before every positive epsilon, with automatic fuel
search and no supplied bound. Both closed families inherit this directly. -/
theorem universal_clock_program {k : ℕ} {P : Clock k} (E : UniversalThresholdRealizer P) :
    ∃ code : ℕ, ∀ input : ℕ, 0 < decodeRat input →
      UniversalProgram.runCode code input = Part.some (P.threshold (decodeRat input)) :=
  ⟨E.code, fun input h => E.runCode_correct input h⟩

#print axioms UniversalThresholdRealizer.runCode_correct
#print axioms lift_every_partrec_parent_program
#print axioms UniversalProgram.evaln_complete
#print axioms lift_every_partrec_parent
#print axioms universal_rpsFamily_correct
#print axioms universal_sevenFamily_correct
#print axioms universal_clock_contract
end Karlin.FaithfulEffectiveContract
