import Karlin.FaithfulProspectiveScale

/-!
# Executable exact-rational scale extraction

Coefficient lists are stored in ascending degree. Every runtime operation below
is finite list recursion or a finite rational sum. The noncomputable polynomial
interpretation is used only in erased correctness proofs.
-/
namespace Karlin.FaithfulScaleEffective
open scoped BigOperators Matrix
open Polynomial

abbrev Poly := List ℚ

/-- Erased mathematical interpretation of the executable coefficient list. -/
noncomputable def interpret : Poly → ℚ[X]
  | [] => 0
  | a :: p => C a + X * interpret p

def coeff : Poly → ℕ → ℚ
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: p, n + 1 => coeff p n

def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def scale (a : ℚ) (p : Poly) : Poly := p.map (a * ·)
def sub (p q : Poly) : Poly := add p (scale (-1) q)
def mul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)
def monomial : ℕ → ℚ → Poly
  | 0, a => [a]
  | n + 1, a => 0 :: monomial n a

def sumFin : (n : ℕ) → (Fin n → Poly) → Poly
  | 0, _ => []
  | n + 1, f => add (f 0) (sumFin n (fun i => f i.succ))

def eval (p : Poly) (t : ℚ) : ℚ := p.foldr (fun a b => a + t * b) 0

@[simp] theorem interpret_nil : interpret [] = 0 := rfl
@[simp] theorem interpret_cons (a : ℚ) (p : Poly) :
    interpret (a :: p) = C a + X * interpret p := rfl

@[simp] theorem interpret_coeff (p : Poly) (n : ℕ) :
    (interpret p).coeff n = coeff p n := by
  induction p generalizing n with
  | nil => simp [interpret, coeff]
  | cons a p ih =>
    cases n with
    | zero => simp [interpret, coeff]
    | succ n => simp [interpret, coeff, ih, Polynomial.coeff_X_mul]

@[simp] theorem interpret_add (p q : Poly) : interpret (add p q) = interpret p + interpret q := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp [add, ih, map_add]; ring

@[simp] theorem interpret_scale (a : ℚ) (p : Poly) :
    interpret (scale a p) = C a * interpret p := by
  induction p with
  | nil => simp [scale]
  | cons b p ih =>
    change C (a * b) + X * interpret (scale a p) = _
    rw [ih, map_mul, interpret_cons]
    ring

@[simp] theorem interpret_sub (p q : Poly) : interpret (sub p q) = interpret p - interpret q := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem interpret_mul (p q : Poly) : interpret (mul p q) = interpret p * interpret q := by
  induction p with
  | nil => simp [mul]
  | cons a p ih => simp [mul, ih]; ring

@[simp] theorem interpret_monomial (n : ℕ) (a : ℚ) :
    interpret (monomial n a) = C a * X ^ n := by
  induction n with
  | zero => simp [monomial]
  | succ n ih => simp [monomial, ih, pow_succ]; ring

@[simp] theorem interpret_sumFin (n : ℕ) (f : Fin n → Poly) :
    interpret (sumFin n f) = ∑ i, interpret (f i) := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih => simp only [sumFin, interpret_add, ih, Fin.sum_univ_succ]

@[simp] theorem eval_spec (p : Poly) (t : ℚ) : eval p t = (interpret p).eval t := by
  induction p with
  | nil => simp [eval]
  | cons a p ih => simpa [eval] using congrArg (fun z : ℚ => a + t * z) ih

theorem coeff_drop (p : Poly) (d n : ℕ) : coeff (p.drop d) n = coeff p (n + d) := by
  induction d generalizing p with
  | zero => simp
  | succ d ih =>
    cases p with
    | nil => simp [coeff]
    | cons a p =>
      change coeff (p.drop d) n = coeff p (n + d)
      exact ih p

theorem coeff_zero_of_length_le (p : Poly) (n : ℕ) (hn : p.length ≤ n) : coeff p n = 0 := by
  induction p generalizing n with
  | nil => rfl
  | cons a p ih =>
    cases n with
    | zero => simp at hn
    | succ n => exact ih n (by simpa using hn)

/-- Division by a known monomial factor is literal list dropping. -/
theorem interpret_drop (p : Poly) (d : ℕ) (hd : X ^ d ∣ interpret p) :
    interpret (p.drop d) = interpret p /ₘ X ^ d := by
  obtain ⟨q, hq⟩ := hd
  have he : interpret (p.drop d) = q := by
    ext n
    rw [interpret_coeff, coeff_drop, ← interpret_coeff, hq]
    exact Polynomial.coeff_X_pow_mul q d n
  rw [he, hq]
  exact (Polynomial.mul_divByMonic_cancel_left q (Polynomial.monic_X.pow d)).symm


/-- Executable symbolic transfer tables, with the same coefficients as v15. -/
def endpoint (k u : ℕ) (a : Fin k) (j : Fin (k + 1)) : Poly :=
  monomial j.val (S_mat (k + 1) ⟨a.val, by omega⟩ j * (u : ℚ) ^ j.val)
def bundle (k : ℕ) (a : Fin k) (j : Fin (k + 1)) : Poly :=
  monomial j.val (S_mat (k + 1) ⟨a.val + 1, by omega⟩ j * ((2 : ℚ) ^ j.val - 1))
def transfer (k : ℕ) (a : Fin k) (j : Fin (k + 1)) : Poly :=
  sub (sumFin (k + 1) (fun r => scale (expN0 (k + 1) 1 r j) (endpoint k 1 a r)))
    (endpoint k 2 a j)
def constant (k : ℕ) (c : ℚ) (j : Fin (k + 1)) : Poly :=
  if j.val = 0 then [c] else []
def psi (k : ℕ) (chi : Fin k → ℚ) (c : ℚ) (j : Fin (k + 1)) : Poly :=
  sub (scale (-1) (sumFin k (fun a => scale (chi a)
    (sub (endpoint k 2 a j) (endpoint k 1 a j))))) (constant k c j)
def frow (k : ℕ) (chi : Fin k → ℚ) (c : ℚ) (j : Fin (k + 1)) : Poly :=
  sub (constant k c j) (sumFin k (fun a => scale (chi a) (transfer k a j)))
def countrow (k : ℕ) (lengthRow : Fin k → ℚ) (j : Fin (k + 1)) : Poly :=
  sumFin k (fun a => scale (lengthRow a) (bundle k a j))
def interior (k : ℕ) (M : Matrix (Fin k) (Fin k) ℚ)
    (lengthRow chi : Fin k → ℚ) (c : ℚ) (i j : Fin (k + 1)) : Poly :=
  add (sumFin k (fun a => sumFin k (fun b =>
    mul (scale (M a b) (transfer k a i)) (bundle k b j))))
    (mul (frow k chi c i) (countrow k lengthRow j))

@[simp] theorem endpoint_spec (k u : ℕ) (a : Fin k) (j : Fin (k + 1)) :
    interpret (endpoint k u a j) = FaithfulScale.endpointHat k u a j := by
  simp [endpoint, FaithfulScale.endpointHat]
@[simp] theorem bundle_spec (k : ℕ) (a : Fin k) (j : Fin (k + 1)) :
    interpret (bundle k a j) = FaithfulScale.bundleHat k a j := by
  simp [bundle, FaithfulScale.bundleHat]
@[simp] theorem transfer_spec (k : ℕ) (a : Fin k) (j : Fin (k + 1)) :
    interpret (transfer k a j) = FaithfulScale.LHat k a j := by
  simp [transfer, FaithfulScale.LHat, mul_comm]
@[simp] theorem constant_spec (k : ℕ) (c : ℚ) (j : Fin (k + 1)) :
    interpret (constant k c j) = FaithfulScale.constantRow k c j := by
  by_cases h : j.val = 0 <;> simp [constant, FaithfulScale.constantRow, h]
@[simp] theorem psi_spec (k : ℕ) (chi : Fin k → ℚ) (c : ℚ) (j : Fin (k + 1)) :
    interpret (psi k chi c j) = FaithfulScale.referencePsi k chi c j := by
  simp [psi, FaithfulScale.referencePsi]
@[simp] theorem frow_spec (k : ℕ) (chi : Fin k → ℚ) (c : ℚ) (j : Fin (k + 1)) :
    interpret (frow k chi c j) = FaithfulScale.referenceFRow k chi c j := by
  simp [frow, FaithfulScale.referenceFRow]
@[simp] theorem countrow_spec (k : ℕ) (lengthRow : Fin k → ℚ) (j : Fin (k + 1)) :
    interpret (countrow k lengthRow j) = FaithfulScale.referenceCountRow k lengthRow j := by
  simp [countrow, FaithfulScale.referenceCountRow]
@[simp] theorem interior_spec (k : ℕ) (M : Matrix (Fin k) (Fin k) ℚ)
    (lengthRow chi : Fin k → ℚ) (c : ℚ) (i j : Fin (k + 1)) :
    interpret (interior k M lengthRow chi c i j) =
      FaithfulScale.referenceInterior k M lengthRow chi c i j := by
  simp [interior, FaithfulScale.referenceInterior, mul_comm]

def inner (k h : ℕ) (F : Matrix (Fin (k + 1)) (Fin (k + 1)) Poly) : Poly :=
  sumFin (k + 1) (fun a => sumFin (k + 1) (fun b => scale (Z_DP (k + 1) h a b) (F a b)))
def tail (k : ℕ) (psi ell : Fin (k + 1) → Poly) (i : ℕ) : Poly :=
  sumFin (k + 1) (fun a => if a.val > i then
    sumFin (k + 1) (fun b => if b.val < k then
      scale (Z_DP (k + 1) (i + k - 1) a b) (mul (ell a) (psi b)) else []) else [])
def numerator (k : ℕ) (F : Matrix (Fin (k + 1)) (Fin (k + 1)) Poly)
    (psi ell : Fin (k + 1) → Poly) (i : ℕ) : Poly :=
  sub (inner k (i + k - 1) F) (tail k psi ell i)
def pivot (k : ℕ) (F : Matrix (Fin (k + 1)) (Fin (k + 1)) Poly)
    (psi ell : Fin (k + 1) → Poly) (beta : ℚ) (i : ℕ) : Poly :=
  scale (((-1 : ℚ) ^ i * beta)⁻¹) ((numerator k F psi ell i).drop (k - 1))
def helper (k : ℕ) (F : Matrix (Fin (k + 1)) (Fin (k + 1)) Poly)
    (psi : Fin (k + 1) → Poly) (beta : ℚ) : ℕ → (Fin (k + 1) → Poly)
  | 0 => fun _ => []
  | s + 1 =>
    let prev := helper k F psi beta s
    let i := k - 1 - s
    if 1 < i ∧ i < k ∧ (i + k - 1) % 2 = 0 then
      fun x => if x.val = i then pivot k F psi prev beta i else prev x
    else prev

@[simp] theorem numerator_spec (k i : ℕ)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) Poly) (psi ell : Fin (k + 1) → Poly) :
    interpret (numerator k F psi ell i) =
      FaithfulScale.polynomialNumerator k (fun a b => interpret (F a b))
        (fun b => interpret (psi b)) (fun a => interpret (ell a)) i := by
  simp [numerator, inner, tail, FaithfulScale.polynomialNumerator,
    FaithfulScale.polynomialInner, FaithfulScale.polynomialTail, Finset.sum_filter, mul_assoc, apply_ite]

theorem pivot_spec (k i : ℕ) (F : Matrix (Fin (k + 1)) (Fin (k + 1)) Poly)
    (psi ell : Fin (k + 1) → Poly) (beta : ℚ)
    (hN : X ^ (k - 1) ∣ FaithfulScale.polynomialNumerator k (fun a b => interpret (F a b))
      (fun b => interpret (psi b)) (fun a => interpret (ell a)) i) :
    interpret (pivot k F psi ell beta i) =
      FaithfulScale.polynomialPivot k (fun a b => interpret (F a b))
        (fun b => interpret (psi b)) (fun a => interpret (ell a)) beta i := by
  rw [pivot, interpret_scale, interpret_drop _ _ (by simpa using hN), numerator_spec]
  rfl

theorem helper_spec (k : ℕ) (F : Matrix (Fin (k + 1)) (Fin (k + 1)) Poly)
    (psi : Fin (k + 1) → Poly) (beta : ℚ) (hbeta : beta ≠ 0)
    (hF : ∀ a b, 0 < a.val → 0 < b.val → X ^ (a.val + b.val) ∣ interpret (F a b))
    (hpsi : ∀ b, X ^ b.val ∣ interpret (psi b)) :
    ∀ s, (fun a => interpret (helper k F psi beta s a)) =
      FaithfulScale.polynomialHelper k (fun a b => interpret (F a b))
        (fun b => interpret (psi b)) beta s := by
  intro s
  induction s with
  | zero => rfl
  | succ s ih =>
    by_cases hp : 1 < k - 1 - s ∧ k - 1 - s < k ∧ (k - 1 - s + k - 1) % 2 = 0
    · simp only [helper, FaithfulScale.polynomialHelper, if_pos hp]
      funext a
      by_cases ha : a.val = k - 1 - s
      · rw [if_pos ha, if_pos ha, pivot_spec]
        · rw [ih]
        · rw [ih]
          apply (pow_dvd_pow X (by omega : k - 1 ≤ k - 1 - s + (k - 1))).trans
          exact FaithfulScale.polynomialNumerator_divisible hp.1 hp.2.1 _ _ _ hF hpsi
            (FaithfulScale.polynomialHelper_divisible k _ _ beta hbeta hF hpsi s)
      · rw [if_neg ha, if_neg ha]
        exact congrFun ih a
    · simp only [helper, FaithfulScale.polynomialHelper, if_neg hp]
      exact ih


/-- Denominators of all stored coefficients, including harmless zero padding. -/
def denominator (p : Poly) : ℕ :=
  (Finset.range p.length).lcm (fun n => (coeff p n).den)

theorem denominator_spec (p : Poly) :
    denominator p = (interpret p).support.lcm (fun n => ((interpret p).coeff n).den) := by
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro n _
    by_cases hc : coeff p n = 0
    · simp [hc]
    · have hm : n ∈ (interpret p).support := Polynomial.mem_support_iff.mpr (by simpa using hc)
      simpa using (Finset.dvd_lcm (f := fun n => ((interpret p).coeff n).den) hm)
  · apply Finset.lcm_dvd
    intro n hn
    have hlt : n < p.length := by
      by_contra h
      have hz := coeff_zero_of_length_le p n (by omega)
      exact Polynomial.mem_support_iff.mp hn (by simpa using hz)
    exact (show ((interpret p).coeff n).den ∣ denominator p from by
      simpa [denominator] using
        (Finset.dvd_lcm (f := fun n => (coeff p n).den) (Finset.mem_range.mpr hlt)))

def polynomials (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ) :
    Fin (k + 1) → Poly :=
  helper k (interior k M lengthRow chi c) (psi k chi c)
    (-chi ⟨k - 1, by omega⟩ * ((2 : ℚ) ^ (k - 1) - 1)) (k - 1)

theorem polynomials_spec (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ)
    (hchi : chi ⟨k - 1, by omega⟩ ≠ 0) :
    (fun j => interpret (polynomials k hk M lengthRow chi c j)) =
      FaithfulScale.referenceSolver k hk M lengthRow chi c := by
  have h := helper_spec k (interior k M lengthRow chi c) (psi k chi c) _
    (FaithfulScale.referencePivot_ne_zero k hk chi hchi)
    (fun a b _ _ => by simpa using FaithfulScale.referenceInterior_divisible k M lengthRow chi c a b)
    (fun b => by simpa using FaithfulScale.referencePsi_divisible k chi c b) (k - 1)
  simpa only [polynomials, interior_spec, psi_spec, FaithfulScale.referenceSolver,
    FaithfulScale.polynomialSolver] using h

def computedDenominator (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ) : ℕ :=
  Finset.univ.lcm (fun j => denominator (polynomials k hk M lengthRow chi c j))

def computedScale (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ) : ℕ :=
  computedDenominator k hk M lengthRow chi c * k.factorial

def computedCorrection (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ) :
    Fin (k + 1) → ℤ :=
  fun j => (Matrix.vecMul
    (fun i => eval (polynomials k hk M lengthRow chi c i) (computedScale k hk M lengthRow chi c : ℚ))
      (S_inv_mat (k + 1)) j).num

/-- The actual executable output. There is no search or classical choice. -/
def compute (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ) :
    ℕ × (Fin (k + 1) → ℤ) :=
  (computedScale k hk M lengthRow chi c, computedCorrection k hk M lengthRow chi c)

/-- The nested LCM is precisely the support-based LCM prescribed in v15. -/
theorem computedDenominator_spec (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ)
    (hchi : chi ⟨k - 1, by omega⟩ ≠ 0) :
    computedDenominator k hk M lengthRow chi c =
      FaithfulScale.scaleDenominator (FaithfulScale.referenceSolver k hk M lengthRow chi c) := by
  unfold computedDenominator FaithfulScale.scaleDenominator
  apply Finset.lcm_congr rfl
  intro j _
  rw [denominator_spec]
  rw [congrFun (polynomials_spec k hk M lengthRow chi c hchi) j]

theorem computedScale_spec (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ)
    (hchi : chi ⟨k - 1, by omega⟩ ≠ 0) :
    computedScale k hk M lengthRow chi c =
      FaithfulScale.integerScale k (FaithfulScale.referenceSolver k hk M lengthRow chi c) := by
  unfold computedScale FaithfulScale.integerScale
  rw [computedDenominator_spec k hk M lengthRow chi c hchi]

theorem computedCorrection_spec (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ)
    (hchi : chi ⟨k - 1, by omega⟩ ≠ 0) :
    computedCorrection k hk M lengthRow chi c =
      FaithfulScale.referenceCorrectionInt k hk M lengthRow chi c := by
  have hp := polynomials_spec k hk M lengthRow chi c hchi
  unfold computedCorrection FaithfulScale.referenceCorrectionInt FaithfulScale.referenceCorrection
  simp only [eval_spec, computedScale_spec k hk M lengthRow chi c hchi]
  simp_rw [congrFun hp]

theorem compute_spec (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ)
    (hchi : chi ⟨k - 1, by omega⟩ ≠ 0) :
    compute k hk M lengthRow chi c =
      (FaithfulScale.integerScale k (FaithfulScale.referenceSolver k hk M lengthRow chi c),
        FaithfulScale.referenceCorrectionInt k hk M lengthRow chi c) := by
  rw [compute, computedScale_spec k hk M lengthRow chi c hchi,
    computedCorrection_spec k hk M lengthRow chi c hchi]

/-- A finite execution trace: state zero and the subsequent k-1 pivot attempts.
Both the trace and its individual states are executable definitions. -/
def executionTrace (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ) :
    List (Fin (k + 1) → Poly) :=
  List.ofFn (fun s : Fin k => helper k (interior k M lengthRow chi c) (psi k chi c)
    (-chi ⟨k - 1, by omega⟩ * ((2 : ℚ) ^ (k - 1) - 1)) s.val)

theorem executionTrace_length (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ) :
    (executionTrace k hk M lengthRow chi c).length = k := by simp [executionTrace]

theorem executionTrace_final (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ) :
    (executionTrace k hk M lengthRow chi c)[k - 1]? =
      some (polynomials k hk M lengthRow chi c) := by
  simp [executionTrace, polynomials, show k - 1 < k by omega]

/-- The computed pair inherits the exact row-zero and constant-score
independence of the specified algebraic algorithm. -/
theorem compute_independent (k : ℕ) (hk : 2 ≤ k)
    (M M' : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi chi' : Fin k → ℚ) (c c' : ℚ)
    (hchi0 : chi ⟨k - 1, by omega⟩ ≠ 0)
    (hM : ∀ a b, 0 < a.val → M a b = M' a b)
    (hchi : ∀ a, 0 < a.val → chi a = chi' a) :
    compute k hk M lengthRow chi c = compute k hk M' lengthRow chi' c' := by
  have hchi0' : chi' ⟨k - 1, by omega⟩ ≠ 0 := by
    rw [← hchi _ (by dsimp; omega)]
    exact hchi0
  rw [compute_spec k hk M lengthRow chi c hchi0,
    compute_spec k hk M' lengthRow chi' c' hchi0']
  obtain ⟨htau, hell⟩ := FaithfulScale.referenceCorrectionInt_scale_independent k hk
    M M' lengthRow chi chi' c c' hM hchi
  rw [htau, hell]

/-- Every listed state is the corresponding structurally recursive stage. -/
theorem executionTrace_state (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ)
    (s : ℕ) (hs : s < k) :
    (executionTrace k hk M lengthRow chi c)[s]? = some
      (helper k (interior k M lengthRow chi c) (psi k chi c)
        (-chi ⟨k - 1, by omega⟩ * ((2 : ℚ) ^ (k - 1) - 1)) s) := by
  simp [executionTrace, hs]

/-- End-to-end correctness of the executable output: positive prescribed
integer scale and every higher compatibility test, including the top test. -/
theorem compute_correct (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ)
    (hchi : chi ⟨k - 1, by omega⟩ ≠ 0) :
    let result := compute k hk M lengthRow chi c
    0 < result.1 ∧ ∀ h, k < h → h ≤ 2 * k → Even h →
      matInnerProd (Z_DP (k + 1) h)
        ((Matrix.of fun i j => (FaithfulScale.referenceInterior k M lengthRow chi c i j).eval
          (result.1 : ℚ)) -
          outerProd (Matrix.vecMul (fun j => (result.2 j : ℚ)) (S_mat (k + 1)))
            (fun j => (FaithfulScale.referencePsi k chi c j).eval (result.1 : ℚ))) = 0 := by
  rw [compute_spec k hk M lengthRow chi c hchi]
  exact FaithfulProspectiveScale.canonicalCorrection_DP_higher_tests k hk M lengthRow chi c hchi

/-- Degenerate pivots also agree computationally: both implementations return
zero, so equality of representations does not require a nonzero leading row. -/
theorem helper_spec_zero (k : ℕ) (F : Matrix (Fin (k + 1)) (Fin (k + 1)) Poly)
    (psi : Fin (k + 1) → Poly) :
    ∀ s, (fun a => interpret (helper k F psi 0 s a)) =
      FaithfulScale.polynomialHelper k (fun a b => interpret (F a b))
        (fun b => interpret (psi b)) 0 s := by
  intro s
  induction s with
  | zero => rfl
  | succ s ih =>
    by_cases hp : 1 < k - 1 - s ∧ k - 1 - s < k ∧ (k - 1 - s + k - 1) % 2 = 0
    · simp only [helper, FaithfulScale.polynomialHelper, if_pos hp]
      funext a
      by_cases ha : a.val = k - 1 - s
      · simp [ha, pivot, FaithfulScale.polynomialPivot, FaithfulScale.monomialPivot]
      · simp only [if_neg ha]
        exact congrFun ih a
    · simp only [helper, FaithfulScale.polynomialHelper, if_neg hp]
      exact ih

/-- Unconditional representation equality, for compiler rewriting of generic
algebraic formulas. Compatibility still requires nondegenerate clock data. -/
theorem polynomials_spec_all (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ) :
    (fun j => interpret (polynomials k hk M lengthRow chi c j)) =
      FaithfulScale.referenceSolver k hk M lengthRow chi c := by
  by_cases hz : chi ⟨k - 1, by omega⟩ = 0
  · have h := helper_spec_zero k (interior k M lengthRow chi c) (psi k chi c) (k - 1)
    simpa only [polynomials, FaithfulScale.referenceSolver, FaithfulScale.polynomialSolver,
      hz, neg_zero, zero_mul, interior_spec, psi_spec] using h
  · exact polynomials_spec k hk M lengthRow chi c hz

theorem computedDenominator_spec_all (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ) :
    computedDenominator k hk M lengthRow chi c =
      FaithfulScale.scaleDenominator (FaithfulScale.referenceSolver k hk M lengthRow chi c) := by
  unfold computedDenominator FaithfulScale.scaleDenominator
  apply Finset.lcm_congr rfl
  intro j _
  rw [denominator_spec, congrFun (polynomials_spec_all k hk M lengthRow chi c) j]

theorem computedScale_spec_all (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ) :
    computedScale k hk M lengthRow chi c =
      FaithfulScale.integerScale k (FaithfulScale.referenceSolver k hk M lengthRow chi c) := by
  unfold computedScale FaithfulScale.integerScale
  rw [computedDenominator_spec_all]

theorem computedCorrection_spec_all (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ) :
    computedCorrection k hk M lengthRow chi c =
      FaithfulScale.referenceCorrectionInt k hk M lengthRow chi c := by
  have hp := polynomials_spec_all k hk M lengthRow chi c
  unfold computedCorrection FaithfulScale.referenceCorrectionInt FaithfulScale.referenceCorrection
  simp only [eval_spec, computedScale_spec_all]
  simp_rw [congrFun hp]

theorem compute_spec_all (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (c : ℚ) :
    compute k hk M lengthRow chi c =
      (FaithfulScale.integerScale k (FaithfulScale.referenceSolver k hk M lengthRow chi c),
        FaithfulScale.referenceCorrectionInt k hk M lengthRow chi c) := by
  rw [compute, computedScale_spec_all, computedCorrection_spec_all]

#print axioms compute
#print axioms compute_spec
#print axioms computedDenominator_spec
#print axioms executionTrace_final
#print axioms compute_independent
#print axioms compute_correct
#print axioms compute_spec_all

end Karlin.FaithfulScaleEffective
