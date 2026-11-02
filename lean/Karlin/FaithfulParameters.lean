import Karlin.FaithfulGain
import Karlin.FaithfulGrowth
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Integer parameters for the v15 reset construction

The reference height is fixed before choosing its least positive denominator
multiplier. The integer correction row is left unscaled. Reset counts use the
paper's literal W and W_E tables; the moment correction remains rational.
-/
namespace Karlin.FaithfulParameters
open scoped BigOperators Matrix

/-- The executable least common multiple of the reduced denominators. -/
def heightMultiplier {ι : Type*} [Fintype ι] (z : ι → ℚ) : ℕ :=
  Finset.univ.lcm (fun i => (z i).den)

theorem heightMultiplier_pos {ι : Type*} [Fintype ι] (z : ι → ℚ) :
    0 < heightMultiplier z := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr (by intro i _; exact (z i).den_nz)

theorem den_dvd_heightMultiplier {ι : Type*} [Fintype ι] (z : ι → ℚ) (i : ι) :
    (z i).den ∣ heightMultiplier z := Finset.dvd_lcm (Finset.mem_univ i)

/-- An explicit integer numerator after clearing the denominator. -/
def clearedHeight {ι : Type*} [Fintype ι] (z : ι → ℚ) (i : ι) : ℤ :=
  Int.ofNat (heightMultiplier z / (z i).den) * (z i).num

theorem clearedHeight_cast {ι : Type*} [Fintype ι] (z : ι → ℚ) (i : ι) :
    (clearedHeight z i : ℚ) = (heightMultiplier z : ℚ) * z i := by
  unfold clearedHeight
  rw [Int.cast_mul]
  change ((heightMultiplier z / (z i).den : ℕ) : ℚ) * (z i).num = _
  rw [Rat.natCast_div _ _ (den_dvd_heightMultiplier z i)]
  rw [div_mul_eq_mul_div, mul_div_assoc, Rat.num_div_den]

theorem den_dvd_of_integer_multiple (q : ℚ) (n : ℕ) (a : ℤ)
    (ha : (a : ℚ) = (n : ℚ) * q) : q.den ∣ n := by
  by_cases hn : n = 0
  · simp [hn]
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have he : q = (a : ℚ) / (n : ℚ) := by rw [ha]; field_simp
  have hd := Rat.den_dvd a (n : ℤ)
  rw [Rat.divInt_eq_div] at hd
  have he' : (a : ℚ) / ((n : ℤ) : ℚ) = q := by simpa using he.symm
  rw [he'] at hd
  exact Int.natCast_dvd_natCast.mp hd

/-- Every integer multiplier clearing the row is divisible by the chosen one. -/
theorem heightMultiplier_dvd {ι : Type*} [Fintype ι] (z : ι → ℚ) (n : ℕ)
    (hn : ∀ i, ∃ a : ℤ, (a : ℚ) = (n : ℚ) * z i) :
    heightMultiplier z ∣ n := by
  apply Finset.lcm_dvd
  intro i _
  obtain ⟨a, ha⟩ := hn i
  exact den_dvd_of_integer_multiple (z i) n a ha

/-- This is the paper's least positive integer, not merely some multiplier. -/
theorem heightMultiplier_minimal {ι : Type*} [Fintype ι] (z : ι → ℚ) (n : ℕ)
    (hnpos : 0 < n) (hn : ∀ i, ∃ a : ℤ, (a : ℚ) = (n : ℚ) * z i) :
    heightMultiplier z ≤ n :=
  Nat.le_of_dvd hnpos (heightMultiplier_dvd z n hn)

/-- The integral adjustment matrix in equation (W). -/
def adjustmentInt (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
  fun x y => match finSumFinEquiv.symm x, finSumFinEquiv.symm y with
    | Sum.inl i, Sum.inl j => if i = j then 1 else 0
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr _, Sum.inl _ => -1
    | Sum.inr _, Sum.inr _ => 0

theorem adjustmentInt_cast (k : ℕ) (i j : Fin (k + 1)) :
    (adjustmentInt k i j : ℚ) = V0_paper k i j := by
  unfold adjustmentInt V0_paper
  simp only [Matrix.of_apply]
  cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> simp

def lateInt {k : ℕ} (z : Fin (k + 1) → ℚ) (T1 T2 : ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
  fun i j => (T1 : ℤ) * clearedHeight z j + (T2 : ℤ) * adjustmentInt k i j

def earlyInt {k : ℕ} (z : Fin (k + 1) → ℚ) (ellStar : Fin (k + 1) → ℤ)
    (T1 T2 : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
  fun i j => lateInt z T1 T2 i j + if i.val = 0 then ellStar j else 0

def resetInt {k : ℕ} (z : Fin (k + 1) → ℚ) (ellStar : Fin (k + 1) → ℤ)
    (T1 T2 : ℕ) := Matrix.fromRows (earlyInt z ellStar T1 T2) (lateInt z T1 T2)

theorem lateInt_cast {k : ℕ} (z : Fin (k + 1) → ℚ) (T1 T2 : ℕ)
    (i j : Fin (k + 1)) :
    (lateInt z T1 T2 i j : ℚ) =
      W_concrete k T1 T2 (heightMultiplier z) z i j := by
  simp only [lateInt, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    clearedHeight_cast, adjustmentInt_cast, W_concrete, W_paper,
    Matrix.add_apply, Matrix.smul_apply, outerProd, Matrix.of_apply,
    Pi.smul_apply, smul_eq_mul, one_mul]
  ring

theorem earlyInt_cast {k : ℕ} (z : Fin (k + 1) → ℚ)
    (ellStar : Fin (k + 1) → ℤ) (T1 T2 : ℕ) (i j : Fin (k + 1)) :
    (earlyInt z ellStar T1 T2 i j : ℚ) =
      WE_concrete k T1 T2 (heightMultiplier z) z (Faithful.earlyUnit k)
        (fun a => (ellStar a : ℚ)) i j := by
  simp only [earlyInt, Int.cast_add, lateInt_cast, WE_concrete,
    Matrix.add_apply, outerProd, Matrix.of_apply, Faithful.earlyUnit]
  split_ifs <;> simp

theorem resetInt_cast {k : ℕ} (z : Fin (k + 1) → ℚ)
    (ellStar : Fin (k + 1) → ℤ) (T1 T2 : ℕ) :
    (fun i j => (resetInt z ellStar T1 T2 i j : ℚ)) =
      Matrix.fromRows
        (WE_concrete k T1 T2 (heightMultiplier z) z (Faithful.earlyUnit k)
          (fun a => (ellStar a : ℚ)))
        (W_concrete k T1 T2 (heightMultiplier z) z) := by
  ext i j
  rcases i with i | i
  · exact earlyInt_cast z ellStar T1 T2 i j
  · exact lateInt_cast z T1 T2 i j

def phaseCounts {ι : Type*} [Fintype ι] {k : ℕ}
    (M : Matrix ι (Fin (k + 1)) ℤ) (q : ℕ) : ι → ℤ :=
  M.mulVec (fun j => (Nat.choose q j.val : ℤ))

theorem phaseCounts_cast {ι : Type*} [Fintype ι] {k : ℕ}
    (M : Matrix ι (Fin (k + 1)) ℤ) (q : ℕ) (i : ι) :
    (phaseCounts M q i : ℚ) =
      Matrix.mulVec (fun i j => (M i j : ℚ)) (binomBasis (k + 1) q) i := by
  simp [phaseCounts, Matrix.mulVec, dotProduct, binomBasis]

def constantTwoRow (k : ℕ) : Fin (k + 1) → ℚ :=
  fun j => if j = 0 then 2 else 0

/-- An executable onset for a single reset count to be at least two. -/
def countOnset {k : ℕ} (c : Fin (k + 1) → ℚ) : ℕ :=
  FaithfulGrowth.rowDominationThreshold c (constantTwoRow k) k 1

theorem countOnset_ge_one {k : ℕ} (c : Fin (k + 1) → ℚ) : 1 ≤ countOnset c :=
  le_max_left _ _

theorem count_ge_two {k : ℕ} (hk : 0 < k) (c : Fin (k + 1) → ℚ)
    (hc : 0 < c (Fin.last k)) (q : ℕ) (hq : countOnset c ≤ q) :
    2 ≤ ∑ j, c j * (Nat.choose q j.val : ℚ) := by
  have hP : (FaithfulGrowth.rowPoly c).natDegree ≤ k := by
    simpa using FaithfulGrowth.rowPoly_natDegree_le c
  have hG : (FaithfulGrowth.rowPoly (constantTwoRow k)).natDegree ≤ k - 1 := by
    apply FaithfulGrowth.rowPoly_natDegree_le_of_vanishing
    intro j hj
    have hj0 : j ≠ 0 := by intro h; subst j; simp at hj
    simp [constantTwoRow, hj0]
  have hL : 0 < (FaithfulGrowth.rowPoly c).coeff k := by
    have h := FaithfulGrowth.rowPoly_top_coeff (Nat.succ_pos k) c
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at h
    rw [h]
    exact div_pos hc (by positivity)
  have hq' : FaithfulGrowth.dominationThreshold (FaithfulGrowth.rowPoly c)
      (FaithfulGrowth.rowPoly (constantTwoRow k)) k 1 ≤ q := by
    simpa only [countOnset, FaithfulGrowth.rowDominationThreshold_eq] using hq
  have h := FaithfulGrowth.polynomial_domination _ _ hk hP hG hL (by norm_num : (0 : ℚ) < 1) hq'
  simpa [FaithfulGrowth.rowPoly_eval_nat, constantTwoRow] using h

/-- A finite maximum chooses one phase onset after the fixed integer table. -/
def resetOnset {ι : Type*} [Fintype ι] {k : ℕ}
    (M : Matrix ι (Fin (k + 1)) ℤ) : ℕ :=
  max 1 (Finset.univ.sup (fun i => countOnset (fun j => (M i j : ℚ))))

theorem resetOnset_ge_one {ι : Type*} [Fintype ι] {k : ℕ}
    (M : Matrix ι (Fin (k + 1)) ℤ) : 1 ≤ resetOnset M := le_max_left _ _

theorem resetCounts_ge_two {ι : Type*} [Fintype ι] {k : ℕ} (hk : 0 < k)
    (M : Matrix ι (Fin (k + 1)) ℤ) (hM : ∀ i, 0 < M i (Fin.last k))
    (q : ℕ) (hq : resetOnset M ≤ q) (i : ι) : 2 ≤ phaseCounts M q i := by
  have hi : countOnset (fun j => (M i j : ℚ)) ≤ q :=
    (Finset.le_sup (Finset.mem_univ i)).trans ((le_max_right _ _).trans hq)
  have h := count_ge_two hk (fun j => (M i j : ℚ))
    (by dsimp only; exact_mod_cast hM i) q hi
  have he := phaseCounts_cast M q i
  simp only [Matrix.mulVec, dotProduct, binomBasis] at he
  rw [← he] at h
  exact_mod_cast h

namespace AdmissibleParameters
variable {k : ℕ} {P : FaithfulClock.Clock k} (A : FaithfulAdmissible.Admissible P)

def lam : ℕ := heightMultiplier A.referenceHeight

theorem lam_pos : 1 ≤ lam A := heightMultiplier_pos A.referenceHeight

theorem lam_minimal (n : ℕ) (hn : 1 ≤ n)
    (hclear : ∀ j, ∃ z : ℤ, (z : ℚ) = (n : ℚ) * A.referenceHeight j) :
    lam A ≤ n := heightMultiplier_minimal _ _ hn hclear

theorem lam_clears (j : Fin (k + 1)) :
    (clearedHeight A.referenceHeight j : ℚ) = (lam A : ℚ) * A.referenceHeight j :=
  clearedHeight_cast _ _

def resetTable (T1 T2 : ℕ) := resetInt A.referenceHeight A.ellStar T1 T2

theorem resetTable_cast (T1 T2 : ℕ) :
    (fun i j => (resetTable A T1 T2 i j : ℚ)) =
      Matrix.fromRows
        (WE_concrete k T1 T2 (lam A) A.referenceHeight (Faithful.earlyUnit k) A.correction)
        (W_concrete k T1 T2 (lam A) A.referenceHeight) :=
  resetInt_cast A.referenceHeight A.ellStar T1 T2

/-- A concrete integral version of the old table derived from the parent's C. -/
def oldTable : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℤ :=
  fun i j => Int.floor (FaithfulTables.X P A.tau i j)

theorem oldTable_cast (i : FaithfulTables.OldAct P) (j : Fin (k + 1)) :
    (oldTable A i j : ℚ) = FaithfulTables.X P A.tau i j := by
  obtain ⟨z, hz⟩ := FaithfulTables.X_integer P A.tau i j
  norm_num at hz
  simp [oldTable, hz]

def countTable (T1 T2 : ℕ) := Matrix.fromRows (oldTable A) (resetTable A T1 T2)

theorem countTable_cast (T1 T2 : ℕ) :
    (fun i j => (countTable A T1 T2 i j : ℚ)) =
      Faithful.coneTable k (FaithfulTables.X P A.tau) T1 T2 (lam A)
        A.referenceHeight A.correction := by
  ext i j
  rcases i with i | i
  · exact oldTable_cast A i j
  · exact congrFun (congrFun (resetTable_cast A T1 T2) i) j

/-- The sum of the reset rows is exactly the parity equation's total count
row, including the original (unscaled) correction. -/
theorem resetTable_total (T1 T2 : ℕ) :
    Matrix.vecMul (fun _ => (1 : ℚ)) (fun i j => (resetTable A T1 T2 i j : ℚ)) =
      FaithfulGain.totalCounts (FaithfulGain.AdmissibleGain.baselineCounts A (lam A))
        A.correction T1 := by
  rw [resetTable_cast, Matrix.vecMul_fromRows]
  change Matrix.vecMul (fun _ => (1 : ℚ))
      (WE_concrete k T1 T2 (lam A) A.referenceHeight (Faithful.earlyUnit k) A.correction) +
    Matrix.vecMul (fun _ => (1 : ℚ))
      (W_concrete k T1 T2 (lam A) A.referenceHeight) = _
  rw [Faithful.early_row_sum, vecMul_one_W_concrete]
  ext j
  simp only [FaithfulGain.totalCounts, FaithfulGain.AdmissibleGain.baselineCounts,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Executable first-scale onset securing the leading reset counts. -/
def resetScaleOnset : ℕ :=
  Nat.floor (max 1 (-A.correction (Fin.last k) /
    ((lam A : ℚ) * A.referenceHeight (Fin.last k)))) + 1

theorem resetScaleOnset_ge_one : 1 ≤ resetScaleOnset A := Nat.le_add_left 1 _

theorem resetTable_leading_pos (T1 T2 : ℕ) (hT1 : resetScaleOnset A ≤ T1) :
    ∀ i, 0 < resetTable A T1 T2 i (Fin.last k) := by
  have hl : 0 < (lam A : ℚ) := by exact_mod_cast (lam_pos A : 0 < lam A)
  have hz := A.reference_leading_pos
  have hbound : max 1 (-A.correction (Fin.last k) /
      ((lam A : ℚ) * A.referenceHeight (Fin.last k))) < (T1 : ℚ) := by
    apply (Nat.lt_floor_add_one _).trans_le
    exact_mod_cast hT1
  have h1 : (1 : ℚ) < T1 := (le_max_left _ _).trans_lt hbound
  have hcorr : -A.correction (Fin.last k) <
      (T1 : ℚ) * ((lam A : ℚ) * A.referenceHeight (Fin.last k)) :=
    (div_lt_iff₀ (mul_pos hl hz)).mp ((le_max_right _ _).trans_lt hbound)
  have hu : 0 < (T1 : ℚ) * lam A * A.referenceHeight (lastIdx k) := by
    change 0 < (T1 : ℚ) * lam A * A.referenceHeight (Fin.last k)
    positivity
  have hearly : 0 < (T1 : ℚ) * lam A * A.referenceHeight (lastIdx k) +
      A.correction (lastIdx k) := by
    change 0 < (T1 : ℚ) * lam A * A.referenceHeight (Fin.last k) +
      A.correction (Fin.last k)
    nlinarith
  have h := Faithful.reset_leading_positive k T1 (lam A) A.referenceHeight A.correction hu hearly T2
  intro i
  have he := congrFun (congrFun (resetTable_cast A T1 T2) i) (Fin.last k)
  have hq : (0 : ℚ) < (resetTable A T1 T2 i (Fin.last k) : ℚ) := by
    rw [he]
    rcases i with i | i
    · exact (h i).1
    · exact (h i).2
  exact_mod_cast hq

/-- Lambda is fixed first; a single executable threshold then works for every
pair of integer reset scales. The phase onset is computed after those scales. -/
theorem eventually_resetCounts :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ T1 : ℕ, N ≤ T1 → ∀ T2 : ℕ, T1 ≤ T2 →
      (∀ i, 0 < resetTable A T1 T2 i (Fin.last k)) ∧
      (∀ q : ℕ, resetOnset (resetTable A T1 T2) ≤ q →
        ∀ i, 2 ≤ phaseCounts (resetTable A T1 T2) q i) := by
  refine ⟨resetScaleOnset A, resetScaleOnset_ge_one A, ?_⟩
  intro T1 hT1 T2 _
  have hlead := resetTable_leading_pos A T1 T2 hT1
  refine ⟨hlead, ?_⟩
  intro q hq i
  exact resetCounts_ge_two (by have := P.order_ge_two; omega) _ hlead q hq i

open FaithfulGain.AdmissibleGain in
/-- Actual bounded moment correction, with lambda already fixed to the least
height denominator. The paper Ebase includes the unscaled rank-one term. -/
theorem eventually_moment_and_counts :
    ∃ (K KE : ℚ) (T0 : ℕ), 0 ≤ K ∧ 0 ≤ KE ∧ 1 ≤ T0 ∧
      ∀ T1 : ℕ, T0 ≤ T1 → ∀ T2 : ℕ, T1 ≤ T2 →
      0 < selectedGain A (lam A) T1 ∧ selectedGain A (lam A) T1 < 1 ∧
      |selectedGain A (lam A) T1 - A.cref| ≤ K / T1 ∧
      (∀ delta : ℚ, L_moment (B_mat (k + 1)) (momentTable A (lam A) T1) =
        (FaithfulTables.D P A.tau (selectedGain A (lam A) T1)
          (FaithfulAdmissible.baseline P) delta).transpose * FaithfulTables.X P A.tau -
        outerProd (FaithfulGain.totalCounts (baselineCounts A (lam A)) A.correction T1)
          (FaithfulTables.psi (P.R P.b) A.tau (selectedGain A (lam A) T1)
            (FaithfulAdmissible.baseline P))) ∧
      Faithful.entrySum (momentTable A (lam A) T1 -
        Faithful.paperEbase k T1 (lam A) A.referenceHeight A.correction) ≤ KE ∧
      (∀ i, 0 < resetTable A T1 T2 i (Fin.last k)) ∧
      (∀ q : ℕ, resetOnset (resetTable A T1 T2) ≤ q →
        ∀ i, 2 ≤ phaseCounts (resetTable A T1 T2) q i) := by
  obtain ⟨K, KE, N1, hK, hKE, hN1, hm⟩ := eventually_momentTable A (lam A) (lam_pos A)
  obtain ⟨N2, hN2, hr⟩ := eventually_resetCounts A
  let R := Faithful.entrySum ((2 : ℚ) • outerProd A.referenceHeight A.correction)
  have hR : 0 ≤ R := Faithful.entrySum_nonneg _
  refine ⟨K, KE + R, max N1 N2, hK, add_nonneg hKE hR,
    hN1.trans (le_max_left _ _), ?_⟩
  intro T1 hT1 T2 hT2
  obtain ⟨_, hcl, hcu, hdc, heq, hb⟩ := hm T1 ((le_max_left _ _).trans hT1)
  obtain ⟨hl, hcounts⟩ := hr T1 ((le_max_right _ _).trans hT1) T2 hT2
  refine ⟨hcl, hcu, hdc, heq, ?_, hl, hcounts⟩
  have hid : momentTable A (lam A) T1 -
      Faithful.paperEbase k T1 (lam A) A.referenceHeight A.correction =
      (momentTable A (lam A) T1 - (T1 : ℚ) • Faithful.paperE0 k (lam A) A.referenceHeight) -
      (2 : ℚ) • outerProd A.referenceHeight A.correction := by
    unfold Faithful.paperEbase
    abel
  rw [hid]
  exact (Faithful.entrySum_sub_le _ _).trans (add_le_add hb le_rfl)

end AdmissibleParameters

end Karlin.FaithfulParameters
