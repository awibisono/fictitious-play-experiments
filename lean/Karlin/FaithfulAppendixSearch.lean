import Karlin.FaithfulAppendixActual

/-! Termination of the literal Appendix candidate search. The fixed constants
are used only to prove termination; each tested candidate uses the exact
Appendix norm and actual moment correction. -/
namespace Karlin.FaithfulAppendix.Search
open scoped BigOperators Matrix
open Faithful FaithfulClock FaithfulAdmissible FaithfulSynthesis
open FaithfulGain.AdmissibleGain FaithfulResetEquations
open FaithfulEffectiveParameters Actual
set_option maxHeartbeats 2000000

section Bounds
variable (k : ℕ) (T lam : ℚ) (z ell : Fin (k+1) → ℚ)

theorem bW_le (ht : 0 < T) :
    bW k T lam z ≤ inverseConstant k lam z / T := by
  exact div_le_div_of_nonneg_right (add_le_add (le_entrySum _) (le_entrySum _)) ht.le

theorem bW_nonneg (ht : 0 ≤ T) : 0 ≤ bW k T lam z :=
  div_nonneg (add_nonneg (nonneg _) (nonneg _)) ht

theorem bC_nonneg (ht : 0 ≤ T) : 0 ≤ bC k T lam z ell :=
  add_nonneg (add_nonneg (nonneg _) (nonneg _)) (div_nonneg (rowAbs_nonneg _) ht)

theorem bC_le (ht : 1 ≤ T) : bC k T lam z ell ≤ countConstant k lam z ell := by
  have hp : 0 < T := by linarith
  have hrow : rowAbs ell / T ≤ rowAbs ell := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [rowAbs_nonneg ell]
  exact add_le_add (add_le_add (le_entrySum _) (le_entrySum _)) hrow

theorem nu_lt (ht : 0 < T)
    (hlarge : 2 * inverseConstant k lam z * rowAbs ell < T) :
    nu k T lam z ell < 1/2 := by
  have h := mul_le_mul_of_nonneg_right (bW_le k T lam z ht) (rowAbs_nonneg ell)
  change nu k T lam z ell ≤ _ at h
  have hh : inverseConstant k lam z / T * rowAbs ell < 1/2 := by
    apply (lt_div_iff₀ (by norm_num : (0:ℚ)<2)).mpr
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply (div_lt_iff₀ ht).mpr
    nlinarith
  exact h.trans_lt hh

theorem bE_le (ht : 0 < T) (hnu : nu k T lam z ell < 1/2) :
    bE k T lam z ell ≤ 2 * inverseConstant k lam z / T := by
  have hw := bW_le k T lam z ht
  have hw0 := bW_nonneg k T lam z ht.le
  have hd : 0 < 1 - nu k T lam z ell := by linarith
  have hh : bE k T lam z ell ≤ 2 * bW k T lam z := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  exact hh.trans (by simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left hw (by norm_num : (0:ℚ) ≤ 2))

theorem bR_le (KE : ℚ) (E L : Matrix (Fin (k+1)) (Fin (k+1)) ℚ)
    (ht : 1 ≤ T) (he : entrySum (E - T • paperE0 k lam z) ≤ KE) :
    bR k T lam z ell E L ≤ residualConstant k lam KE z ell L := by
  have hp : 0 < T := by linarith
  have hbase : E - paperEbase k T lam z ell =
      (E - T • paperE0 k lam z) - (2:ℚ) • outerProd z ell := by
    unfold paperEbase
    abel
  have hb := entrySum_sub_le (E - T • paperE0 k lam z) ((2:ℚ) • outerProd z ell)
  rw [entrySum_smul] at hb
  norm_num at hb
  rw [← hbase] at hb
  have hfirst := (le_entrySum (E - paperEbase k T lam z ell)).trans hb
  have hc := bC_le k T lam z ell ht
  have hc0 := bC_nonneg k T lam z ell hp.le
  have hcc : 0 ≤ countConstant k lam z ell := hc0.trans hc
  have hquad : 2 * normStar L * (bC k T lam z ell)^2 ≤
      2 * entrySum L * (countConstant k lam z ell)^2 := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left (le_entrySum L) (by norm_num))
      (sq_le_sq₀ hc0 hcc |>.mpr hc) (sq_nonneg _)
      (mul_nonneg (by norm_num) (entrySum_nonneg L))
  have hred : 2 * entrySum L * (countConstant k lam z ell)^2 / T ≤
      2 * entrySum L * (countConstant k lam z ell)^2 := by
    apply (div_le_iff₀ hp).mpr
    have hn : 0 ≤ 2 * entrySum L * (countConstant k lam z ell)^2 := by
      exact mul_nonneg (mul_nonneg (by norm_num) (entrySum_nonneg L)) (sq_nonneg _)
    nlinarith
  have hq := (div_le_div_of_nonneg_right hquad hp.le).trans hred
  unfold bR residualConstant
  linarith

theorem bR_nonneg (E L : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (ht : 0 ≤ T) :
    0 ≤ bR k T lam z ell E L := by
  unfold bR
  exact add_nonneg (nonneg _) (div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (nonneg L)) (sq_nonneg _)) ht)

theorem bCross_le (KE : ℚ) (E L : Matrix (Fin (k+1)) (Fin (k+1)) ℚ)
    (ht : 1 ≤ T) (he : entrySum (E - T • paperE0 k lam z) ≤ KE)
    (hnu : nu k T lam z ell < 1/2) :
    bCross k T lam z ell E L ≤ crossConstant k lam KE z ell L / T^2 := by
  have hp : 0 < T := by linarith
  have hw := bW_le k T lam z hp
  have hr := bR_le k T lam z ell KE E L ht he
  have hb := bE_le k T lam z ell hp hnu
  have hw0 := bW_nonneg k T lam z hp.le
  have hr0 := bR_nonneg k T lam z ell E L hp.le
  have hb0 : 0 ≤ bE k T lam z ell := div_nonneg hw0 (by linarith)
  have hw' : 0 ≤ inverseConstant k lam z / T := hw0.trans hw
  have hr' : 0 ≤ residualConstant k lam KE z ell L := hr0.trans hr
  have h := mul_le_mul (mul_le_mul hw hr hr0 hw') hb hb0 (mul_nonneg hw' hr')
  exact h.trans_eq (by unfold crossConstant; ring)

theorem bQ_le (KE Kd : ℚ) (psi : Fin (k+1) → ℚ)
    (E L B : Matrix (Fin (k+1)) (Fin (k+1)) ℚ)
    (ht : 2 ≤ T) (hl : 0 < lam)
    (he : entrySum (E - T • paperE0 k lam z) ≤ KE)
    (hpsi : rowAbs (psi - (Matrix.vecMul z B - z)) ≤ Kd / T)
    (hnu : nu k T lam z ell < 1/2) :
    bQ k T lam z ell psi E L B ≤ scoreConstant k lam KE Kd z ell L B / T := by
  have hp : 0 < T := by linarith
  have h1 : 1 ≤ T := by linarith
  have hw := bW_le k T lam z hp
  have hr := bR_le k T lam z ell KE E L h1 he
  have hb := bE_le k T lam z ell hp hnu
  have hc := bC_le k T lam z ell h1
  have hc0 := bC_nonneg k T lam z ell hp.le
  have hw0 := bW_nonneg k T lam z hp.le
  have hr0 := bR_nonneg k T lam z ell E L hp.le
  have hb0 : 0 ≤ bE k T lam z ell := div_nonneg hw0 (by linarith)
  have hL := le_entrySum L
  have hB := le_entrySum B
  have hL0 := entrySum_nonneg L
  have hB0 := entrySum_nonneg B
  have hC0 := hc0.trans hc
  have hR0 := hr0.trans hr
  have hW0 := hw0.trans hw
  have hE0 := hb0.trans hb
  have hfirst := mul_le_mul_of_nonneg_left hpsi (by positivity : (0:ℚ) ≤ 2*(k+1:ℚ))
  have hthird : 4 * normStar L * bC k T lam z ell * (1+normStar B) / T^2 ≤
      2 * entrySum L * countConstant k lam z ell * (1+entrySum B) / T := by
    have hprod : normStar L * bC k T lam z ell * (1+normStar B) ≤
        entrySum L * countConstant k lam z ell * (1+entrySum B) := by
      exact mul_le_mul (mul_le_mul hL hc hc0 hL0) (add_le_add_right hB 1)
        (by linarith [nonneg B]) (mul_nonneg hL0 hC0)
    have hprod0 : 0 ≤ entrySum L * countConstant k lam z ell * (1+entrySum B) := by positivity
    have hprod' := mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℚ) ≤ 4)
    calc
      _ ≤ 4 * (entrySum L * countConstant k lam z ell * (1+entrySum B)) / T^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg T)
        nlinarith only [hprod']
      _ ≤ _ := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hp) hp).mpr
        nlinarith [mul_nonneg (show 0 ≤ T-2 by linarith) hprod0]
  have hlast : bR k T lam z ell E L *
      (bE k T lam z ell * normStar B + bW k T lam z) ≤
      residualConstant k lam KE z ell L *
        ((2*inverseConstant k lam z/T)*entrySum B + inverseConstant k lam z/T) := by
    have hinside := add_le_add (mul_le_mul hb hB (nonneg B) hE0) hw
    exact mul_le_mul hr hinside
      (add_nonneg (mul_nonneg hb0 (nonneg B)) hw0) hR0
  have hkappa : paperKappa k T lam * (k+1:ℚ)*rowAbs ell = (2*rowAbs ell/lam)/T := by
    unfold paperKappa
    have hk : (k+1:ℚ) ≠ 0 := by positivity
    field_simp
  unfold bQ scoreConstant
  rw [hkappa]
  have hs := add_le_add (add_le_add (add_le_add_left hfirst ((2*rowAbs ell/lam)/T)) hthird) hlast
  exact hs.trans_eq (by ring)


theorem bP_le {m : Type*} [Fintype m] [Nonempty m]
    (KE Kd dc : ℚ) (psi : Fin (k+1) → ℚ)
    (E L B : Matrix (Fin (k+1)) (Fin (k+1)) ℚ)
    (a : m → ℚ) (X LX D0 : Matrix m (Fin (k+1)) ℚ)
    (ht : 2 ≤ T) (hl : 0 < lam)
    (he : entrySum (E - T • paperE0 k lam z) ≤ KE)
    (hdc : |dc| ≤ Kd / T)
    (hpsi : rowAbs (psi - (Matrix.vecMul z B - z)) ≤ Kd / T)
    (hnu : nu k T lam z ell < 1/2) :
    bP k T lam z ell psi E L B a X LX
        (D0 + dc • outerProd (fun _ => 1) (e0_row (k+1))) ≤
      couplingConstant k lam KE Kd a X LX D0 z ell L B / T := by
  have hp : 0 < T := by linarith
  have h1 : 1 ≤ T := by linarith
  have hw := bW_le k T lam z hp
  have hq := bQ_le k T lam z ell KE Kd psi E L B ht hl he hpsi hnu
  have hdc' := gain_abs_le_constant T dc Kd h1 hdc
  let D := D0 + dc • outerProd (fun _ : m => 1) (e0_row (k+1))
  have hd : normStar (D + outerProd a ell) ≤ deficitConstant k Kd a D0 ell := by
    have hid : D + outerProd a ell = (D0 + outerProd a ell) +
        dc • outerProd (fun _ : m => 1) (e0_row (k+1)) := by dsimp [D]; abel
    rw [hid]
    have hh := (le_entrySum _).trans (entrySum_add_le (D0+outerProd a ell)
      (dc • outerProd (fun _ : m => 1) (e0_row (k+1))))
    rw [entrySum_smul] at hh
    exact hh.trans (add_le_add_right
      (mul_le_mul_of_nonneg_right hdc' (entrySum_nonneg _)) _)
  have hw0 := bW_nonneg k T lam z hp.le
  have hD0 := (nonneg (D+outerProd a ell)).trans hd
  have hW0 := hw0.trans hw
  have hX0 := entrySum_nonneg X
  have hLX0 := entrySum_nonneg LX
  have hfirst := mul_le_mul hd hw hw0 hD0
  have htriple : normStar X * normStar (D+outerProd a ell) * bW k T lam z ≤
      entrySum X * deficitConstant k Kd a D0 ell * (inverseConstant k lam z / T) :=
    mul_le_mul (mul_le_mul (le_entrySum X) hd (nonneg _) hX0) hw hw0 (mul_nonneg hX0 hD0)
  have hq0 : 0 ≤ bQ k T lam z ell psi E L B := by
    have hL := nonneg L
    have hB := nonneg B
    have hC := bC_nonneg k T lam z ell hp.le
    have hR := bR_nonneg k T lam z ell E L hp.le
    have he0 : 0 ≤ bE k T lam z ell := div_nonneg hw0 (by linarith)
    have hrow := rowAbs_nonneg (psi-(Matrix.vecMul z B-z))
    have hell := rowAbs_nonneg ell
    have hk : 0 ≤ paperKappa k T lam := by unfold paperKappa; positivity
    unfold bQ
    positivity
  have hinside0 : 0 ≤ bQ k T lam z ell psi E L B +
      normStar X * normStar (D+outerProd a ell) * bW k T lam z := by
    exact add_nonneg hq0 (mul_nonneg (mul_nonneg (nonneg X) (nonneg _)) hw0)
  have hlast := mul_le_mul (le_entrySum LX) (add_le_add hq htriple) hinside0 hLX0
  have hh := add_le_add hfirst hlast
  exact hh.trans_eq (by unfold couplingConstant; ring)

end Bounds
section ActualSearch
variable {k : ℕ} {P : Clock k} (A : Admissible P)

theorem actualPsi_error (lam T : ℕ) (Kd : ℚ)
    (hdc : |selectedGain A lam T - A.cref| ≤ Kd / T) :
    rowAbs (actualPsi A lam T -
      (Matrix.vecMul A.referenceHeight (B_mat (k+1)) - A.referenceHeight)) ≤ Kd / T := by
  have hh : actualPsi A lam T = Matrix.vecMul A.referenceHeight (B_mat (k+1)) -
      A.referenceHeight - (selectedGain A lam T - A.cref) • e0_row (k+1) := actual_psi_eq A _
  rw [hh]
  have hid : Matrix.vecMul A.referenceHeight (B_mat (k+1)) - A.referenceHeight -
      (selectedGain A lam T - A.cref) • e0_row (k+1) -
      (Matrix.vecMul A.referenceHeight (B_mat (k+1)) - A.referenceHeight) =
      -(selectedGain A lam T - A.cref) • e0_row (k+1) := by module
  rw [hid]
  have hn : rowAbs (-(selectedGain A lam T - A.cref) • e0_row (k+1)) =
      |selectedGain A lam T - A.cref| * rowAbs (e0_row (k+1)) := by
    simp only [rowAbs, Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, Finset.mul_sum]
  have he0 : rowAbs (e0_row (k+1)) = 1 := rowAbs_earlyUnit k
  rw [hn, he0, mul_one]
  exact hdc

/-- The cutoff is fixed before T1 and does not mention T2 or a phase index.
It strengthens the conservative coefficient cutoff by T1>2, and its strict
inverse condition secures the Appendix denominator before bE is tested. -/
def appendixCutoff (lam : ℕ) (Kd KE : ℚ) (N0 : ℕ) : ℚ :=
  max 2 (FaithfulEffectiveParameters.cutoff A lam Kd KE N0 (leftInverseLX P A.tau))

theorem candidate_of_cutoff (lam : ℕ) (hlam : 1 ≤ lam) (Kd KE : ℚ) (N0 : ℕ)
    (hup : UpstreamBounds A lam Kd KE N0) (T : ℕ)
    (hT : appendixCutoff A lam Kd KE N0 < (T : ℚ)) : Candidate A lam T := by
  have h2 := (max_lt_iff.mp hT).1
  have hcut := (max_lt_iff.mp hT).2
  have hc := certificate_of_cutoff A lam hlam Kd KE N0 (leftInverseLX P A.tau) T hcut
  rcases hc with ⟨hN, h1, _, hlead, _, hx, hpmin, hpg⟩
  obtain ⟨hgden, hcl, hcu, hdc, hE⟩ := hup.bounds T hN
  have ht : (0:ℚ) < T := by linarith
  have hl : (0:ℚ) < lam := by exact_mod_cast (show 0 < lam by omega)
  have hT2 : (2:ℚ) ≤ T := h2.le
  have hT1 : (1:ℚ) ≤ T := by linarith
  have hs : 2 * inverseConstant k lam A.referenceHeight * rowAbs A.correction < (T:ℚ) := by
    simp only [FaithfulEffectiveParameters.cutoff, max_lt_iff] at hcut
    exact hcut.2.2.2.2.1
  have hnu := nu_lt k T lam A.referenceHeight A.correction ht hs
  have hcross := bCross_le k T lam A.referenceHeight A.correction KE
    (momentTable A lam T) (paperLower k) hT1 hE hnu
  have hpsi := actualPsi_error A lam T Kd hdc
  have hcouple := bP_le k T lam A.referenceHeight A.correction KE Kd
    (selectedGain A lam T - A.cref) (actualPsi A lam T)
    (momentTable A lam T) (paperLower k) (B_mat (k+1)) A.weights
    (FaithfulTables.X P A.tau) (leftInverseLX P A.tau)
    (FaithfulTables.D P A.tau A.cref (baseline P) 0) hT2 hl hE hdc hpsi hnu
  have hd : actualD A lam T = FaithfulTables.D P A.tau A.cref (baseline P) 0 +
      (selectedGain A lam T - A.cref) • outerProd (fun _ => 1) (e0_row (k+1)) := actual_D_eq A _ 0
  change bP k T lam A.referenceHeight A.correction (actualPsi A lam T)
    (momentTable A lam T) (paperLower k) (B_mat (k+1)) A.weights
    (FaithfulTables.X P A.tau) (leftInverseLX P A.tau) _ ≤ _ at hcouple
  rw [← hd] at hcouple
  have hcouple' : couplingCap A lam T ≤ couplingBound A lam Kd KE (leftInverseLX P A.tau) / T := hcouple
  have hcross' : crossCap A lam T ≤ crossBound A lam KE / (T:ℚ)^2 := hcross
  have hsmall : crossBound A lam KE / (T:ℚ)^2 < paperKappa k T lam / 2 := by
    have hr : (0:ℚ) < k+1 := by positivity
    have hprod := mul_lt_mul_of_pos_right hx ht
    have hratio : crossBound A lam KE / (T:ℚ)^2 < 1/((k+1:ℚ)*lam*T) := by
      apply (div_lt_div_iff₀ (sq_pos_of_pos ht) (by positivity)).mpr
      nlinarith
    convert hratio using 1
    unfold paperKappa
    ring
  refine ⟨h1, ?_, hcl, hcu, hlead, hnu, hcross'.trans_lt hsmall,
    lt_min (hcouple'.trans_lt hpmin) (hcouple'.trans_lt hpg)⟩
  intro _
  simpa only [gainDenominator, lastIdx, add_assoc] using hgden

/-- A concrete terminating upper bound, computed from finite rational data. -/
def appendixOnset (lam : ℕ) (Kd KE : ℚ) (N0 : ℕ) : ℕ :=
  Nat.floor (appendixCutoff A lam Kd KE N0) + 1

theorem candidate_after_onset (lam : ℕ) (hlam : 1 ≤ lam) (Kd KE : ℚ) (N0 : ℕ)
    (hup : UpstreamBounds A lam Kd KE N0) (T : ℕ)
    (hT : appendixOnset A lam Kd KE N0 ≤ T) : Candidate A lam T := by
  apply candidate_of_cutoff A lam hlam Kd KE N0 hup T
  exact (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hT)

/-- All upstream numerical data is fixed constructively from A and lambda. -/
def canonicalOnset (lam : ℕ) : ℕ := appendixOnset A lam (fixedKd A lam)
  (fixedKE A lam (FaithfulCokernel.momentSectionBound k)) (fixedGainOnset A lam)

theorem candidate_after_canonicalOnset (lam : ℕ) (hlam : 1 ≤ lam)
    (T : ℕ) (hT : canonicalOnset A lam ≤ T) : Candidate A lam T :=
  candidate_after_onset A lam hlam _ _ _
    (explicit_upstream A lam hlam (FaithfulCokernel.momentSectionBound k)
      (FaithfulCokernel.momentSectionBound_nonneg k) (FaithfulCokernel.momentSection_bound k)) T hT

theorem candidate_exists (lam : ℕ) (hlam : 1 ≤ lam) : ∃ T : ℕ, Candidate A lam T :=
  ⟨canonicalOnset A lam, candidate_after_canonicalOnset A lam hlam _ le_rfl⟩

/-- Literal evaluation order. Neither bE nor either cap is evaluated until the
positive even-gain denominator and nu<1/2 gates have passed. No universal
statement or later parameter is part of this executable checker. -/
def passes (lam T : ℕ) : Bool :=
  if 1 ≤ T then
    if Even k → 0 < gainDenominator A lam T then
      if 0 < selectedGain A lam T ∧ selectedGain A lam T < 1 then
        if 0 < (T:ℚ)*lam*A.referenceHeight (lastIdx k) + A.correction (lastIdx k) then
          if nu k T lam A.referenceHeight A.correction < 1/2 then
            decide (crossCap A lam T < paperKappa k T lam / 2 ∧
              couplingCap A lam T < min (minimumWeight A / 4)
                ((A.weights (Sum.inr 0) - P.Arem - 1)/2))
          else false
        else false
      else false
    else false
  else false

theorem passes_iff (lam T : ℕ) : passes A lam T = true ↔ Candidate A lam T := by
  simp only [passes, Candidate, Bool.ite_eq_true_distrib, Bool.false_eq_true,
    decide_eq_true_eq]
  split_ifs <;> tauto

theorem passes_exists (lam : ℕ) (hlam : 1 ≤ lam) : ∃ T : ℕ, passes A lam T = true := by
  obtain ⟨T,hT⟩ := candidate_exists A lam hlam
  exact ⟨T,(passes_iff A lam T).mpr hT⟩

/-- Successive exact search returns the least passing positive integer. -/
def successiveScale (lam : ℕ) (hlam : 1 ≤ lam) : ℕ :=
  Nat.find (passes_exists A lam hlam)

theorem successiveScale_spec (lam : ℕ) (hlam : 1 ≤ lam) :
    Candidate A lam (successiveScale A lam hlam) :=
  (passes_iff A lam _).mp (Nat.find_spec (passes_exists A lam hlam))

theorem successiveScale_minimal (lam : ℕ) (hlam : 1 ≤ lam) (T : ℕ)
    (hT : Candidate A lam T) : successiveScale A lam hlam ≤ T :=
  Nat.find_min' (passes_exists A lam hlam) ((passes_iff A lam T).mpr hT)

theorem successiveScale_le_onset (lam : ℕ) (hlam : 1 ≤ lam) :
    successiveScale A lam hlam ≤ canonicalOnset A lam :=
  successiveScale_minimal A lam hlam _ (candidate_after_canonicalOnset A lam hlam _ le_rfl)

theorem doubling_exists (lam : ℕ) (hlam : 1 ≤ lam) : ∃ j : ℕ, passes A lam (2^j) = true := by
  refine ⟨canonicalOnset A lam, (passes_iff A lam _).mpr ?_⟩
  exact candidate_after_canonicalOnset A lam hlam _ Nat.lt_two_pow_self.le

/-- The exponent of the first successful doubling candidate 1,2,4,8,... . -/
def doublingIndex (lam : ℕ) (hlam : 1 ≤ lam) : ℕ :=
  Nat.find (doubling_exists A lam hlam)

def doublingScale (lam : ℕ) (hlam : 1 ≤ lam) : ℕ := 2 ^ doublingIndex A lam hlam

theorem doublingScale_spec (lam : ℕ) (hlam : 1 ≤ lam) :
    Candidate A lam (doublingScale A lam hlam) :=
  (passes_iff A lam _).mp (Nat.find_spec (doubling_exists A lam hlam))

theorem doublingIndex_minimal (lam : ℕ) (hlam : 1 ≤ lam) (j : ℕ)
    (hT : Candidate A lam (2^j)) : doublingIndex A lam hlam ≤ j :=
  Nat.find_min' (doubling_exists A lam hlam) ((passes_iff A lam _).mpr hT)

theorem doublingIndex_le_onset (lam : ℕ) (hlam : 1 ≤ lam) :
    doublingIndex A lam hlam ≤ canonicalOnset A lam :=
  doublingIndex_minimal A lam hlam _
    (candidate_after_canonicalOnset A lam hlam _ Nat.lt_two_pow_self.le)

/-- The paper's lambda is fixed before either search; these contain no phase or
second reset parameter. The two search conventions are intentionally distinct. -/
def canonicalSuccessiveScale : ℕ :=
  successiveScale A (FaithfulParameters.AdmissibleParameters.lam A)
    (FaithfulParameters.AdmissibleParameters.lam_pos A)

def canonicalDoublingScale : ℕ :=
  doublingScale A (FaithfulParameters.AdmissibleParameters.lam A)
    (FaithfulParameters.AdmissibleParameters.lam_pos A)

theorem canonicalSuccessiveScale_spec :
    Candidate A (FaithfulParameters.AdmissibleParameters.lam A) (canonicalSuccessiveScale A) :=
  successiveScale_spec A _ _

theorem canonicalDoublingScale_spec :
    Candidate A (FaithfulParameters.AdmissibleParameters.lam A) (canonicalDoublingScale A) :=
  doublingScale_spec A _ _

/-- Successful successive search secures every second scale at or above T1. -/
theorem successiveScale_valid (lam : ℕ) (hlam : 1 ≤ lam) (T2 : ℕ)
    (hT2 : successiveScale A lam hlam ≤ T2) :
    ValidScales A lam (successiveScale A lam hlam) T2 (leftInverseLX P A.tau) :=
  candidate_validScales A lam _ (by omega) (successiveScale_spec A lam hlam) T2 hT2

/-- The separately specified doubling search has the same uniform validity. -/
theorem doublingScale_valid (lam : ℕ) (hlam : 1 ≤ lam) (T2 : ℕ)
    (hT2 : doublingScale A lam hlam ≤ T2) :
    ValidScales A lam (doublingScale A lam hlam) T2 (leftInverseLX P A.tau) :=
  candidate_validScales A lam _ (by omega) (doublingScale_spec A lam hlam) T2 hT2

theorem canonicalSuccessiveScale_valid (T2 : ℕ) (hT2 : canonicalSuccessiveScale A ≤ T2) :
    ValidScales A (FaithfulParameters.AdmissibleParameters.lam A)
      (canonicalSuccessiveScale A) T2 (leftInverseLX P A.tau) :=
  successiveScale_valid A _ _ T2 hT2

theorem canonicalDoublingScale_valid (T2 : ℕ) (hT2 : canonicalDoublingScale A ≤ T2) :
    ValidScales A (FaithfulParameters.AdmissibleParameters.lam A)
      (canonicalDoublingScale A) T2 (leftInverseLX P A.tau) :=
  doublingScale_valid A _ _ T2 hT2

/-- These rejection identities expose the two mandatory evaluation gates. -/
theorem passes_reject_denominator (lam T : ℕ) (heven : Even k)
    (hden : gainDenominator A lam T ≤ 0) : passes A lam T = false := by
  have hh : ¬(Even k → 0 < gainDenominator A lam T) := by intro h; linarith [h heven]
  simp [passes, hh]

theorem passes_reject_nu (lam T : ℕ)
    (hnu : 1/2 ≤ nu k T lam A.referenceHeight A.correction) : passes A lam T = false := by
  have hh : ¬nu k T lam A.referenceHeight A.correction < 1/2 := not_lt.mpr hnu
  simp only [passes, if_neg hh, ite_self]

#print axioms candidate_after_canonicalOnset
#print axioms successiveScale_spec
#print axioms doublingScale_spec
#print axioms canonicalSuccessiveScale_spec
#print axioms canonicalDoublingScale_valid
#print axioms canonicalSuccessiveScale_valid
#print axioms canonicalDoublingScale_spec
end ActualSearch
end Karlin.FaithfulAppendix.Search
