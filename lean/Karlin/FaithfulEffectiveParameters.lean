import Karlin.FaithfulSynthesis
import Karlin.FaithfulParameters
import Karlin.FaithfulEffectiveGramBridge

/-! Executable finite certificates for the first reset parameter.  Rational
uniform bounds and the fixed rational LX table are explicit data.  Their
correctness proofs are erased; the search never decides a universal statement.
The conservative entry-sum bounds preserve the literal paper matrices. -/
namespace Karlin.FaithfulEffectiveParameters
open scoped BigOperators Matrix
open Faithful FaithfulClock FaithfulAdmissible FaithfulSynthesis
open FaithfulGain.AdmissibleGain
set_option maxHeartbeats 1200000

variable {k : ℕ} {P : Clock k} (A : Admissible P)

/-- The upstream information needed by the numerical first-scale certificate.
Every runtime input is explicit; no rational bound is selected by this record. -/
structure UpstreamBounds (lam : ℕ) (Kd KE : ℚ) (N0 : ℕ) : Prop where
  bounds : ∀ T : ℕ, N0 ≤ T →
    0 < baselineCounts A lam ⟨k, by omega⟩ * T +
      (oldTotals A ⟨k, by omega⟩ + A.correction ⟨k, by omega⟩) ∧
    0 < selectedGain A lam T ∧ selectedGain A lam T < 1 ∧
    |selectedGain A lam T - A.cref| ≤ Kd / T ∧
    entrySum (momentTable A lam T - (T : ℚ) • paperE0 k lam A.referenceHeight) ≤ KE

theorem upstreamBounds_exist (lam : ℕ) (hlam : 1 ≤ lam) :
    ∃ (Kd KE : ℚ) (N0 : ℕ), UpstreamBounds A lam Kd KE N0 := by
  obtain ⟨Kd, KE, N0, _, _, _, hb⟩ := eventually_momentTable A lam hlam
  refine ⟨Kd, KE, N0, ⟨?_⟩⟩
  intro T hT
  obtain ⟨hd, hcl, hcu, hc, _, he⟩ := hb T hT
  exact ⟨hd, hcl, hcu, hc, he⟩

def denominatorA (lam : ℕ) : ℚ :=
  dotProduct A.correction ((Phi0_concrete k lam A.referenceHeight).mulVec (earlyUnit k))

def denominatorB : ℚ :=
  dotProduct A.correction ((Phi1_concrete k A.referenceHeight).mulVec (earlyUnit k))

def crossBound (lam : ℕ) (KE : ℚ) : ℚ :=
  crossConstant k lam KE A.referenceHeight A.correction (L_strict (k + 1))

def couplingBound (lam : ℕ) (Kd KE : ℚ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ) : ℚ :=
  couplingConstant k lam KE Kd A.weights (FaithfulTables.X P A.tau) LX
    (FaithfulTables.D P A.tau A.cref (baseline P) 0) A.referenceHeight A.correction
    (L_strict (k + 1)) (B_mat (k + 1))

/-- Eight decidable rational/natural tests; in particular T2 is absent. -/
def Certificate (lam : ℕ) (Kd KE : ℚ) (N0 : ℕ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ) (T : ℕ) : Prop :=
  N0 ≤ T ∧ 1 ≤ T ∧
  2 * (|denominatorA A lam| + |denominatorB A|) < (T : ℚ) ∧
  0 < (T : ℚ) * lam * A.referenceHeight (lastIdx k) + A.correction (lastIdx k) ∧
  2 * inverseConstant k lam A.referenceHeight * rowAbs A.correction ≤ (T : ℚ) ∧
  (k + 1 : ℚ) * lam * crossBound A lam KE < (T : ℚ) ∧
  couplingBound A lam Kd KE LX / T < minimumWeight A / 4 ∧
  couplingBound A lam Kd KE LX / T <
    (A.weights (Sum.inr 0) - P.Arem - 1) / 2

instance certificateDecidable (lam : ℕ) (Kd KE : ℚ) (N0 : ℕ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ) (T : ℕ) :
    Decidable (Certificate A lam Kd KE N0 LX T) := by
  unfold Certificate
  infer_instance

/-- A closed rational upper bound proves termination of the finite search. -/
def cutoff (lam : ℕ) (Kd KE : ℚ) (N0 : ℕ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ) : ℚ :=
  max (N0 : ℚ) (max 1
    (max (2 * (|denominatorA A lam| + |denominatorB A|))
      (max (-A.correction (lastIdx k) / ((lam : ℚ) * A.referenceHeight (lastIdx k)))
        (max (2 * inverseConstant k lam A.referenceHeight * rowAbs A.correction)
          (max ((k + 1 : ℚ) * lam * crossBound A lam KE)
            (max (4 * couplingBound A lam Kd KE LX / minimumWeight A)
              (2 * couplingBound A lam Kd KE LX /
                (A.weights (Sum.inr 0) - P.Arem - 1))))))))

theorem certificate_of_cutoff (lam : ℕ) (hlam : 1 ≤ lam) (Kd KE : ℚ) (N0 : ℕ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ) (T : ℕ)
    (hT : cutoff A lam Kd KE N0 LX < (T : ℚ)) : Certificate A lam Kd KE N0 LX T := by
  simp only [cutoff, max_lt_iff] at hT
  rcases hT with ⟨hn, h1, hd, hl, hs, hx, hp, hg⟩
  have ht : (0 : ℚ) < T := by linarith
  have hlamq : (0 : ℚ) < lam := by exact_mod_cast (show 0 < lam by omega)
  have hz := A.reference_leading_pos
  have ha := minimumWeight_pos A
  have hgap : 0 < A.weights (Sum.inr 0) - P.Arem - 1 := by
    have := A.gateway_weight_margin
    linarith
  refine ⟨by exact_mod_cast hn.le, by exact_mod_cast h1.le, hd, ?_, hs.le, hx, ?_, ?_⟩
  · have hh := (div_lt_iff₀ (mul_pos hlamq hz)).mp hl
    change -A.correction (lastIdx k) < (T : ℚ) * (lam * A.referenceHeight (lastIdx k)) at hh
    nlinarith
  · apply (div_lt_iff₀ ht).mpr
    have hh := (div_lt_iff₀ ha).mp hp
    nlinarith
  · apply (div_lt_iff₀ ht).mpr
    have hh := (div_lt_iff₀ hgap).mp hg
    nlinarith

/-- A directly executable alternative to the least-passing search. -/
def closedScale (lam : ℕ) (Kd KE : ℚ) (N0 : ℕ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ) : ℕ :=
  Nat.floor (cutoff A lam Kd KE N0 LX) + 1

theorem closedScale_certificate (lam : ℕ) (hlam : 1 ≤ lam) (Kd KE : ℚ) (N0 : ℕ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ) :
    Certificate A lam Kd KE N0 LX (closedScale A lam Kd KE N0 LX) := by
  apply certificate_of_cutoff A lam hlam Kd KE N0 LX
  simpa only [closedScale, Nat.cast_add, Nat.cast_one] using
    Nat.lt_floor_add_one (cutoff A lam Kd KE N0 LX)

theorem certificate_exists (lam : ℕ) (hlam : 1 ≤ lam) (Kd KE : ℚ) (N0 : ℕ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ) :
    ∃ T : ℕ, Certificate A lam Kd KE N0 LX T :=
  ⟨closedScale A lam Kd KE N0 LX, closedScale_certificate A lam hlam Kd KE N0 LX⟩

/-- The executable least-natural search, with a proof of termination.  Its
predicate contains finite exact rational tests only. -/
def searchScale (lam : ℕ) (hlam : 1 ≤ lam) (Kd KE : ℚ) (N0 : ℕ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ) : ℕ :=
  Nat.find (certificate_exists A lam hlam Kd KE N0 LX)

theorem searchScale_certificate (lam : ℕ) (hlam : 1 ≤ lam) (Kd KE : ℚ) (N0 : ℕ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ) :
    Certificate A lam Kd KE N0 LX (searchScale A lam hlam Kd KE N0 LX) :=
  Nat.find_spec (certificate_exists A lam hlam Kd KE N0 LX)

theorem searchScale_minimal (lam : ℕ) (hlam : 1 ≤ lam) (Kd KE : ℚ) (N0 : ℕ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ) (T : ℕ)
    (hT : Certificate A lam Kd KE N0 LX T) : searchScale A lam hlam Kd KE N0 LX ≤ T :=
  Nat.find_min' (certificate_exists A lam hlam Kd KE N0 LX) hT

theorem certificate_mono (lam : ℕ) (hlam : 1 ≤ lam) (Kd KE : ℚ) (N0 : ℕ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ) {T U : ℕ}
    (hT : Certificate A lam Kd KE N0 LX T) (hTU : T ≤ U) :
    Certificate A lam Kd KE N0 LX U := by
  rcases hT with ⟨hn, h1, hd, hl, hs, hx, hp, hg⟩
  have htu : (T : ℚ) ≤ U := by exact_mod_cast hTU
  have ht : (0 : ℚ) < T := by exact_mod_cast (show 0 < T by omega)
  have hu : (0 : ℚ) < U := ht.trans_le htu
  have hlamq : (0 : ℚ) < lam := by exact_mod_cast (show 0 < lam by omega)
  have hz := A.reference_leading_pos
  have hamin := minimumWeight_pos A
  have hgap : 0 < A.weights (Sum.inr 0) - P.Arem - 1 := by
    have := A.gateway_weight_margin
    linarith
  refine ⟨hn.trans hTU, h1.trans hTU, hd.trans_le htu, ?_, hs.trans htu,
    hx.trans_le htu, ?_, ?_⟩
  · change 0 < A.referenceHeight (lastIdx k) at hz
    have hh := mul_le_mul_of_nonneg_right htu (mul_pos hlamq hz).le
    nlinarith
  · apply (div_lt_iff₀ hu).mpr
    exact ((div_lt_iff₀ ht).mp hp).trans_le
      (mul_le_mul_of_nonneg_left htu (by positivity))
  · apply (div_lt_iff₀ hu).mpr
    exact ((div_lt_iff₀ ht).mp hg).trans_le
      (mul_le_mul_of_nonneg_left htu (by positivity))

/-- Every certificate secures every later second parameter. The only
universal input is an erased proof of the upstream gain/moment bounds. -/
theorem certificate_valid (lam : ℕ) (hlam : 1 ≤ lam) (Kd KE : ℚ) (N0 : ℕ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ)
    (hup : UpstreamBounds A lam Kd KE N0) (T1 : ℕ)
    (hcert : Certificate A lam Kd KE N0 LX T1) (T2 : ℕ) (hT2 : T1 ≤ T2) :
    ValidScales A lam T1 T2 LX := by
  rcases hcert with ⟨hN0, hT1one, hdenbound, hlead, hlarge, hcross, hpmin, hpg⟩
  obtain ⟨hgden, hcl, hcu, hdc, hE⟩ := hup.bounds T1 hN0
  have ht1 : (0 : ℚ) < T1 := by exact_mod_cast (show 0 < T1 by omega)
  have ht2 : (0 : ℚ) < T2 := by exact_mod_cast (show 0 < T2 by omega)
  have hlamq : (0 : ℚ) < lam := by exact_mod_cast (show 0 < lam by omega)
  have hT2q : (T1 : ℚ) ≤ T2 := by exact_mod_cast hT2
  have hsmall := two_scale_abs_lt_half (denominatorA A lam) (denominatorB A)
    T1 T2 ht1 hT2q hdenbound
  have hden : (1 / 2 : ℚ) < 1 + dotProduct A.correction
      ((Winv_concrete k T1 T2 lam A.referenceHeight).mulVec (earlyUnit k)) := by
    rw [denominator_two_scale]
    have hh := (abs_lt.mp hsmall).1
    change -(1 / 2 : ℚ) < (T1 : ℚ)⁻¹ * denominatorA A lam +
      (T2 : ℚ)⁻¹ * denominatorB A at hh
    change (1 / 2 : ℚ) < 1 + ((T1 : ℚ)⁻¹ * denominatorA A lam +
      (T2 : ℚ)⁻¹ * denominatorB A)
    linarith
  have hu : 0 < (T1 : ℚ) * lam * A.referenceHeight (lastIdx k) :=
    mul_pos (mul_pos ht1 hlamq) A.reference_leading_pos
  have hleading := reset_leading_positive k T1 lam A.referenceHeight A.correction hu hlead T2
  obtain ⟨hC, hP, hreserve⟩ := actual_reset_signs k T1 T2 lam KE Kd
    (selectedGain A lam T1 - A.cref) A.weights (FaithfulTables.X P A.tau) LX
    (FaithfulTables.D P A.tau A.cref (baseline P) 0) A.referenceHeight A.correction
    (momentTable A lam T1) (L_strict (k + 1)) (B_mat (k + 1)) (Sum.inr 0)
    (minimumWeight A) P.Arem (selectedGain A lam T1) A.reference_cone
    (by exact_mod_cast hT1one) hT2q hlamq A.reference_leading_pos hden hlarge hE hdc
    (minimumWeight_pos A) (minimumWeight_le A) A.gateway_weight_margin hcu hcross hpmin hpg
  refine ⟨by omega, by omega, hgden, hcl, hcu, ?_, ?_, ?_, hleading, hden, hC, hP, hreserve, ?_⟩
  · exact lt_min (by positivity) (by have := P.marker_pos; positivity)
  · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  · exact lt_of_le_of_lt (min_le_right _ _) (by have := P.marker_pos; linarith)
  · intro delta
    exact momentTable_solves A lam T1 delta (fun _ => hgden.ne')

theorem searchScale_valid (lam : ℕ) (hlam : 1 ≤ lam) (Kd KE : ℚ) (N0 : ℕ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ)
    (hup : UpstreamBounds A lam Kd KE N0) :
    ∀ T2 : ℕ, searchScale A lam hlam Kd KE N0 LX ≤ T2 →
      ValidScales A lam (searchScale A lam hlam Kd KE N0 LX) T2 LX :=
  certificate_valid A lam hlam Kd KE N0 LX hup _
    (searchScale_certificate A lam hlam Kd KE N0 LX)

/-- The searched first scale is a uniform onset, including every larger first
scale. It can replace an existentially chosen onset without changing formulas. -/
theorem searchScale_uniform_valid (lam : ℕ) (hlam : 1 ≤ lam) (Kd KE : ℚ) (N0 : ℕ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ)
    (hup : UpstreamBounds A lam Kd KE N0) :
    ∀ T1 : ℕ, searchScale A lam hlam Kd KE N0 LX ≤ T1 →
    ∀ T2 : ℕ, T1 ≤ T2 → ValidScales A lam T1 T2 LX := by
  intro T1 hT1 T2 hT2
  exact certificate_valid A lam hlam Kd KE N0 LX hup T1
    (certificate_mono A lam hlam Kd KE N0 LX
      (searchScale_certificate A lam hlam Kd KE N0 LX) hT1) T2 hT2

theorem closedScale_uniform_valid (lam : ℕ) (hlam : 1 ≤ lam) (Kd KE : ℚ) (N0 : ℕ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ)
    (hup : UpstreamBounds A lam Kd KE N0) :
    ∀ T1 : ℕ, closedScale A lam Kd KE N0 LX ≤ T1 →
    ∀ T2 : ℕ, T1 ≤ T2 → ValidScales A lam T1 T2 LX := by
  intro T1 hT1 T2 hT2
  exact certificate_valid A lam hlam Kd KE N0 LX hup T1
    (certificate_mono A lam hlam Kd KE N0 LX
      (closedScale_certificate A lam hlam Kd KE N0 LX) hT1) T2 hT2

/-- Explicit coefficient of the O(1/T) gain error. -/
def gainSize (N a : ℚ) : ℚ := 2 * |N| / a

def gainStart (cref N a b : ℚ) : ℕ :=
  Nat.floor (max 1 (max (2 * |b| / a) (gainSize N a / min cref (1 - cref)))) + 1

theorem gainStart_pos (cref N a b : ℚ) : 1 ≤ gainStart cref N a b := by
  unfold gainStart
  omega

theorem explicit_gain_bounds (k : ℕ) (cref N a b : ℚ)
    (hcref : 0 < cref ∧ cref < 1) (ha : 0 < a)
    (T : ℕ) (hT : gainStart cref N a b ≤ T) :
    0 < a * T + b ∧ 0 < FaithfulGain.gain k cref N a b T ∧
      FaithfulGain.gain k cref N a b T < 1 ∧
      |FaithfulGain.gainShift k N a b T| ≤ gainSize N a / T := by
  let delta := min cref (1 - cref)
  have hd : 0 < delta := lt_min hcref.1 (by linarith)
  have hK : 0 ≤ gainSize N a := div_nonneg (by positivity) ha.le
  have hmax : max 1 (max (2 * |b| / a) (gainSize N a / delta)) < (T : ℚ) := by
    apply (Nat.lt_floor_add_one _).trans_le
    exact_mod_cast hT
  have ht : (0 : ℚ) < T := by have := (le_max_left _ _).trans_lt hmax; linarith
  have hb : 2 * |b| / a < (T : ℚ) :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hmax
  have hb' := (div_lt_iff₀ ha).mp hb
  have hdenlower : a * T / 2 ≤ a * T + b := by
    have hh := neg_abs_le b
    nlinarith
  have hden : 0 < a * T + b := (by positivity : (0 : ℚ) < a * T / 2).trans_le hdenlower
  have hKexact : gainSize N a * a = 2 * |N| := by unfold gainSize; field_simp
  have hdc : |FaithfulGain.gainShift k N a b T| ≤ gainSize N a / T := by
    by_cases hk : Even k
    · rw [FaithfulGain.gainShift, if_pos hk, abs_div, abs_neg, abs_of_pos hden]
      apply (div_le_div_iff₀ hden ht).mpr
      calc |N| * (T : ℚ) = (2 * |N|) * T / 2 := by ring
        _ = (gainSize N a * a) * T / 2 := by rw [hKexact]
        _ = gainSize N a * (a * T / 2) := by ring
        _ ≤ gainSize N a * (a * T + b) := mul_le_mul_of_nonneg_left hdenlower hK
    · rw [FaithfulGain.gainShift, if_neg hk, abs_zero]
      exact div_nonneg hK ht.le
  have hdelta : gainSize N a / delta < (T : ℚ) :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hmax
  have hsmall : gainSize N a / (T : ℚ) < delta := by
    apply (div_lt_iff₀ ht).mpr
    have hh := (div_lt_iff₀ hd).mp hdelta
    nlinarith
  have hs := abs_lt.mp (hdc.trans_lt hsmall)
  have hd1 : delta ≤ cref := min_le_left _ _
  have hd2 : delta ≤ 1 - cref := min_le_right _ _
  refine ⟨hden, ?_, ?_, hdc⟩ <;> dsimp [FaithfulGain.gain] <;> linarith

def fixedKd (lam : ℕ) : ℚ :=
  gainSize (matInnerProd (Z_binom_concrete (k + 1) k) (referenceResidual A))
    (baselineCounts A lam ⟨k, by omega⟩)

def fixedGainOnset (lam : ℕ) : ℕ :=
  gainStart A.cref (matInnerProd (Z_binom_concrete (k + 1) k) (referenceResidual A))
    (baselineCounts A lam ⟨k, by omega⟩)
    (oldTotals A ⟨k, by omega⟩ + A.correction ⟨k, by omega⟩)

def fixedKE (lam : ℕ) (sectionBound : ℚ) : ℚ :=
  sectionBound * FaithfulGain.residualBound (referenceResidual A) (oldTotals A)
    (baselineCounts A lam) A.correction (fixedKd A lam)

/-- The supplied finite section bound gives explicit computable Kd, KE and N0.
Only the section's bound proof is required; no numerical existential witness is
used in any of the definitions above. -/
theorem explicit_upstream (lam : ℕ) (hlam : 1 ≤ lam) (sectionBound : ℚ)
    (hsection_nonneg : 0 ≤ sectionBound)
    (hsection : ∀ F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ,
      entrySum (FaithfulCokernel.momentSection k F) ≤ sectionBound * entrySum F) :
    UpstreamBounds A lam (fixedKd A lam) (fixedKE A lam sectionBound) (fixedGainOnset A lam) := by
  constructor
  intro T hT
  have ha := baselineCounts_top_positive A lam hlam
  obtain ⟨hden, hcl, hcu, hdc⟩ := explicit_gain_bounds k A.cref
    (matInnerProd (Z_binom_concrete (k + 1) k) (referenceResidual A))
    (baselineCounts A lam ⟨k, by omega⟩)
    (oldTotals A ⟨k, by omega⟩ + A.correction ⟨k, by omega⟩)
    ⟨A.cref_pos, A.cref_lt_one⟩ ha T hT
  have hKd : 0 ≤ fixedKd A lam := div_nonneg (by positivity) ha.le
  have hTpos : 1 ≤ T := (gainStart_pos _ _ _ _).trans hT
  have hr := FaithfulGain.correctedResidual_bound (referenceResidual A) (oldTotals A)
    (baselineCounts A lam) A.correction T (fixedKd A lam) hTpos hKd hdc
  have he : momentTable A lam T - (T : ℚ) • paperE0 k lam A.referenceHeight =
      FaithfulCokernel.momentSection k (FaithfulGain.correctedResidual
        (referenceResidual A) (oldTotals A) (baselineCounts A lam) A.correction T) := by
    unfold momentTable FaithfulGain.correctedMoment
    abel
  refine ⟨hden, hcl, hcu, ?_, ?_⟩
  · rwa [selectedGain_sub_reference]
  · rw [he]
    exact (hsection _).trans (mul_le_mul_of_nonneg_left hr hsection_nonneg)

/-- An executable first-parameter onset from finite parent/section/Gram data. -/
def effectiveFirstScale (lam : ℕ) (sectionBound : ℚ)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ) : ℕ :=
  closedScale A lam (fixedKd A lam) (fixedKE A lam sectionBound) (fixedGainOnset A lam) LX

theorem effectiveFirstScale_spec (lam : ℕ) (hlam : 1 ≤ lam) (sectionBound : ℚ)
    (hsection_nonneg : 0 ≤ sectionBound)
    (hsection : ∀ F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ,
      entrySum (FaithfulCokernel.momentSection k F) ≤ sectionBound * entrySum F)
    (LX : Matrix (FaithfulTables.OldAct P) (Fin (k + 1)) ℚ) :
    ∀ T1 : ℕ, effectiveFirstScale A lam sectionBound LX ≤ T1 →
    ∀ T2 : ℕ, T1 ≤ T2 → ValidScales A lam T1 T2 LX :=
  closedScale_uniform_valid A lam hlam _ _ _ LX
    (explicit_upstream A lam hlam sectionBound hsection_nonneg hsection)

/-- The actual first parameter: least height multiplier, one fixed executable
moment section, and the paper's prescribed Gram section are all fixed before
the first scale, the second scale, or any phase/time index. -/
def canonicalFirstScale : ℕ :=
  effectiveFirstScale A (FaithfulParameters.AdmissibleParameters.lam A)
    (FaithfulCokernel.momentSectionBound k)
    (FaithfulResetEquations.leftInverseLX P A.tau)

theorem canonicalFirstScale_pos : 1 ≤ canonicalFirstScale A := by
  unfold canonicalFirstScale effectiveFirstScale closedScale
  omega

/-- A fully discharged, uniform specification of the executable first scale. -/
theorem canonicalFirstScale_spec :
    ∀ T1 : ℕ, canonicalFirstScale A ≤ T1 → ∀ T2 : ℕ, T1 ≤ T2 →
      ValidScales A (FaithfulParameters.AdmissibleParameters.lam A) T1 T2
        (FaithfulResetEquations.leftInverseLX P A.tau) :=
  effectiveFirstScale_spec A _ (FaithfulParameters.AdmissibleParameters.lam_pos A)
    (FaithfulCokernel.momentSectionBound k) (FaithfulCokernel.momentSectionBound_nonneg k)
    (FaithfulCokernel.momentSection_bound k) _

#print axioms explicit_upstream
#print axioms effectiveFirstScale_spec
#print axioms canonicalFirstScale_spec
#print axioms certificate_valid
#print axioms searchScale_valid
#print axioms searchScale_minimal
#print axioms searchScale_uniform_valid
#print axioms closedScale_uniform_valid
end Karlin.FaithfulEffectiveParameters
