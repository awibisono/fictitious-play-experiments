import Karlin.GatewayLift
import Karlin.AllOrdersComplete
import Karlin.AdmissibleLift
import Karlin.ChronologyBounds

namespace Karlin

def C_zeta_sum {w : ℕ} (clock : AlgebraicClock w) (delta c_zeta : ℚ) : ℚ :=
  ∑ c : Fin (w + 1), |zeta_bundle_scaled clock delta c_zeta c|

def bundle_c_high_gen {k : ℕ} (fc : FullRankClock k) (delta c_zeta shift : ℚ) (phaseShift : ℕ) : ℚ :=
  (2 * (C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1))) ^ (k + 1) *
    ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k

theorem bundle_c_high_gen_pos {k : ℕ} (fc : FullRankClock k) (delta c_zeta shift : ℚ) (phaseShift : ℕ) :
    0 < bundle_c_high_gen fc delta c_zeta shift phaseShift := by
  unfold bundle_c_high_gen
  have hpos_base : 0 < 2 * (C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1)) := by
    have : 0 < |shift| + 1 := by positivity
    have : 0 ≤ C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k := by
      unfold C_zeta_sum
      have : 0 ≤ ∑ c : Fin (k + 1), |zeta_bundle_scaled fc.clock delta c_zeta c| :=
        Finset.sum_nonneg fun c _ => abs_nonneg _
      positivity
    linarith
  positivity

def C_zeta_sum_admissible {w : ℕ} (clock : AlgebraicClock w) (b : Fin clock.m) (H0 ch delta c_zeta : ℚ) : ℚ :=
  ∑ c : Fin (w + 1), |zeta_admissible_scaled clock b H0 ch delta c_zeta c|

def admissible_c_high_gen {k : ℕ} (fc : FullRankClock k) (b : Fin fc.clock.m) (H0 ch delta c_zeta shift : ℚ) (phaseShift : ℕ) : ℚ :=
  (2 * (C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1))) ^ (k + 1) *
    ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k

theorem admissible_c_high_gen_pos {k : ℕ} (fc : FullRankClock k) (b : Fin fc.clock.m) (H0 ch delta c_zeta shift : ℚ) (phaseShift : ℕ) :
    0 < admissible_c_high_gen fc b H0 ch delta c_zeta shift phaseShift := by
  unfold admissible_c_high_gen
  have hpos_base : 0 < 2 * (C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1)) := by
    have : 0 < |shift| + 1 := by positivity
    have : 0 ≤ C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k := by
      unfold C_zeta_sum_admissible
      have : 0 ≤ ∑ c : Fin (k + 1), |zeta_admissible_scaled fc.clock b H0 ch delta c_zeta c| :=
        Finset.sum_nonneg fun c _ => abs_nonneg _
      positivity
    linarith
  positivity

theorem dotProduct_zeta_bundle_scaled_le {w : ℕ} (clock : AlgebraicClock w) (delta c_zeta : ℚ)
    (q phaseShift : ℕ) :
    dotProduct (zeta_bundle_scaled clock delta c_zeta) (binomBasis (w + 1) (q + phaseShift)) ≤
      C_zeta_sum clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ w) * ((q + 1 : ℚ) ^ w) := by
  dsimp only [dotProduct]
  have h_term_le : ∀ c ∈ (Finset.univ : Finset (Fin (w + 1))),
      zeta_bundle_scaled clock delta c_zeta c * binomBasis (w + 1) (q + phaseShift) c ≤
        |zeta_bundle_scaled clock delta c_zeta c| * (((phaseShift + 1 : ℚ) ^ w) * ((q + 1 : ℚ) ^ w)) := by
    intro c _
    have h1 : zeta_bundle_scaled clock delta c_zeta c ≤ |zeta_bundle_scaled clock delta c_zeta c| := le_abs_self _
    have h2 := binomBasis_upper_bound w q phaseShift c
    have h_nonneg : 0 ≤ binomBasis (w + 1) (q + phaseShift) c := by unfold binomBasis; positivity
    calc zeta_bundle_scaled clock delta c_zeta c * binomBasis (w + 1) (q + phaseShift) c ≤
        |zeta_bundle_scaled clock delta c_zeta c| * binomBasis (w + 1) (q + phaseShift) c :=
          mul_le_mul_of_nonneg_right h1 h_nonneg
      _ ≤ |zeta_bundle_scaled clock delta c_zeta c| * (((phaseShift + 1 : ℚ) ^ w) * ((q + 1 : ℚ) ^ w)) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have h_sum_le := Finset.sum_le_sum h_term_le
  rw [← Finset.sum_mul] at h_sum_le
  unfold C_zeta_sum
  rw [mul_assoc]
  exact h_sum_le

theorem dotProduct_zeta_admissible_scaled_le {w : ℕ} (clock : AlgebraicClock w) (b : Fin clock.m)
    (H0 ch delta c_zeta : ℚ) (q phaseShift : ℕ) :
    dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) (q + phaseShift)) ≤
      C_zeta_sum_admissible clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ w) * ((q + 1 : ℚ) ^ w) := by
  dsimp only [dotProduct]
  have h_term_le : ∀ c ∈ (Finset.univ : Finset (Fin (w + 1))),
      zeta_admissible_scaled clock b H0 ch delta c_zeta c * binomBasis (w + 1) (q + phaseShift) c ≤
        |zeta_admissible_scaled clock b H0 ch delta c_zeta c| * (((phaseShift + 1 : ℚ) ^ w) * ((q + 1 : ℚ) ^ w)) := by
    intro c _
    have h1 : zeta_admissible_scaled clock b H0 ch delta c_zeta c ≤ |zeta_admissible_scaled clock b H0 ch delta c_zeta c| := le_abs_self _
    have h2 := binomBasis_upper_bound w q phaseShift c
    have h_nonneg : 0 ≤ binomBasis (w + 1) (q + phaseShift) c := by unfold binomBasis; positivity
    calc zeta_admissible_scaled clock b H0 ch delta c_zeta c * binomBasis (w + 1) (q + phaseShift) c ≤
        |zeta_admissible_scaled clock b H0 ch delta c_zeta c| * binomBasis (w + 1) (q + phaseShift) c :=
          mul_le_mul_of_nonneg_right h1 h_nonneg
      _ ≤ |zeta_admissible_scaled clock b H0 ch delta c_zeta c| * (((phaseShift + 1 : ℚ) ^ w) * ((q + 1 : ℚ) ^ w)) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have h_sum_le := Finset.sum_le_sum h_term_le
  rw [← Finset.sum_mul] at h_sum_le
  unfold C_zeta_sum_admissible
  rw [mul_assoc]
  exact h_sum_le

theorem bundleBiasedScoreShift_nonneg {k : ℕ} (hw : 2 ≤ k) (fc : FullRankClock k)
    (delta c_zeta c_P0 : ℚ) {m_rank : ℕ} (hm : 0 < m_rank)
    (rank : Fin (bundleFullRankLift hw fc delta c_zeta c_P0).clock.m → Fin m_rank)
    (phaseShift : ℕ) :
    0 ≤ bundleBiasedScoreShift hw fc delta c_zeta c_P0 rank phaseShift := by
  unfold bundleBiasedScoreShift bundleTieRemovalBias
  have h1 : 0 ≤ canonicalTieRemovalBias
      (bundleFullRankLift hw fc delta c_zeta c_P0).clock.G
      (bundleInitScoreVec hw fc delta c_zeta c_P0 phaseShift) rank
      (finSumFinEquiv (Sum.inr ⟨0, by omega⟩)) :=
    canonicalTieRemovalBias_nonneg _ _ hm rank _
  have h2 : 1 ≤ canonicalScoreShift
      (bundleBiasedInitScoreVec hw fc delta c_zeta c_P0 rank phaseShift phaseShift) :=
    one_le_canonicalScoreShift _
  linarith

theorem admissibleBiasedScoreShift_nonneg {k : ℕ} (hw : 2 ≤ k) (fc : FullRankClock k)
    (b : Fin fc.clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (fc.clock.m + 1) → ℚ)
    {m_rank : ℕ} (hm : 0 < m_rank)
    (rank : Fin (admissibleScaledFullRankLift hw fc b H0 ch delta c_zeta c_P0 a_old).clock.m → Fin m_rank)
    (phaseShift : ℕ) :
    0 ≤ admissibleBiasedScoreShift hw fc b H0 ch delta c_zeta c_P0 a_old rank phaseShift := by
  unfold admissibleBiasedScoreShift admissibleTieRemovalBias
  have h1 : 0 ≤ canonicalTieRemovalBias
      (admissibleScaledFullRankLift hw fc b H0 ch delta c_zeta c_P0 a_old).clock.G
      (admissibleInitScoreVec hw fc b H0 ch delta c_zeta c_P0 a_old phaseShift) rank
      ⟨0, by have := admissibleScaledFullRankLift_m_pos hw fc b H0 ch delta c_zeta c_P0 a_old; omega⟩ :=
    canonicalTieRemovalBias_nonneg _ _ hm rank _
  have h2 : 1 ≤ canonicalScoreShift
      (admissibleBiasedInitScoreVec hw fc b H0 ch delta c_zeta c_P0 a_old rank phaseShift phaseShift) :=
    one_le_canonicalScoreShift _
  linarith



theorem bundle_hgap_low_unconditional {k : ℕ} (hw : 2 ≤ k) (fc : FullRankClock k)
    (delta c_P0 : ℚ) (phaseShift : ℕ) (hshift : k ≤ phaseShift)
    (parentWord : ℕ → List (Fin fc.clock.m))
    (hparent_count : ∀ σ : ℕ, wordCountVec (parentWord σ) = fc.clock.C.mulVec (binomBasis k σ))
    {m_rank : ℕ} (hm_rank : 0 < m_rank)
    (rank : Fin (bundleFullRankLift hw fc delta (canonicalCZeta fc.clock delta) c_P0).clock.m → Fin m_rank)
    (p : ℕ) :
    let c_zeta := canonicalCZeta fc.clock delta
    let shift := bundleBiasedScoreShift hw fc delta c_zeta c_P0 rank phaseShift
    bundle_c_low fc phaseShift *
      (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map
        (finSumFinEquiv : _ ≃ Fin (bundleFullRankLift hw fc delta c_zeta c_P0).clock.m)) (p + 1) : ℚ) ^ k ≤
      (2 * (dotProduct (zeta_bundle_scaled fc.clock delta c_zeta)
        (binomBasis (k + 1) (p + phaseShift)) + shift)) ^ (k + 1) := by
  intro c_zeta shift
  have hshift_nonneg : 0 ≤ shift := bundleBiasedScoreShift_nonneg hw fc delta (canonicalCZeta fc.clock delta) c_P0 hm_rank rank phaseShift
  have h_hw1 : 1 ≤ k := by omega
  have h_dot_ge := ceiling_canonicalCZeta_ge_choose h_hw1 fc.clock delta (p + phaseShift)
  have h_choose_le : (p + 1 : ℚ) ^ k ≤ (k.factorial : ℚ) * (Nat.choose (p + phaseShift) k : ℚ) := by
    exact_mod_cast pow_le_factorial_mul_choose_shifted k phaseShift hshift p
  have h_fact_pos : 0 < (k.factorial : ℚ) := by positivity
  have h_choose_div : (p + 1 : ℚ) ^ k / (k.factorial : ℚ) ≤ (Nat.choose (p + phaseShift) k : ℚ) := by
    rw [div_le_iff₀ h_fact_pos]
    linarith [h_choose_le]
  have h_score_ge : (p + 1 : ℚ) ^ k / (k.factorial : ℚ) ≤
      dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift := by
    calc (p + 1 : ℚ) ^ k / (k.factorial : ℚ) ≤ (Nat.choose (p + phaseShift) k : ℚ) := h_choose_div
      _ ≤ 1 + (Nat.choose (p + phaseShift) k : ℚ) := by linarith
      _ ≤ dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) := h_dot_ge
      _ ≤ dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift := by linarith [hshift_nonneg]
  have h_score_mul : (2 / (k.factorial : ℚ)) * ((p + 1 : ℚ) ^ k) ≤
      2 * (dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift) := by
    calc (2 / (k.factorial : ℚ)) * ((p + 1 : ℚ) ^ k) = 2 * ((p + 1 : ℚ) ^ k / (k.factorial : ℚ)) := by ring
      _ ≤ 2 * (dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift) :=
        mul_le_mul_of_nonneg_left h_score_ge (by positivity)
  have h_pow_score : ((2 / (k.factorial : ℚ)) * ((p + 1 : ℚ) ^ k)) ^ (k + 1) ≤
      (2 * (dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift)) ^ (k + 1) := by
    have h_nonneg_lhs : 0 ≤ (2 / (k.factorial : ℚ)) * ((p + 1 : ℚ) ^ k) := by positivity
    exact pow_le_pow_left₀ h_nonneg_lhs h_score_mul (k + 1)
  rw [mul_pow] at h_pow_score
  have h_pow_comm1 : (((p + 1 : ℚ) ^ k) ^ (k + 1)) = (p + 1 : ℚ) ^ (k * (k + 1)) := by
    exact (pow_mul (p + 1 : ℚ) k (k + 1)).symm
  rw [h_pow_comm1] at h_pow_score
  have h_upper := wordPhaseStartStep_shifted_upper_pow fc parentWord hparent_count phaseShift p
  have h_step_nonneg : 0 ≤ (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) := by positivity
  have h_upper_pow : (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) ^ k ≤
      ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) * ((p + 1 : ℚ) ^ (k + 1))) ^ k :=
    pow_le_pow_left₀ h_step_nonneg h_upper k
  rw [mul_pow] at h_upper_pow
  have h_pow_comm2 : (((p + 1 : ℚ) ^ (k + 1)) ^ k) = (p + 1 : ℚ) ^ (k * (k + 1)) := by
    have h1 : (((p + 1 : ℚ) ^ (k + 1)) ^ k) = (p + 1 : ℚ) ^ ((k + 1) * k) := by
      exact (pow_mul (p + 1 : ℚ) (k + 1) k).symm
    have h2 : (k + 1) * k = k * (k + 1) := by ring
    rw [h1, h2]
  rw [h_pow_comm2] at h_upper_pow
  have h_denom_pos : 0 < (1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k := by
    have : 0 < C_len fc := C_len_pos fc
    positivity
  have h_low_step : bundle_c_low fc phaseShift * (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) ^ k ≤
      (2 / (k.factorial : ℚ)) ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := by
    unfold bundle_c_low
    have h_div_mul : (2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
        (((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) * (p + 1 : ℚ) ^ (k * (k + 1))) =
        (2 / (k.factorial : ℚ)) ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := by
      calc (2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
          (((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) * (p + 1 : ℚ) ^ (k * (k + 1))) =
          ((2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
            ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k)) * (p + 1 : ℚ) ^ (k * (k + 1)) := by ring
        _ = (2 / (k.factorial : ℚ)) ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := by
          rw [div_mul_cancel₀ _ (ne_of_gt h_denom_pos)]
    calc (2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
          (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) ^ k ≤
        (2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
          (((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) * (p + 1 : ℚ) ^ (k * (k + 1))) :=
        mul_le_mul_of_nonneg_left h_upper_pow (by positivity)
      _ = (2 / (k.factorial : ℚ)) ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := h_div_mul
  exact le_trans h_low_step h_pow_score

theorem score_upper_bound {k : ℕ} (fc : FullRankClock k) (delta c_zeta shift : ℚ)
    (phaseShift p : ℕ) :
    2 * (dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift) ≤
      (2 * (C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1))) * (p + 1 : ℚ) ^ k := by
  have h_dot := dotProduct_zeta_bundle_scaled_le fc.clock delta c_zeta (p + 1) phaseShift
  have h_p2_pow : (p + 1 + 1 : ℚ) ^ k ≤ (2 ^ k : ℚ) * (p + 1 : ℚ) ^ k := by
    have h1 : (p + 1 + 1 : ℚ) ≤ 2 * (p + 1 : ℚ) := by linarith
    have h2 : 0 ≤ (p + 1 + 1 : ℚ) := by positivity
    have h3 := pow_le_pow_left₀ h2 h1 k
    rw [mul_pow] at h3
    exact h3
  have h_C_nonneg : 0 ≤ C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) := by
    unfold C_zeta_sum
    have : 0 ≤ ∑ c : Fin (k + 1), |zeta_bundle_scaled fc.clock delta c_zeta c| :=
      Finset.sum_nonneg fun c _ => abs_nonneg _
    positivity
  have h_cast_p1 : ((p + 1 : ℕ) + 1 : ℚ) = (p + 1 + 1 : ℚ) := by push_cast; ring
  rw [h_cast_p1] at h_dot
  have h_dot_le : dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) ≤
      (C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k) * (p + 1 : ℚ) ^ k := by
    calc dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) ≤
        C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * ((p + 1 + 1 : ℚ) ^ k) := h_dot
      _ ≤ C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * ((2 ^ k : ℚ) * (p + 1 : ℚ) ^ k) :=
        mul_le_mul_of_nonneg_left h_p2_pow h_C_nonneg
      _ = (C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k) * (p + 1 : ℚ) ^ k := by ring
  have h_shift_le : shift ≤ (|shift| + 1) * (p + 1 : ℚ) ^ k := by
    have h1 : shift ≤ |shift| := le_abs_self shift
    have h2 : |shift| ≤ |shift| + 1 := by linarith
    have hp : 1 ≤ (p + 1 : ℚ) := by
      have : (0 : ℚ) ≤ (p : ℚ) := Nat.cast_nonneg p
      linarith
    have h3 : (1 : ℚ) ≤ (p + 1 : ℚ) ^ k := one_le_pow₀ hp
    have hpos : 0 ≤ |shift| + 1 := by positivity
    calc shift ≤ |shift| := h1
      _ ≤ |shift| + 1 := h2
      _ = (|shift| + 1) * 1 := by ring
      _ ≤ (|shift| + 1) * (p + 1 : ℚ) ^ k := mul_le_mul_of_nonneg_left h3 hpos
  have h_sum_le : dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift ≤
      (C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1)) * (p + 1 : ℚ) ^ k := by
    calc dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift ≤
        (C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k) * (p + 1 : ℚ) ^ k +
          (|shift| + 1) * (p + 1 : ℚ) ^ k := by linarith [h_dot_le, h_shift_le]
      _ = (C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1)) * (p + 1 : ℚ) ^ k := by ring
  calc 2 * (dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift) ≤
      2 * ((C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1)) * (p + 1 : ℚ) ^ k) :=
        mul_le_mul_of_nonneg_left h_sum_le (by positivity)
    _ = (2 * (C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1))) * (p + 1 : ℚ) ^ k := by ring

theorem bundle_hgap_high_unconditional {k : ℕ} (hw : 2 ≤ k) (fc : FullRankClock k)
    (delta c_P0 : ℚ) (phaseShift : ℕ) (hshift : k ≤ phaseShift)
    (parentWord : ℕ → List (Fin fc.clock.m))
    (hparent_count : ∀ σ : ℕ, wordCountVec (parentWord σ) = fc.clock.C.mulVec (binomBasis k σ))
    {m_rank : ℕ} (hm_rank : 0 < m_rank)
    (rank : Fin (bundleFullRankLift hw fc delta (canonicalCZeta fc.clock delta) c_P0).clock.m → Fin m_rank)
    (p : ℕ) :
    let c_zeta := canonicalCZeta fc.clock delta
    let shift := bundleBiasedScoreShift hw fc delta c_zeta c_P0 rank phaseShift
    (2 * (dotProduct (zeta_bundle_scaled fc.clock delta c_zeta)
      (binomBasis (k + 1) (p + 1 + phaseShift)) + shift)) ^ (k + 1) ≤
      bundle_c_high_gen fc delta c_zeta shift phaseShift *
        (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map
          (finSumFinEquiv : _ ≃ Fin (bundleFullRankLift hw fc delta c_zeta c_P0).clock.m)) p : ℚ) ^ k := by
  intro c_zeta shift
  have hshift_nonneg : 0 ≤ shift := bundleBiasedScoreShift_nonneg hw fc delta (canonicalCZeta fc.clock delta) c_P0 hm_rank rank phaseShift
  let C_base := 2 * (C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1))
  have hC_base_pos : 0 < C_base := by
    unfold C_base
    have : 0 < |shift| + 1 := by positivity
    have : 0 ≤ C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k := by
      unfold C_zeta_sum
      have : 0 ≤ ∑ c : Fin (k + 1), |zeta_bundle_scaled fc.clock delta c_zeta c| :=
        Finset.sum_nonneg fun c _ => abs_nonneg _
      positivity
    linarith
  have h_hw1 : 1 ≤ k := by omega
  have h_dot_ge := ceiling_canonicalCZeta_ge_choose h_hw1 fc.clock delta (p + 1 + phaseShift)
  have h_nonneg_score : 0 ≤ 2 * (dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift) := by
    have h1 : 0 ≤ (Nat.choose (p + 1 + phaseShift) k : ℚ) := by positivity
    have h2 : 0 ≤ dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) := by linarith
    have h3 : 0 ≤ dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift := by linarith [hshift_nonneg]
    linarith
  have h_bound_lin := score_upper_bound fc delta c_zeta shift phaseShift p
  have h_bound_pow : (2 * (dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift)) ^ (k + 1) ≤
      (C_base * (p + 1 : ℚ) ^ k) ^ (k + 1) :=
    pow_le_pow_left₀ h_nonneg_score h_bound_lin (k + 1)
  have h_rhs_rw : (C_base * (p + 1 : ℚ) ^ k) ^ (k + 1) = C_base ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := by
    rw [mul_pow]
    have h_pow_comm : (((p + 1 : ℚ) ^ k) ^ (k + 1)) = (p + 1 : ℚ) ^ (k * (k + 1)) := by
      exact (pow_mul (p + 1 : ℚ) k (k + 1)).symm
    rw [h_pow_comm]
  rw [h_rhs_rw] at h_bound_pow
  let phaseWord : ℕ → List (Fin (fc.clock.m + 1 + ((k + 1) + (k + 1)))) := fun q =>
    (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv
  have h_step_rw : (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map
      (finSumFinEquiv : _ ≃ Fin (bundleFullRankLift hw fc delta c_zeta c_P0).clock.m)) p : ℚ) =
      (wordPhaseStartStep phaseWord p : ℚ) := rfl
  rw [h_step_rw]
  cases p with
  | zero =>
    have h_p0_step : (wordPhaseStartStep phaseWord 0 : ℚ) = 1 := by
      unfold wordPhaseStartStep runStart
      push_cast
      simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    have hp0_pow : (↑(0 : ℕ) + 1 : ℚ) ^ (k * (k + 1)) = 1 := by ring
    rw [hp0_pow, mul_one] at h_bound_pow
    have h_denom_pos_nat : 0 < 2 ^ (k + 1) * (k + 1).factorial := by positivity
    have h_denom_ge_one : 1 ≤ ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) := by
      exact_mod_cast Nat.succ_le_of_lt h_denom_pos_nat
    have h_pow_denom_ge_one : 1 ≤ ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k :=
      one_le_pow₀ h_denom_ge_one
    have h_c_high_ge : C_base ^ (k + 1) ≤
        bundle_c_high_gen fc delta c_zeta shift phaseShift := by
      unfold bundle_c_high_gen
      calc C_base ^ (k + 1) = C_base ^ (k + 1) * 1 := by ring
        _ ≤ C_base ^ (k + 1) * ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k :=
          mul_le_mul_of_nonneg_left h_pow_denom_ge_one (by positivity)
    have h_trans := le_trans h_bound_pow h_c_high_ge
    rw [h_p0_step, one_pow, mul_one]
    exact h_trans
  | succ m =>
    have h_lower := wordPhaseStartStep_shifted_lower_pow fc parentWord hparent_count phaseShift hshift (m + 1)
    have h_denom_pos : 0 < ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) := by positivity
    have h_cast_m : ((m + 1 : ℕ) + 1 : ℚ) = (m + 1 + 1 : ℚ) := by push_cast; ring
    rw [h_cast_m] at h_lower
    have h_m1_le : (m + 1 + 1 : ℚ) ^ (k + 1) ≤ ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) * (wordPhaseStartStep phaseWord (m + 1) : ℚ) := by
      have h := (div_le_iff₀ h_denom_pos).mp h_lower
      linarith [h]
    have h_m1_pow_k : ((m + 1 + 1 : ℚ) ^ (k + 1)) ^ k ≤
        (((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) * (wordPhaseStartStep phaseWord (m + 1) : ℚ)) ^ k :=
      pow_le_pow_left₀ (by positivity) h_m1_le k
    rw [mul_pow] at h_m1_pow_k
    have h_pow_comm2 : (((m + 1 + 1 : ℚ) ^ (k + 1)) ^ k) = (m + 1 + 1 : ℚ) ^ (k * (k + 1)) := by
      have h1 : (((m + 1 + 1 : ℚ) ^ (k + 1)) ^ k) = (m + 1 + 1 : ℚ) ^ ((k + 1) * k) := by
        exact (pow_mul (m + 1 + 1 : ℚ) (k + 1) k).symm
      have h2 : (k + 1) * k = k * (k + 1) := by ring
      rw [h1, h2]
    rw [h_pow_comm2] at h_m1_pow_k
    have h_step_bound : C_base ^ (k + 1) * (m + 1 + 1 : ℚ) ^ (k * (k + 1)) ≤
        (C_base ^ (k + 1) * ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k) *
          (wordPhaseStartStep phaseWord (m + 1) : ℚ) ^ k := by
      calc C_base ^ (k + 1) * (m + 1 + 1 : ℚ) ^ (k * (k + 1)) ≤
          C_base ^ (k + 1) * ((((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k) * (wordPhaseStartStep phaseWord (m + 1) : ℚ) ^ k) :=
            mul_le_mul_of_nonneg_left h_m1_pow_k (by positivity)
        _ = (C_base ^ (k + 1) * ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k) *
              (wordPhaseStartStep phaseWord (m + 1) : ℚ) ^ k := by ring
    rw [h_cast_m] at h_bound_pow
    exact le_trans h_bound_pow h_step_bound

theorem score_upper_bound_admissible {k : ℕ} (fc : FullRankClock k) (b : Fin fc.clock.m)
    (H0 ch delta c_zeta shift : ℚ) (phaseShift p : ℕ) :
    2 * (dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift) ≤
      (2 * (C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1))) * (p + 1 : ℚ) ^ k := by
  have h_dot := dotProduct_zeta_admissible_scaled_le fc.clock b H0 ch delta c_zeta (p + 1) phaseShift
  have h_p2_pow : (p + 1 + 1 : ℚ) ^ k ≤ (2 ^ k : ℚ) * (p + 1 : ℚ) ^ k := by
    have h1 : (p + 1 + 1 : ℚ) ≤ 2 * (p + 1 : ℚ) := by linarith
    have h2 : 0 ≤ (p + 1 + 1 : ℚ) := by positivity
    have h3 := pow_le_pow_left₀ h2 h1 k
    rw [mul_pow] at h3
    exact h3
  have h_C_nonneg : 0 ≤ C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) := by
    unfold C_zeta_sum_admissible
    have : 0 ≤ ∑ c : Fin (k + 1), |zeta_admissible_scaled fc.clock b H0 ch delta c_zeta c| :=
      Finset.sum_nonneg fun c _ => abs_nonneg _
    positivity
  have h_cast_p1 : ((p + 1 : ℕ) + 1 : ℚ) = (p + 1 + 1 : ℚ) := by push_cast; ring
  rw [h_cast_p1] at h_dot
  have h_dot_le : dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) ≤
      (C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k) * (p + 1 : ℚ) ^ k := by
    calc dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) ≤
        C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * ((p + 1 + 1 : ℚ) ^ k) := h_dot
      _ ≤ C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * ((2 ^ k : ℚ) * (p + 1 : ℚ) ^ k) :=
        mul_le_mul_of_nonneg_left h_p2_pow h_C_nonneg
      _ = (C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k) * (p + 1 : ℚ) ^ k := by ring
  have h_shift_le : shift ≤ (|shift| + 1) * (p + 1 : ℚ) ^ k := by
    have h1 : shift ≤ |shift| := le_abs_self shift
    have h2 : |shift| ≤ |shift| + 1 := by linarith
    have hp : 1 ≤ (p + 1 : ℚ) := by
      have : (0 : ℚ) ≤ (p : ℚ) := Nat.cast_nonneg p
      linarith
    have h3 : (1 : ℚ) ≤ (p + 1 : ℚ) ^ k := one_le_pow₀ hp
    have hpos : 0 ≤ |shift| + 1 := by positivity
    calc shift ≤ |shift| := h1
      _ ≤ |shift| + 1 := h2
      _ = (|shift| + 1) * 1 := by ring
      _ ≤ (|shift| + 1) * (p + 1 : ℚ) ^ k := mul_le_mul_of_nonneg_left h3 hpos
  have h_sum_le : dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift ≤
      (C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1)) * (p + 1 : ℚ) ^ k := by
    calc dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift ≤
        (C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k) * (p + 1 : ℚ) ^ k +
          (|shift| + 1) * (p + 1 : ℚ) ^ k := by linarith [h_dot_le, h_shift_le]
      _ = (C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1)) * (p + 1 : ℚ) ^ k := by ring
  calc 2 * (dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift) ≤
      2 * ((C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1)) * (p + 1 : ℚ) ^ k) :=
        mul_le_mul_of_nonneg_left h_sum_le (by positivity)
    _ = (2 * (C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1))) * (p + 1 : ℚ) ^ k := by ring

theorem admissible_hgap_low_unconditional {k : ℕ} (hw : 2 ≤ k) (fc : FullRankClock k)
    (b : Fin fc.clock.m) (H0 ch delta c_P0 : ℚ) (a_old : Fin (fc.clock.m + 1) → ℚ)
    (phaseShift : ℕ) (hshift : k ≤ phaseShift)
    (parentWord : ℕ → List (Fin fc.clock.m))
    (hparent_count : ∀ σ : ℕ, wordCountVec (parentWord σ) = fc.clock.C.mulVec (binomBasis k σ))
    {m_rank : ℕ} (hm_rank : 0 < m_rank)
    (rank : Fin (admissibleScaledFullRankLift hw fc b H0 ch delta
      (canonicalCZeta_admissible fc.clock b H0 ch delta) c_P0 a_old).clock.m → Fin m_rank)
    (p : ℕ) :
    let c_zeta := canonicalCZeta_admissible fc.clock b H0 ch delta
    let shift := admissibleBiasedScoreShift hw fc b H0 ch delta c_zeta c_P0 a_old rank phaseShift
    bundle_c_low fc phaseShift *
      (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map
        (rotLeaderEquiv (fc.clock.m + 1) ((k + 1) + (k + 1)) : _ ≃ Fin (admissibleScaledFullRankLift hw fc b H0 ch delta c_zeta c_P0 a_old).clock.m)) (p + 1) : ℚ) ^ k ≤
      (2 * (dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta)
        (binomBasis (k + 1) (p + phaseShift)) + shift)) ^ (k + 1) := by
  intro c_zeta shift
  have hshift_nonneg : 0 ≤ shift := admissibleBiasedScoreShift_nonneg hw fc b H0 ch delta c_zeta c_P0 a_old hm_rank rank phaseShift
  have h_hw1 : 1 ≤ k := by omega
  have h_dot_ge := ceiling_canonicalCZeta_admissible_ge_choose h_hw1 fc.clock b H0 ch delta (p + phaseShift)
  have h_choose_le : (p + 1 : ℚ) ^ k ≤ (k.factorial : ℚ) * (Nat.choose (p + phaseShift) k : ℚ) := by
    exact_mod_cast pow_le_factorial_mul_choose_shifted k phaseShift hshift p
  have h_fact_pos : 0 < (k.factorial : ℚ) := by positivity
  have h_choose_div : (p + 1 : ℚ) ^ k / (k.factorial : ℚ) ≤ (Nat.choose (p + phaseShift) k : ℚ) := by
    rw [div_le_iff₀ h_fact_pos]
    linarith [h_choose_le]
  have h_score_ge : (p + 1 : ℚ) ^ k / (k.factorial : ℚ) ≤
      dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift := by
    calc (p + 1 : ℚ) ^ k / (k.factorial : ℚ) ≤ (Nat.choose (p + phaseShift) k : ℚ) := h_choose_div
      _ ≤ 1 + (Nat.choose (p + phaseShift) k : ℚ) := by linarith
      _ ≤ dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) := h_dot_ge
      _ ≤ dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift := by linarith [hshift_nonneg]
  have h_score_mul : (2 / (k.factorial : ℚ)) * ((p + 1 : ℚ) ^ k) ≤
      2 * (dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift) := by
    calc (2 / (k.factorial : ℚ)) * ((p + 1 : ℚ) ^ k) = 2 * ((p + 1 : ℚ) ^ k / (k.factorial : ℚ)) := by ring
      _ ≤ 2 * (dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift) :=
        mul_le_mul_of_nonneg_left h_score_ge (by positivity)
  have h_pow_score : ((2 / (k.factorial : ℚ)) * ((p + 1 : ℚ) ^ k)) ^ (k + 1) ≤
      (2 * (dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift)) ^ (k + 1) := by
    have h_nonneg_lhs : 0 ≤ (2 / (k.factorial : ℚ)) * ((p + 1 : ℚ) ^ k) := by positivity
    exact pow_le_pow_left₀ h_nonneg_lhs h_score_mul (k + 1)
  rw [mul_pow] at h_pow_score
  have h_pow_comm1 : (((p + 1 : ℚ) ^ k) ^ (k + 1)) = (p + 1 : ℚ) ^ (k * (k + 1)) := by
    exact (pow_mul (p + 1 : ℚ) k (k + 1)).symm
  rw [h_pow_comm1] at h_pow_score
  let rotEquiv := rotLeaderEquiv (fc.clock.m + 1) ((k + 1) + (k + 1))
  have h_step_equiv :
      (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map rotEquiv) (p + 1) : ℚ) =
      (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) := by
    unfold wordPhaseStartStep runStart
    simp only [List.length_map]
  rw [h_step_equiv]
  have h_upper := wordPhaseStartStep_shifted_upper_pow fc parentWord hparent_count phaseShift p
  have h_step_nonneg : 0 ≤ (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) := by positivity
  have h_upper_pow : (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) ^ k ≤
      ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) * ((p + 1 : ℚ) ^ (k + 1))) ^ k :=
    pow_le_pow_left₀ h_step_nonneg h_upper k
  rw [mul_pow] at h_upper_pow
  have h_pow_comm2 : (((p + 1 : ℚ) ^ (k + 1)) ^ k) = (p + 1 : ℚ) ^ (k * (k + 1)) := by
    have h1 : (((p + 1 : ℚ) ^ (k + 1)) ^ k) = (p + 1 : ℚ) ^ ((k + 1) * k) := by
      exact (pow_mul (p + 1 : ℚ) (k + 1) k).symm
    have h2 : (k + 1) * k = k * (k + 1) := by ring
    rw [h1, h2]
  rw [h_pow_comm2] at h_upper_pow
  have h_denom_pos : 0 < (1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k := by
    have : 0 < C_len fc := C_len_pos fc
    positivity
  have h_low_step : bundle_c_low fc phaseShift * (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) ^ k ≤
      (2 / (k.factorial : ℚ)) ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := by
    unfold bundle_c_low
    have h_div_mul : (2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
        (((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) * (p + 1 : ℚ) ^ (k * (k + 1))) =
        (2 / (k.factorial : ℚ)) ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := by
      calc (2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
          (((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) * (p + 1 : ℚ) ^ (k * (k + 1))) =
          ((2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
            ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k)) * (p + 1 : ℚ) ^ (k * (k + 1)) := by ring
        _ = (2 / (k.factorial : ℚ)) ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := by
          rw [div_mul_cancel₀ _ (ne_of_gt h_denom_pos)]
    calc (2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
          (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) ^ k ≤
        (2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
          (((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) * (p + 1 : ℚ) ^ (k * (k + 1))) :=
        mul_le_mul_of_nonneg_left h_upper_pow (by positivity)
      _ = (2 / (k.factorial : ℚ)) ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := h_div_mul
  exact le_trans h_low_step h_pow_score

theorem admissible_hgap_high_unconditional {k : ℕ} (hw : 2 ≤ k) (fc : FullRankClock k)
    (b : Fin fc.clock.m) (H0 ch delta c_P0 : ℚ) (a_old : Fin (fc.clock.m + 1) → ℚ)
    (phaseShift : ℕ) (hshift : k ≤ phaseShift)
    (parentWord : ℕ → List (Fin fc.clock.m))
    (hparent_count : ∀ σ : ℕ, wordCountVec (parentWord σ) = fc.clock.C.mulVec (binomBasis k σ))
    {m_rank : ℕ} (hm_rank : 0 < m_rank)
    (rank : Fin (admissibleScaledFullRankLift hw fc b H0 ch delta
      (canonicalCZeta_admissible fc.clock b H0 ch delta) c_P0 a_old).clock.m → Fin m_rank)
    (p : ℕ) :
    let c_zeta := canonicalCZeta_admissible fc.clock b H0 ch delta
    let shift := admissibleBiasedScoreShift hw fc b H0 ch delta c_zeta c_P0 a_old rank phaseShift
    (2 * (dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta)
      (binomBasis (k + 1) (p + 1 + phaseShift)) + shift)) ^ (k + 1) ≤
      admissible_c_high_gen fc b H0 ch delta c_zeta shift phaseShift *
        (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map
          (rotLeaderEquiv (fc.clock.m + 1) ((k + 1) + (k + 1)) : _ ≃ Fin (admissibleScaledFullRankLift hw fc b H0 ch delta c_zeta c_P0 a_old).clock.m)) p : ℚ) ^ k := by
  intro c_zeta shift
  have hshift_nonneg : 0 ≤ shift := admissibleBiasedScoreShift_nonneg hw fc b H0 ch delta c_zeta c_P0 a_old hm_rank rank phaseShift
  let C_base := 2 * (C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1))
  have h_nonneg_score : 0 ≤ 2 * (dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift) := by
    have h_hw1 : 1 ≤ k := by omega
    have h_dot_ge := ceiling_canonicalCZeta_admissible_ge_choose h_hw1 fc.clock b H0 ch delta (p + 1 + phaseShift)
    have h1 : 0 ≤ (Nat.choose (p + 1 + phaseShift) k : ℚ) := by positivity
    have h2 : 0 ≤ dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) := by linarith
    have h3 : 0 ≤ dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift := by linarith [hshift_nonneg]
    linarith
  have h_bound_lin := score_upper_bound_admissible fc b H0 ch delta c_zeta shift phaseShift p
  have h_bound_pow : (2 * (dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift)) ^ (k + 1) ≤
      (C_base * (p + 1 : ℚ) ^ k) ^ (k + 1) :=
    pow_le_pow_left₀ h_nonneg_score h_bound_lin (k + 1)
  have h_rhs_rw : (C_base * (p + 1 : ℚ) ^ k) ^ (k + 1) = C_base ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := by
    rw [mul_pow]
    have h_pow_comm : (((p + 1 : ℚ) ^ k) ^ (k + 1)) = (p + 1 : ℚ) ^ (k * (k + 1)) := by
      exact (pow_mul (p + 1 : ℚ) k (k + 1)).symm
    rw [h_pow_comm]
  rw [h_rhs_rw] at h_bound_pow
  have hC_base_nonneg : 0 ≤ C_base := by
    have : 0 ≤ C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k := by
      unfold C_zeta_sum_admissible
      have : 0 ≤ ∑ c : Fin (k + 1), |zeta_admissible_scaled fc.clock b H0 ch delta c_zeta c| :=
        Finset.sum_nonneg fun c _ => abs_nonneg _
      positivity
    linarith [abs_nonneg shift]
  have hC_base_pow_nonneg : 0 ≤ C_base ^ (k + 1) := by
    exact pow_nonneg hC_base_nonneg (k + 1)
  let rotEquiv := rotLeaderEquiv (fc.clock.m + 1) ((k + 1) + (k + 1))
  have h_step_equiv :
      (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map rotEquiv) p : ℚ) =
      (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) p : ℚ) := by
    unfold wordPhaseStartStep runStart
    simp only [List.length_map]
  let phaseWord : ℕ → List (Fin (fc.clock.m + 1 + ((k + 1) + (k + 1)))) := fun q =>
    (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv
  have h_step_rw : (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map rotEquiv) p : ℚ) =
      (wordPhaseStartStep phaseWord p : ℚ) := h_step_equiv
  rw [h_step_rw]
  cases p with
  | zero =>
    have h_p0_step : (wordPhaseStartStep phaseWord 0 : ℚ) = 1 := by
      unfold wordPhaseStartStep runStart
      push_cast
      simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    have hp0_pow : (↑(0 : ℕ) + 1 : ℚ) ^ (k * (k + 1)) = 1 := by ring
    rw [hp0_pow, mul_one] at h_bound_pow
    have h_denom_pos_nat : 0 < 2 ^ (k + 1) * (k + 1).factorial := by positivity
    have h_denom_ge_one : 1 ≤ ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) := by
      exact_mod_cast Nat.succ_le_of_lt h_denom_pos_nat
    have h_pow_denom_ge_one : 1 ≤ ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k :=
      one_le_pow₀ h_denom_ge_one
    have h_c_high_ge : C_base ^ (k + 1) ≤
        admissible_c_high_gen fc b H0 ch delta c_zeta shift phaseShift := by
      unfold admissible_c_high_gen
      calc C_base ^ (k + 1) = C_base ^ (k + 1) * 1 := by ring
        _ ≤ C_base ^ (k + 1) * ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k :=
          mul_le_mul_of_nonneg_left h_pow_denom_ge_one hC_base_pow_nonneg
    have h_trans := le_trans h_bound_pow h_c_high_ge
    rw [h_p0_step, one_pow, mul_one]
    exact h_trans
  | succ m =>
    have h_lower := wordPhaseStartStep_shifted_lower_pow fc parentWord hparent_count phaseShift hshift (m + 1)
    have h_denom_pos : 0 < ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) := by positivity
    have h_cast_m : ((m + 1 : ℕ) + 1 : ℚ) = (m + 1 + 1 : ℚ) := by push_cast; ring
    rw [h_cast_m] at h_lower
    have h_m1_le : (m + 1 + 1 : ℚ) ^ (k + 1) ≤ ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) * (wordPhaseStartStep phaseWord (m + 1) : ℚ) := by
      have h := (div_le_iff₀ h_denom_pos).mp h_lower
      linarith [h]
    have h_m1_pow_k : ((m + 1 + 1 : ℚ) ^ (k + 1)) ^ k ≤
        (((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) * (wordPhaseStartStep phaseWord (m + 1) : ℚ)) ^ k :=
      pow_le_pow_left₀ (by positivity) h_m1_le k
    rw [mul_pow] at h_m1_pow_k
    have h_pow_comm2 : (((m + 1 + 1 : ℚ) ^ (k + 1)) ^ k) = (m + 1 + 1 : ℚ) ^ (k * (k + 1)) := by
      have h1 : (((m + 1 + 1 : ℚ) ^ (k + 1)) ^ k) = (m + 1 + 1 : ℚ) ^ ((k + 1) * k) := by
        exact (pow_mul (m + 1 + 1 : ℚ) (k + 1) k).symm
      have h2 : (k + 1) * k = k * (k + 1) := by ring
      rw [h1, h2]
    rw [h_pow_comm2] at h_m1_pow_k
    have h_step_bound : C_base ^ (k + 1) * (m + 1 + 1 : ℚ) ^ (k * (k + 1)) ≤
        (C_base ^ (k + 1) * ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k) *
          (wordPhaseStartStep phaseWord (m + 1) : ℚ) ^ k := by
      calc C_base ^ (k + 1) * (m + 1 + 1 : ℚ) ^ (k * (k + 1)) ≤
          C_base ^ (k + 1) * ((((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k) * (wordPhaseStartStep phaseWord (m + 1) : ℚ) ^ k) :=
            mul_le_mul_of_nonneg_left h_m1_pow_k hC_base_pow_nonneg
        _ = (C_base ^ (k + 1) * ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k) *
              (wordPhaseStartStep phaseWord (m + 1) : ℚ) ^ k := by ring
    rw [h_cast_m] at h_bound_pow
    exact le_trans h_bound_pow h_step_bound

/-- Unconditional gap-free chronology specification for the four-stage scaled bundle lift. -/
structure BundleChronologySpec {k : ℕ} (hw : 2 ≤ k) (fc : FullRankClock k)
    (delta c_P0 : ℚ) where
  phaseShift : ℕ
  hshift : k ≤ phaseShift
  parentWord : ℕ → List (Fin fc.clock.m)
  hparent_count : ∀ σ : ℕ, wordCountVec (parentWord σ) = fc.clock.C.mulVec (binomBasis k σ)
  m_rank : ℕ
  hm_rank : 0 < m_rank
  rank : Fin (bundleFullRankLift hw fc delta (canonicalCZeta fc.clock delta) c_P0).clock.m → Fin m_rank
  hpriority_raw : ∀ p : ℕ,
    IsValidPriorityWord
      (liftedGameMat (adjoinGatewayEndpointG fc.clock.G fc.clock.v)
        (P_bundle fc.clock fc.L_C delta (canonicalCZeta fc.clock delta) c_P0)
        (J_bundle fc.clock delta (canonicalCZeta fc.clock delta)))
      ((liftedScoreMat (adjoinGatewayEndpointG fc.clock.G fc.clock.v)
        (J_bundle fc.clock delta (canonicalCZeta fc.clock delta)) (S_bundle fc.clock 0 delta)
        (X_gateway fc.clock) (M_coupled k)
        (zeta_bundle_scaled fc.clock delta (canonicalCZeta fc.clock delta))).mulVec
          (binomBasis (k + 1) (p + phaseShift)))
      (fun i => rank (finSumFinEquiv i))
      (rawFourStageWord fc.clock parentWord (p + phaseShift))

def BundleChronologySpec.toBundleLiftSpec {k : ℕ} {hw : 2 ≤ k} {fc : FullRankClock k}
    {delta c_P0 : ℚ} (spec : BundleChronologySpec hw fc delta c_P0) :
    BundleLiftSpec hw fc delta (canonicalCZeta fc.clock delta) c_P0 where
  phaseShift := spec.phaseShift
  parentWord := spec.parentWord
  hparent_count := spec.hparent_count
  m_rank := spec.m_rank
  hm_rank := spec.hm_rank
  rank := spec.rank
  hpriority_raw := spec.hpriority_raw
  c_low := bundle_c_low fc spec.phaseShift
  c_high := bundle_c_high_gen fc delta (canonicalCZeta fc.clock delta)
    (bundleBiasedScoreShift hw fc delta (canonicalCZeta fc.clock delta) c_P0 spec.rank spec.phaseShift)
    spec.phaseShift
  hc_low_pos := bundle_c_low_pos fc spec.phaseShift
  hc_high_pos := bundle_c_high_gen_pos fc delta (canonicalCZeta fc.clock delta)
    (bundleBiasedScoreShift hw fc delta (canonicalCZeta fc.clock delta) c_P0 spec.rank spec.phaseShift)
    spec.phaseShift
  hgap_low := fun p => bundle_hgap_low_unconditional hw fc delta c_P0 spec.phaseShift spec.hshift
    spec.parentWord spec.hparent_count spec.hm_rank spec.rank p
  hgap_high := fun p => bundle_hgap_high_unconditional hw fc delta c_P0 spec.phaseShift spec.hshift
    spec.parentWord spec.hparent_count spec.hm_rank spec.rank p

def RealizedClock.ofBundleChronology {k : ℕ} (hw : 2 ≤ k) (fc : FullRankClock k)
    (delta c_P0 : ℚ) (spec : BundleChronologySpec hw fc delta c_P0) : RealizedClock (k + 1) :=
  RealizedClock.ofBundleLift hw fc delta (canonicalCZeta fc.clock delta) c_P0 spec.toBundleLiftSpec

structure AdmissibleChronologySpec {k : ℕ} (hw : 2 ≤ k) (fc : FullRankClock k)
    (b : Fin fc.clock.m) (H0 ch delta c_P0 : ℚ) (a_old : Fin (fc.clock.m + 1) → ℚ) where
  phaseShift : ℕ
  hshift : k ≤ phaseShift
  parentWord : ℕ → List (Fin fc.clock.m)
  hparent_count : ∀ σ : ℕ, wordCountVec (parentWord σ) = fc.clock.C.mulVec (binomBasis k σ)
  m_rank : ℕ
  hm_rank : 0 < m_rank
  rank : Fin (admissibleScaledFullRankLift hw fc b H0 ch delta
    (canonicalCZeta_admissible fc.clock b H0 ch delta) c_P0 a_old).clock.m → Fin m_rank
  hpriority_raw : ∀ p : ℕ,
    IsValidPriorityWord
      (liftedGameMat (AdjoinLeaderEndpointG fc.clock.G b fc.clock.v)
        (P_admissible_scaled fc.clock b H0 ch delta
          (canonicalCZeta_admissible fc.clock b H0 ch delta) c_P0 a_old fc.L_C)
        (J_admissible_scaled fc.clock b H0 ch delta (canonicalCZeta_admissible fc.clock b H0 ch delta)))
      ((liftedScoreMat (AdjoinLeaderEndpointG fc.clock.G b fc.clock.v)
        (J_admissible_scaled fc.clock b H0 ch delta (canonicalCZeta_admissible fc.clock b H0 ch delta))
        (S_admissible fc.clock b H0 ch delta)
        (X_gateway fc.clock) (M_coupled k)
        (zeta_admissible_scaled fc.clock b H0 ch delta
          (canonicalCZeta_admissible fc.clock b H0 ch delta))).mulVec
          (binomBasis (k + 1) (p + phaseShift)))
      (fun i => rank ((rotLeaderEquiv (fc.clock.m + 1) ((k + 1) + (k + 1))) i))
      (rawFourStageWord fc.clock parentWord (p + phaseShift))

def AdmissibleChronologySpec.toAdmissibleLiftSpec {k : ℕ} {hw : 2 ≤ k} {fc : FullRankClock k}
    {b : Fin fc.clock.m} {H0 ch delta c_P0 : ℚ} {a_old : Fin (fc.clock.m + 1) → ℚ}
    (spec : AdmissibleChronologySpec hw fc b H0 ch delta c_P0 a_old) :
    AdmissibleLiftSpec hw fc b H0 ch delta (canonicalCZeta_admissible fc.clock b H0 ch delta) c_P0 a_old where
  phaseShift := spec.phaseShift
  parentWord := spec.parentWord
  hparent_count := spec.hparent_count
  m_rank := spec.m_rank
  hm_rank := spec.hm_rank
  rank := spec.rank
  hpriority_raw := spec.hpriority_raw
  c_low := bundle_c_low fc spec.phaseShift
  c_high := admissible_c_high_gen fc b H0 ch delta (canonicalCZeta_admissible fc.clock b H0 ch delta)
    (admissibleBiasedScoreShift hw fc b H0 ch delta (canonicalCZeta_admissible fc.clock b H0 ch delta) c_P0 a_old spec.rank spec.phaseShift)
    spec.phaseShift
  hc_low_pos := bundle_c_low_pos fc spec.phaseShift
  hc_high_pos := admissible_c_high_gen_pos fc b H0 ch delta (canonicalCZeta_admissible fc.clock b H0 ch delta)
    (admissibleBiasedScoreShift hw fc b H0 ch delta (canonicalCZeta_admissible fc.clock b H0 ch delta) c_P0 a_old spec.rank spec.phaseShift)
    spec.phaseShift
  hgap_low := fun p => admissible_hgap_low_unconditional hw fc b H0 ch delta c_P0 a_old spec.phaseShift spec.hshift
    spec.parentWord spec.hparent_count spec.hm_rank spec.rank p
  hgap_high := fun p => admissible_hgap_high_unconditional hw fc b H0 ch delta c_P0 a_old spec.phaseShift spec.hshift
    spec.parentWord spec.hparent_count spec.hm_rank spec.rank p

def RealizedClock.ofAdmissibleChronology {k : ℕ} (hw : 2 ≤ k) (fc : FullRankClock k)
    (b : Fin fc.clock.m) (H0 ch delta c_P0 : ℚ) (a_old : Fin (fc.clock.m + 1) → ℚ)
    (spec : AdmissibleChronologySpec hw fc b H0 ch delta c_P0 a_old) : RealizedClock (k + 1) :=
  RealizedClock.ofAdmissibleLift hw fc b H0 ch delta
    (canonicalCZeta_admissible fc.clock b H0 ch delta) c_P0 a_old spec.toAdmissibleLiftSpec

theorem all_orders_admissible_chronology_karlin_theorem (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (lifts : ∀ d : ℕ,
      AdmissibleChronologySpec (by omega)
        (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d)
        ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
        (H0 d) (ch d) (delta d) (c_P0 d) (fun _ => 1))
    (hc_zeta : ∀ d : ℕ, c_zeta d = canonicalCZeta_admissible (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩ (H0 d) (ch d) (delta d))
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  have lifts' : ∀ d : ℕ,
      AdmissibleLiftSpec (by omega)
        (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d)
        ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
        (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) := by
    intro d
    have hspec := (lifts d).toAdmissibleLiftSpec
    rw [hc_zeta d]
    exact hspec
  exact all_orders_admissible_realized_karlin_theorem H0 ch delta c_zeta c_P0 lifts' k hk

/-!
## Section 3: Plumbing Elimination & The 1-Field Pure Admissible Chronology Spec
-/

-- `rpsPhaseWord` and `wordCountVec_rpsPhaseWord` are now provided by `Karlin.AdmissibleLift`.

/-- Recursive closed-form phase word family for the admissible full-rank clock family. -/
def admissiblePhaseWordFamily (H0 ch delta c_zeta c_P0 : ℕ → ℚ) :
    (d : ℕ) → ℕ → List (Fin (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m)
  | 0, q => rpsPhaseWord q
  | d + 1, q =>
      (rawFourStageWord (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
        (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) q).map
        (rotLeaderEquiv ((admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m + 1)
          ((d + 2 + 1) + (d + 2 + 1)))

/-- Unconditional play-count vector identity for the recursive admissible phase word family. -/
theorem wordCountVec_admissiblePhaseWordFamily (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (d : ℕ) (q : ℕ) :
    wordCountVec (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d q) =
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.C.mulVec (binomBasis (d + 2) q) := by
  induction d generalizing q with
  | zero =>
      exact wordCountVec_rpsPhaseWord q
  | succ d ih =>
      dsimp only [admissiblePhaseWordFamily]
      set e := rotLeaderEquiv ((admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m + 1)
        ((d + 2 + 1) + (d + 2 + 1))
      ext x
      rw [wordCountVec_map_equiv e]
      have hraw := congr_fun (wordCountVec_rawFourStageWord
        (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
        (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) ih q) (e.symm x)
      rw [hraw]
      rfl

/-- Priority stage rank routing parent actions, gateway endpoint, and reset actions. -/
def admissibleStageRank (m w : ℕ) (parent_rank : Fin m → Fin m) :
    Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → Fin ((m + 1) + ((w + 1) + (w + 1)))
  | Sum.inl u =>
      match (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).symm u with
      | Sum.inl i => ⟨(parent_rank i).val, by omega⟩
      | Sum.inr _ => ⟨m + ((w + 1) + (w + 1)), by omega⟩
  | Sum.inr r => ⟨m + ((w + 1) + (w + 1)) - 1 - r.val, by omega⟩

/-- Recursive closed-form priority rank family for the admissible full-rank clock family. -/
def admissiblePriorityRankFamily (H0 ch delta c_zeta c_P0 : ℕ → ℚ) :
    (d : ℕ) →
      Fin (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m →
      Fin (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m
  | 0 => id
  | d + 1 => fun i =>
      admissibleStageRank
        (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m
        (d + 2)
        (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
        ((rotLeaderEquiv ((admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m + 1)
          ((d + 2 + 1) + (d + 2 + 1))).symm i)

/-- Grounded 1-field pure admissible chronology specification containing only `hpriority_raw`. -/
structure PureAdmissibleChronologySpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hpriority_raw : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let cz := canonicalCZeta_admissible fc.clock b (H0 d) (ch d) (delta d)
    IsValidPriorityWord
      (liftedGameMat (AdjoinLeaderEndpointG fc.clock.G b fc.clock.v)
        (P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) cz (c_P0 d) (fun _ => 1) fc.L_C)
        (J_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) cz))
      ((liftedScoreMat (AdjoinLeaderEndpointG fc.clock.G b fc.clock.v)
        (J_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) cz)
        (S_admissible fc.clock b (H0 d) (ch d) (delta d))
        (X_gateway fc.clock) (M_coupled (d + 2))
        (zeta_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) cz)).mulVec
          (binomBasis (d + 3) (p + (d + 2))))
      (admissibleStageRank fc.clock.m (d + 2) (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d))
      (rawFourStageWord fc.clock (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (p + (d + 2)))

/-- Automatic plumbing conversion from `PureAdmissibleChronologySpec` to `AdmissibleChronologySpec`. -/
def PureAdmissibleChronologySpec.toAdmissibleChronologySpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ)
    (spec : PureAdmissibleChronologySpec H0 ch delta c_zeta c_P0 d) :
    AdmissibleChronologySpec (by omega)
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d)
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) (c_P0 d) (fun _ => 1) where
  phaseShift := d + 2
  hshift := le_rfl
  parentWord := admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d
  hparent_count := wordCountVec_admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d
  m_rank := ((admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m + 1) + ((d + 2 + 1) + (d + 2 + 1))
  hm_rank := by omega
  rank := fun i =>
    admissibleStageRank
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m
      (d + 2)
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      ((rotLeaderEquiv ((admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m + 1)
        ((d + 2 + 1) + (d + 2 + 1))).symm i)
  hpriority_raw := fun p => by
    have hp := spec.hpriority_raw p
    simpa only [Equiv.symm_apply_apply] using hp

/-- **All-Orders Pure Admissible Karlin Theorem**:
    Duality gap scaling across all polynomial orders $k \ge 2$ governed by 1-field pure admissible specs. -/
theorem all_orders_pure_admissible_karlin_theorem (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (pure_lifts : ∀ d : ℕ, PureAdmissibleChronologySpec H0 ch delta c_zeta c_P0 d)
    (hc_zeta : ∀ d : ℕ, c_zeta d = canonicalCZeta_admissible (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩ (H0 d) (ch d) (delta d))
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  have lifts : ∀ d : ℕ,
      AdmissibleChronologySpec (by omega)
        (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d)
        ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
        (H0 d) (ch d) (delta d) (c_P0 d) (fun _ => 1) :=
    fun d => (pure_lifts d).toAdmissibleChronologySpec H0 ch delta c_zeta c_P0 d
  exact all_orders_admissible_chronology_karlin_theorem H0 ch delta c_zeta c_P0 lifts hc_zeta k hk

/-- Recursive closed-form phase word family for the scaled bundle full-rank clock family. -/
def bundlePhaseWordFamily (delta c_zeta c_P0 : ℕ → ℚ) :
    (d : ℕ) → ℕ → List (Fin (bundleFullRankClockFamily delta c_zeta c_P0 d).clock.m)
  | 0, q => rpsPhaseWord q
  | d + 1, q =>
      (rawFourStageWord (bundleFullRankClockFamily delta c_zeta c_P0 d).clock
        (bundlePhaseWordFamily delta c_zeta c_P0 d) q).map finSumFinEquiv

/-- Unconditional play-count vector identity for the recursive bundle phase word family. -/
theorem wordCountVec_bundlePhaseWordFamily (delta c_zeta c_P0 : ℕ → ℚ)
    (d : ℕ) (q : ℕ) :
    wordCountVec (bundlePhaseWordFamily delta c_zeta c_P0 d q) =
      (bundleFullRankClockFamily delta c_zeta c_P0 d).clock.C.mulVec (binomBasis (d + 2) q) := by
  induction d generalizing q with
  | zero =>
      exact wordCountVec_rpsPhaseWord q
  | succ d ih =>
      dsimp only [bundlePhaseWordFamily]
      ext x
      rw [wordCountVec_map_equiv finSumFinEquiv]
      have hraw := congr_fun (wordCountVec_rawFourStageWord
        (bundleFullRankClockFamily delta c_zeta c_P0 d).clock
        (bundlePhaseWordFamily delta c_zeta c_P0 d) ih q) (finSumFinEquiv.symm x)
      rw [hraw]
      rfl

/-- Recursive closed-form priority rank family for the scaled bundle full-rank clock family. -/
def bundlePriorityRankFamily (delta c_zeta c_P0 : ℕ → ℚ) :
    (d : ℕ) →
      Fin (bundleFullRankClockFamily delta c_zeta c_P0 d).clock.m →
      Fin (bundleFullRankClockFamily delta c_zeta c_P0 d).clock.m
  | 0 => id
  | d + 1 => fun i =>
      admissibleStageRank
        (bundleFullRankClockFamily delta c_zeta c_P0 d).clock.m
        (d + 2)
        (bundlePriorityRankFamily delta c_zeta c_P0 d)
        (finSumFinEquiv.symm i)

/-- Grounded 1-field pure bundle chronology specification containing only `hpriority_raw`. -/
structure PureBundleChronologySpec (delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hpriority_raw : ∀ p : ℕ,
    let fc := bundleFullRankClockFamily delta c_zeta c_P0 d
    let cz := canonicalCZeta fc.clock (delta d)
    IsValidPriorityWord
      (liftedGameMat (adjoinGatewayEndpointG fc.clock.G fc.clock.v)
        (P_bundle fc.clock fc.L_C (delta d) cz (c_P0 d))
        (J_bundle fc.clock (delta d) cz))
      ((liftedScoreMat (adjoinGatewayEndpointG fc.clock.G fc.clock.v)
        (J_bundle fc.clock (delta d) cz) (S_bundle fc.clock 0 (delta d))
        (X_gateway fc.clock) (M_coupled (d + 2))
        (zeta_bundle_scaled fc.clock (delta d) cz)).mulVec
          (binomBasis (d + 3) (p + (d + 2))))
      (admissibleStageRank fc.clock.m (d + 2) (bundlePriorityRankFamily delta c_zeta c_P0 d))
      (rawFourStageWord fc.clock (bundlePhaseWordFamily delta c_zeta c_P0 d) (p + (d + 2)))

/-- Automatic plumbing conversion from `PureBundleChronologySpec` to `BundleChronologySpec`. -/
def PureBundleChronologySpec.toBundleChronologySpec (delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ)
    (spec : PureBundleChronologySpec delta c_zeta c_P0 d) :
    BundleChronologySpec (by omega)
      (bundleFullRankClockFamily delta c_zeta c_P0 d)
      (delta d) (c_P0 d) where
  phaseShift := d + 2
  hshift := le_rfl
  parentWord := bundlePhaseWordFamily delta c_zeta c_P0 d
  hparent_count := wordCountVec_bundlePhaseWordFamily delta c_zeta c_P0 d
  m_rank := ((bundleFullRankClockFamily delta c_zeta c_P0 d).clock.m + 1) + ((d + 2 + 1) + (d + 2 + 1))
  hm_rank := by omega
  rank := fun i =>
    admissibleStageRank
      (bundleFullRankClockFamily delta c_zeta c_P0 d).clock.m
      (d + 2)
      (bundlePriorityRankFamily delta c_zeta c_P0 d)
      (finSumFinEquiv.symm i)
  hpriority_raw := fun p => by
    have hp := spec.hpriority_raw p
    simpa only [Equiv.symm_apply_apply] using hp

/-- **All-Orders Pure Bundle Karlin Theorem**:
    Duality gap scaling across all polynomial orders $k \ge 2$ governed by 1-field pure bundle specs. -/
theorem all_orders_pure_bundle_karlin_theorem (delta c_zeta c_P0 : ℕ → ℚ)
    (pure_lifts : ∀ d : ℕ, PureBundleChronologySpec delta c_zeta c_P0 d)
    (hc_zeta : ∀ d : ℕ, c_zeta d = canonicalCZeta (bundleFullRankClockFamily delta c_zeta c_P0 d).clock (delta d))
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  have lifts : ∀ d : ℕ, BundleLiftSpec (by omega) (bundleFullRankClockFamily delta c_zeta c_P0 d)
      (delta d) (c_zeta d) (c_P0 d) := by
    intro d
    have hspec := (pure_lifts d).toBundleChronologySpec delta c_zeta c_P0 d
    have hlift := hspec.toBundleLiftSpec
    rw [hc_zeta d]
    exact hlift
  exact all_orders_bundle_realized_karlin_theorem delta c_zeta c_P0 lifts k hk

/-!
## Section 5: All-Phase Ceiling Dominance (`mulVec_binomBasis_lt_dotProduct_zeta`) and Rank-Value Congruence
-/

/-- The sum of coordinates of `binomBasis n q` is at least 1 for any positive dimension `n` and any phase `q`. -/
theorem one_le_sum_binomBasis (n q : ℕ) (hn : 0 < n) : 1 ≤ ∑ c : Fin n, binomBasis n q c := by
  have hnonneg : ∀ c ∈ (Finset.univ : Finset (Fin n)), 0 ≤ binomBasis n q c := by
    intro c _
    unfold binomBasis
    positivity
  have hmem : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have hsingle := Finset.single_le_sum hnonneg hmem
  have h0 : binomBasis n q ⟨0, hn⟩ = 1 := by
    unfold binomBasis
    simp only [Nat.choose_zero_right, Nat.cast_one]
  rw [h0] at hsingle
  exact hsingle

/-- If every entry of row `x` of matrix `M` is strictly bounded by `zeta - 1`, then for all `q : ℕ`,
    `(M * p(q))_x < zeta · p(q)`. -/
theorem mulVec_binomBasis_lt_dotProduct_zeta {α : Type*} {n : ℕ} (hn : 0 < n)
    (M : Matrix α (Fin n) ℚ) (zeta : Fin n → ℚ) (x : α)
    (hdom : ∀ c : Fin n, M x c + 1 ≤ zeta c) (q : ℕ) :
    (M.mulVec (binomBasis n q)) x < dotProduct zeta (binomBasis n q) := by
  have h_term : ∀ c : Fin n, (M x c + 1) * binomBasis n q c ≤ zeta c * binomBasis n q c := by
    intro c
    have hb_nonneg : 0 ≤ binomBasis n q c := by
      unfold binomBasis
      positivity
    exact mul_le_mul_of_nonneg_right (hdom c) hb_nonneg
  have h_sum := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => h_term c
  have h_distrib :
      (∑ c : Fin n, (M x c + 1) * binomBasis n q c) =
        (∑ c : Fin n, M x c * binomBasis n q c) + ∑ c : Fin n, binomBasis n q c := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => by ring
  rw [h_distrib] at h_sum
  have h_one_le := one_le_sum_binomBasis n q hn
  dsimp only [Matrix.mulVec, dotProduct]
  linarith

/-- Old-block actions strictly remain below ceiling across all phase indices `q` in Stage 1. -/
theorem admissible_stage1_old_below_ceiling_all_q {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ) (u : Fin (clock.m + 1))
    (hdom : ∀ c : Fin (w + 1),
      (S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c + 1 ≤
        zeta_admissible_scaled clock b H0 ch delta c_zeta c)
    (q : ℕ) :
    ((liftedScoreMat (AdjoinLeaderEndpointG clock.G b clock.v)
      (J_admissible_scaled clock b H0 ch delta c_zeta)
      (S_admissible clock b H0 ch delta)
      (X_gateway clock) (M_coupled w)
      (zeta_admissible_scaled clock b H0 ch delta c_zeta)).mulVec (binomBasis (w + 1) q)) (Sum.inl u) <
      dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) q) := by
  have hn : 0 < w + 1 := Nat.succ_pos w
  let M := liftedScoreMat (AdjoinLeaderEndpointG clock.G b clock.v)
    (J_admissible_scaled clock b H0 ch delta c_zeta)
    (S_admissible clock b H0 ch delta)
    (X_gateway clock) (M_coupled w)
    (zeta_admissible_scaled clock b H0 ch delta c_zeta)
  have hM_inl : ∀ c : Fin (w + 1), M (Sum.inl u) c =
      (S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c := by
    intro c
    dsimp only [M, liftedScoreMat]
    simp only [Matrix.of_apply]
  have hdom' : ∀ c : Fin (w + 1), M (Sum.inl u) c + 1 ≤ zeta_admissible_scaled clock b H0 ch delta c_zeta c := by
    intro c
    rw [hM_inl c]
    exact hdom c
  exact mulVec_binomBasis_lt_dotProduct_zeta hn M (zeta_admissible_scaled clock b H0 ch delta c_zeta) (Sum.inl u) hdom' q

/-- Old-block actions strictly remain below ceiling across all phase indices `q` in Stage 2. -/
theorem admissible_stage2_old_below_ceiling_all_q {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ) (u : Fin (clock.m + 1))
    (hdom : ∀ c : Fin (w + 1),
      (S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c + 1 ≤
        zeta_admissible_scaled clock b H0 ch delta c_zeta c)
    (q : ℕ) :
    (S_admissible clock b H0 ch delta).mulVec (binomBasis (w + 1) (q + 1)) u <
      dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) q) := by
  have hn : 0 < w + 1 := Nat.succ_pos w
  have hbasis : binomBasis (w + 1) (q + 1) = (1 + N_mat (w + 1)).mulVec (binomBasis (w + 1) q) :=
    binomBasis_succ (w + 1) q
  rw [hbasis, Matrix.mulVec_mulVec]
  exact mulVec_binomBasis_lt_dotProduct_zeta hn (S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ))
    (zeta_admissible_scaled clock b H0 ch delta c_zeta) u hdom q

/-- Priority step validity depends only on the numeric value of the ranking function. -/
theorem isValidPriorityStep_congr_rank_val {α : Type*} [Fintype α] [DecidableEq α] {m1 m2 : ℕ}
    (s : α → ℚ) (rank1 : α → Fin m1) (rank2 : α → Fin m2)
    (hrank : ∀ x : α, (rank1 x).val = (rank2 x).val) (a : α) :
    IsValidPriorityStep s rank1 a ↔ IsValidPriorityStep s rank2 a := by
  constructor
  · intro h j
    obtain ⟨h1, h2⟩ := h j
    refine ⟨h1, fun hne heq => ?_⟩
    rw [← hrank a, ← hrank j]
    exact h2 hne heq
  · intro h j
    obtain ⟨h1, h2⟩ := h j
    refine ⟨h1, fun hne heq => ?_⟩
    rw [hrank a, hrank j]
    exact h2 hne heq

/-- Priority word validity depends only on the numeric value of the ranking function. -/
theorem isValidPriorityWord_congr_rank_val {α : Type*} [Fintype α] [DecidableEq α] {m1 m2 : ℕ}
    (M : Matrix α α ℚ) (s0 : α → ℚ) (rank1 : α → Fin m1) (rank2 : α → Fin m2)
    (hrank : ∀ x : α, (rank1 x).val = (rank2 x).val) (W : List α) :
    IsValidPriorityWord M s0 rank1 W ↔ IsValidPriorityWord M s0 rank2 W := by
  constructor
  · intro h k hk j
    obtain ⟨h1, h2⟩ := h k hk j
    refine ⟨h1, fun hne heq => ?_⟩
    rw [← hrank W[k], ← hrank j]
    exact h2 hne heq
  · intro h k hk j
    obtain ⟨h1, h2⟩ := h k hk j
    refine ⟨h1, fun hne heq => ?_⟩
    rw [hrank W[k], hrank j]
    exact h2 hne heq

/-!
## Section 6: Explicit Full Ceiling Thresholds (`canonicalCZeta_full_admissible`, `canonicalCZeta_full_bundle`) & Unconditional All-`q` Stage 1–2 Ceiling Dominance
-/

/-- Old-block actions strictly remain below ceiling across all phase indices `q` in Stage 1 for the scaled bundle lift. -/
theorem bundle_stage1_old_below_ceiling_all_q {w : ℕ} (clock : AlgebraicClock w)
    (delta c_zeta : ℚ) (u : Fin (clock.m + 1))
    (hdom : ∀ c : Fin (w + 1),
      (S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c + 1 ≤
        zeta_bundle_scaled clock delta c_zeta c)
    (q : ℕ) :
    ((liftedScoreMat (adjoinGatewayEndpointG clock.G clock.v)
      (J_bundle clock delta c_zeta)
      (S_bundle clock 0 delta)
      (X_gateway clock) (M_coupled w)
      (zeta_bundle_scaled clock delta c_zeta)).mulVec (binomBasis (w + 1) q)) (Sum.inl u) <
      dotProduct (zeta_bundle_scaled clock delta c_zeta) (binomBasis (w + 1) q) := by
  have hn : 0 < w + 1 := Nat.succ_pos w
  let M := liftedScoreMat (adjoinGatewayEndpointG clock.G clock.v)
    (J_bundle clock delta c_zeta)
    (S_bundle clock 0 delta)
    (X_gateway clock) (M_coupled w)
    (zeta_bundle_scaled clock delta c_zeta)
  have hM_inl : ∀ c : Fin (w + 1), M (Sum.inl u) c =
      (S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c := by
    intro c
    dsimp only [M, liftedScoreMat]
    simp only [Matrix.of_apply]
  have hdom' : ∀ c : Fin (w + 1), M (Sum.inl u) c + 1 ≤ zeta_bundle_scaled clock delta c_zeta c := by
    intro c
    rw [hM_inl c]
    exact hdom c
  exact mulVec_binomBasis_lt_dotProduct_zeta hn M (zeta_bundle_scaled clock delta c_zeta) (Sum.inl u) hdom' q

/-- Old-block actions strictly remain below ceiling across all phase indices `q` in Stage 2 for the scaled bundle lift. -/
theorem bundle_stage2_old_below_ceiling_all_q {w : ℕ} (clock : AlgebraicClock w)
    (delta c_zeta : ℚ) (u : Fin (clock.m + 1))
    (hdom : ∀ c : Fin (w + 1),
      (S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c + 1 ≤
        zeta_bundle_scaled clock delta c_zeta c)
    (q : ℕ) :
    (S_bundle clock 0 delta).mulVec (binomBasis (w + 1) (q + 1)) u <
      dotProduct (zeta_bundle_scaled clock delta c_zeta) (binomBasis (w + 1) q) := by
  have hn : 0 < w + 1 := Nat.succ_pos w
  have hbasis : binomBasis (w + 1) (q + 1) = (1 + N_mat (w + 1)).mulVec (binomBasis (w + 1) q) :=
    binomBasis_succ (w + 1) q
  rw [hbasis, Matrix.mulVec_mulVec]
  exact mulVec_binomBasis_lt_dotProduct_zeta hn (S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ))
    (zeta_bundle_scaled clock delta c_zeta) u hdom q

/-- Full canonical ceiling scaling constant guaranteeing Stage 1-2 dominance for the scaled admissible lift. -/
def canonicalCZeta_full_admissible {w : ℕ} (clock : AlgebraicClock w) (b : Fin clock.m)
    (H0 ch delta : ℚ) : ℚ :=
  canonicalCZeta_admissible clock b H0 ch delta +
    ∑ u : Fin (clock.m + 1), ∑ c : Fin (w + 1),
      (|(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c| +
       |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c|)

/-- The full admissible ceiling scale is at least the base canonical ceiling scale. -/
theorem canonicalCZeta_admissible_le_full {w : ℕ} (clock : AlgebraicClock w) (b : Fin clock.m)
    (H0 ch delta : ℚ) :
    canonicalCZeta_admissible clock b H0 ch delta ≤ canonicalCZeta_full_admissible clock b H0 ch delta := by
  unfold canonicalCZeta_full_admissible
  have hnonneg : 0 ≤ ∑ u : Fin (clock.m + 1), ∑ c : Fin (w + 1),
      (|(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c| +
       |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c|) := by
    refine Finset.sum_nonneg fun u _ => ?_
    refine Finset.sum_nonneg fun c _ => ?_
    positivity
  linarith

/-- Whenever `c_zeta ≥ canonicalCZeta_full_admissible`, Stage 1 scores are bounded entrywise by `zeta - 1`. -/
theorem stage1_dom_of_ge_canonicalCZeta_full_admissible {w : ℕ} (clock : AlgebraicClock w) (b : Fin clock.m)
    (H0 ch delta c_zeta : ℚ) (h_cz : canonicalCZeta_full_admissible clock b H0 ch delta ≤ c_zeta)
    (u : Fin (clock.m + 1)) (c : Fin (w + 1)) :
    (S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c + 1 ≤
      zeta_admissible_scaled clock b H0 ch delta c_zeta c := by
  have hbase_le_c_zeta : canonicalCZeta_admissible clock b H0 ch delta ≤ c_zeta :=
    le_trans (canonicalCZeta_admissible_le_full clock b H0 ch delta) h_cz
  have h1 : 1 ≤ zeta_admissible_scaled clock b H0 ch delta (canonicalCZeta_admissible clock b H0 ch delta) c :=
    zeta_admissible_scaled_canonicalCZeta_ge_one clock b H0 ch delta c
  have hzeta_split : zeta_admissible_scaled clock b H0 ch delta c_zeta c =
      zeta_admissible_scaled clock b H0 ch delta (canonicalCZeta_admissible clock b H0 ch delta) c +
        (c_zeta - canonicalCZeta_admissible clock b H0 ch delta) := by
    have : zeta_coupled w c = 1 := rfl
    unfold zeta_admissible_scaled
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, this]
    ring
  rw [hzeta_split]
  have hsum_le :
      |(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c| ≤
        c_zeta - canonicalCZeta_admissible clock b H0 ch delta := by
    have hterm_le :
        |(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c| ≤
          |(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c| +
          |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c| := by
      have : 0 ≤ |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c| := abs_nonneg _
      linarith
    have hsum_c :
        |(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c| +
        |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c| ≤
          ∑ c_idx : Fin (w + 1),
            (|(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c_idx| +
             |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c_idx|) := by
      exact Finset.single_le_sum (f := fun c_idx =>
        |(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c_idx| +
        |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c_idx|)
        (fun _ _ => by positivity) (Finset.mem_univ c)
    have hsum_u :
        (∑ c_idx : Fin (w + 1),
          (|(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c_idx| +
           |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c_idx|)) ≤
          ∑ u_idx : Fin (clock.m + 1), ∑ c_idx : Fin (w + 1),
            (|(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u_idx c_idx| +
             |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u_idx c_idx|) := by
      exact Finset.single_le_sum (f := fun u_idx =>
        ∑ c_idx : Fin (w + 1),
          (|(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u_idx c_idx| +
           |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u_idx c_idx|))
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ u)
    have hdiff :
        (∑ u_idx : Fin (clock.m + 1), ∑ c_idx : Fin (w + 1),
          (|(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u_idx c_idx| +
           |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u_idx c_idx|)) ≤
        c_zeta - canonicalCZeta_admissible clock b H0 ch delta := by
      unfold canonicalCZeta_full_admissible at h_cz
      linarith
    linarith
  have h_abs : (S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c ≤
      |(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c| := le_abs_self _
  linarith

/-- Whenever `c_zeta ≥ canonicalCZeta_full_admissible`, Stage 2 scores are bounded entrywise by `zeta - 1`. -/
theorem stage2_dom_of_ge_canonicalCZeta_full_admissible {w : ℕ} (clock : AlgebraicClock w) (b : Fin clock.m)
    (H0 ch delta c_zeta : ℚ) (h_cz : canonicalCZeta_full_admissible clock b H0 ch delta ≤ c_zeta)
    (u : Fin (clock.m + 1)) (c : Fin (w + 1)) :
    (S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c + 1 ≤
      zeta_admissible_scaled clock b H0 ch delta c_zeta c := by
  have hbase_le_c_zeta : canonicalCZeta_admissible clock b H0 ch delta ≤ c_zeta :=
    le_trans (canonicalCZeta_admissible_le_full clock b H0 ch delta) h_cz
  have h1 : 1 ≤ zeta_admissible_scaled clock b H0 ch delta (canonicalCZeta_admissible clock b H0 ch delta) c :=
    zeta_admissible_scaled_canonicalCZeta_ge_one clock b H0 ch delta c
  have hzeta_split : zeta_admissible_scaled clock b H0 ch delta c_zeta c =
      zeta_admissible_scaled clock b H0 ch delta (canonicalCZeta_admissible clock b H0 ch delta) c +
        (c_zeta - canonicalCZeta_admissible clock b H0 ch delta) := by
    have : zeta_coupled w c = 1 := rfl
    unfold zeta_admissible_scaled
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, this]
    ring
  rw [hzeta_split]
  have hsum_le :
      |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c| ≤
        c_zeta - canonicalCZeta_admissible clock b H0 ch delta := by
    have hterm_le :
        |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c| ≤
          |(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c| +
          |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c| := by
      have : 0 ≤ |(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c| := abs_nonneg _
      linarith
    have hsum_c :
        |(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c| +
        |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c| ≤
          ∑ c_idx : Fin (w + 1),
            (|(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c_idx| +
             |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c_idx|) := by
      exact Finset.single_le_sum (f := fun c_idx =>
        |(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c_idx| +
        |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c_idx|)
        (fun _ _ => by positivity) (Finset.mem_univ c)
    have hsum_u :
        (∑ c_idx : Fin (w + 1),
          (|(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u c_idx| +
           |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c_idx|)) ≤
          ∑ u_idx : Fin (clock.m + 1), ∑ c_idx : Fin (w + 1),
            (|(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u_idx c_idx| +
             |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u_idx c_idx|) := by
      exact Finset.single_le_sum (f := fun u_idx =>
        ∑ c_idx : Fin (w + 1),
          (|(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u_idx c_idx| +
           |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u_idx c_idx|))
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ u)
    have hdiff :
        (∑ u_idx : Fin (clock.m + 1), ∑ c_idx : Fin (w + 1),
          (|(S_admissible clock b H0 ch delta + AdjoinLeaderEndpointG clock.G b clock.v * X_gateway clock) u_idx c_idx| +
           |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u_idx c_idx|)) ≤
        c_zeta - canonicalCZeta_admissible clock b H0 ch delta := by
      unfold canonicalCZeta_full_admissible at h_cz
      linarith
    linarith
  have h_abs : (S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c ≤
      |(S_admissible clock b H0 ch delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c| := le_abs_self _
  linarith

/-- Unconditional Stage 1 ceiling dominance across all `q` for `c_zeta ≥ canonicalCZeta_full_admissible`. -/
theorem admissible_stage1_old_below_ceiling_unconditional {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ)
    (h_cz : canonicalCZeta_full_admissible clock b H0 ch delta ≤ c_zeta)
    (u : Fin (clock.m + 1)) (q : ℕ) :
    ((liftedScoreMat (AdjoinLeaderEndpointG clock.G b clock.v)
      (J_admissible_scaled clock b H0 ch delta c_zeta)
      (S_admissible clock b H0 ch delta)
      (X_gateway clock) (M_coupled w)
      (zeta_admissible_scaled clock b H0 ch delta c_zeta)).mulVec (binomBasis (w + 1) q)) (Sum.inl u) <
      dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) q) :=
  admissible_stage1_old_below_ceiling_all_q clock b H0 ch delta c_zeta u
    (fun c => stage1_dom_of_ge_canonicalCZeta_full_admissible clock b H0 ch delta c_zeta h_cz u c) q

/-- Unconditional Stage 2 ceiling dominance across all `q` for `c_zeta ≥ canonicalCZeta_full_admissible`. -/
theorem admissible_stage2_old_below_ceiling_unconditional {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ)
    (h_cz : canonicalCZeta_full_admissible clock b H0 ch delta ≤ c_zeta)
    (u : Fin (clock.m + 1)) (q : ℕ) :
    (S_admissible clock b H0 ch delta).mulVec (binomBasis (w + 1) (q + 1)) u <
      dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) q) :=
  admissible_stage2_old_below_ceiling_all_q clock b H0 ch delta c_zeta u
    (fun c => stage2_dom_of_ge_canonicalCZeta_full_admissible clock b H0 ch delta c_zeta h_cz u c) q

/-- Full canonical ceiling scaling constant guaranteeing Stage 1-2 dominance for the scaled bundle lift. -/
def canonicalCZeta_full_bundle {w : ℕ} (clock : AlgebraicClock w) (delta : ℚ) : ℚ :=
  canonicalCZeta clock delta +
    ∑ u : Fin (clock.m + 1), ∑ c : Fin (w + 1),
      (|(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c| +
       |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c|)

/-- The full bundle ceiling scale is at least the base canonical ceiling scale. -/
theorem canonicalCZeta_bundle_le_full {w : ℕ} (clock : AlgebraicClock w) (delta : ℚ) :
    canonicalCZeta clock delta ≤ canonicalCZeta_full_bundle clock delta := by
  unfold canonicalCZeta_full_bundle
  have hnonneg : 0 ≤ ∑ u : Fin (clock.m + 1), ∑ c : Fin (w + 1),
      (|(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c| +
       |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c|) := by
    refine Finset.sum_nonneg fun u _ => ?_
    refine Finset.sum_nonneg fun c _ => ?_
    positivity
  linarith

/-- Whenever `c_zeta ≥ canonicalCZeta_full_bundle`, Stage 1 scores are bounded entrywise by `zeta - 1`. -/
theorem stage1_dom_of_ge_canonicalCZeta_full_bundle {w : ℕ} (clock : AlgebraicClock w)
    (delta c_zeta : ℚ) (h_cz : canonicalCZeta_full_bundle clock delta ≤ c_zeta)
    (u : Fin (clock.m + 1)) (c : Fin (w + 1)) :
    (S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c + 1 ≤
      zeta_bundle_scaled clock delta c_zeta c := by
  have hbase_le_c_zeta : canonicalCZeta clock delta ≤ c_zeta :=
    le_trans (canonicalCZeta_bundle_le_full clock delta) h_cz
  have h1 : 1 ≤ zeta_bundle_scaled clock delta (canonicalCZeta clock delta) c :=
    zeta_bundle_scaled_canonicalCZeta_ge_one clock delta c
  have hzeta_split : zeta_bundle_scaled clock delta c_zeta c =
      zeta_bundle_scaled clock delta (canonicalCZeta clock delta) c +
        (c_zeta - canonicalCZeta clock delta) := by
    have : zeta_coupled w c = 1 := rfl
    unfold zeta_bundle_scaled
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, this]
    ring
  rw [hzeta_split]
  have hsum_le :
      |(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c| ≤
        c_zeta - canonicalCZeta clock delta := by
    have hterm_le :
        |(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c| ≤
          |(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c| +
          |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c| := by
      have : 0 ≤ |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c| := abs_nonneg _
      linarith
    have hsum_c :
        |(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c| +
        |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c| ≤
          ∑ c_idx : Fin (w + 1),
            (|(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c_idx| +
             |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c_idx|) := by
      exact Finset.single_le_sum (f := fun c_idx =>
        |(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c_idx| +
        |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c_idx|)
        (fun _ _ => by positivity) (Finset.mem_univ c)
    have hsum_u :
        (∑ c_idx : Fin (w + 1),
          (|(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c_idx| +
           |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c_idx|)) ≤
          ∑ u_idx : Fin (clock.m + 1), ∑ c_idx : Fin (w + 1),
            (|(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u_idx c_idx| +
             |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u_idx c_idx|) := by
      exact Finset.single_le_sum (f := fun u_idx =>
        ∑ c_idx : Fin (w + 1),
          (|(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u_idx c_idx| +
           |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u_idx c_idx|))
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ u)
    have hdiff :
        (∑ u_idx : Fin (clock.m + 1), ∑ c_idx : Fin (w + 1),
          (|(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u_idx c_idx| +
           |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u_idx c_idx|)) ≤
        c_zeta - canonicalCZeta clock delta := by
      unfold canonicalCZeta_full_bundle at h_cz
      linarith
    linarith
  have h_abs : (S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c ≤
      |(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c| := le_abs_self _
  linarith

/-- Whenever `c_zeta ≥ canonicalCZeta_full_bundle`, Stage 2 scores are bounded entrywise by `zeta - 1`. -/
theorem stage2_dom_of_ge_canonicalCZeta_full_bundle {w : ℕ} (clock : AlgebraicClock w)
    (delta c_zeta : ℚ) (h_cz : canonicalCZeta_full_bundle clock delta ≤ c_zeta)
    (u : Fin (clock.m + 1)) (c : Fin (w + 1)) :
    (S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c + 1 ≤
      zeta_bundle_scaled clock delta c_zeta c := by
  have hbase_le_c_zeta : canonicalCZeta clock delta ≤ c_zeta :=
    le_trans (canonicalCZeta_bundle_le_full clock delta) h_cz
  have h1 : 1 ≤ zeta_bundle_scaled clock delta (canonicalCZeta clock delta) c :=
    zeta_bundle_scaled_canonicalCZeta_ge_one clock delta c
  have hzeta_split : zeta_bundle_scaled clock delta c_zeta c =
      zeta_bundle_scaled clock delta (canonicalCZeta clock delta) c +
        (c_zeta - canonicalCZeta clock delta) := by
    have : zeta_coupled w c = 1 := rfl
    unfold zeta_bundle_scaled
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, this]
    ring
  rw [hzeta_split]
  have hsum_le :
      |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c| ≤
        c_zeta - canonicalCZeta clock delta := by
    have hterm_le :
        |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c| ≤
          |(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c| +
          |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c| := by
      have : 0 ≤ |(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c| := abs_nonneg _
      linarith
    have hsum_c :
        |(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c| +
        |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c| ≤
          ∑ c_idx : Fin (w + 1),
            (|(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c_idx| +
             |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c_idx|) := by
      exact Finset.single_le_sum (f := fun c_idx =>
        |(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c_idx| +
        |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c_idx|)
        (fun _ _ => by positivity) (Finset.mem_univ c)
    have hsum_u :
        (∑ c_idx : Fin (w + 1),
          (|(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u c_idx| +
           |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c_idx|)) ≤
          ∑ u_idx : Fin (clock.m + 1), ∑ c_idx : Fin (w + 1),
            (|(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u_idx c_idx| +
             |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u_idx c_idx|) := by
      exact Finset.single_le_sum (f := fun u_idx =>
        ∑ c_idx : Fin (w + 1),
          (|(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u_idx c_idx| +
           |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u_idx c_idx|))
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ u)
    have hdiff :
        (∑ u_idx : Fin (clock.m + 1), ∑ c_idx : Fin (w + 1),
          (|(S_bundle clock 0 delta + adjoinGatewayEndpointG clock.G clock.v * X_gateway clock) u_idx c_idx| +
           |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u_idx c_idx|)) ≤
        c_zeta - canonicalCZeta clock delta := by
      unfold canonicalCZeta_full_bundle at h_cz
      linarith
    linarith
  have h_abs : (S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c ≤
      |(S_bundle clock 0 delta * (1 + N_mat (w + 1) : Matrix (Fin (w + 1)) (Fin (w + 1)) ℚ)) u c| := le_abs_self _
  linarith

/-- Unconditional Stage 1 ceiling dominance across all `q` for `c_zeta ≥ canonicalCZeta_full_bundle`. -/
theorem bundle_stage1_old_below_ceiling_unconditional {w : ℕ} (clock : AlgebraicClock w)
    (delta c_zeta : ℚ)
    (h_cz : canonicalCZeta_full_bundle clock delta ≤ c_zeta)
    (u : Fin (clock.m + 1)) (q : ℕ) :
    ((liftedScoreMat (adjoinGatewayEndpointG clock.G clock.v)
      (J_bundle clock delta c_zeta)
      (S_bundle clock 0 delta)
      (X_gateway clock) (M_coupled w)
      (zeta_bundle_scaled clock delta c_zeta)).mulVec (binomBasis (w + 1) q)) (Sum.inl u) <
      dotProduct (zeta_bundle_scaled clock delta c_zeta) (binomBasis (w + 1) q) :=
  bundle_stage1_old_below_ceiling_all_q clock delta c_zeta u
    (fun c => stage1_dom_of_ge_canonicalCZeta_full_bundle clock delta c_zeta h_cz u c) q

/-- Unconditional Stage 2 ceiling dominance across all `q` for `c_zeta ≥ canonicalCZeta_full_bundle`. -/
theorem bundle_stage2_old_below_ceiling_unconditional {w : ℕ} (clock : AlgebraicClock w)
    (delta c_zeta : ℚ)
    (h_cz : canonicalCZeta_full_bundle clock delta ≤ c_zeta)
    (u : Fin (clock.m + 1)) (q : ℕ) :
    (S_bundle clock 0 delta).mulVec (binomBasis (w + 1) (q + 1)) u <
      dotProduct (zeta_bundle_scaled clock delta c_zeta) (binomBasis (w + 1) q) :=
  bundle_stage2_old_below_ceiling_all_q clock delta c_zeta u
    (fun c => stage2_dom_of_ge_canonicalCZeta_full_bundle clock delta c_zeta h_cz u c) q

/-!
## Section 7: Unconditional All-`q` Stage 1 & Stage 2 Reset Priority Validity
-/

/-- Strict subdiagonal positivity of `J_admissible_scaled` for all `c_zeta ≥ canonicalCZeta_admissible`. -/
theorem J_admissible_scaled_subdiag_pos_of_ge {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ)
    (h_cz : canonicalCZeta_admissible clock b H0 ch delta ≤ c_zeta)
    (a b_idx : Fin ((w + 1) + (w + 1))) (hab : b_idx.val < a.val) :
    0 < J_admissible_scaled clock b H0 ch delta c_zeta a b_idx := by
  have hbase := (J_admissible_scaled_canonicalCZeta_subdiag_pos clock b H0 ch delta a b_idx hab).2
  have hJ := (J_coupled_subdiag_ge w a b_idx hab).2
  have hsplit : J_admissible_scaled clock b H0 ch delta c_zeta a b_idx =
      J_admissible_scaled clock b H0 ch delta (canonicalCZeta_admissible clock b H0 ch delta) a b_idx +
        (c_zeta - canonicalCZeta_admissible clock b H0 ch delta) * J_coupled w a b_idx := by
    dsimp only [J_admissible_scaled]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hsplit]
  have h_nonneg : 0 ≤ (c_zeta - canonicalCZeta_admissible clock b H0 ch delta) * J_coupled w a b_idx :=
    mul_nonneg (by linarith) (le_of_lt hJ)
  linarith

/-- Strict subdiagonal positivity of `J_bundle` for all `c_zeta ≥ canonicalCZeta`. -/
theorem J_bundle_subdiag_pos_of_ge {w : ℕ} (clock : AlgebraicClock w)
    (delta c_zeta : ℚ)
    (h_cz : canonicalCZeta clock delta ≤ c_zeta)
    (a b_idx : Fin ((w + 1) + (w + 1))) (hab : b_idx.val < a.val) :
    0 < J_bundle clock delta c_zeta a b_idx := by
  have hbase := (J_bundle_canonicalCZeta_subdiag_pos clock delta a b_idx hab).2
  have hJ := (J_coupled_subdiag_ge w a b_idx hab).2
  have hsplit : J_bundle clock delta c_zeta a b_idx =
      J_bundle clock delta (canonicalCZeta clock delta) a b_idx +
        (c_zeta - canonicalCZeta clock delta) * J_coupled w a b_idx := by
    dsimp only [J_bundle]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hsplit]
  have h_nonneg : 0 ≤ (c_zeta - canonicalCZeta clock delta) * J_coupled w a b_idx :=
    mul_nonneg (by linarith) (le_of_lt hJ)
  linarith

/-- **Unconditional All-`q` Stage 1 Priority Validity for Scaled Admissible Lift**:
    Whenever `c_zeta ≥ canonicalCZeta_full_admissible` and early reset couplings are nonpositive,
    `W_early_word` is a valid priority word across all phase indices `q : ℕ`. -/
theorem admissible_stage1_priority_valid_unconditional {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (parent_rank : Fin clock.m → Fin clock.m)
    (h_cz : canonicalCZeta_full_admissible clock b H0 ch delta ≤ c_zeta)
    (hP_early_nonpos : ∀ (j : Fin (w + 1)) (x : Fin (clock.m + 1)),
      P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C x (finSumFinEquiv (Sum.inl j)) ≤ 0)
    (q : ℕ) :
    IsValidPriorityWord
      (liftedGameMat (AdjoinLeaderEndpointG clock.G b clock.v)
        (P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C)
        (J_admissible_scaled clock b H0 ch delta c_zeta))
      ((liftedScoreMat (AdjoinLeaderEndpointG clock.G b clock.v)
        (J_admissible_scaled clock b H0 ch delta c_zeta)
        (S_admissible clock b H0 ch delta)
        (X_gateway clock) (M_coupled w)
        (zeta_admissible_scaled clock b H0 ch delta c_zeta)).mulVec (binomBasis (w + 1) q))
      (paperPriorityRank clock.m w parent_rank)
      (W_early_word clock.m w q) := by
  have hbase_le_cz : canonicalCZeta_admissible clock b H0 ch delta ≤ c_zeta :=
    le_trans (canonicalCZeta_admissible_le_full clock b H0 ch delta) h_cz
  apply isValidPriorityWord_W_early_word_of_start
  · intro a b_idx hab
    exact J_admissible_scaled_lower clock b H0 ch delta c_zeta a b_idx hab
  · intro a b_idx hab
    exact J_admissible_scaled_subdiag_pos_of_ge clock b H0 ch delta c_zeta hbase_le_cz a b_idx hab
  · exact hP_early_nonpos
  · intro x
    exact admissible_stage1_old_below_ceiling_unconditional clock b H0 ch delta c_zeta h_cz x q

/-- **Unconditional All-`q` Stage 2 Priority Validity for Scaled Admissible Lift**:
    Whenever `c_zeta ≥ canonicalCZeta_full_admissible` and late reset couplings are nonnegative,
    `W_late_word` is a valid priority word across all phase indices `q : ℕ`. -/
theorem admissible_stage2_priority_valid_unconditional {w : ℕ} (hw : 2 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (parent_rank : Fin clock.m → Fin clock.m)
    (h_cz : canonicalCZeta_full_admissible clock b H0 ch delta ≤ c_zeta)
    (hP_late_nonneg : ∀ (j : Fin (w + 1)) (x : Fin (clock.m + 1)),
      0 ≤ P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C x (finSumFinEquiv (Sum.inr j)))
    (q : ℕ) :
    IsValidPriorityWord
      (liftedGameMat (AdjoinLeaderEndpointG clock.G b clock.v)
        (P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C)
        (J_admissible_scaled clock b H0 ch delta c_zeta))
      (wordScore
        (liftedGameMat (AdjoinLeaderEndpointG clock.G b clock.v)
          (P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C)
          (J_admissible_scaled clock b H0 ch delta c_zeta))
        ((liftedScoreMat (AdjoinLeaderEndpointG clock.G b clock.v)
          (J_admissible_scaled clock b H0 ch delta c_zeta)
          (S_admissible clock b H0 ch delta)
          (X_gateway clock) (M_coupled w)
          (zeta_admissible_scaled clock b H0 ch delta c_zeta)).mulVec (binomBasis (w + 1) q))
        (W_early_word clock.m w q))
      (paperPriorityRank clock.m w parent_rank)
      (W_late_word clock.m w q) := by
  have hbase_le_cz : canonicalCZeta_admissible clock b H0 ch delta ≤ c_zeta :=
    le_trans (canonicalCZeta_admissible_le_full clock b H0 ch delta) h_cz
  apply isValidPriorityWord_W_late_word_of_end
  · intro a b_idx hab
    exact J_admissible_scaled_lower clock b H0 ch delta c_zeta a b_idx hab
  · intro a b_idx hab
    exact J_admissible_scaled_subdiag_pos_of_ge clock b H0 ch delta c_zeta hbase_le_cz a b_idx hab
  · exact hP_late_nonneg
  · intro x
    rw [wordScore_after_reset_stages_admissible_inl hw clock b H0 ch delta c_zeta c_P0 a_old L_C q x]
    exact admissible_stage2_old_below_ceiling_unconditional clock b H0 ch delta c_zeta h_cz x q

/-- **Unconditional All-`q` Combined Reset Stages Priority Validity for Scaled Admissible Lift**:
    Combines Stage 1 and Stage 2 into full priority validity of `W_early_word ++ W_late_word`
    for all `q : ℕ`. -/
theorem admissible_reset_stages_priority_valid_unconditional {w : ℕ} (hw : 2 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (parent_rank : Fin clock.m → Fin clock.m)
    (h_cz : canonicalCZeta_full_admissible clock b H0 ch delta ≤ c_zeta)
    (hP_early_nonpos : ∀ (j : Fin (w + 1)) (x : Fin (clock.m + 1)),
      P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C x (finSumFinEquiv (Sum.inl j)) ≤ 0)
    (hP_late_nonneg : ∀ (j : Fin (w + 1)) (x : Fin (clock.m + 1)),
      0 ≤ P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C x (finSumFinEquiv (Sum.inr j)))
    (q : ℕ) :
    IsValidPriorityWord
      (liftedGameMat (AdjoinLeaderEndpointG clock.G b clock.v)
        (P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C)
        (J_admissible_scaled clock b H0 ch delta c_zeta))
      ((liftedScoreMat (AdjoinLeaderEndpointG clock.G b clock.v)
        (J_admissible_scaled clock b H0 ch delta c_zeta)
        (S_admissible clock b H0 ch delta)
        (X_gateway clock) (M_coupled w)
        (zeta_admissible_scaled clock b H0 ch delta c_zeta)).mulVec (binomBasis (w + 1) q))
      (paperPriorityRank clock.m w parent_rank)
      (W_early_word clock.m w q ++ W_late_word clock.m w q) :=
  isValidPriorityWord_reset_stages
    (AdjoinLeaderEndpointG clock.G b clock.v)
    (P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C)
    (J_admissible_scaled clock b H0 ch delta c_zeta)
    parent_rank _
    (admissible_stage1_priority_valid_unconditional clock b H0 ch delta c_zeta c_P0 a_old L_C parent_rank h_cz hP_early_nonpos q)
    (admissible_stage2_priority_valid_unconditional hw clock b H0 ch delta c_zeta c_P0 a_old L_C parent_rank h_cz hP_late_nonneg q)

/-- **Cone-Synchronized All-`q` Combined Reset Stages Priority Validity (`c_P0 = c_zeta`)**:
    Under synchronized cone scaling `c_P0 = c_zeta`, the sign conditions on `P_admissible_scaled`
    follow automatically from `P_admissible_scaled_cone_sign_bounds`. -/
theorem admissible_cone_reset_stages_priority_valid_unconditional {w : ℕ} (hw : 2 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (parent_rank : Fin clock.m → Fin clock.m)
    (h_cz : canonicalCZeta_full_admissible clock b H0 ch delta ≤ c_zeta)
    (hcone : (P0_cone a_old w).transpose * X_gateway clock =
      Q_reset (J_coupled w) (M_coupled w) (B_mat (w + 1)) (zeta_coupled w))
    (ha_pos : ∀ x, 0 < a_old x)
    (hdom : ∀ x r, |P_admissible_scaled clock b H0 ch delta 0 0 a_old L_C x r| ≤ c_zeta * a_old x / 2)
    (q : ℕ) :
    IsValidPriorityWord
      (liftedGameMat (AdjoinLeaderEndpointG clock.G b clock.v)
        (P_admissible_scaled clock b H0 ch delta c_zeta c_zeta a_old L_C)
        (J_admissible_scaled clock b H0 ch delta c_zeta))
      ((liftedScoreMat (AdjoinLeaderEndpointG clock.G b clock.v)
        (J_admissible_scaled clock b H0 ch delta c_zeta)
        (S_admissible clock b H0 ch delta)
        (X_gateway clock) (M_coupled w)
        (zeta_admissible_scaled clock b H0 ch delta c_zeta)).mulVec (binomBasis (w + 1) q))
      (paperPriorityRank clock.m w parent_rank)
      (W_early_word clock.m w q ++ W_late_word clock.m w q) := by
  have h1 : 1 ≤ canonicalCZeta_admissible clock b H0 ch delta :=
    one_le_canonicalCZeta_admissible clock b H0 ch delta
  have h2 : canonicalCZeta_admissible clock b H0 ch delta ≤ c_zeta :=
    le_trans (canonicalCZeta_admissible_le_full clock b H0 ch delta) h_cz
  have hc_pos : 0 < c_zeta := by linarith
  apply admissible_reset_stages_priority_valid_unconditional hw clock b H0 ch delta c_zeta c_zeta a_old L_C parent_rank h_cz
  · intro j x
    exact le_of_lt (P_admissible_scaled_cone_sign_bounds clock b H0 ch delta c_zeta a_old L_C hcone ha_pos hc_pos hdom x j).1.2
  · intro j x
    exact le_of_lt (P_admissible_scaled_cone_sign_bounds clock b H0 ch delta c_zeta a_old L_C hcone ha_pos hc_pos hdom x j).2.2

/-- Exact score evolution on old actions after the reset stages `W_early_word ++ W_late_word` for the scaled bundle lift. -/
theorem wordScore_after_reset_stages_bundle_inl {w : ℕ} (hw : 2 ≤ w) (clock : AlgebraicClock w)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (delta c_zeta c_P0 : ℚ) (q : ℕ) (u : Fin (clock.m + 1)) :
    wordScore (liftedGameMat (adjoinGatewayEndpointG clock.G clock.v)
        (P_bundle clock L_C delta c_zeta c_P0)
        (J_bundle clock delta c_zeta))
      ((liftedScoreMat (adjoinGatewayEndpointG clock.G clock.v)
          (J_bundle clock delta c_zeta)
          (S_bundle clock 0 delta)
          (X_gateway clock) (M_coupled w)
          (zeta_bundle_scaled clock delta c_zeta)).mulVec (binomBasis (w + 1) q))
      (W_early_word clock.m w q ++ W_late_word clock.m w q) (Sum.inl u) =
    (S_bundle clock 0 delta).mulVec (binomBasis (w + 1) (q + 1)) u := by
  have hPM := P_bundle_mul_M hw clock L_C delta c_zeta c_P0
  exact wordScore_after_reset_stages_inl clock
    (adjoinGatewayEndpointG clock.G clock.v)
    (P_bundle clock L_C delta c_zeta c_P0)
    (J_bundle clock delta c_zeta)
    (S_bundle clock 0 delta)
    (zeta_bundle_scaled clock delta c_zeta)
    hPM q u

/-- **Unconditional All-`q` Stage 1 Priority Validity for Scaled Bundle Lift**:
    Whenever `c_zeta ≥ canonicalCZeta_full_bundle` and early reset couplings are nonpositive,
    `W_early_word` is a valid priority word across all phase indices `q : ℕ`. -/
theorem bundle_stage1_priority_valid_unconditional {w : ℕ} (clock : AlgebraicClock w)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (delta c_zeta c_P0 : ℚ)
    (parent_rank : Fin clock.m → Fin clock.m)
    (h_cz : canonicalCZeta_full_bundle clock delta ≤ c_zeta)
    (hP_early_nonpos : ∀ (j : Fin (w + 1)) (x : Fin (clock.m + 1)),
      P_bundle clock L_C delta c_zeta c_P0 x (finSumFinEquiv (Sum.inl j)) ≤ 0)
    (q : ℕ) :
    IsValidPriorityWord
      (liftedGameMat (adjoinGatewayEndpointG clock.G clock.v)
        (P_bundle clock L_C delta c_zeta c_P0)
        (J_bundle clock delta c_zeta))
      ((liftedScoreMat (adjoinGatewayEndpointG clock.G clock.v)
        (J_bundle clock delta c_zeta)
        (S_bundle clock 0 delta)
        (X_gateway clock) (M_coupled w)
        (zeta_bundle_scaled clock delta c_zeta)).mulVec (binomBasis (w + 1) q))
      (paperPriorityRank clock.m w parent_rank)
      (W_early_word clock.m w q) := by
  have hbase_le_cz : canonicalCZeta clock delta ≤ c_zeta :=
    le_trans (canonicalCZeta_bundle_le_full clock delta) h_cz
  apply isValidPriorityWord_W_early_word_of_start
  · intro a b_idx hab
    exact J_bundle_lower clock delta c_zeta a b_idx hab
  · intro a b_idx hab
    exact J_bundle_subdiag_pos_of_ge clock delta c_zeta hbase_le_cz a b_idx hab
  · exact hP_early_nonpos
  · intro x
    exact bundle_stage1_old_below_ceiling_unconditional clock delta c_zeta h_cz x q

/-- **Unconditional All-`q` Stage 2 Priority Validity for Scaled Bundle Lift**:
    Whenever `c_zeta ≥ canonicalCZeta_full_bundle` and late reset couplings are nonnegative,
    `W_late_word` is a valid priority word across all phase indices `q : ℕ`. -/
theorem bundle_stage2_priority_valid_unconditional {w : ℕ} (hw : 2 ≤ w) (clock : AlgebraicClock w)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (delta c_zeta c_P0 : ℚ)
    (parent_rank : Fin clock.m → Fin clock.m)
    (h_cz : canonicalCZeta_full_bundle clock delta ≤ c_zeta)
    (hP_late_nonneg : ∀ (j : Fin (w + 1)) (x : Fin (clock.m + 1)),
      0 ≤ P_bundle clock L_C delta c_zeta c_P0 x (finSumFinEquiv (Sum.inr j)))
    (q : ℕ) :
    IsValidPriorityWord
      (liftedGameMat (adjoinGatewayEndpointG clock.G clock.v)
        (P_bundle clock L_C delta c_zeta c_P0)
        (J_bundle clock delta c_zeta))
      (wordScore
        (liftedGameMat (adjoinGatewayEndpointG clock.G clock.v)
          (P_bundle clock L_C delta c_zeta c_P0)
          (J_bundle clock delta c_zeta))
        ((liftedScoreMat (adjoinGatewayEndpointG clock.G clock.v)
          (J_bundle clock delta c_zeta)
          (S_bundle clock 0 delta)
          (X_gateway clock) (M_coupled w)
          (zeta_bundle_scaled clock delta c_zeta)).mulVec (binomBasis (w + 1) q))
        (W_early_word clock.m w q))
      (paperPriorityRank clock.m w parent_rank)
      (W_late_word clock.m w q) := by
  have hbase_le_cz : canonicalCZeta clock delta ≤ c_zeta :=
    le_trans (canonicalCZeta_bundle_le_full clock delta) h_cz
  apply isValidPriorityWord_W_late_word_of_end
  · intro a b_idx hab
    exact J_bundle_lower clock delta c_zeta a b_idx hab
  · intro a b_idx hab
    exact J_bundle_subdiag_pos_of_ge clock delta c_zeta hbase_le_cz a b_idx hab
  · exact hP_late_nonneg
  · intro x
    rw [wordScore_after_reset_stages_bundle_inl hw clock L_C delta c_zeta c_P0 q x]
    exact bundle_stage2_old_below_ceiling_unconditional clock delta c_zeta h_cz x q

/-- **Unconditional All-`q` Combined Reset Stages Priority Validity for Scaled Bundle Lift**:
    Combines Stage 1 and Stage 2 into full priority validity of `W_early_word ++ W_late_word`
    for all `q : ℕ`. -/
theorem bundle_reset_stages_priority_valid_unconditional {w : ℕ} (hw : 2 ≤ w) (clock : AlgebraicClock w)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (delta c_zeta c_P0 : ℚ)
    (parent_rank : Fin clock.m → Fin clock.m)
    (h_cz : canonicalCZeta_full_bundle clock delta ≤ c_zeta)
    (hP_early_nonpos : ∀ (j : Fin (w + 1)) (x : Fin (clock.m + 1)),
      P_bundle clock L_C delta c_zeta c_P0 x (finSumFinEquiv (Sum.inl j)) ≤ 0)
    (hP_late_nonneg : ∀ (j : Fin (w + 1)) (x : Fin (clock.m + 1)),
      0 ≤ P_bundle clock L_C delta c_zeta c_P0 x (finSumFinEquiv (Sum.inr j)))
    (q : ℕ) :
    IsValidPriorityWord
      (liftedGameMat (adjoinGatewayEndpointG clock.G clock.v)
        (P_bundle clock L_C delta c_zeta c_P0)
        (J_bundle clock delta c_zeta))
      ((liftedScoreMat (adjoinGatewayEndpointG clock.G clock.v)
        (J_bundle clock delta c_zeta)
        (S_bundle clock 0 delta)
        (X_gateway clock) (M_coupled w)
        (zeta_bundle_scaled clock delta c_zeta)).mulVec (binomBasis (w + 1) q))
      (paperPriorityRank clock.m w parent_rank)
      (W_early_word clock.m w q ++ W_late_word clock.m w q) :=
  isValidPriorityWord_reset_stages
    (adjoinGatewayEndpointG clock.G clock.v)
    (P_bundle clock L_C delta c_zeta c_P0)
    (J_bundle clock delta c_zeta)
    parent_rank _
    (bundle_stage1_priority_valid_unconditional clock L_C delta c_zeta c_P0 parent_rank h_cz hP_early_nonpos q)
    (bundle_stage2_priority_valid_unconditional hw clock L_C delta c_zeta c_P0 parent_rank h_cz hP_late_nonneg q)

/-!
## Section 8: Stage 3–4 Reduced Chronology Specifications & All-Orders Theorems

With Stage 1 (`W_early_word`) and Stage 2 (`W_late_word`) unconditionally verified across all
phases `q : ℕ` whenever `c_zeta ≥ canonicalCZeta_full_admissible` (resp. `canonicalCZeta_full_bundle`),
we now:
1. Prove the exact value equivalence between `admissibleStageRank` and `paperPriorityRank`.
2. Generalize the all-time duality gap bounds (`admissible_hgap_low_of_ge`, `admissible_hgap_high_of_ge`,
   `bundle_hgap_low_of_ge`, `bundle_hgap_high_of_ge`) to any `c_zeta ≥ canonicalCZeta_admissible`
   (resp. `canonicalCZeta`).
3. Verify the unconditional `d = 0` base case of `admissiblePhaseWordFamily` and `bundlePhaseWordFamily`
   for all `q : ℕ`.
4. Package `Stage34AdmissibleChronologySpec` and `Stage34BundleChronologySpec` — where Stages 1 & 2
   are completely eliminated — and prove the corresponding all-orders Karlin theorems
   `all_orders_stage34_admissible_karlin_theorem` and `all_orders_stage34_bundle_karlin_theorem`.
-/

/-- `admissibleStageRank` and `paperPriorityRank` assign the exact same numeric priority value to every action. -/
theorem admissibleStageRank_val_eq_paperPriorityRank_val (m w : ℕ) (parent_rank : Fin m → Fin m)
    (x : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1))) :
    (admissibleStageRank m w parent_rank x).val = (paperPriorityRank m w parent_rank x).val := by
  cases x with
  | inl u =>
    dsimp only [admissibleStageRank, paperPriorityRank]
    cases (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).symm u with
    | inl i => rfl
    | inr _ =>
      dsimp only
      omega
  | inr r =>
    dsimp only [admissibleStageRank, paperPriorityRank]
    have hr := r.isLt
    omega

/-- Priority word validity under `admissibleStageRank` is equivalent to priority word validity under `paperPriorityRank`. -/
theorem isValidPriorityWord_admissibleStageRank_iff_paperPriorityRank {m w : ℕ}
    (M : Matrix (Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1))) (Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1))) ℚ)
    (s0 : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (parent_rank : Fin m → Fin m)
    (W : List (Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))) :
    IsValidPriorityWord M s0 (admissibleStageRank m w parent_rank) W ↔
      IsValidPriorityWord M s0 (paperPriorityRank m w parent_rank) W :=
  isValidPriorityWord_congr_rank_val M s0
    (admissibleStageRank m w parent_rank)
    (paperPriorityRank m w parent_rank)
    (admissibleStageRank_val_eq_paperPriorityRank_val m w parent_rank) W

/-- Unconditional priority validity of `admissiblePhaseWordFamily` at base level `d = 0` across all `q : ℕ`. -/
theorem isValidPriorityWord_admissiblePhaseWordFamily_zero (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (q : ℕ) :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 0
    IsValidPriorityWord fc.clock.G (fc.clock.R.mulVec (binomBasis 2 q))
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 0)
      (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 0 q) :=
  isValidPriorityWord_rpsPhaseWord q id

/-- Unconditional priority validity of `bundlePhaseWordFamily` at base level `d = 0` across all `q : ℕ`. -/
theorem isValidPriorityWord_bundlePhaseWordFamily_zero (delta c_zeta c_P0 : ℕ → ℚ) (q : ℕ) :
    let fc := bundleFullRankClockFamily delta c_zeta c_P0 0
    IsValidPriorityWord fc.clock.G (fc.clock.R.mulVec (binomBasis 2 q))
      (bundlePriorityRankFamily delta c_zeta c_P0 0)
      (bundlePhaseWordFamily delta c_zeta c_P0 0 q) :=
  isValidPriorityWord_rpsPhaseWord q id

/-- Degree-`w` lower bound on the phase-start ceiling score for the admissible lift for any `c_zeta ≥ canonicalCZeta_admissible`. -/
theorem ceiling_admissible_ge_choose_of_ge {w : ℕ} (hw : 1 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ)
    (h_cz : canonicalCZeta_admissible clock b H0 ch delta ≤ c_zeta) (q : ℕ) :
    1 + (Nat.choose q w : ℚ) ≤
      dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) q) := by
  have hbase := ceiling_canonicalCZeta_admissible_ge_choose hw clock b H0 ch delta q
  have hmono : dotProduct (zeta_admissible_scaled clock b H0 ch delta (canonicalCZeta_admissible clock b H0 ch delta))
      (binomBasis (w + 1) q) ≤
      dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) q) := by
    dsimp only [dotProduct]
    refine Finset.sum_le_sum fun c _ => ?_
    have hb : 0 ≤ binomBasis (w + 1) q c := by unfold binomBasis; positivity
    have hzeta : zeta_admissible_scaled clock b H0 ch delta (canonicalCZeta_admissible clock b H0 ch delta) c ≤
        zeta_admissible_scaled clock b H0 ch delta c_zeta c := by
      have : zeta_coupled w c = 1 := rfl
      unfold zeta_admissible_scaled
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, this]
      linarith
    exact mul_le_mul_of_nonneg_right hzeta hb
  exact le_trans hbase hmono

/-- Degree-`w` lower bound on the phase-start ceiling score for the bundle lift for any `c_zeta ≥ canonicalCZeta`. -/
theorem ceiling_bundle_ge_choose_of_ge {w : ℕ} (hw : 1 ≤ w) (clock : AlgebraicClock w)
    (delta c_zeta : ℚ)
    (h_cz : canonicalCZeta clock delta ≤ c_zeta) (q : ℕ) :
    1 + (Nat.choose q w : ℚ) ≤
      dotProduct (zeta_bundle_scaled clock delta c_zeta) (binomBasis (w + 1) q) := by
  have hbase := ceiling_canonicalCZeta_ge_choose hw clock delta q
  have hmono : dotProduct (zeta_bundle_scaled clock delta (canonicalCZeta clock delta))
      (binomBasis (w + 1) q) ≤
      dotProduct (zeta_bundle_scaled clock delta c_zeta) (binomBasis (w + 1) q) := by
    dsimp only [dotProduct]
    refine Finset.sum_le_sum fun c _ => ?_
    have hb : 0 ≤ binomBasis (w + 1) q c := by unfold binomBasis; positivity
    have hzeta : zeta_bundle_scaled clock delta (canonicalCZeta clock delta) c ≤
        zeta_bundle_scaled clock delta c_zeta c := by
      have : zeta_coupled w c = 1 := rfl
      unfold zeta_bundle_scaled
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, this]
      linarith
    exact mul_le_mul_of_nonneg_right hzeta hb
  exact le_trans hbase hmono

/-- General-`c_zeta` lower duality-gap bound for the scaled admissible lift (`c_zeta ≥ canonicalCZeta_admissible`). -/
theorem admissible_hgap_low_of_ge {k : ℕ} (hw : 2 ≤ k) (fc : FullRankClock k)
    (b : Fin fc.clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (fc.clock.m + 1) → ℚ)
    (h_cz : canonicalCZeta_admissible fc.clock b H0 ch delta ≤ c_zeta)
    (phaseShift : ℕ) (hshift : k ≤ phaseShift)
    (parentWord : ℕ → List (Fin fc.clock.m))
    (hparent_count : ∀ σ : ℕ, wordCountVec (parentWord σ) = fc.clock.C.mulVec (binomBasis k σ))
    {m_rank : ℕ} (hm_rank : 0 < m_rank)
    (rank : Fin (admissibleScaledFullRankLift hw fc b H0 ch delta c_zeta c_P0 a_old).clock.m → Fin m_rank)
    (p : ℕ) :
    let shift := admissibleBiasedScoreShift hw fc b H0 ch delta c_zeta c_P0 a_old rank phaseShift
    bundle_c_low fc phaseShift *
      (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map
        (rotLeaderEquiv (fc.clock.m + 1) ((k + 1) + (k + 1)) : _ ≃ Fin (admissibleScaledFullRankLift hw fc b H0 ch delta c_zeta c_P0 a_old).clock.m)) (p + 1) : ℚ) ^ k ≤
      (2 * (dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta)
        (binomBasis (k + 1) (p + phaseShift)) + shift)) ^ (k + 1) := by
  intro shift
  have hshift_nonneg : 0 ≤ shift := admissibleBiasedScoreShift_nonneg hw fc b H0 ch delta c_zeta c_P0 a_old hm_rank rank phaseShift
  have h_hw1 : 1 ≤ k := by omega
  have h_dot_ge := ceiling_admissible_ge_choose_of_ge h_hw1 fc.clock b H0 ch delta c_zeta h_cz (p + phaseShift)
  have h_choose_le : (p + 1 : ℚ) ^ k ≤ (k.factorial : ℚ) * (Nat.choose (p + phaseShift) k : ℚ) := by
    exact_mod_cast pow_le_factorial_mul_choose_shifted k phaseShift hshift p
  have h_fact_pos : 0 < (k.factorial : ℚ) := by positivity
  have h_choose_div : (p + 1 : ℚ) ^ k / (k.factorial : ℚ) ≤ (Nat.choose (p + phaseShift) k : ℚ) := by
    rw [div_le_iff₀ h_fact_pos]
    linarith [h_choose_le]
  have h_score_ge : (p + 1 : ℚ) ^ k / (k.factorial : ℚ) ≤
      dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift := by
    calc (p + 1 : ℚ) ^ k / (k.factorial : ℚ) ≤ (Nat.choose (p + phaseShift) k : ℚ) := h_choose_div
      _ ≤ 1 + (Nat.choose (p + phaseShift) k : ℚ) := by linarith
      _ ≤ dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) := h_dot_ge
      _ ≤ dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift := by linarith [hshift_nonneg]
  have h_score_mul : (2 / (k.factorial : ℚ)) * ((p + 1 : ℚ) ^ k) ≤
      2 * (dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift) := by
    calc (2 / (k.factorial : ℚ)) * ((p + 1 : ℚ) ^ k) = 2 * ((p + 1 : ℚ) ^ k / (k.factorial : ℚ)) := by ring
      _ ≤ 2 * (dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift) :=
        mul_le_mul_of_nonneg_left h_score_ge (by positivity)
  have h_pow_score : ((2 / (k.factorial : ℚ)) * ((p + 1 : ℚ) ^ k)) ^ (k + 1) ≤
      (2 * (dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift)) ^ (k + 1) := by
    have h_nonneg_lhs : 0 ≤ (2 / (k.factorial : ℚ)) * ((p + 1 : ℚ) ^ k) := by positivity
    exact pow_le_pow_left₀ h_nonneg_lhs h_score_mul (k + 1)
  rw [mul_pow] at h_pow_score
  have h_pow_comm1 : (((p + 1 : ℚ) ^ k) ^ (k + 1)) = (p + 1 : ℚ) ^ (k * (k + 1)) :=
    (pow_mul (p + 1 : ℚ) k (k + 1)).symm
  rw [h_pow_comm1] at h_pow_score
  let rotEquiv := rotLeaderEquiv (fc.clock.m + 1) ((k + 1) + (k + 1))
  have h_step_equiv :
      (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map rotEquiv) (p + 1) : ℚ) =
      (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) := by
    unfold wordPhaseStartStep runStart
    simp only [List.length_map]
  rw [h_step_equiv]
  have h_upper := wordPhaseStartStep_shifted_upper_pow fc parentWord hparent_count phaseShift p
  have h_step_nonneg : 0 ≤ (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) := by positivity
  have h_upper_pow : (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) ^ k ≤
      ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) * ((p + 1 : ℚ) ^ (k + 1))) ^ k :=
    pow_le_pow_left₀ h_step_nonneg h_upper k
  rw [mul_pow] at h_upper_pow
  have h_pow_comm2 : (((p + 1 : ℚ) ^ (k + 1)) ^ k) = (p + 1 : ℚ) ^ (k * (k + 1)) := by
    have h1 : (((p + 1 : ℚ) ^ (k + 1)) ^ k) = (p + 1 : ℚ) ^ ((k + 1) * k) :=
      (pow_mul (p + 1 : ℚ) (k + 1) k).symm
    have h2 : (k + 1) * k = k * (k + 1) := by ring
    rw [h1, h2]
  rw [h_pow_comm2] at h_upper_pow
  have h_denom_pos : 0 < (1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k := by
    have : 0 < C_len fc := C_len_pos fc
    positivity
  have h_low_step : bundle_c_low fc phaseShift * (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) ^ k ≤
      (2 / (k.factorial : ℚ)) ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := by
    unfold bundle_c_low
    have h_div_mul : (2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
        (((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) * (p + 1 : ℚ) ^ (k * (k + 1))) =
        (2 / (k.factorial : ℚ)) ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := by
      calc (2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
          (((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) * (p + 1 : ℚ) ^ (k * (k + 1))) =
          ((2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
            ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k)) * (p + 1 : ℚ) ^ (k * (k + 1)) := by ring
        _ = (2 / (k.factorial : ℚ)) ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := by
          rw [div_mul_cancel₀ _ (ne_of_gt h_denom_pos)]
    calc (2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
          (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) ^ k ≤
        (2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
          (((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) * (p + 1 : ℚ) ^ (k * (k + 1))) :=
        mul_le_mul_of_nonneg_left h_upper_pow (by positivity)
      _ = (2 / (k.factorial : ℚ)) ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := h_div_mul
  exact le_trans h_low_step h_pow_score

/-- General-`c_zeta` upper duality-gap bound for the scaled admissible lift (`c_zeta ≥ canonicalCZeta_admissible`). -/
theorem admissible_hgap_high_of_ge {k : ℕ} (hw : 2 ≤ k) (fc : FullRankClock k)
    (b : Fin fc.clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (fc.clock.m + 1) → ℚ)
    (h_cz : canonicalCZeta_admissible fc.clock b H0 ch delta ≤ c_zeta)
    (phaseShift : ℕ) (hshift : k ≤ phaseShift)
    (parentWord : ℕ → List (Fin fc.clock.m))
    (hparent_count : ∀ σ : ℕ, wordCountVec (parentWord σ) = fc.clock.C.mulVec (binomBasis k σ))
    {m_rank : ℕ} (hm_rank : 0 < m_rank)
    (rank : Fin (admissibleScaledFullRankLift hw fc b H0 ch delta c_zeta c_P0 a_old).clock.m → Fin m_rank)
    (p : ℕ) :
    let shift := admissibleBiasedScoreShift hw fc b H0 ch delta c_zeta c_P0 a_old rank phaseShift
    (2 * (dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta)
      (binomBasis (k + 1) (p + 1 + phaseShift)) + shift)) ^ (k + 1) ≤
      admissible_c_high_gen fc b H0 ch delta c_zeta shift phaseShift *
        (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map
          (rotLeaderEquiv (fc.clock.m + 1) ((k + 1) + (k + 1)) : _ ≃ Fin (admissibleScaledFullRankLift hw fc b H0 ch delta c_zeta c_P0 a_old).clock.m)) p : ℚ) ^ k := by
  intro shift
  have hshift_nonneg : 0 ≤ shift := admissibleBiasedScoreShift_nonneg hw fc b H0 ch delta c_zeta c_P0 a_old hm_rank rank phaseShift
  let C_base := 2 * (C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1))
  have h_nonneg_score : 0 ≤ 2 * (dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift) := by
    have h_hw1 : 1 ≤ k := by omega
    have h_dot_ge := ceiling_admissible_ge_choose_of_ge h_hw1 fc.clock b H0 ch delta c_zeta h_cz (p + 1 + phaseShift)
    have h1 : 0 ≤ (Nat.choose (p + 1 + phaseShift) k : ℚ) := by positivity
    have h2 : 0 ≤ dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) := by linarith
    have h3 : 0 ≤ dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift := by linarith [hshift_nonneg]
    linarith
  have h_bound_lin := score_upper_bound_admissible fc b H0 ch delta c_zeta shift phaseShift p
  have h_bound_pow : (2 * (dotProduct (zeta_admissible_scaled fc.clock b H0 ch delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift)) ^ (k + 1) ≤
      (C_base * (p + 1 : ℚ) ^ k) ^ (k + 1) :=
    pow_le_pow_left₀ h_nonneg_score h_bound_lin (k + 1)
  have h_rhs_rw : (C_base * (p + 1 : ℚ) ^ k) ^ (k + 1) = C_base ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := by
    rw [mul_pow]
    have h_pow_comm : (((p + 1 : ℚ) ^ k) ^ (k + 1)) = (p + 1 : ℚ) ^ (k * (k + 1)) :=
      (pow_mul (p + 1 : ℚ) k (k + 1)).symm
    rw [h_pow_comm]
  rw [h_rhs_rw] at h_bound_pow
  have hC_base_nonneg : 0 ≤ C_base := by
    have : 0 ≤ C_zeta_sum_admissible fc.clock b H0 ch delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k := by
      unfold C_zeta_sum_admissible
      have : 0 ≤ ∑ c : Fin (k + 1), |zeta_admissible_scaled fc.clock b H0 ch delta c_zeta c| :=
        Finset.sum_nonneg fun c _ => abs_nonneg _
      positivity
    linarith [abs_nonneg shift]
  have hC_base_pow_nonneg : 0 ≤ C_base ^ (k + 1) := pow_nonneg hC_base_nonneg (k + 1)
  let rotEquiv := rotLeaderEquiv (fc.clock.m + 1) ((k + 1) + (k + 1))
  have h_step_equiv :
      (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map rotEquiv) p : ℚ) =
      (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) p : ℚ) := by
    unfold wordPhaseStartStep runStart
    simp only [List.length_map]
  let phaseWord : ℕ → List (Fin (fc.clock.m + 1 + ((k + 1) + (k + 1)))) := fun q =>
    (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv
  have h_step_rw : (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map rotEquiv) p : ℚ) =
      (wordPhaseStartStep phaseWord p : ℚ) := h_step_equiv
  rw [h_step_rw]
  cases p with
  | zero =>
    have h_p0_step : (wordPhaseStartStep phaseWord 0 : ℚ) = 1 := by
      unfold wordPhaseStartStep runStart
      push_cast
      simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    have hp0_pow : (↑(0 : ℕ) + 1 : ℚ) ^ (k * (k + 1)) = 1 := by ring
    rw [hp0_pow, mul_one] at h_bound_pow
    have h_denom_pos_nat : 0 < 2 ^ (k + 1) * (k + 1).factorial := by positivity
    have h_denom_ge_one : 1 ≤ ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) := by
      exact_mod_cast Nat.succ_le_of_lt h_denom_pos_nat
    have h_pow_denom_ge_one : 1 ≤ ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k :=
      one_le_pow₀ h_denom_ge_one
    have h_c_high_ge : C_base ^ (k + 1) ≤
        admissible_c_high_gen fc b H0 ch delta c_zeta shift phaseShift := by
      unfold admissible_c_high_gen
      calc C_base ^ (k + 1) = C_base ^ (k + 1) * 1 := by ring
        _ ≤ C_base ^ (k + 1) * ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k :=
          mul_le_mul_of_nonneg_left h_pow_denom_ge_one hC_base_pow_nonneg
    have h_trans := le_trans h_bound_pow h_c_high_ge
    rw [h_p0_step, one_pow, mul_one]
    exact h_trans
  | succ m =>
    have h_lower := wordPhaseStartStep_shifted_lower_pow fc parentWord hparent_count phaseShift hshift (m + 1)
    have h_denom_pos : 0 < ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) := by positivity
    have h_cast_m : ((m + 1 : ℕ) + 1 : ℚ) = (m + 1 + 1 : ℚ) := by push_cast; ring
    rw [h_cast_m] at h_lower
    have h_m1_le : (m + 1 + 1 : ℚ) ^ (k + 1) ≤ ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) * (wordPhaseStartStep phaseWord (m + 1) : ℚ) := by
      have h := (div_le_iff₀ h_denom_pos).mp h_lower
      linarith [h]
    have h_m1_pow_k : ((m + 1 + 1 : ℚ) ^ (k + 1)) ^ k ≤
        (((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) * (wordPhaseStartStep phaseWord (m + 1) : ℚ)) ^ k :=
      pow_le_pow_left₀ (by positivity) h_m1_le k
    rw [mul_pow] at h_m1_pow_k
    have h_pow_comm2 : (((m + 1 + 1 : ℚ) ^ (k + 1)) ^ k) = (m + 1 + 1 : ℚ) ^ (k * (k + 1)) := by
      have h1 : (((m + 1 + 1 : ℚ) ^ (k + 1)) ^ k) = (m + 1 + 1 : ℚ) ^ ((k + 1) * k) :=
        (pow_mul (m + 1 + 1 : ℚ) (k + 1) k).symm
      have h2 : (k + 1) * k = k * (k + 1) := by ring
      rw [h1, h2]
    rw [h_pow_comm2] at h_m1_pow_k
    have h_step_bound : C_base ^ (k + 1) * (m + 1 + 1 : ℚ) ^ (k * (k + 1)) ≤
        (C_base ^ (k + 1) * ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k) *
          (wordPhaseStartStep phaseWord (m + 1) : ℚ) ^ k := by
      calc C_base ^ (k + 1) * (m + 1 + 1 : ℚ) ^ (k * (k + 1)) ≤
          C_base ^ (k + 1) * ((((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k) * (wordPhaseStartStep phaseWord (m + 1) : ℚ) ^ k) :=
            mul_le_mul_of_nonneg_left h_m1_pow_k hC_base_pow_nonneg
        _ = (C_base ^ (k + 1) * ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k) *
              (wordPhaseStartStep phaseWord (m + 1) : ℚ) ^ k := by ring
    rw [h_cast_m] at h_bound_pow
    exact le_trans h_bound_pow h_step_bound

/-- General-`c_zeta` lower duality-gap bound for the scaled bundle lift (`c_zeta ≥ canonicalCZeta`). -/
theorem bundle_hgap_low_of_ge {k : ℕ} (hw : 2 ≤ k) (fc : FullRankClock k)
    (delta c_zeta c_P0 : ℚ)
    (h_cz : canonicalCZeta fc.clock delta ≤ c_zeta)
    (phaseShift : ℕ) (hshift : k ≤ phaseShift)
    (parentWord : ℕ → List (Fin fc.clock.m))
    (hparent_count : ∀ σ : ℕ, wordCountVec (parentWord σ) = fc.clock.C.mulVec (binomBasis k σ))
    {m_rank : ℕ} (hm_rank : 0 < m_rank)
    (rank : Fin (bundleFullRankLift hw fc delta c_zeta c_P0).clock.m → Fin m_rank)
    (p : ℕ) :
    let shift := bundleBiasedScoreShift hw fc delta c_zeta c_P0 rank phaseShift
    bundle_c_low fc phaseShift *
      (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map
        (finSumFinEquiv : _ ≃ Fin (bundleFullRankLift hw fc delta c_zeta c_P0).clock.m)) (p + 1) : ℚ) ^ k ≤
      (2 * (dotProduct (zeta_bundle_scaled fc.clock delta c_zeta)
        (binomBasis (k + 1) (p + phaseShift)) + shift)) ^ (k + 1) := by
  intro shift
  have hshift_nonneg : 0 ≤ shift := bundleBiasedScoreShift_nonneg hw fc delta c_zeta c_P0 hm_rank rank phaseShift
  have h_hw1 : 1 ≤ k := by omega
  have h_dot_ge := ceiling_bundle_ge_choose_of_ge h_hw1 fc.clock delta c_zeta h_cz (p + phaseShift)
  have h_choose_le : (p + 1 : ℚ) ^ k ≤ (k.factorial : ℚ) * (Nat.choose (p + phaseShift) k : ℚ) := by
    exact_mod_cast pow_le_factorial_mul_choose_shifted k phaseShift hshift p
  have h_fact_pos : 0 < (k.factorial : ℚ) := by positivity
  have h_choose_div : (p + 1 : ℚ) ^ k / (k.factorial : ℚ) ≤ (Nat.choose (p + phaseShift) k : ℚ) := by
    rw [div_le_iff₀ h_fact_pos]
    linarith [h_choose_le]
  have h_score_ge : (p + 1 : ℚ) ^ k / (k.factorial : ℚ) ≤
      dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift := by
    calc (p + 1 : ℚ) ^ k / (k.factorial : ℚ) ≤ (Nat.choose (p + phaseShift) k : ℚ) := h_choose_div
      _ ≤ 1 + (Nat.choose (p + phaseShift) k : ℚ) := by linarith
      _ ≤ dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) := h_dot_ge
      _ ≤ dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift := by linarith [hshift_nonneg]
  have h_score_mul : (2 / (k.factorial : ℚ)) * ((p + 1 : ℚ) ^ k) ≤
      2 * (dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift) := by
    calc (2 / (k.factorial : ℚ)) * ((p + 1 : ℚ) ^ k) = 2 * ((p + 1 : ℚ) ^ k / (k.factorial : ℚ)) := by ring
      _ ≤ 2 * (dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift) :=
        mul_le_mul_of_nonneg_left h_score_ge (by positivity)
  have h_pow_score : ((2 / (k.factorial : ℚ)) * ((p + 1 : ℚ) ^ k)) ^ (k + 1) ≤
      (2 * (dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + phaseShift)) + shift)) ^ (k + 1) := by
    have h_nonneg_lhs : 0 ≤ (2 / (k.factorial : ℚ)) * ((p + 1 : ℚ) ^ k) := by positivity
    exact pow_le_pow_left₀ h_nonneg_lhs h_score_mul (k + 1)
  rw [mul_pow] at h_pow_score
  have h_pow_comm1 : (((p + 1 : ℚ) ^ k) ^ (k + 1)) = (p + 1 : ℚ) ^ (k * (k + 1)) :=
    (pow_mul (p + 1 : ℚ) k (k + 1)).symm
  rw [h_pow_comm1] at h_pow_score
  have h_upper := wordPhaseStartStep_shifted_upper_pow fc parentWord hparent_count phaseShift p
  have h_step_nonneg : 0 ≤ (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) := by positivity
  have h_upper_pow : (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) ^ k ≤
      ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) * ((p + 1 : ℚ) ^ (k + 1))) ^ k :=
    pow_le_pow_left₀ h_step_nonneg h_upper k
  rw [mul_pow] at h_upper_pow
  have h_pow_comm2 : (((p + 1 : ℚ) ^ (k + 1)) ^ k) = (p + 1 : ℚ) ^ (k * (k + 1)) := by
    have h1 : (((p + 1 : ℚ) ^ (k + 1)) ^ k) = (p + 1 : ℚ) ^ ((k + 1) * k) :=
      (pow_mul (p + 1 : ℚ) (k + 1) k).symm
    have h2 : (k + 1) * k = k * (k + 1) := by ring
    rw [h1, h2]
  rw [h_pow_comm2] at h_upper_pow
  have h_denom_pos : 0 < (1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k := by
    have : 0 < C_len fc := C_len_pos fc
    positivity
  have h_low_step : bundle_c_low fc phaseShift * (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) ^ k ≤
      (2 / (k.factorial : ℚ)) ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := by
    unfold bundle_c_low
    have h_div_mul : (2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
        (((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) * (p + 1 : ℚ) ^ (k * (k + 1))) =
        (2 / (k.factorial : ℚ)) ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := by
      calc (2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
          (((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) * (p + 1 : ℚ) ^ (k * (k + 1))) =
          ((2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
            ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k)) * (p + 1 : ℚ) ^ (k * (k + 1)) := by ring
        _ = (2 / (k.factorial : ℚ)) ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := by
          rw [div_mul_cancel₀ _ (ne_of_gt h_denom_pos)]
    calc (2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
          (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv) (p + 1) : ℚ) ^ k ≤
        (2 / (k.factorial : ℚ)) ^ (k + 1) / ((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) *
          (((1 + C_len fc * ((phaseShift + 1 : ℚ) ^ k)) ^ k) * (p + 1 : ℚ) ^ (k * (k + 1))) :=
        mul_le_mul_of_nonneg_left h_upper_pow (by positivity)
      _ = (2 / (k.factorial : ℚ)) ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := h_div_mul
  exact le_trans h_low_step h_pow_score

/-- General-`c_zeta` upper duality-gap bound for the scaled bundle lift (`c_zeta ≥ canonicalCZeta`). -/
theorem bundle_hgap_high_of_ge {k : ℕ} (hw : 2 ≤ k) (fc : FullRankClock k)
    (delta c_zeta c_P0 : ℚ)
    (h_cz : canonicalCZeta fc.clock delta ≤ c_zeta)
    (phaseShift : ℕ) (hshift : k ≤ phaseShift)
    (parentWord : ℕ → List (Fin fc.clock.m))
    (hparent_count : ∀ σ : ℕ, wordCountVec (parentWord σ) = fc.clock.C.mulVec (binomBasis k σ))
    {m_rank : ℕ} (hm_rank : 0 < m_rank)
    (rank : Fin (bundleFullRankLift hw fc delta c_zeta c_P0).clock.m → Fin m_rank)
    (p : ℕ) :
    let shift := bundleBiasedScoreShift hw fc delta c_zeta c_P0 rank phaseShift
    (2 * (dotProduct (zeta_bundle_scaled fc.clock delta c_zeta)
      (binomBasis (k + 1) (p + 1 + phaseShift)) + shift)) ^ (k + 1) ≤
      bundle_c_high_gen fc delta c_zeta shift phaseShift *
        (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map
          (finSumFinEquiv : _ ≃ Fin (bundleFullRankLift hw fc delta c_zeta c_P0).clock.m)) p : ℚ) ^ k := by
  intro shift
  have hshift_nonneg : 0 ≤ shift := bundleBiasedScoreShift_nonneg hw fc delta c_zeta c_P0 hm_rank rank phaseShift
  let C_base := 2 * (C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k + (|shift| + 1))
  have h_hw1 : 1 ≤ k := by omega
  have h_dot_ge := ceiling_bundle_ge_choose_of_ge h_hw1 fc.clock delta c_zeta h_cz (p + 1 + phaseShift)
  have h_nonneg_score : 0 ≤ 2 * (dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift) := by
    have h1 : 0 ≤ (Nat.choose (p + 1 + phaseShift) k : ℚ) := by positivity
    have h2 : 0 ≤ dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) := by linarith
    have h3 : 0 ≤ dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift := by linarith [hshift_nonneg]
    linarith
  have h_bound_lin := score_upper_bound fc delta c_zeta shift phaseShift p
  have h_bound_pow : (2 * (dotProduct (zeta_bundle_scaled fc.clock delta c_zeta) (binomBasis (k + 1) (p + 1 + phaseShift)) + shift)) ^ (k + 1) ≤
      (C_base * (p + 1 : ℚ) ^ k) ^ (k + 1) :=
    pow_le_pow_left₀ h_nonneg_score h_bound_lin (k + 1)
  have h_rhs_rw : (C_base * (p + 1 : ℚ) ^ k) ^ (k + 1) = C_base ^ (k + 1) * (p + 1 : ℚ) ^ (k * (k + 1)) := by
    rw [mul_pow]
    have h_pow_comm : (((p + 1 : ℚ) ^ k) ^ (k + 1)) = (p + 1 : ℚ) ^ (k * (k + 1)) :=
      (pow_mul (p + 1 : ℚ) k (k + 1)).symm
    rw [h_pow_comm]
  rw [h_rhs_rw] at h_bound_pow
  have hC_base_nonneg : 0 ≤ C_base := by
    have : 0 ≤ C_zeta_sum fc.clock delta c_zeta * ((phaseShift + 1 : ℚ) ^ k) * 2 ^ k := by
      unfold C_zeta_sum
      have : 0 ≤ ∑ c : Fin (k + 1), |zeta_bundle_scaled fc.clock delta c_zeta c| :=
        Finset.sum_nonneg fun c _ => abs_nonneg _
      positivity
    linarith [abs_nonneg shift]
  have hC_base_pow_nonneg : 0 ≤ C_base ^ (k + 1) := pow_nonneg hC_base_nonneg (k + 1)
  let phaseWord : ℕ → List (Fin (fc.clock.m + 1 + ((k + 1) + (k + 1)))) := fun q =>
    (rawFourStageWord fc.clock parentWord (q + phaseShift)).map finSumFinEquiv
  have h_step_rw : (wordPhaseStartStep (fun q => (rawFourStageWord fc.clock parentWord (q + phaseShift)).map
      (finSumFinEquiv : _ ≃ Fin (bundleFullRankLift hw fc delta c_zeta c_P0).clock.m)) p : ℚ) =
      (wordPhaseStartStep phaseWord p : ℚ) := rfl
  rw [h_step_rw]
  cases p with
  | zero =>
    have h_p0_step : (wordPhaseStartStep phaseWord 0 : ℚ) = 1 := by
      unfold wordPhaseStartStep runStart
      push_cast
      simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    have hp0_pow : (↑(0 : ℕ) + 1 : ℚ) ^ (k * (k + 1)) = 1 := by ring
    rw [hp0_pow, mul_one] at h_bound_pow
    have h_denom_pos_nat : 0 < 2 ^ (k + 1) * (k + 1).factorial := by positivity
    have h_denom_ge_one : 1 ≤ ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) := by
      exact_mod_cast Nat.succ_le_of_lt h_denom_pos_nat
    have h_pow_denom_ge_one : 1 ≤ ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k :=
      one_le_pow₀ h_denom_ge_one
    have h_c_high_ge : C_base ^ (k + 1) ≤
        bundle_c_high_gen fc delta c_zeta shift phaseShift := by
      unfold bundle_c_high_gen
      calc C_base ^ (k + 1) = C_base ^ (k + 1) * 1 := by ring
        _ ≤ C_base ^ (k + 1) * ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k :=
          mul_le_mul_of_nonneg_left h_pow_denom_ge_one hC_base_pow_nonneg
    have h_trans := le_trans h_bound_pow h_c_high_ge
    rw [h_p0_step, one_pow, mul_one]
    exact h_trans
  | succ m =>
    have h_lower := wordPhaseStartStep_shifted_lower_pow fc parentWord hparent_count phaseShift hshift (m + 1)
    have h_denom_pos : 0 < ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) := by positivity
    have h_cast_m : ((m + 1 : ℕ) + 1 : ℚ) = (m + 1 + 1 : ℚ) := by push_cast; ring
    rw [h_cast_m] at h_lower
    have h_m1_le : (m + 1 + 1 : ℚ) ^ (k + 1) ≤ ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) * (wordPhaseStartStep phaseWord (m + 1) : ℚ) := by
      have h := (div_le_iff₀ h_denom_pos).mp h_lower
      linarith [h]
    have h_m1_pow_k : ((m + 1 + 1 : ℚ) ^ (k + 1)) ^ k ≤
        (((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) * (wordPhaseStartStep phaseWord (m + 1) : ℚ)) ^ k :=
      pow_le_pow_left₀ (by positivity) h_m1_le k
    rw [mul_pow] at h_m1_pow_k
    have h_pow_comm2 : (((m + 1 + 1 : ℚ) ^ (k + 1)) ^ k) = (m + 1 + 1 : ℚ) ^ (k * (k + 1)) := by
      have h1 : (((m + 1 + 1 : ℚ) ^ (k + 1)) ^ k) = (m + 1 + 1 : ℚ) ^ ((k + 1) * k) :=
        (pow_mul (m + 1 + 1 : ℚ) (k + 1) k).symm
      have h2 : (k + 1) * k = k * (k + 1) := by ring
      rw [h1, h2]
    rw [h_pow_comm2] at h_m1_pow_k
    have h_step_bound : C_base ^ (k + 1) * (m + 1 + 1 : ℚ) ^ (k * (k + 1)) ≤
        (C_base ^ (k + 1) * ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k) *
          (wordPhaseStartStep phaseWord (m + 1) : ℚ) ^ k := by
      calc C_base ^ (k + 1) * (m + 1 + 1 : ℚ) ^ (k * (k + 1)) ≤
          C_base ^ (k + 1) * ((((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k) * (wordPhaseStartStep phaseWord (m + 1) : ℚ) ^ k) :=
            mul_le_mul_of_nonneg_left h_m1_pow_k hC_base_pow_nonneg
        _ = (C_base ^ (k + 1) * ((2 ^ (k + 1) * (k + 1).factorial : ℕ) : ℚ) ^ k) *
              (wordPhaseStartStep phaseWord (m + 1) : ℚ) ^ k := by ring
    rw [h_cast_m] at h_bound_pow
    exact le_trans h_bound_pow h_step_bound

/-- **Reduced Stage 3–4 Admissible Chronology Specification (`Stage34AdmissibleChronologySpec`)**:
    Under `c_zeta ≥ canonicalCZeta_full_admissible`, Stage 1 (`W_early_word`) and Stage 2 (`W_late_word`)
    are discharged unconditionally for all `p : ℕ`, leaving only the coupling signs and Stages 3 & 4. -/
structure Stage34AdmissibleChronologySpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hP_early_nonpos :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        x (finSumFinEquiv (Sum.inl j)) ≤ 0
  hP_late_nonneg :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      0 ≤ P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        x (finSumFinEquiv (Sum.inr j))
  hstage3_bundle : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let M_game := liftedGameMat (AdjoinLeaderEndpointG fc.clock.G b fc.clock.v)
      (P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C)
      (J_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d))
    let s0 := (liftedScoreMat (AdjoinLeaderEndpointG fc.clock.G b fc.clock.v)
      (J_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d))
      (S_admissible fc.clock b (H0 d) (ch d) (delta d))
      (X_gateway fc.clock) (M_coupled (d + 2))
      (zeta_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d))).mulVec
        (binomBasis (d + 3) q)
    IsValidPriorityWord M_game
      (wordScore M_game s0 (W_early_word fc.clock.m (d + 2) q ++ W_late_word fc.clock.m (d + 2) q))
      (paperPriorityRank fc.clock.m (d + 2) (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d))
      ((W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map
        (bundleToLiftedAct fc.clock.m (d + 2)))
  hstage4_gw : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let M_game := liftedGameMat (AdjoinLeaderEndpointG fc.clock.G b fc.clock.v)
      (P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C)
      (J_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d))
    let s0 := (liftedScoreMat (AdjoinLeaderEndpointG fc.clock.G b fc.clock.v)
      (J_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d))
      (S_admissible fc.clock b (H0 d) (ch d) (delta d))
      (X_gateway fc.clock) (M_coupled (d + 2))
      (zeta_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d))).mulVec
        (binomBasis (d + 3) q)
    ∀ y, y ≠ gatewayToLiftedAct fc.clock.m (d + 2) →
      wordScore M_game s0
        (W_early_word fc.clock.m (d + 2) q ++ W_late_word fc.clock.m (d + 2) q ++
          ((W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map
            (bundleToLiftedAct fc.clock.m (d + 2)))) y <
      wordScore M_game s0
        (W_early_word fc.clock.m (d + 2) q ++ W_late_word fc.clock.m (d + 2) q ++
          ((W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map
            (bundleToLiftedAct fc.clock.m (d + 2))))
        (gatewayToLiftedAct fc.clock.m (d + 2))

/-- Automatic conversion from `Stage34AdmissibleChronologySpec` to `AdmissibleLiftSpec` by discharging
    Stages 1 & 2 (`W_early_word` and `W_late_word`) and all-time duality gap bounds unconditionally. -/
def Stage34AdmissibleChronologySpec.toAdmissibleLiftSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ)
    (h_cz : canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (spec : Stage34AdmissibleChronologySpec H0 ch delta c_zeta c_P0 d) :
    AdmissibleLiftSpec (by omega)
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d)
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) where
  phaseShift := d + 2
  parentWord := admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d
  hparent_count := wordCountVec_admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d
  m_rank := ((admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m + 1) + ((d + 2 + 1) + (d + 2 + 1))
  hm_rank := by omega
  rank := fun i =>
    admissibleStageRank
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m
      (d + 2)
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      ((rotLeaderEquiv ((admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m + 1)
        ((d + 2 + 1) + (d + 2 + 1))).symm i)
  hpriority_raw := fun p => by
    have h1 := admissible_stage1_priority_valid_unconditional
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d)
      (fun _ => 1) (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).L_C
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      h_cz spec.hP_early_nonpos (p + (d + 2))
    have h2 := admissible_stage2_priority_valid_unconditional (by omega)
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d)
      (fun _ => 1) (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).L_C
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      h_cz spec.hP_late_nonneg (p + (d + 2))
    have h3 := spec.hstage3_bundle p
    have h4 := spec.hstage4_gw p
    have h_paper := chronology_rawFourStageWord_of_stage_conditions
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (p + (d + 2))
      (AdjoinLeaderEndpointG (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.G
        ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
        (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.v)
      (P_admissible_scaled (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
        ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
        (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1)
        (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).L_C)
      (J_admissible_scaled (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
        ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
        (H0 d) (ch d) (delta d) (c_zeta d))
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      ((liftedScoreMat
        (AdjoinLeaderEndpointG (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.G
          ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
          (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.v)
        (J_admissible_scaled (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
          ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
          (H0 d) (ch d) (delta d) (c_zeta d))
        (S_admissible (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
          ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
          (H0 d) (ch d) (delta d))
        (X_gateway (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock) (M_coupled (d + 2))
        (zeta_admissible_scaled (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
          ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
          (H0 d) (ch d) (delta d) (c_zeta d))).mulVec
          (binomBasis (d + 3) (p + (d + 2))))
      h1 h2 h3 h4
    have h_adm := (isValidPriorityWord_admissibleStageRank_iff_paperPriorityRank _ _
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d) _).mpr h_paper
    simpa only [Equiv.symm_apply_apply] using h_adm
  c_low := bundle_c_low (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d) (d + 2)
  c_high := admissible_c_high_gen (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d)
    ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    (H0 d) (ch d) (delta d) (c_zeta d)
    (admissibleBiasedScoreShift (by omega)
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d)
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1)
      (fun i =>
        admissibleStageRank
          (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m
          (d + 2)
          (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
          ((rotLeaderEquiv ((admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m + 1)
            ((d + 2 + 1) + (d + 2 + 1))).symm i))
      (d + 2))
    (d + 2)
  hc_low_pos := bundle_c_low_pos (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d) (d + 2)
  hc_high_pos := admissible_c_high_gen_pos (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d)
    ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    (H0 d) (ch d) (delta d) (c_zeta d)
    (admissibleBiasedScoreShift (by omega)
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d)
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1)
      (fun i =>
        admissibleStageRank
          (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m
          (d + 2)
          (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
          ((rotLeaderEquiv ((admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m + 1)
            ((d + 2 + 1) + (d + 2 + 1))).symm i))
      (d + 2))
    (d + 2)
  hgap_low := fun p => admissible_hgap_low_of_ge (by omega)
    (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d)
    ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1)
    (le_trans (canonicalCZeta_admissible_le_full
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d)) h_cz)
    (d + 2) le_rfl (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d)
    (wordCountVec_admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (by omega)
    (fun i =>
      admissibleStageRank
        (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m
        (d + 2)
        (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
        ((rotLeaderEquiv ((admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m + 1)
          ((d + 2 + 1) + (d + 2 + 1))).symm i)) p
  hgap_high := fun p => admissible_hgap_high_of_ge (by omega)
    (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d)
    ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1)
    (le_trans (canonicalCZeta_admissible_le_full
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d)) h_cz)
    (d + 2) le_rfl (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d)
    (wordCountVec_admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (by omega)
    (fun i =>
      admissibleStageRank
        (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m
        (d + 2)
        (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
        ((rotLeaderEquiv ((admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m + 1)
          ((d + 2 + 1) + (d + 2 + 1))).symm i)) p

/-- **All-Orders Stage 3–4 Reduced Admissible Karlin Theorem**:
    With Stage 1 (`W_early_word`) and Stage 2 (`W_late_word`) unconditionally discharged across all
    phases `q : ℕ`, polynomial duality gap scaling across all orders $k \ge 2$ follows from
    `Stage34AdmissibleChronologySpec`. -/
theorem all_orders_stage34_admissible_karlin_theorem (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (stage34_lifts : ∀ d : ℕ, Stage34AdmissibleChronologySpec H0 ch delta c_zeta c_P0 d)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  let lifts : ∀ d : ℕ,
      AdmissibleLiftSpec (by omega)
        (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d)
        ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
        (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) :=
    fun d => (stage34_lifts d).toAdmissibleLiftSpec H0 ch delta c_zeta c_P0 d (h_cz d)
  exact all_orders_admissible_realized_karlin_theorem H0 ch delta c_zeta c_P0 lifts k hk

/-- **Reduced Stage 3–4 Bundle Chronology Specification (`Stage34BundleChronologySpec`)**:
    Under `c_zeta ≥ canonicalCZeta_full_bundle`, Stage 1 (`W_early_word`) and Stage 2 (`W_late_word`)
    are discharged unconditionally for all `p : ℕ`, leaving only the coupling signs and Stages 3 & 4. -/
structure Stage34BundleChronologySpec (delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hP_early_nonpos :
    let fc := bundleFullRankClockFamily delta c_zeta c_P0 d
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      P_bundle fc.clock fc.L_C (delta d) (c_zeta d) (c_P0 d) x (finSumFinEquiv (Sum.inl j)) ≤ 0
  hP_late_nonneg :
    let fc := bundleFullRankClockFamily delta c_zeta c_P0 d
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      0 ≤ P_bundle fc.clock fc.L_C (delta d) (c_zeta d) (c_P0 d) x (finSumFinEquiv (Sum.inr j))
  hstage3_bundle : ∀ p : ℕ,
    let fc := bundleFullRankClockFamily delta c_zeta c_P0 d
    let q := p + (d + 2)
    let M_game := liftedGameMat (adjoinGatewayEndpointG fc.clock.G fc.clock.v)
      (P_bundle fc.clock fc.L_C (delta d) (c_zeta d) (c_P0 d))
      (J_bundle fc.clock (delta d) (c_zeta d))
    let s0 := (liftedScoreMat (adjoinGatewayEndpointG fc.clock.G fc.clock.v)
      (J_bundle fc.clock (delta d) (c_zeta d))
      (S_bundle fc.clock 0 (delta d))
      (X_gateway fc.clock) (M_coupled (d + 2))
      (zeta_bundle_scaled fc.clock (delta d) (c_zeta d))).mulVec
        (binomBasis (d + 3) q)
    IsValidPriorityWord M_game
      (wordScore M_game s0 (W_early_word fc.clock.m (d + 2) q ++ W_late_word fc.clock.m (d + 2) q))
      (paperPriorityRank fc.clock.m (d + 2) (bundlePriorityRankFamily delta c_zeta c_P0 d))
      ((W_bundle_word (bundlePhaseWordFamily delta c_zeta c_P0 d) (q + 1)).map
        (bundleToLiftedAct fc.clock.m (d + 2)))
  hstage4_gw : ∀ p : ℕ,
    let fc := bundleFullRankClockFamily delta c_zeta c_P0 d
    let q := p + (d + 2)
    let M_game := liftedGameMat (adjoinGatewayEndpointG fc.clock.G fc.clock.v)
      (P_bundle fc.clock fc.L_C (delta d) (c_zeta d) (c_P0 d))
      (J_bundle fc.clock (delta d) (c_zeta d))
    let s0 := (liftedScoreMat (adjoinGatewayEndpointG fc.clock.G fc.clock.v)
      (J_bundle fc.clock (delta d) (c_zeta d))
      (S_bundle fc.clock 0 (delta d))
      (X_gateway fc.clock) (M_coupled (d + 2))
      (zeta_bundle_scaled fc.clock (delta d) (c_zeta d))).mulVec
        (binomBasis (d + 3) q)
    ∀ y, y ≠ gatewayToLiftedAct fc.clock.m (d + 2) →
      wordScore M_game s0
        (W_early_word fc.clock.m (d + 2) q ++ W_late_word fc.clock.m (d + 2) q ++
          ((W_bundle_word (bundlePhaseWordFamily delta c_zeta c_P0 d) (q + 1)).map
            (bundleToLiftedAct fc.clock.m (d + 2)))) y <
      wordScore M_game s0
        (W_early_word fc.clock.m (d + 2) q ++ W_late_word fc.clock.m (d + 2) q ++
          ((W_bundle_word (bundlePhaseWordFamily delta c_zeta c_P0 d) (q + 1)).map
            (bundleToLiftedAct fc.clock.m (d + 2))))
        (gatewayToLiftedAct fc.clock.m (d + 2))

/-- Automatic conversion from `Stage34BundleChronologySpec` to `BundleLiftSpec` by discharging
    Stages 1 & 2 (`W_early_word` and `W_late_word`) and all-time duality gap bounds unconditionally. -/
def Stage34BundleChronologySpec.toBundleLiftSpec (delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ)
    (h_cz : canonicalCZeta_full_bundle
      (bundleFullRankClockFamily delta c_zeta c_P0 d).clock (delta d) ≤ c_zeta d)
    (spec : Stage34BundleChronologySpec delta c_zeta c_P0 d) :
    BundleLiftSpec (by omega)
      (bundleFullRankClockFamily delta c_zeta c_P0 d)
      (delta d) (c_zeta d) (c_P0 d) where
  phaseShift := d + 2
  parentWord := bundlePhaseWordFamily delta c_zeta c_P0 d
  hparent_count := wordCountVec_bundlePhaseWordFamily delta c_zeta c_P0 d
  m_rank := ((bundleFullRankClockFamily delta c_zeta c_P0 d).clock.m + 1) + ((d + 2 + 1) + (d + 2 + 1))
  hm_rank := by omega
  rank := fun i =>
    admissibleStageRank
      (bundleFullRankClockFamily delta c_zeta c_P0 d).clock.m
      (d + 2)
      (bundlePriorityRankFamily delta c_zeta c_P0 d)
      (finSumFinEquiv.symm i)
  hpriority_raw := fun p => by
    have h1 := bundle_stage1_priority_valid_unconditional
      (bundleFullRankClockFamily delta c_zeta c_P0 d).clock
      (bundleFullRankClockFamily delta c_zeta c_P0 d).L_C
      (delta d) (c_zeta d) (c_P0 d)
      (bundlePriorityRankFamily delta c_zeta c_P0 d)
      h_cz spec.hP_early_nonpos (p + (d + 2))
    have h2 := bundle_stage2_priority_valid_unconditional (by omega)
      (bundleFullRankClockFamily delta c_zeta c_P0 d).clock
      (bundleFullRankClockFamily delta c_zeta c_P0 d).L_C
      (delta d) (c_zeta d) (c_P0 d)
      (bundlePriorityRankFamily delta c_zeta c_P0 d)
      h_cz spec.hP_late_nonneg (p + (d + 2))
    have h3 := spec.hstage3_bundle p
    have h4 := spec.hstage4_gw p
    have h_paper := chronology_rawFourStageWord_of_stage_conditions
      (bundleFullRankClockFamily delta c_zeta c_P0 d).clock
      (bundlePhaseWordFamily delta c_zeta c_P0 d) (p + (d + 2))
      (adjoinGatewayEndpointG (bundleFullRankClockFamily delta c_zeta c_P0 d).clock.G
        (bundleFullRankClockFamily delta c_zeta c_P0 d).clock.v)
      (P_bundle (bundleFullRankClockFamily delta c_zeta c_P0 d).clock
        (bundleFullRankClockFamily delta c_zeta c_P0 d).L_C (delta d) (c_zeta d) (c_P0 d))
      (J_bundle (bundleFullRankClockFamily delta c_zeta c_P0 d).clock (delta d) (c_zeta d))
      (bundlePriorityRankFamily delta c_zeta c_P0 d)
      ((liftedScoreMat
        (adjoinGatewayEndpointG (bundleFullRankClockFamily delta c_zeta c_P0 d).clock.G
          (bundleFullRankClockFamily delta c_zeta c_P0 d).clock.v)
        (J_bundle (bundleFullRankClockFamily delta c_zeta c_P0 d).clock (delta d) (c_zeta d))
        (S_bundle (bundleFullRankClockFamily delta c_zeta c_P0 d).clock 0 (delta d))
        (X_gateway (bundleFullRankClockFamily delta c_zeta c_P0 d).clock) (M_coupled (d + 2))
        (zeta_bundle_scaled (bundleFullRankClockFamily delta c_zeta c_P0 d).clock (delta d) (c_zeta d))).mulVec
          (binomBasis (d + 3) (p + (d + 2))))
      h1 h2 h3 h4
    have h_adm := (isValidPriorityWord_admissibleStageRank_iff_paperPriorityRank _ _
      (bundlePriorityRankFamily delta c_zeta c_P0 d) _).mpr h_paper
    simpa only [Equiv.symm_apply_apply] using h_adm
  c_low := bundle_c_low (bundleFullRankClockFamily delta c_zeta c_P0 d) (d + 2)
  c_high := bundle_c_high_gen (bundleFullRankClockFamily delta c_zeta c_P0 d)
    (delta d) (c_zeta d)
    (bundleBiasedScoreShift (by omega)
      (bundleFullRankClockFamily delta c_zeta c_P0 d)
      (delta d) (c_zeta d) (c_P0 d)
      (fun i =>
        admissibleStageRank
          (bundleFullRankClockFamily delta c_zeta c_P0 d).clock.m
          (d + 2)
          (bundlePriorityRankFamily delta c_zeta c_P0 d)
          (finSumFinEquiv.symm i))
      (d + 2))
    (d + 2)
  hc_low_pos := bundle_c_low_pos (bundleFullRankClockFamily delta c_zeta c_P0 d) (d + 2)
  hc_high_pos := bundle_c_high_gen_pos (bundleFullRankClockFamily delta c_zeta c_P0 d)
    (delta d) (c_zeta d)
    (bundleBiasedScoreShift (by omega)
      (bundleFullRankClockFamily delta c_zeta c_P0 d)
      (delta d) (c_zeta d) (c_P0 d)
      (fun i =>
        admissibleStageRank
          (bundleFullRankClockFamily delta c_zeta c_P0 d).clock.m
          (d + 2)
          (bundlePriorityRankFamily delta c_zeta c_P0 d)
          (finSumFinEquiv.symm i))
      (d + 2))
    (d + 2)
  hgap_low := fun p => bundle_hgap_low_of_ge (by omega)
    (bundleFullRankClockFamily delta c_zeta c_P0 d)
    (delta d) (c_zeta d) (c_P0 d)
    (le_trans (canonicalCZeta_bundle_le_full
      (bundleFullRankClockFamily delta c_zeta c_P0 d).clock (delta d)) h_cz)
    (d + 2) le_rfl (bundlePhaseWordFamily delta c_zeta c_P0 d)
    (wordCountVec_bundlePhaseWordFamily delta c_zeta c_P0 d) (by omega)
    (fun i =>
      admissibleStageRank
        (bundleFullRankClockFamily delta c_zeta c_P0 d).clock.m
        (d + 2)
        (bundlePriorityRankFamily delta c_zeta c_P0 d)
        (finSumFinEquiv.symm i)) p
  hgap_high := fun p => bundle_hgap_high_of_ge (by omega)
    (bundleFullRankClockFamily delta c_zeta c_P0 d)
    (delta d) (c_zeta d) (c_P0 d)
    (le_trans (canonicalCZeta_bundle_le_full
      (bundleFullRankClockFamily delta c_zeta c_P0 d).clock (delta d)) h_cz)
    (d + 2) le_rfl (bundlePhaseWordFamily delta c_zeta c_P0 d)
    (wordCountVec_bundlePhaseWordFamily delta c_zeta c_P0 d) (by omega)
    (fun i =>
      admissibleStageRank
        (bundleFullRankClockFamily delta c_zeta c_P0 d).clock.m
        (d + 2)
        (bundlePriorityRankFamily delta c_zeta c_P0 d)
        (finSumFinEquiv.symm i)) p

/-- **All-Orders Stage 3–4 Reduced Bundle Karlin Theorem**:
    With Stage 1 (`W_early_word`) and Stage 2 (`W_late_word`) unconditionally discharged across all
    phases `q : ℕ`, polynomial duality gap scaling across all orders $k \ge 2$ follows from
    `Stage34BundleChronologySpec`. -/
theorem all_orders_stage34_bundle_karlin_theorem (delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_full_bundle
      (bundleFullRankClockFamily delta c_zeta c_P0 d).clock (delta d) ≤ c_zeta d)
    (stage34_lifts : ∀ d : ℕ, Stage34BundleChronologySpec delta c_zeta c_P0 d)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  let lifts : ∀ d : ℕ,
      BundleLiftSpec (by omega)
        (bundleFullRankClockFamily delta c_zeta c_P0 d)
        (delta d) (c_zeta d) (c_P0 d) :=
    fun d => (stage34_lifts d).toBundleLiftSpec delta c_zeta c_P0 d (h_cz d)
  exact all_orders_bundle_realized_karlin_theorem delta c_zeta c_P0 lifts k hk

/-!
## Section 7: Combined Cone-Ceiling Threshold (`canonicalCZeta_cone_admissible`), Stage 3 Monotonicity & Stage 4 Algebraic Reduction
-/

/-- Combined canonical ceiling and cone dominance threshold guaranteeing both Stage 1–2 ceiling
    dominance (`canonicalCZeta_full_admissible ≤ canonicalCZeta_cone_admissible`) and residual
    coupling dominance (`canonicalCP0_admissible ≤ canonicalCZeta_cone_admissible`). -/
def canonicalCZeta_cone_admissible {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) : ℚ :=
  canonicalCZeta_full_admissible clock b H0 ch delta +
    canonicalCP0_admissible clock b H0 ch delta a_old L_C

/-- `canonicalCZeta_full_admissible ≤ canonicalCZeta_cone_admissible`. -/
theorem canonicalCZeta_full_le_cone_admissible {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) :
    canonicalCZeta_full_admissible clock b H0 ch delta ≤
      canonicalCZeta_cone_admissible clock b H0 ch delta a_old L_C := by
  unfold canonicalCZeta_cone_admissible
  have h1 := one_le_canonicalCP0_admissible clock b H0 ch delta a_old L_C
  linarith

/-- `canonicalCP0_admissible ≤ canonicalCZeta_cone_admissible`. -/
theorem canonicalCP0_le_cone_admissible {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) :
    canonicalCP0_admissible clock b H0 ch delta a_old L_C ≤
      canonicalCZeta_cone_admissible clock b H0 ch delta a_old L_C := by
  unfold canonicalCZeta_cone_admissible
  have h1 := one_le_canonicalCZeta_admissible clock b H0 ch delta
  have h2 := canonicalCZeta_admissible_le_full clock b H0 ch delta
  linarith

/-- **Stage 3 Reset Waiting from Monotone Endpoint Bounds (`admissible_stage3_reset_waits_of_endpoint_bounds`)**:
    Under `hP_early_nonpos` and `hP_late_nonneg`, every reset action `r` strictly waits at step `k`
    of Stage 3 whenever:
    1. Every early reset action `finSumFinEquiv (Sum.inl j)` has Stage 3 *end* score strictly below
       the active parent action's score at step `k`, and
    2. Every late reset action `finSumFinEquiv (Sum.inr j)` has Stage 3 *start* score strictly below
       the active parent action's score at step `k`. -/
theorem admissible_stage3_reset_waits_of_endpoint_bounds {w : ℕ} (hw : 2 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (hLC : clock.C.transpose * L_C = 1)
    (parentWord : ℕ → List (Fin clock.m))
    (hparent_count : ∀ σ : ℕ, wordCountVec (parentWord σ) = clock.C.mulVec (binomBasis w σ))
    (hP_early_nonpos : ∀ (j : Fin (w + 1)) (u : Fin (clock.m + 1)),
      P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C u (finSumFinEquiv (Sum.inl j)) ≤ 0)
    (hP_late_nonneg : ∀ (j : Fin (w + 1)) (u : Fin (clock.m + 1)),
      0 ≤ P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C u (finSumFinEquiv (Sum.inr j)))
    (q k : ℕ)
    (hk : k < ((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).length)
    (hearly_end_lt : ∀ j : Fin (w + 1),
      let r := finSumFinEquiv (Sum.inl j)
      dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) (q + 1)) -
        ((J_admissible_scaled clock b H0 ch delta c_zeta * M_coupled w).mulVec (binomBasis (w + 1) (q + 1))) r +
        P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) r <
      wordScore (AdjoinLeaderEndpointG clock.G b clock.v)
        ((S_admissible clock b H0 ch delta).mulVec (binomBasis (w + 1) (q + 1)))
        (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).take k)
        (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m))[k]))
    (hlate_start_lt : ∀ j : Fin (w + 1),
      let r := finSumFinEquiv (Sum.inr j)
      ((V_reset (J_admissible_scaled clock b H0 ch delta c_zeta) (M_coupled w) (B_mat (w + 1))
        (zeta_admissible_scaled clock b H0 ch delta c_zeta)).mulVec (binomBasis (w + 1) (q + 1))) r <
      wordScore (AdjoinLeaderEndpointG clock.G b clock.v)
        ((S_admissible clock b H0 ch delta).mulVec (binomBasis (w + 1) (q + 1)))
        (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).take k)
        (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m))[k]))
    (r : Fin ((w + 1) + (w + 1))) :
    let G_O := AdjoinLeaderEndpointG clock.G b clock.v
    let P := P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C
    let J := J_admissible_scaled clock b H0 ch delta c_zeta
    let S := S_admissible clock b H0 ch delta
    let zeta := zeta_admissible_scaled clock b H0 ch delta c_zeta
    let M_game := liftedGameMat G_O P J
    let s0 := (liftedScoreMat G_O J S (X_gateway clock) (M_coupled w) zeta).mulVec (binomBasis (w + 1) q)
    let s_mid := wordScore M_game s0 (W_early_word clock.m w q ++ W_late_word clock.m w q)
    let W_O := (W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)
    s_mid (Sum.inr r) - ∑ u, P u r * wordCountVec (W_O.take k) u <
      wordScore G_O (fun u => s_mid (Sum.inl u)) (W_O.take k) (W_O[k]) := by
  intro G_O P J S zeta M_game s0 s_mid W_O
  have hs_mid_inl : (fun u => s_mid (Sum.inl u)) = S.mulVec (binomBasis (w + 1) (q + 1)) := by
    ext u
    exact wordScore_after_reset_stages_admissible_inl hw clock b H0 ch delta c_zeta c_P0 a_old L_C q u
  rw [hs_mid_inl]
  have htake_map : ((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w)).take k =
      (W_O.take k).map Sum.inl := by
    rw [map_bundleToLiftedAct_eq_map_inl, List.map_take]
  have hscore_eq : s_mid (Sum.inr r) - ∑ u, P u r * wordCountVec (W_O.take k) u =
      wordScore M_game s_mid
        (((W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w)).take k) (Sum.inr r) := by
    rw [htake_map]
    have hnew := wordScore_map_inl_new G_O P J s_mid (W_O.take k) r
    change wordScore M_game s_mid ((W_O.take k).map Sum.inl) (Sum.inr r) = _ at hnew
    exact hnew.symm
  rw [hscore_eq]
  rcases (finSumFinEquiv : Fin (w + 1) ⊕ Fin (w + 1) ≃ Fin ((w + 1) + (w + 1))).surjective r with ⟨s, rfl⟩
  cases s with
  | inl j =>
    have hPtX := P_admissible_scaled_transpose_mul_X clock b H0 ch delta c_zeta c_P0 a_old L_C hLC
    have hle := wordScore_stage3_take_early_inr_le_end clock parentWord hparent_count G_O P J S zeta
      hPtX j (hP_early_nonpos j) q k
    exact lt_of_le_of_lt hle (hearly_end_lt j)
  | inr j =>
    have hle := wordScore_stage3_take_late_inr_le_start clock parentWord G_O P J S zeta
      j (hP_late_nonneg j) q k
    exact lt_of_le_of_lt hle (hlate_start_lt j)

/-- **Algebraically Reduced Stage 3–4 Admissible Chronology Specification (`ReducedStage34AdmissibleSpec`)**:
    Reduces `Stage34AdmissibleChronologySpec` by replacing the raw Stage 4 lifted condition with
    the exact closed-form parent and reset polynomial inequalities at `q + 1`, and decomposing
    Stage 3 into old-block priority validity (`W_O`) and reset waiting. -/
structure ReducedStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hP_early_nonpos :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        x (finSumFinEquiv (Sum.inl j)) ≤ 0
  hP_late_nonneg :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      0 ≤ P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        x (finSumFinEquiv (Sum.inr j))
  hstage3_old : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let G_O := AdjoinLeaderEndpointG fc.clock.G b fc.clock.v
    let s_old := (S_admissible fc.clock b (H0 d) (ch d) (delta d)).mulVec (binomBasis (d + 3) (q + 1))
    let W_O := (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map
      (parentToOldAct fc.clock.m)
    IsValidPriorityWord G_O s_old
      (fun u => paperPriorityRank fc.clock.m (d + 2) (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d) (Sum.inl u))
      W_O
  hstage3_early_end_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let G_O := AdjoinLeaderEndpointG fc.clock.G b fc.clock.v
    let s_old := (S_admissible fc.clock b (H0 d) (ch d) (delta d)).mulVec (binomBasis (d + 3) (q + 1))
    let W_O := (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map
      (parentToOldAct fc.clock.m)
    ∀ (k : ℕ) (hk : k < W_O.length) (j : Fin (d + 3)),
      let r := finSumFinEquiv (Sum.inl j)
      dotProduct (zeta_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)) (binomBasis (d + 3) (q + 1)) -
        ((J_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) * M_coupled (d + 2)).mulVec (binomBasis (d + 3) (q + 1))) r +
        P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C (gatewayOldAct fc.clock.m) r <
      wordScore G_O s_old (W_O.take k) (W_O[k])
  hstage3_late_start_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let G_O := AdjoinLeaderEndpointG fc.clock.G b fc.clock.v
    let s_old := (S_admissible fc.clock b (H0 d) (ch d) (delta d)).mulVec (binomBasis (d + 3) (q + 1))
    let W_O := (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map
      (parentToOldAct fc.clock.m)
    ∀ (k : ℕ) (hk : k < W_O.length) (j : Fin (d + 3)),
      let r := finSumFinEquiv (Sum.inr j)
      ((V_reset (J_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)) (M_coupled (d + 2)) (B_mat (d + 3))
        (zeta_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d))).mulVec (binomBasis (d + 3) (q + 1))) r <
      wordScore G_O s_old (W_O.take k) (W_O[k])
  hdelta_pos : 0 < delta d
  hstage4_parent_bound : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    ∀ i : Fin fc.clock.m, i ≠ b →
      (shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)) i +
        (fc.clock.R.mulVec (binomBasis (d + 2) (q + 1)) i - fc.clock.R.mulVec (binomBasis (d + 2) 0) i) <
      (shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)) b +
        (fc.clock.R.mulVec (binomBasis (d + 2) (q + 1)) b - fc.clock.R.mulVec (binomBasis (d + 2) 0) b) + delta d
  hstage4_reset_bound : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    ∀ r : Fin ((d + 3) + (d + 3)),
      dotProduct (zeta_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)) (binomBasis (d + 3) (q + 1)) -
        ((J_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) * M_coupled (d + 2)).mulVec (binomBasis (d + 3) (q + 1))) r +
        P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C (gatewayOldAct fc.clock.m) r <
      (shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)) b +
        (fc.clock.R.mulVec (binomBasis (d + 2) (q + 1)) b - fc.clock.R.mulVec (binomBasis (d + 2) 0) b) +
        dotProduct (h_row_lin (d + 2) (H0 d) (ch d)) (binomBasis (d + 3) (q + 1)) + delta d

/-- Automatic conversion from `ReducedStage34AdmissibleSpec` to `Stage34AdmissibleChronologySpec`. -/
def ReducedStage34AdmissibleSpec.toStage34AdmissibleChronologySpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ)
    (spec : ReducedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d) :
    Stage34AdmissibleChronologySpec H0 ch delta c_zeta c_P0 d where
  hP_early_nonpos := spec.hP_early_nonpos
  hP_late_nonneg := spec.hP_late_nonneg
  hstage3_bundle := fun p => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let G_O := AdjoinLeaderEndpointG fc.clock.G b fc.clock.v
    let P := P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
    let J := J_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)
    let S := S_admissible fc.clock b (H0 d) (ch d) (delta d)
    let zeta := zeta_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)
    let M_game := liftedGameMat G_O P J
    let s0 := (liftedScoreMat G_O J S (X_gateway fc.clock) (M_coupled (d + 2)) zeta).mulVec (binomBasis (d + 3) q)
    let s_mid := wordScore M_game s0 (W_early_word fc.clock.m (d + 2) q ++ W_late_word fc.clock.m (d + 2) q)
    have hs_mid_inl : (fun u => s_mid (Sum.inl u)) = S.mulVec (binomBasis (d + 3) (q + 1)) := by
      ext u
      exact wordScore_after_reset_stages_admissible_inl (by omega) fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C q u
    have h_parent : IsValidPriorityWord G_O (fun u => s_mid (Sum.inl u))
        (fun u => paperPriorityRank fc.clock.m (d + 2) (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d) (Sum.inl u))
        ((W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map (parentToOldAct fc.clock.m)) := by
      rw [hs_mid_inl]
      exact spec.hstage3_old p
    have h_reset : ∀ (k : ℕ) (hk : k < ((W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map (parentToOldAct fc.clock.m)).length)
        (r : Fin ((d + 3) + (d + 3))),
        s_mid (Sum.inr r) - ∑ u, P u r * wordCountVec (((W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map (parentToOldAct fc.clock.m)).take k) u <
          wordScore G_O (fun u => s_mid (Sum.inl u))
            (((W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map (parentToOldAct fc.clock.m)).take k)
            (((W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map (parentToOldAct fc.clock.m))[k]) := by
      intro k hk r
      exact admissible_stage3_reset_waits_of_endpoint_bounds (by omega) fc.clock b
        (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C fc.hLC
        (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d)
        (wordCountVec_admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d)
        spec.hP_early_nonpos spec.hP_late_nonneg q k hk
        (spec.hstage3_early_end_lt p k hk) (spec.hstage3_late_start_lt p k hk) r
    exact isValidPriorityWord_stage3_bundle_of_priority fc.clock
      (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) q G_O P J
      (paperPriorityRank fc.clock.m (d + 2) (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d))
      s_mid h_parent h_reset
  hstage4_gw := fun p =>
    admissible_stage4_gw_of_parent_and_reset_bounds (by omega)
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1)
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).L_C
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).hLC
      (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d)
      (wordCountVec_admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d)
      (p + (d + 2))
      spec.hdelta_pos
      (spec.hstage4_parent_bound p)
      (spec.hstage4_reset_bound p)

/-- **All-Orders Algebraically Reduced Stage 3–4 Admissible Karlin Theorem**:
    Polynomial duality gap scaling across all orders $k \ge 2$ from `ReducedStage34AdmissibleSpec`. -/
theorem all_orders_reduced_stage34_admissible_karlin_theorem (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (reduced_lifts : ∀ d : ℕ, ReducedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  let stage34_lifts : ∀ d : ℕ, Stage34AdmissibleChronologySpec H0 ch delta c_zeta c_P0 d :=
    fun d => (reduced_lifts d).toStage34AdmissibleChronologySpec H0 ch delta c_zeta c_P0 d
  exact all_orders_stage34_admissible_karlin_theorem H0 ch delta c_zeta c_P0 h_cz stage34_lifts k hk

/-- **Stage 3 Reset Waiting from Pure Ceiling Bounds (`admissible_stage3_reset_waits_of_ceiling_bounds`)**:
    When `canonicalCZeta_admissible clock b H0 ch delta ≤ c_zeta`, `(J_admissible_scaled * M_coupled).mulVec`
    and `((J_admissible_scaled)ᵀ * M_coupled).mulVec` are entrywise non-negative, so `J_admissible_scaled`,
    `M_coupled`, and `V_reset` drop out completely! Every reset action `r` strictly waits at step `k`
    of Stage 3 whenever:
    1. Every early reset action `r = finSumFinEquiv (Sum.inl j)` satisfies
       `dotProduct zeta (binomBasis (w + 1) (q + 1)) + P (gatewayOldAct clock.m) r < score_O(W_O[k])`, and
    2. Every late reset action satisfies
       `dotProduct zeta (binomBasis (w + 1) q) < score_O(W_O[k])`. -/
theorem admissible_stage3_reset_waits_of_ceiling_bounds {w : ℕ} (hw : 2 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (hLC : clock.C.transpose * L_C = 1)
    (parentWord : ℕ → List (Fin clock.m))
    (hparent_count : ∀ σ : ℕ, wordCountVec (parentWord σ) = clock.C.mulVec (binomBasis w σ))
    (h_cz : canonicalCZeta_admissible clock b H0 ch delta ≤ c_zeta)
    (hP_early_nonpos : ∀ (j : Fin (w + 1)) (u : Fin (clock.m + 1)),
      P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C u (finSumFinEquiv (Sum.inl j)) ≤ 0)
    (hP_late_nonneg : ∀ (j : Fin (w + 1)) (u : Fin (clock.m + 1)),
      0 ≤ P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C u (finSumFinEquiv (Sum.inr j)))
    (q k : ℕ)
    (hk : k < ((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).length)
    (hearly_ceil_lt : ∀ j : Fin (w + 1),
      let r := finSumFinEquiv (Sum.inl j)
      dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) (q + 1)) +
        P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) r <
      wordScore (AdjoinLeaderEndpointG clock.G b clock.v)
        ((S_admissible clock b H0 ch delta).mulVec (binomBasis (w + 1) (q + 1)))
        (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).take k)
        (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m))[k]))
    (hlate_ceil_lt :
      dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) q) <
      wordScore (AdjoinLeaderEndpointG clock.G b clock.v)
        ((S_admissible clock b H0 ch delta).mulVec (binomBasis (w + 1) (q + 1)))
        (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)).take k)
        (((W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m))[k]))
    (r : Fin ((w + 1) + (w + 1))) :
    let G_O := AdjoinLeaderEndpointG clock.G b clock.v
    let P := P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C
    let J := J_admissible_scaled clock b H0 ch delta c_zeta
    let S := S_admissible clock b H0 ch delta
    let zeta := zeta_admissible_scaled clock b H0 ch delta c_zeta
    let M_game := liftedGameMat G_O P J
    let s0 := (liftedScoreMat G_O J S (X_gateway clock) (M_coupled w) zeta).mulVec (binomBasis (w + 1) q)
    let s_mid := wordScore M_game s0 (W_early_word clock.m w q ++ W_late_word clock.m w q)
    let W_O := (W_bundle_word parentWord (q + 1)).map (parentToOldAct clock.m)
    s_mid (Sum.inr r) - ∑ u, P u r * wordCountVec (W_O.take k) u <
      wordScore G_O (fun u => s_mid (Sum.inl u)) (W_O.take k) (W_O[k]) := by
  refine admissible_stage3_reset_waits_of_endpoint_bounds hw clock b H0 ch delta c_zeta c_P0 a_old L_C hLC
    parentWord hparent_count hP_early_nonpos hP_late_nonneg q k hk ?_ ?_ r
  · intro j
    have hjm := JM_admissible_scaled_mulVec_binomBasis_nonneg clock b H0 ch delta c_zeta h_cz (q + 1) (finSumFinEquiv (Sum.inl j))
    have hc := hearly_ceil_lt j
    dsimp only at hc ⊢
    linarith
  · intro j
    have hV := V_reset_admissible_scaled_mulVec_binomBasis_le_zeta clock b H0 ch delta c_zeta h_cz q (finSumFinEquiv (Sum.inr j))
    dsimp only
    linarith

/-- **Stage 4 All-Competitor Gateway Dominance from Pure Ceiling Bounds (`admissible_stage4_gw_of_parent_and_ceiling_bounds`)**:
    When `canonicalCZeta_admissible clock b H0 ch delta ≤ c_zeta`, `(J_admissible_scaled * M_coupled).mulVec`
    is entrywise non-negative, so `J_admissible_scaled` and `M_coupled` drop out of the Stage 4 reset
    dominance condition completely! -/
theorem admissible_stage4_gw_of_parent_and_ceiling_bounds {w : ℕ} (hw : 2 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (hLC : clock.C.transpose * L_C = 1)
    (parentWord : ℕ → List (Fin clock.m))
    (hparent_count : ∀ σ : ℕ, wordCountVec (parentWord σ) = clock.C.mulVec (binomBasis w σ))
    (h_cz : canonicalCZeta_admissible clock b H0 ch delta ≤ c_zeta)
    (q : ℕ)
    (hdelta_pos : 0 < delta)
    (hparent_bound : ∀ i : Fin clock.m, i ≠ b →
      (shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1)) i +
        (clock.R.mulVec (binomBasis w (q + 1)) i - clock.R.mulVec (binomBasis w 0) i) <
      (shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1)) b +
        (clock.R.mulVec (binomBasis w (q + 1)) b - clock.R.mulVec (binomBasis w 0) b) + delta)
    (hreset_ceil_bound : ∀ r : Fin ((w + 1) + (w + 1)),
      dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) (q + 1)) +
        P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) r <
      (shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1)) b +
        (clock.R.mulVec (binomBasis w (q + 1)) b - clock.R.mulVec (binomBasis w 0) b) +
        dotProduct (h_row_lin w H0 ch) (binomBasis (w + 1) (q + 1)) + delta) :
    let M_game := liftedGameMat (AdjoinLeaderEndpointG clock.G b clock.v)
      (P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C)
      (J_admissible_scaled clock b H0 ch delta c_zeta)
    let s0 := (liftedScoreMat (AdjoinLeaderEndpointG clock.G b clock.v)
      (J_admissible_scaled clock b H0 ch delta c_zeta)
      (S_admissible clock b H0 ch delta)
      (X_gateway clock) (M_coupled w)
      (zeta_admissible_scaled clock b H0 ch delta c_zeta)).mulVec (binomBasis (w + 1) q)
    let W_stage123 := W_early_word clock.m w q ++ W_late_word clock.m w q ++
      (W_bundle_word parentWord (q + 1)).map (bundleToLiftedAct clock.m w)
    ∀ y, y ≠ gatewayToLiftedAct clock.m w →
      wordScore M_game s0 W_stage123 y <
        wordScore M_game s0 W_stage123 (gatewayToLiftedAct clock.m w) := by
  refine admissible_stage4_gw_of_parent_and_reset_bounds hw clock b H0 ch delta c_zeta c_P0 a_old L_C hLC
    parentWord hparent_count q hdelta_pos hparent_bound ?_
  intro r
  have hjm := JM_admissible_scaled_mulVec_binomBasis_nonneg clock b H0 ch delta c_zeta h_cz (q + 1) r
  have hc := hreset_ceil_bound r
  linarith

/-- **Ceiling-Simplified Stage 3–4 Admissible Chronology Specification (`SimplifiedStage34AdmissibleSpec`)**:
    Eliminates `J_admissible_scaled`, `M_coupled`, and `V_reset` completely from `ReducedStage34AdmissibleSpec`
    using the entrywise non-negativity of `(J * M)` and `(Jᵀ * M)` whenever `c_zeta ≥ canonicalCZeta_admissible`. -/
structure SimplifiedStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hP_early_nonpos :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        x (finSumFinEquiv (Sum.inl j)) ≤ 0
  hP_late_nonneg :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      0 ≤ P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        x (finSumFinEquiv (Sum.inr j))
  hstage3_old : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let G_O := AdjoinLeaderEndpointG fc.clock.G b fc.clock.v
    let s_old := (S_admissible fc.clock b (H0 d) (ch d) (delta d)).mulVec (binomBasis (d + 3) (q + 1))
    let W_O := (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map
      (parentToOldAct fc.clock.m)
    IsValidPriorityWord G_O s_old
      (fun u => paperPriorityRank fc.clock.m (d + 2) (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d) (Sum.inl u))
      W_O
  hstage3_early_ceil_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let G_O := AdjoinLeaderEndpointG fc.clock.G b fc.clock.v
    let s_old := (S_admissible fc.clock b (H0 d) (ch d) (delta d)).mulVec (binomBasis (d + 3) (q + 1))
    let W_O := (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map
      (parentToOldAct fc.clock.m)
    ∀ (k : ℕ) (hk : k < W_O.length) (j : Fin (d + 3)),
      let r := finSumFinEquiv (Sum.inl j)
      dotProduct (zeta_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)) (binomBasis (d + 3) (q + 1)) +
        P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C (gatewayOldAct fc.clock.m) r <
      wordScore G_O s_old (W_O.take k) (W_O[k])
  hstage3_late_ceil_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let G_O := AdjoinLeaderEndpointG fc.clock.G b fc.clock.v
    let s_old := (S_admissible fc.clock b (H0 d) (ch d) (delta d)).mulVec (binomBasis (d + 3) (q + 1))
    let W_O := (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map
      (parentToOldAct fc.clock.m)
    ∀ (k : ℕ) (hk : k < W_O.length),
      dotProduct (zeta_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)) (binomBasis (d + 3) q) <
      wordScore G_O s_old (W_O.take k) (W_O[k])
  hdelta_pos : 0 < delta d
  hstage4_parent_bound : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    ∀ i : Fin fc.clock.m, i ≠ b →
      (shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)) i +
        (fc.clock.R.mulVec (binomBasis (d + 2) (q + 1)) i - fc.clock.R.mulVec (binomBasis (d + 2) 0) i) <
      (shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)) b +
        (fc.clock.R.mulVec (binomBasis (d + 2) (q + 1)) b - fc.clock.R.mulVec (binomBasis (d + 2) 0) b) + delta d
  hstage4_reset_ceil_bound : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    ∀ r : Fin ((d + 3) + (d + 3)),
      dotProduct (zeta_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)) (binomBasis (d + 3) (q + 1)) +
        P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C (gatewayOldAct fc.clock.m) r <
      (shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)) b +
        (fc.clock.R.mulVec (binomBasis (d + 2) (q + 1)) b - fc.clock.R.mulVec (binomBasis (d + 2) 0) b) +
        dotProduct (h_row_lin (d + 2) (H0 d) (ch d)) (binomBasis (d + 3) (q + 1)) + delta d

/-- Automatic conversion from `SimplifiedStage34AdmissibleSpec` to `ReducedStage34AdmissibleSpec`. -/
def SimplifiedStage34AdmissibleSpec.toReducedStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ)
    (h_cz : canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (spec : SimplifiedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d) :
    ReducedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d where
  hP_early_nonpos := spec.hP_early_nonpos
  hP_late_nonneg := spec.hP_late_nonneg
  hstage3_old := spec.hstage3_old
  hstage3_early_end_lt := fun p k hk j => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    have h_cz0 : canonicalCZeta_admissible fc.clock b (H0 d) (ch d) (delta d) ≤ c_zeta d :=
      le_trans (canonicalCZeta_admissible_le_full fc.clock b (H0 d) (ch d) (delta d)) h_cz
    have hjm := JM_admissible_scaled_mulVec_binomBasis_nonneg fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)
      h_cz0 ((p + (d + 2)) + 1) (finSumFinEquiv (Sum.inl j))
    have hc := spec.hstage3_early_ceil_lt p k hk j
    dsimp only at hc ⊢
    linarith
  hstage3_late_start_lt := fun p k hk j => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    have h_cz0 : canonicalCZeta_admissible fc.clock b (H0 d) (ch d) (delta d) ≤ c_zeta d :=
      le_trans (canonicalCZeta_admissible_le_full fc.clock b (H0 d) (ch d) (delta d)) h_cz
    have hV := V_reset_admissible_scaled_mulVec_binomBasis_le_zeta fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)
      h_cz0 (p + (d + 2)) (finSumFinEquiv (Sum.inr j))
    have hc := spec.hstage3_late_ceil_lt p k hk
    dsimp only at hc ⊢
    linarith
  hdelta_pos := spec.hdelta_pos
  hstage4_parent_bound := spec.hstage4_parent_bound
  hstage4_reset_bound := fun p r => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    have h_cz0 : canonicalCZeta_admissible fc.clock b (H0 d) (ch d) (delta d) ≤ c_zeta d :=
      le_trans (canonicalCZeta_admissible_le_full fc.clock b (H0 d) (ch d) (delta d)) h_cz
    have hjm := JM_admissible_scaled_mulVec_binomBasis_nonneg fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)
      h_cz0 ((p + (d + 2)) + 1) r
    have hc := spec.hstage4_reset_ceil_bound p r
    linarith

/-- **All-Orders Ceiling-Simplified Stage 3–4 Admissible Karlin Theorem**:
    Polynomial duality gap scaling across all orders $k \ge 2$ from `SimplifiedStage34AdmissibleSpec`,
    free of any explicit dependence on `J_admissible_scaled`, `M_coupled`, or `V_reset`. -/
theorem all_orders_simplified_stage34_admissible_karlin_theorem (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (simplified_lifts : ∀ d : ℕ, SimplifiedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  let reduced_lifts : ∀ d : ℕ, ReducedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d :=
    fun d => (simplified_lifts d).toReducedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d (h_cz d)
  exact all_orders_reduced_stage34_admissible_karlin_theorem H0 ch delta c_zeta c_P0 h_cz reduced_lifts k hk

-- `rpsAlgebraicClock_leader_zero_dom` is now provided by `Karlin.AdmissibleLift`.

/-- Reset actions in `liftedScoreMat` are bounded by the ceiling under `c_zeta ≥ canonicalCZeta_admissible`. -/
theorem liftedScoreMat_admissible_scaled_inr_mulVec_binomBasis_le_zeta {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ)
    (h_cz : canonicalCZeta_admissible clock b H0 ch delta ≤ c_zeta)
    (σ : ℕ) (r : Fin ((w + 1) + (w + 1))) :
    ((liftedScoreMat (AdjoinLeaderEndpointG clock.G b clock.v)
      (J_admissible_scaled clock b H0 ch delta c_zeta)
      (S_admissible clock b H0 ch delta)
      (X_gateway clock) (M_coupled w)
      (zeta_admissible_scaled clock b H0 ch delta c_zeta)).mulVec (binomBasis (w + 1) σ)) (Sum.inr r) ≤
      dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) σ) := by
  have hs_r : ((liftedScoreMat (AdjoinLeaderEndpointG clock.G b clock.v)
      (J_admissible_scaled clock b H0 ch delta c_zeta)
      (S_admissible clock b H0 ch delta)
      (X_gateway clock) (M_coupled w)
      (zeta_admissible_scaled clock b H0 ch delta c_zeta)).mulVec (binomBasis (w + 1) σ)) (Sum.inr r) =
      ((one_zeta (Fin ((w + 1) + (w + 1))) (zeta_admissible_scaled clock b H0 ch delta c_zeta) -
        J_admissible_scaled clock b H0 ch delta c_zeta * M_coupled w).mulVec (binomBasis (w + 1) σ)) r := rfl
  rw [hs_r, Matrix.sub_mulVec, Pi.sub_apply]
  have h_one : ((one_zeta (Fin ((w + 1) + (w + 1)))
      (zeta_admissible_scaled clock b H0 ch delta c_zeta)).mulVec
        (binomBasis (w + 1) σ)) r =
      dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) σ) := by
    simp only [Matrix.mulVec, dotProduct, one_zeta, Matrix.of_apply]
  rw [h_one]
  have hjm := JM_admissible_scaled_mulVec_binomBasis_nonneg clock b H0 ch delta c_zeta h_cz σ r
  linarith

/-- In `admissibleScaledLiftClock`, the leader action 0 weakly dominates all actions
    at every phase start `σ : ℕ` whenever `c_zeta ≥ canonicalCZeta_full_admissible`. -/
theorem admissibleScaledLiftClock_leader_zero_dom {w : ℕ} (hw : 2 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (hLC : clock.C.transpose * L_C = 1)
    (h_cz : canonicalCZeta_full_admissible clock b H0 ch delta ≤ c_zeta)
    (σ : ℕ)
    (x : Fin (admissibleScaledLiftClock hw clock b H0 ch delta c_zeta c_P0 a_old L_C hLC).m) :
    ((admissibleScaledLiftClock hw clock b H0 ch delta c_zeta c_P0 a_old L_C hLC).R.mulVec (binomBasis (w + 1) σ)) x ≤
      ((admissibleScaledLiftClock hw clock b H0 ch delta c_zeta c_P0 a_old L_C hLC).R.mulVec (binomBasis (w + 1) σ))
        ⟨0, by dsimp [admissibleScaledLiftClock, AlgebraicClock.ofEquiv]; omega⟩ := by
  have h_lead : ((admissibleScaledLiftClock hw clock b H0 ch delta c_zeta c_P0 a_old L_C hLC).R.mulVec
      (binomBasis (w + 1) σ)) ⟨0, by dsimp [admissibleScaledLiftClock, AlgebraicClock.ofEquiv]; omega⟩ =
      dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) σ) := by
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [admissibleScaledLiftClock_leader_zero_score hw clock b H0 ch delta c_zeta c_P0 a_old L_C hLC c]
  have h_row : ((admissibleScaledLiftClock hw clock b H0 ch delta c_zeta c_P0 a_old L_C hLC).R.mulVec
      (binomBasis (w + 1) σ)) x =
      ((liftedScoreMat (AdjoinLeaderEndpointG clock.G b clock.v)
        (J_admissible_scaled clock b H0 ch delta c_zeta)
        (S_admissible clock b H0 ch delta)
        (X_gateway clock) (M_coupled w)
        (zeta_admissible_scaled clock b H0 ch delta c_zeta)).mulVec (binomBasis (w + 1) σ))
        ((rotLeaderEquiv (clock.m + 1) ((w + 1) + (w + 1))).symm x) := by
    dsimp only [admissibleScaledLiftClock, AlgebraicClock.ofEquiv]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [h_lead, h_row]
  cases (rotLeaderEquiv (clock.m + 1) ((w + 1) + (w + 1))).symm x with
  | inl u =>
    exact le_of_lt (admissible_stage1_old_below_ceiling_unconditional clock b H0 ch delta c_zeta h_cz u σ)
  | inr r =>
    have h_cz_adm : canonicalCZeta_admissible clock b H0 ch delta ≤ c_zeta :=
      le_trans (canonicalCZeta_admissible_le_full clock b H0 ch delta) h_cz
    exact liftedScoreMat_admissible_scaled_inr_mulVec_binomBasis_le_zeta clock b H0 ch delta c_zeta h_cz_adm σ r

/-- In the recursive family `admissibleFullRankClockFamily`, the canonical leader action 0
    weakly dominates all actions at every phase start `σ : ℕ` and every depth `d : ℕ`
    whenever `c_zeta d ≥ canonicalCZeta_full_admissible ...`. -/
theorem admissibleFullRankClockFamily_leader_zero_dom (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (d σ : ℕ) (i : Fin (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m) :
    ((admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.R.mulVec (binomBasis (d + 2) σ)) i ≤
      ((admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.R.mulVec (binomBasis (d + 2) σ))
        ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩ := by
  cases d with
  | zero =>
      exact rpsAlgebraicClock_leader_zero_dom σ i
  | succ d =>
      exact admissibleScaledLiftClock_leader_zero_dom (by omega)
        (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
        ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
        (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d)
        (fun _ => 1)
        (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).L_C
        (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).hLC
        (h_cz d) σ i

/-- **Unconditional Stage 4 Parent Dominance (`admissibleFullRankClockFamily_stage4_parent_bound_unconditional`)**:
    In `admissibleFullRankClockFamily`, for every depth `d`, every phase `q`, and every parent action `i`,
    the Stage 4 parent competitor inequality holds unconditionally whenever `0 < delta d` and
    `canonicalCZeta_full_admissible ≤ c_zeta`. -/
theorem admissibleFullRankClockFamily_stage4_parent_bound_unconditional (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (d : ℕ) (hdelta : 0 < delta d) (q : ℕ)
    (i : Fin (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m) :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    (shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)) i +
      (fc.clock.R.mulVec (binomBasis (d + 2) (q + 1)) i - fc.clock.R.mulVec (binomBasis (d + 2) 0) i) <
    (shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)) b +
      (fc.clock.R.mulVec (binomBasis (d + 2) (q + 1)) b - fc.clock.R.mulVec (binomBasis (d + 2) 0) b) + delta d := by
  intro fc b
  exact stage4_parent_bound_of_phase_leader fc.clock b (delta d) hdelta q i
    (fun σ _ => admissibleFullRankClockFamily_leader_zero_dom H0 ch delta c_zeta c_P0 h_cz d (σ + 1) i)

/-- **Minimal Stage 3–4 Admissible Chronology Specification (`MinimalStage34AdmissibleSpec`)**:
    Eliminates `hstage4_parent_bound` completely (proved unconditionally across all depths `d` via
    `admissibleFullRankClockFamily_stage4_parent_bound_unconditional`), as well as `J_admissible_scaled`,
    `M_coupled`, and `V_reset`. At Stage 4, ALL parent actions (both the designated leader `b` and
    every non-leader parent action `i ≠ b`) are now discharged unconditionally from `0 < delta d`! -/
structure MinimalStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hP_early_nonpos :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        x (finSumFinEquiv (Sum.inl j)) ≤ 0
  hP_late_nonneg :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      0 ≤ P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        x (finSumFinEquiv (Sum.inr j))
  hstage3_old : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let G_O := AdjoinLeaderEndpointG fc.clock.G b fc.clock.v
    let s_old := (S_admissible fc.clock b (H0 d) (ch d) (delta d)).mulVec (binomBasis (d + 3) (q + 1))
    let W_O := (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map
      (parentToOldAct fc.clock.m)
    IsValidPriorityWord G_O s_old
      (fun u => paperPriorityRank fc.clock.m (d + 2) (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d) (Sum.inl u))
      W_O
  hstage3_early_ceil_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let G_O := AdjoinLeaderEndpointG fc.clock.G b fc.clock.v
    let s_old := (S_admissible fc.clock b (H0 d) (ch d) (delta d)).mulVec (binomBasis (d + 3) (q + 1))
    let W_O := (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map
      (parentToOldAct fc.clock.m)
    ∀ (k : ℕ) (hk : k < W_O.length) (j : Fin (d + 3)),
      let r := finSumFinEquiv (Sum.inl j)
      dotProduct (zeta_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)) (binomBasis (d + 3) (q + 1)) +
        P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C (gatewayOldAct fc.clock.m) r <
      wordScore G_O s_old (W_O.take k) (W_O[k])
  hstage3_late_ceil_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let G_O := AdjoinLeaderEndpointG fc.clock.G b fc.clock.v
    let s_old := (S_admissible fc.clock b (H0 d) (ch d) (delta d)).mulVec (binomBasis (d + 3) (q + 1))
    let W_O := (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)).map
      (parentToOldAct fc.clock.m)
    ∀ (k : ℕ) (hk : k < W_O.length),
      dotProduct (zeta_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)) (binomBasis (d + 3) q) <
      wordScore G_O s_old (W_O.take k) (W_O[k])
  hdelta_pos : 0 < delta d
  hstage4_reset_ceil_bound : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    ∀ r : Fin ((d + 3) + (d + 3)),
      dotProduct (zeta_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)) (binomBasis (d + 3) (q + 1)) +
        P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C (gatewayOldAct fc.clock.m) r <
      (shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)) b +
        (fc.clock.R.mulVec (binomBasis (d + 2) (q + 1)) b - fc.clock.R.mulVec (binomBasis (d + 2) 0) b) +
        dotProduct (h_row_lin (d + 2) (H0 d) (ch d)) (binomBasis (d + 3) (q + 1)) + delta d

/-- Automatic conversion from `MinimalStage34AdmissibleSpec` to `SimplifiedStage34AdmissibleSpec`. -/
def MinimalStage34AdmissibleSpec.toSimplifiedStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (d : ℕ) (spec : MinimalStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d) :
    SimplifiedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d where
  hP_early_nonpos := spec.hP_early_nonpos
  hP_late_nonneg := spec.hP_late_nonneg
  hstage3_old := spec.hstage3_old
  hstage3_early_ceil_lt := spec.hstage3_early_ceil_lt
  hstage3_late_ceil_lt := spec.hstage3_late_ceil_lt
  hdelta_pos := spec.hdelta_pos
  hstage4_parent_bound := fun p i _ =>
    admissibleFullRankClockFamily_stage4_parent_bound_unconditional H0 ch delta c_zeta c_P0 h_cz
      d spec.hdelta_pos (p + (d + 2)) i
  hstage4_reset_ceil_bound := spec.hstage4_reset_ceil_bound

/-- **All-Orders Minimal Stage 3–4 Admissible Karlin Theorem**:
    Polynomial duality gap scaling across all orders $k \ge 2$ from `MinimalStage34AdmissibleSpec`,
    where at Stage 4 ALL parent actions (both leader and non-leader) are discharged unconditionally
    from `0 < delta d` and `c_zeta d ≥ canonicalCZeta_full_admissible`. -/
theorem all_orders_minimal_stage34_admissible_karlin_theorem (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (minimal_lifts : ∀ d : ℕ, MinimalStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  let simplified_lifts : ∀ d : ℕ, SimplifiedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d :=
    fun d => (minimal_lifts d).toSimplifiedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 h_cz d
  exact all_orders_simplified_stage34_admissible_karlin_theorem H0 ch delta c_zeta c_P0 h_cz simplified_lifts k hk

-- `rpsPhaseWord_take_v_dot_nonpos` is now provided by `Karlin.AdmissibleLift`.

/-- Unconditional nonpositivity of endpoint counter inner product on proper prefixes of `admissiblePhaseWordFamily`
    at every depth `d : ℕ`, phase `σ : ℕ`, and proper prefix `r < (admissiblePhaseWordFamily ... d σ).length`. -/
theorem admissiblePhaseWordFamily_take_v_dot_nonpos (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (d σ r : ℕ) (hr : r < (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d σ).length) :
    dotProduct (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.v
      (wordCountVec ((admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d σ).take r)) ≤ 0 := by
  cases d with
  | zero =>
      exact rpsPhaseWord_take_v_dot_nonpos σ r hr
  | succ d =>
      dsimp only [admissiblePhaseWordFamily] at hr ⊢
      set fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
      set e := rotLeaderEquiv (fc.clock.m + 1) ((d + 2 + 1) + (d + 2 + 1))
      set W_raw := rawFourStageWord fc.clock (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) σ
      rw [List.length_map] at hr
      rw [← List.map_take]
      have hdot_eq :
          dotProduct (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 (d + 1)).clock.v
            (wordCountVec ((W_raw.take r).map e)) =
          dotProduct (liftedWeightVec (v_old_coupled fc.clock.m) (0 : Fin ((d + 2 + 1) + (d + 2 + 1)) → ℚ))
            (wordCountVec (W_raw.take r)) := by
        dsimp only [dotProduct]
        have hcomp := (Equiv.sum_comp e (fun x =>
          (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 (d + 1)).clock.v x *
            wordCountVec ((W_raw.take r).map e) x)).symm
        refine Eq.trans hcomp (Finset.sum_congr rfl fun y _ => ?_)
        have hcount := wordCountVec_map_equiv e (W_raw.take r) (e y)
        rw [Equiv.symm_apply_apply] at hcount
        have hv : (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 (d + 1)).clock.v (e y) =
            liftedWeightVec (v_old_coupled fc.clock.m) (0 : Fin ((d + 2 + 1) + (d + 2 + 1)) → ℚ) y := by
          change liftedWeightVec (v_old_coupled fc.clock.m) (0 : Fin ((d + 2 + 1) + (d + 2 + 1)) → ℚ) (e.symm (e y)) = _
          rw [Equiv.symm_apply_apply]
        rw [hcount, hv]
      rw [hdot_eq, rawFourStageWord_take_v_dot_eq_zero fc.clock _ σ r hr]

/-- Unconditional unit dot product of `fc.clock.v` with any complete phase word `admissiblePhaseWordFamily ... d σ`. -/
theorem admissiblePhaseWordFamily_full_v_dot_eq_one (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (d σ : ℕ) :
    dotProduct (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.v
      (wordCountVec (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d σ)) = 1 := by
  let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
  rw [wordCountVec_admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d σ]
  exact clock_endpoint_increment_eq_one (by omega) fc.clock.v fc.clock.C fc.clock.hvC σ

/-- **Unconditional Stage 3 Bundle Prefix Inner-Product Bound (`admissibleFullRankClockFamily_stage3_v_bound_unconditional`)**:
    At every depth `d : ℕ`, every bundle length `Q : ℕ`, and every proper prefix `k < (W_bundle_word ... Q).length`,
    `fc.clock.v · wordCountVec ((W_bundle_word ... Q).take k) ≤ Q - 1`. -/
theorem admissibleFullRankClockFamily_stage3_v_bound_unconditional (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (d Q k : ℕ)
    (hk : k < (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) Q).length) :
    dotProduct (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.v
      (wordCountVec ((W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) Q).take k)) ≤
      (Q : ℚ) - 1 := by
  exact dotProduct_wordCountVec_flatMap_take_le
    (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.v
    (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d)
    (admissiblePhaseWordFamily_full_v_dot_eq_one H0 ch delta c_zeta c_P0 d)
    (admissiblePhaseWordFamily_take_v_dot_nonpos H0 ch delta c_zeta c_P0 d)
    Q k hk

/-- Stage 3 parent priority word validity under embedding `parentToOldAct clock.m`:
    the embedded word `W_p.map (parentToOldAct clock.m)` is valid on `AdjoinLeaderEndpointG` whenever
    `W_p` is valid on `clock.G`, `delta < 1`, and the endpoint inner product `v · count(W_p.take k)`
    remains bounded by `Q - 1`. -/
theorem isValidPriorityWord_stage3_old_of_parent_and_v_bound {w : ℕ} (hw : 1 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta : ℚ) (hdelta_lt_one : delta < 1)
    (parent_rank : Fin clock.m → Fin clock.m) (W_p : List (Fin clock.m)) (Q : ℕ)
    (h_p : IsValidPriorityWord clock.G
      ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) Q))
      parent_rank W_p)
    (hv_bound : ∀ (k : ℕ), k < W_p.length →
      dotProduct clock.v (wordCountVec (W_p.take k)) ≤ (Q : ℚ) - 1) :
    IsValidPriorityWord (AdjoinLeaderEndpointG clock.G b clock.v)
      ((S_admissible clock b H0 ch delta).mulVec (binomBasis (w + 1) Q))
      (fun u => paperPriorityRank clock.m w parent_rank (Sum.inl u))
      (W_p.map (parentToOldAct clock.m)) := by
  refine isValidPriorityWord_map_parentToOldAct clock.G
    ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) Q))
    (dotProduct (h_row_lin w H0 ch) (binomBasis (w + 1) Q))
    parent_rank W_p h_p
    (AdjoinLeaderEndpointG clock.G b clock.v)
    ((S_admissible clock b H0 ch delta).mulVec (binomBasis (w + 1) Q))
    (fun i j => AdjoinLeaderEndpointG_parent_parent clock.G b clock.v i j)
    (fun i => S_admissible_mulVec_binomBasis_inl clock b H0 ch delta Q i)
    fun k hk => ?_
  have hdiff := wordScore_bundle_take_gateway_sub_leader hw clock b H0 ch delta W_p Q k
  have hscore_b := wordScore_bundle_take_parentToOldAct clock b H0 ch delta W_p Q k b
  have hscore_k := wordScore_bundle_take_parentToOldAct clock b H0 ch delta W_p Q k (W_p[k]'hk)
  have hp_le := (h_p k hk b).1
  have hv := hv_bound k hk
  linarith

/-- **Unconditional Stage 3 Gateway Waiting Reduction (`admissibleFullRankClockFamily_stage3_old_of_parent_priority`)**:
    Whenever `delta d < 1`, Stage 3 priority validity on the old block `AdjoinLeaderEndpointG` follows
    unconditionally from pure parent-clock priority validity on `fc.clock.G`, because the gateway endpoint
    strictly waits at every step of Stage 3 across all depths `d ≥ 0`! -/
theorem admissibleFullRankClockFamily_stage3_old_of_parent_priority (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (d : ℕ) (hdelta_lt_one : delta d < 1) (Q : ℕ)
    (hparent :
      let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
      IsValidPriorityWord fc.clock.G
        ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) Q))
        (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
        (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) Q)) :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let G_O := AdjoinLeaderEndpointG fc.clock.G b fc.clock.v
    let s_old := (S_admissible fc.clock b (H0 d) (ch d) (delta d)).mulVec (binomBasis (d + 3) Q)
    let W_O := (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) Q).map
      (parentToOldAct fc.clock.m)
    IsValidPriorityWord G_O s_old
      (fun u => paperPriorityRank fc.clock.m (d + 2) (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d) (Sum.inl u))
      W_O := by
  exact isValidPriorityWord_stage3_old_of_parent_and_v_bound (by omega)
    (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
    ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    (H0 d) (ch d) (delta d) hdelta_lt_one
    (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
    (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) Q) Q
    hparent
    (fun k hk => admissibleFullRankClockFamily_stage3_v_bound_unconditional H0 ch delta c_zeta c_P0 d Q k hk)

/-- **Parent-Reduced Stage 3–4 Admissible Chronology Specification (`ParentReducedStage34AdmissibleSpec`)**:
    Simultaneously:
    1. Eliminates `hstage4_parent_bound` unconditionally across all depths `d` (from `0 < delta d`),
    2. Eliminates Stage 3 gateway waiting unconditionally across all depths `d` (from `delta d < 1`),
       reducing `hstage3_old` to pure parent-clock priority validity `hstage3_parent` on `fc.clock.G`
       (completely free of `AdjoinLeaderEndpointG`, `S_admissible`, `parentToOldAct`, `H0 d`, and `ch d`), and
    3. Preserves the exact Stage 3–4 reset endpoint bounds (`hstage3_early_end_lt`, `hstage3_late_start_lt`,
       `hstage4_reset_bound`) with the `-J*M` and `-Jᵀ*M` terms intact! -/
structure ParentReducedStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hP_early_nonpos :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        x (finSumFinEquiv (Sum.inl j)) ≤ 0
  hP_late_nonneg :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      0 ≤ P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        x (finSumFinEquiv (Sum.inr j))
  hdelta_pos : 0 < delta d
  hdelta_lt_one : delta d < 1
  hstage3_parent : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let q := p + (d + 2)
    IsValidPriorityWord fc.clock.G
      ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)))
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1))
  hstage3_early_end_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length) (j : Fin (d + 3)),
      let r := finSumFinEquiv (Sum.inl j)
      dotProduct (zeta_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)) (binomBasis (d + 3) (q + 1)) -
        ((J_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) * M_coupled (d + 2)).mulVec (binomBasis (d + 3) (q + 1))) r +
        P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C (gatewayOldAct fc.clock.m) r <
      wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) +
        dotProduct (h_row_lin (d + 2) (H0 d) (ch d)) (binomBasis (d + 3) (q + 1))
  hstage3_late_start_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length) (j : Fin (d + 3)),
      let r := finSumFinEquiv (Sum.inr j)
      ((V_reset (J_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)) (M_coupled (d + 2)) (B_mat (d + 3))
        (zeta_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d))).mulVec (binomBasis (d + 3) (q + 1))) r <
      wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) +
        dotProduct (h_row_lin (d + 2) (H0 d) (ch d)) (binomBasis (d + 3) (q + 1))
  hstage4_reset_bound : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    ∀ r : Fin ((d + 3) + (d + 3)),
      dotProduct (zeta_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)) (binomBasis (d + 3) (q + 1)) -
        ((J_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) * M_coupled (d + 2)).mulVec (binomBasis (d + 3) (q + 1))) r +
        P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C (gatewayOldAct fc.clock.m) r <
      (shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)) b +
        (fc.clock.R.mulVec (binomBasis (d + 2) (q + 1)) b - fc.clock.R.mulVec (binomBasis (d + 2) 0) b) +
        dotProduct (h_row_lin (d + 2) (H0 d) (ch d)) (binomBasis (d + 3) (q + 1)) + delta d

/-- Automatic conversion from `ParentReducedStage34AdmissibleSpec` to `ReducedStage34AdmissibleSpec`. -/
def ParentReducedStage34AdmissibleSpec.toReducedStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (d : ℕ) (spec : ParentReducedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d) :
    ReducedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d where
  hP_early_nonpos := spec.hP_early_nonpos
  hP_late_nonneg := spec.hP_late_nonneg
  hstage3_old := fun p =>
    admissibleFullRankClockFamily_stage3_old_of_parent_priority H0 ch delta c_zeta c_P0
      d spec.hdelta_lt_one ((p + (d + 2)) + 1) (spec.hstage3_parent p)
  hstage3_early_end_lt := fun p k hk j => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    have hk_p : k < W_p.length := by
      simpa only [List.length_map] using hk
    have hget : (W_p.map (parentToOldAct fc.clock.m))[k]'hk = parentToOldAct fc.clock.m (W_p[k]'hk_p) :=
      List.getElem_map _
    rw [hget]
    rw [wordScore_bundle_take_parentToOldAct fc.clock b (H0 d) (ch d) (delta d) W_p (q + 1) k (W_p[k]'hk_p)]
    exact spec.hstage3_early_end_lt p k hk_p j
  hstage3_late_start_lt := fun p k hk j => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    have hk_p : k < W_p.length := by
      simpa only [List.length_map] using hk
    have hget : (W_p.map (parentToOldAct fc.clock.m))[k]'hk = parentToOldAct fc.clock.m (W_p[k]'hk_p) :=
      List.getElem_map _
    rw [hget]
    rw [wordScore_bundle_take_parentToOldAct fc.clock b (H0 d) (ch d) (delta d) W_p (q + 1) k (W_p[k]'hk_p)]
    exact spec.hstage3_late_start_lt p k hk_p j
  hdelta_pos := spec.hdelta_pos
  hstage4_parent_bound := fun p i _ =>
    admissibleFullRankClockFamily_stage4_parent_bound_unconditional H0 ch delta c_zeta c_P0 h_cz
      d spec.hdelta_pos (p + (d + 2)) i
  hstage4_reset_bound := spec.hstage4_reset_bound

/-- **All-Orders Parent-Reduced Stage 3–4 Admissible Karlin Theorem**:
    Polynomial duality gap scaling across all orders $k \ge 2$ from `ParentReducedStage34AdmissibleSpec`,
    where Stage 4 parent dominance AND Stage 3 gateway waiting are both proved unconditionally across
    all depths `d ≥ 0` from `0 < delta d < 1` and `c_zeta d ≥ canonicalCZeta_full_admissible`. -/
theorem all_orders_parent_reduced_stage34_admissible_karlin_theorem (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (parent_reduced_lifts : ∀ d : ℕ, ParentReducedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  let reduced_lifts : ∀ d : ℕ, ReducedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d :=
    fun d => (parent_reduced_lifts d).toReducedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 h_cz d
  exact all_orders_reduced_stage34_admissible_karlin_theorem H0 ch delta c_zeta c_P0 h_cz reduced_lifts k hk

/-- Strict early reset waiting at Stage 3 end from baseline $H_0$ dominance:
    when $H_0$ exceeds the base threshold at $H_0 = 0$, the Stage 3 end reset inequality holds strictly. -/
theorem stage3_early_end_lt_of_H0_gt {w : ℕ} (hw : 1 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ)
    (W_p : List (Fin clock.m)) (q k : ℕ) (hk : k < W_p.length) (j : Fin (w + 1)) :
    let r := finSumFinEquiv (Sum.inl j)
    dotProduct (zeta_admissible_scaled clock b 0 ch delta c_zeta) (binomBasis (w + 1) (q + 1)) -
      ((J_admissible_scaled clock b 0 ch delta c_zeta * M_coupled w).mulVec (binomBasis (w + 1) (q + 1))) r +
      P_admissible_scaled clock b 0 ch delta c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) r <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      (ch * ((q + 1 : ℕ) : ℚ) + H0) →
    dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) (q + 1)) -
      ((J_admissible_scaled clock b H0 ch delta c_zeta * M_coupled w).mulVec (binomBasis (w + 1) (q + 1))) r +
      P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) r <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      dotProduct (h_row_lin w H0 ch) (binomBasis (w + 1) (q + 1)) := by
  intro r h_base
  rw [zeta_admissible_scaled_indep_of_H0 clock b H0 ch delta c_zeta]
  rw [J_admissible_scaled_indep_of_H0 clock b H0 ch delta c_zeta]
  rw [P_admissible_scaled_indep_of_H0 clock b H0 ch delta c_zeta c_P0 a_old L_C]
  rw [dotProduct_h_row_lin_binomBasis hw H0 ch (q + 1)]
  linarith

/-- Strict late reset waiting at Stage 3 start from baseline $H_0$ dominance:
    when $H_0$ exceeds the base threshold at $H_0 = 0$, the Stage 3 start reset inequality holds strictly. -/
theorem stage3_late_start_lt_of_H0_gt {w : ℕ} (hw : 1 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ)
    (W_p : List (Fin clock.m)) (q k : ℕ) (hk : k < W_p.length) (j : Fin (w + 1)) :
    let r := finSumFinEquiv (Sum.inr j)
    ((V_reset (J_admissible_scaled clock b 0 ch delta c_zeta) (M_coupled w) (B_mat (w + 1))
      (zeta_admissible_scaled clock b 0 ch delta c_zeta)).mulVec (binomBasis (w + 1) (q + 1))) r <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      (ch * ((q + 1 : ℕ) : ℚ) + H0) →
    ((V_reset (J_admissible_scaled clock b H0 ch delta c_zeta) (M_coupled w) (B_mat (w + 1))
      (zeta_admissible_scaled clock b H0 ch delta c_zeta)).mulVec (binomBasis (w + 1) (q + 1))) r <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      dotProduct (h_row_lin w H0 ch) (binomBasis (w + 1) (q + 1)) := by
  intro r h_base
  rw [zeta_admissible_scaled_indep_of_H0 clock b H0 ch delta c_zeta]
  rw [J_admissible_scaled_indep_of_H0 clock b H0 ch delta c_zeta]
  rw [dotProduct_h_row_lin_binomBasis hw H0 ch (q + 1)]
  linarith

/-- Strict reset score bound at Stage 4 boundary from baseline $H_0$ dominance:
    when $H_0$ exceeds the base threshold at $H_0 = 0$, Stage 4 gateway dominance over reset actions holds strictly. -/
theorem stage4_reset_bound_of_H0_gt {w : ℕ} (hw : 1 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ)
    (q : ℕ) (r : Fin ((w + 1) + (w + 1)))
    (h_base :
      dotProduct (zeta_admissible_scaled clock b 0 ch delta c_zeta) (binomBasis (w + 1) (q + 1)) -
        ((J_admissible_scaled clock b 0 ch delta c_zeta * M_coupled w).mulVec (binomBasis (w + 1) (q + 1))) r +
        P_admissible_scaled clock b 0 ch delta c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) r <
      (shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1)) b +
        (clock.R.mulVec (binomBasis w (q + 1)) b - clock.R.mulVec (binomBasis w 0) b) +
        (ch * ((q + 1 : ℕ) : ℚ) + H0) + delta) :
    dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) (q + 1)) -
      ((J_admissible_scaled clock b H0 ch delta c_zeta * M_coupled w).mulVec (binomBasis (w + 1) (q + 1))) r +
      P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) r <
    (shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1)) b +
      (clock.R.mulVec (binomBasis w (q + 1)) b - clock.R.mulVec (binomBasis w 0) b) +
      dotProduct (h_row_lin w H0 ch) (binomBasis (w + 1) (q + 1)) + delta := by
  rw [zeta_admissible_scaled_indep_of_H0 clock b H0 ch delta c_zeta]
  rw [J_admissible_scaled_indep_of_H0 clock b H0 ch delta c_zeta]
  rw [P_admissible_scaled_indep_of_H0 clock b H0 ch delta c_zeta c_P0 a_old L_C]
  rw [dotProduct_h_row_lin_binomBasis hw H0 ch (q + 1)]
  linarith

/-- Ceiling-sufficient version of Stage 3 end early reset waiting from $H_0$ dominance:
    dropping the non-negative subtractive term $((J * M) p)_{inl(j)}$ yields a simpler, sufficient condition. -/
theorem stage3_early_end_lt_of_ceiling_H0_gt {w : ℕ} (hw : 1 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ)
    (h_cz : canonicalCZeta_admissible clock b 0 ch delta ≤ c_zeta)
    (W_p : List (Fin clock.m)) (q k : ℕ) (hk : k < W_p.length) (j : Fin (w + 1)) :
    let r := finSumFinEquiv (Sum.inl j)
    dotProduct (zeta_admissible_scaled clock b 0 ch delta c_zeta) (binomBasis (w + 1) (q + 1)) +
      P_admissible_scaled clock b 0 ch delta c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) r <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      (ch * ((q + 1 : ℕ) : ℚ) + H0) →
    dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) (q + 1)) -
      ((J_admissible_scaled clock b H0 ch delta c_zeta * M_coupled w).mulVec (binomBasis (w + 1) (q + 1))) r +
      P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) r <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      dotProduct (h_row_lin w H0 ch) (binomBasis (w + 1) (q + 1)) := by
  intro r h_ceil
  apply stage3_early_end_lt_of_H0_gt hw clock b H0 ch delta c_zeta c_P0 a_old L_C W_p q k hk j
  have hjm := JM_admissible_scaled_mulVec_binomBasis_nonneg clock b 0 ch delta c_zeta h_cz (q + 1) (finSumFinEquiv (Sum.inl j))
  linarith

/-- Ceiling-sufficient version of Stage 3 start late reset waiting from $H_0$ dominance:
    bounding $V_{\mathrm{reset}} p_{q+1}$ by $\zeta \cdot p_q$ yields a simpler, sufficient condition. -/
theorem stage3_late_start_lt_of_ceiling_H0_gt {w : ℕ} (hw : 1 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ)
    (h_cz : canonicalCZeta_admissible clock b 0 ch delta ≤ c_zeta)
    (W_p : List (Fin clock.m)) (q k : ℕ) (hk : k < W_p.length) (j : Fin (w + 1)) :
    let r := finSumFinEquiv (Sum.inr j)
    dotProduct (zeta_admissible_scaled clock b 0 ch delta c_zeta) (binomBasis (w + 1) q) <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      (ch * ((q + 1 : ℕ) : ℚ) + H0) →
    ((V_reset (J_admissible_scaled clock b H0 ch delta c_zeta) (M_coupled w) (B_mat (w + 1))
      (zeta_admissible_scaled clock b H0 ch delta c_zeta)).mulVec (binomBasis (w + 1) (q + 1))) r <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      dotProduct (h_row_lin w H0 ch) (binomBasis (w + 1) (q + 1)) := by
  intro r h_ceil
  apply stage3_late_start_lt_of_H0_gt hw clock b H0 ch delta c_zeta W_p q k hk j
  have hV := V_reset_admissible_scaled_mulVec_binomBasis_le_zeta clock b 0 ch delta c_zeta h_cz q (finSumFinEquiv (Sum.inr j))
  linarith

/-- Ceiling-sufficient version of Stage 4 reset bound from $H_0$ dominance:
    dropping the non-negative subtractive term $((J * M) p)_r$ yields a simpler, sufficient condition. -/
theorem stage4_reset_bound_of_ceiling_H0_gt {w : ℕ} (hw : 1 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ)
    (h_cz : canonicalCZeta_admissible clock b 0 ch delta ≤ c_zeta)
    (q : ℕ) (r : Fin ((w + 1) + (w + 1)))
    (h_ceil :
      dotProduct (zeta_admissible_scaled clock b 0 ch delta c_zeta) (binomBasis (w + 1) (q + 1)) +
        P_admissible_scaled clock b 0 ch delta c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) r <
      (shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1)) b +
        (clock.R.mulVec (binomBasis w (q + 1)) b - clock.R.mulVec (binomBasis w 0) b) +
        (ch * ((q + 1 : ℕ) : ℚ) + H0) + delta) :
    dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) (q + 1)) -
      ((J_admissible_scaled clock b H0 ch delta c_zeta * M_coupled w).mulVec (binomBasis (w + 1) (q + 1))) r +
      P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) r <
    (shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1)) b +
      (clock.R.mulVec (binomBasis w (q + 1)) b - clock.R.mulVec (binomBasis w 0) b) +
      dotProduct (h_row_lin w H0 ch) (binomBasis (w + 1) (q + 1)) + delta := by
  apply stage4_reset_bound_of_H0_gt hw clock b H0 ch delta c_zeta c_P0 a_old L_C q r
  have hjm := JM_admissible_scaled_mulVec_binomBasis_nonneg clock b 0 ch delta c_zeta h_cz (q + 1) r
  linarith

/-- **H0-Calibrated Stage 3–4 Admissible Chronology Specification (`H0CalibratedStage34AdmissibleSpec`)**:
    Replaces raw Stage 3–4 reset endpoint inequalities with their decoupled $H_0$-calibrated ceiling forms:
    1. Early reset endpoint bound evaluated at $H_0 = 0$ with additive $H_0$ shift, dropping $-J*M$,
    2. Late reset start bound evaluated at $H_0 = 0$ with additive $H_0$ shift, bounding $V_{\mathrm{reset}}$ by $\zeta \cdot p_q$,
    3. Stage 4 reset bound evaluated at $H_0 = 0$ with additive $H_0$ shift, dropping $-J*M$. -/
structure H0CalibratedStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hP_early_nonpos :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        x (finSumFinEquiv (Sum.inl j)) ≤ 0
  hP_late_nonneg :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      0 ≤ P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        x (finSumFinEquiv (Sum.inr j))
  hdelta_pos : 0 < delta d
  hdelta_lt_one : delta d < 1
  hstage3_parent : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let q := p + (d + 2)
    IsValidPriorityWord fc.clock.G
      ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)))
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1))
  hstage3_early_ceil_H0_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length) (j : Fin (d + 3)),
      let r := finSumFinEquiv (Sum.inl j)
      dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) (delta d) (c_zeta d)) (binomBasis (d + 3) (q + 1)) +
        P_admissible_scaled fc.clock b 0 (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C (gatewayOldAct fc.clock.m) r <
      wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) +
        (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)
  hstage3_late_ceil_H0_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length),
      dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) (delta d) (c_zeta d)) (binomBasis (d + 3) q) <
      wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) +
        (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)
  hstage4_reset_ceil_H0_bound : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    ∀ r : Fin ((d + 3) + (d + 3)),
      dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) (delta d) (c_zeta d)) (binomBasis (d + 3) (q + 1)) +
        P_admissible_scaled fc.clock b 0 (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C (gatewayOldAct fc.clock.m) r <
      (shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)) b +
        (fc.clock.R.mulVec (binomBasis (d + 2) (q + 1)) b - fc.clock.R.mulVec (binomBasis (d + 2) 0) b) +
        (ch d * ((q + 1 : ℕ) : ℚ) + H0 d) + delta d

/-- Automatic conversion from `H0CalibratedStage34AdmissibleSpec` to `ParentReducedStage34AdmissibleSpec`. -/
def H0CalibratedStage34AdmissibleSpec.toParentReducedStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (d : ℕ) (spec : H0CalibratedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d) :
    ParentReducedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d where
  hP_early_nonpos := spec.hP_early_nonpos
  hP_late_nonneg := spec.hP_late_nonneg
  hdelta_pos := spec.hdelta_pos
  hdelta_lt_one := spec.hdelta_lt_one
  hstage3_parent := spec.hstage3_parent
  hstage3_early_end_lt := fun p k hk j => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    have h_cz0 : canonicalCZeta_admissible fc.clock b 0 (ch d) (delta d) ≤ c_zeta d := by
      rw [← canonicalCZeta_admissible_indep_of_H0 fc.clock b (H0 d) (ch d) (delta d)]
      exact le_trans (canonicalCZeta_admissible_le_full fc.clock b (H0 d) (ch d) (delta d)) (h_cz d)
    exact stage3_early_end_lt_of_ceiling_H0_gt (by omega) fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)
      (c_P0 d) (fun _ => 1) fc.L_C h_cz0 W_p q k hk j (spec.hstage3_early_ceil_H0_lt p k hk j)
  hstage3_late_start_lt := fun p k hk j => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    have h_cz0 : canonicalCZeta_admissible fc.clock b 0 (ch d) (delta d) ≤ c_zeta d := by
      rw [← canonicalCZeta_admissible_indep_of_H0 fc.clock b (H0 d) (ch d) (delta d)]
      exact le_trans (canonicalCZeta_admissible_le_full fc.clock b (H0 d) (ch d) (delta d)) (h_cz d)
    exact stage3_late_start_lt_of_ceiling_H0_gt (by omega) fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)
      h_cz0 W_p q k hk j (spec.hstage3_late_ceil_H0_lt p k hk)
  hstage4_reset_bound := fun p r => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    have h_cz0 : canonicalCZeta_admissible fc.clock b 0 (ch d) (delta d) ≤ c_zeta d := by
      rw [← canonicalCZeta_admissible_indep_of_H0 fc.clock b (H0 d) (ch d) (delta d)]
      exact le_trans (canonicalCZeta_admissible_le_full fc.clock b (H0 d) (ch d) (delta d)) (h_cz d)
    exact stage4_reset_bound_of_ceiling_H0_gt (by omega) fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)
      (c_P0 d) (fun _ => 1) fc.L_C h_cz0 q r (spec.hstage4_reset_ceil_H0_bound p r)

/-- **All-Orders H0-Calibrated Stage 3–4 Admissible Karlin Theorem**:
    Polynomial duality gap scaling across all orders $k \ge 2$ from `H0CalibratedStage34AdmissibleSpec`,
    where Stage 3 early/late reset waiting and Stage 4 reset bounds are calibrated from $H_0$ dominance,
    free of $-J*M$, $-Jᵀ*M$, and $V_{\mathrm{reset}}$. -/
theorem all_orders_H0_calibrated_stage34_admissible_karlin_theorem (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (calibrated_lifts : ∀ d : ℕ, H0CalibratedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  let parent_reduced_lifts : ∀ d : ℕ, ParentReducedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d :=
    fun d => (calibrated_lifts d).toParentReducedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 h_cz d
  exact all_orders_parent_reduced_stage34_admissible_karlin_theorem H0 ch delta c_zeta c_P0 h_cz parent_reduced_lifts k hk

/-- Q-reset version of Stage 3 end early reset waiting from $H_0$ dominance:
    evaluates the early reset baseline at `(H0 = 0, delta = 0)` using `Q_reset`
    in place of `P_admissible_scaled` via `P_admissible_scaled_gateway_row_eq_Q_reset`. -/
theorem stage3_early_end_lt_of_Q_reset_H0_gt {w : ℕ} (hw : 1 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (hLC : clock.C.transpose * L_C = 1)
    (h_cz : canonicalCZeta_admissible clock b 0 ch 0 ≤ c_zeta)
    (W_p : List (Fin clock.m)) (q k : ℕ) (hk : k < W_p.length) (j : Fin (w + 1)) :
    let r := finSumFinEquiv (Sum.inl j)
    dotProduct (zeta_admissible_scaled clock b 0 ch 0 c_zeta) (binomBasis (w + 1) (q + 1)) +
      (Q_reset (J_admissible_scaled clock b 0 ch 0 c_zeta) (M_coupled w) (B_mat (w + 1))
        (zeta_admissible_scaled clock b 0 ch 0 c_zeta)) r 0 <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      (ch * ((q + 1 : ℕ) : ℚ) + H0) →
    dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) (q + 1)) -
      ((J_admissible_scaled clock b H0 ch delta c_zeta * M_coupled w).mulVec (binomBasis (w + 1) (q + 1))) r +
      P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) r <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      dotProduct (h_row_lin w H0 ch) (binomBasis (w + 1) (q + 1)) := by
  intro r h_qres
  have h_cz_delta : canonicalCZeta_admissible clock b 0 ch delta ≤ c_zeta := by
    rw [canonicalCZeta_admissible_indep_of_delta clock b 0 ch delta]
    exact h_cz
  apply stage3_early_end_lt_of_ceiling_H0_gt hw clock b H0 ch delta c_zeta c_P0 a_old L_C h_cz_delta W_p q k hk j
  dsimp only [r] at h_qres ⊢
  rw [zeta_admissible_scaled_indep_of_delta clock b 0 ch delta c_zeta]
  rw [P_admissible_scaled_gateway_row_eq_Q_reset clock b 0 ch delta c_zeta c_P0 a_old L_C hLC]
  rw [J_admissible_scaled_indep_of_delta clock b 0 ch delta c_zeta]
  rw [zeta_admissible_scaled_indep_of_delta clock b 0 ch delta c_zeta]
  exact h_qres

/-- Q-reset version of Stage 3 start late reset waiting from $H_0$ dominance:
    evaluates the late reset baseline at `(H0 = 0, delta = 0)` using `zeta_admissible_scaled`
    independent of `delta`. -/
theorem stage3_late_start_lt_of_Q_reset_H0_gt {w : ℕ} (hw : 1 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ)
    (h_cz : canonicalCZeta_admissible clock b 0 ch 0 ≤ c_zeta)
    (W_p : List (Fin clock.m)) (q k : ℕ) (hk : k < W_p.length) (j : Fin (w + 1)) :
    let r := finSumFinEquiv (Sum.inr j)
    dotProduct (zeta_admissible_scaled clock b 0 ch 0 c_zeta) (binomBasis (w + 1) q) <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      (ch * ((q + 1 : ℕ) : ℚ) + H0) →
    ((V_reset (J_admissible_scaled clock b H0 ch delta c_zeta) (M_coupled w) (B_mat (w + 1))
      (zeta_admissible_scaled clock b H0 ch delta c_zeta)).mulVec (binomBasis (w + 1) (q + 1))) r <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      dotProduct (h_row_lin w H0 ch) (binomBasis (w + 1) (q + 1)) := by
  intro r h_ceil
  have h_cz_delta : canonicalCZeta_admissible clock b 0 ch delta ≤ c_zeta := by
    rw [canonicalCZeta_admissible_indep_of_delta clock b 0 ch delta]
    exact h_cz
  apply stage3_late_start_lt_of_ceiling_H0_gt hw clock b H0 ch delta c_zeta h_cz_delta W_p q k hk j
  rw [zeta_admissible_scaled_indep_of_delta clock b 0 ch delta c_zeta]
  exact h_ceil

/-- Strict reset score bound at Stage 4 boundary from non-strict, `delta`-free Q-reset bound and `0 < delta`:
    when the Stage 3 end reset ceiling is weakly bounded by the Stage 3 end leader score without `delta`,
    the positivity `0 < delta` strictly elevates the gateway score, establishing strict gateway dominance. -/
theorem stage4_reset_bound_of_Q_reset_H0_le {w : ℕ} (hw : 1 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (hLC : clock.C.transpose * L_C = 1)
    (h_cz : canonicalCZeta_admissible clock b 0 ch 0 ≤ c_zeta)
    (hdelta_pos : 0 < delta)
    (q : ℕ) (r : Fin ((w + 1) + (w + 1)))
    (h_le :
      dotProduct (zeta_admissible_scaled clock b 0 ch 0 c_zeta) (binomBasis (w + 1) (q + 1)) +
        (Q_reset (J_admissible_scaled clock b 0 ch 0 c_zeta) (M_coupled w) (B_mat (w + 1))
          (zeta_admissible_scaled clock b 0 ch 0 c_zeta)) r 0 ≤
      (∑ σ ∈ Finset.range (q + 1), (clock.R.mulVec (binomBasis w (σ + 1))) b) +
        (ch * ((q + 1 : ℕ) : ℚ) + H0)) :
    dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) (q + 1)) -
      ((J_admissible_scaled clock b H0 ch delta c_zeta * M_coupled w).mulVec (binomBasis (w + 1) (q + 1))) r +
      P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) r <
    (shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1)) b +
      (clock.R.mulVec (binomBasis w (q + 1)) b - clock.R.mulVec (binomBasis w 0) b) +
      dotProduct (h_row_lin w H0 ch) (binomBasis (w + 1) (q + 1)) + delta := by
  have h_cz_delta : canonicalCZeta_admissible clock b 0 ch delta ≤ c_zeta := by
    rw [canonicalCZeta_admissible_indep_of_delta clock b 0 ch delta]
    exact h_cz
  apply stage4_reset_bound_of_ceiling_H0_gt hw clock b H0 ch delta c_zeta c_P0 a_old L_C h_cz_delta q r
  rw [zeta_admissible_scaled_indep_of_delta clock b 0 ch delta c_zeta]
  rw [P_admissible_scaled_gateway_row_eq_Q_reset clock b 0 ch delta c_zeta c_P0 a_old L_C hLC]
  rw [J_admissible_scaled_indep_of_delta clock b 0 ch delta c_zeta]
  rw [zeta_admissible_scaled_indep_of_delta clock b 0 ch delta c_zeta]
  rw [stage3_end_parent_score_base_eq_sum_succ clock.R q b]
  linarith

/-- **Q-Reset-Calibrated Stage 3–4 Admissible Chronology Specification (`QResetCalibratedStage34AdmissibleSpec`)**:
    Decouples all Stage 3–4 reset conditions from `delta`, `c_P0`, `a_old`, and `L_C`:
    1. Early reset endpoint bound evaluated at `(H0 = 0, delta = 0)` using `Q_reset ... r 0`,
    2. Late reset start bound evaluated at `(H0 = 0, delta = 0)` using `zeta_admissible_scaled`,
    3. Stage 4 reset bound evaluated as a non-strict `≤` inequality at `(H0 = 0, delta = 0)` using `Q_reset ... r 0`
       against the Stage 3 end leader score `∑ σ < q + 1, R p(σ + 1) b` without `delta`. -/
structure QResetCalibratedStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hP_early_nonpos :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        x (finSumFinEquiv (Sum.inl j)) ≤ 0
  hP_late_nonneg :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      0 ≤ P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        x (finSumFinEquiv (Sum.inr j))
  hdelta_pos : 0 < delta d
  hdelta_lt_one : delta d < 1
  hstage3_parent : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let q := p + (d + 2)
    IsValidPriorityWord fc.clock.G
      ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)))
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1))
  hstage3_early_qreset_H0_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length) (j : Fin (d + 3)),
      let r := finSumFinEquiv (Sum.inl j)
      dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (binomBasis (d + 3) (q + 1)) +
        (Q_reset (J_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (M_coupled (d + 2)) (B_mat (d + 3))
          (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d))) r 0 <
      wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) +
        (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)
  hstage3_late_qreset_H0_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length),
      dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (binomBasis (d + 3) q) <
      wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) +
        (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)
  hstage4_reset_qreset_H0_le : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    ∀ r : Fin ((d + 3) + (d + 3)),
      dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (binomBasis (d + 3) (q + 1)) +
        (Q_reset (J_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (M_coupled (d + 2)) (B_mat (d + 3))
          (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d))) r 0 ≤
      (∑ σ ∈ Finset.range (q + 1), (fc.clock.R.mulVec (binomBasis (d + 2) (σ + 1))) b) +
        (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)

/-- Automatic conversion from `QResetCalibratedStage34AdmissibleSpec` to `H0CalibratedStage34AdmissibleSpec`. -/
def QResetCalibratedStage34AdmissibleSpec.toH0CalibratedStage34AdmissibleSpec
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (d : ℕ) (spec : QResetCalibratedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d) :
    H0CalibratedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d where
  hP_early_nonpos := spec.hP_early_nonpos
  hP_late_nonneg := spec.hP_late_nonneg
  hdelta_pos := spec.hdelta_pos
  hdelta_lt_one := spec.hdelta_lt_one
  hstage3_parent := spec.hstage3_parent
  hstage3_early_ceil_H0_lt := fun p k hk j => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    have h_gw := P_admissible_scaled_gateway_row_eq_Q_reset fc.clock b 0 (ch d) (delta d)
      (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C fc.hLC (finSumFinEquiv (Sum.inl j))
    have h_zeta := zeta_admissible_scaled_indep_of_delta fc.clock b 0 (ch d) (delta d) (c_zeta d)
    have h_J := J_admissible_scaled_indep_of_delta fc.clock b 0 (ch d) (delta d) (c_zeta d)
    have h_early := spec.hstage3_early_qreset_H0_lt p k hk j
    dsimp only [b, q] at *
    rw [h_zeta, h_gw, h_J, h_zeta]
    exact h_early
  hstage3_late_ceil_H0_lt := fun p k hk => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    have h_zeta := zeta_admissible_scaled_indep_of_delta fc.clock b 0 (ch d) (delta d) (c_zeta d)
    have h_late := spec.hstage3_late_qreset_H0_lt p k hk
    dsimp only [b, q] at *
    rw [h_zeta]
    exact h_late
  hstage4_reset_ceil_H0_bound := fun p r => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    have h_gw := P_admissible_scaled_gateway_row_eq_Q_reset fc.clock b 0 (ch d) (delta d)
      (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C fc.hLC r
    have h_zeta := zeta_admissible_scaled_indep_of_delta fc.clock b 0 (ch d) (delta d) (c_zeta d)
    have h_J := J_admissible_scaled_indep_of_delta fc.clock b 0 (ch d) (delta d) (c_zeta d)
    have h_sum := stage3_end_parent_score_base_eq_sum_succ fc.clock.R q b
    have h_le := spec.hstage4_reset_qreset_H0_le p r
    have h_pos := spec.hdelta_pos
    dsimp only [b, q] at *
    rw [h_zeta, h_gw, h_J, h_zeta, h_sum]
    linarith

/-- **All-Orders Q-Reset-Calibrated Stage 3–4 Admissible Karlin Theorem**:
    Polynomial duality gap scaling across all orders $k \ge 2$ from `QResetCalibratedStage34AdmissibleSpec`,
    where Stage 3 early/late reset waiting and Stage 4 reset bounds are decoupled from `delta`,
    free of $-J*M$, $-Jᵀ*M$, and $V_{\mathrm{reset}}$, and where Stage 4 reset bound is non-strict
    and completely free of `delta`. -/
theorem all_orders_Q_reset_calibrated_stage34_admissible_karlin_theorem
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (qreset_lifts : ∀ d : ℕ, QResetCalibratedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  let h0_lifts : ∀ d : ℕ, H0CalibratedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d :=
    fun d => (qreset_lifts d).toH0CalibratedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d
  exact all_orders_H0_calibrated_stage34_admissible_karlin_theorem H0 ch delta c_zeta c_P0 h_cz h0_lifts k hk

/-!
## Section 14: Boundary vs. Interior Subdiagonal Drift Calibration (`BoundaryInteriorStage34AdmissibleSpec`)
-/

/-- For any positive early reset action `0 < j.val`, `r = finSumFinEquiv (Sum.inl j)` satisfies `0 < r.val`,
    so the Stage 3 end score gains the strictly positive degree-`w` subdiagonal drift slack
    `(1 + (c_zeta - canonicalCZeta_admissible)) * (4 * (w + 1))⁻¹ * ∑ c, binomBasis (w + 1) (q + 1) c`. -/
theorem stage3_early_end_lt_of_pos_drift_H0_gt {w : ℕ} (hw : 1 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (hLC : clock.C.transpose * L_C = 1)
    (h_cz : canonicalCZeta_admissible clock b 0 ch 0 ≤ c_zeta)
    (W_p : List (Fin clock.m)) (q k : ℕ) (hk : k < W_p.length) (j : Fin (w + 1)) (hj_pos : 0 < j.val) :
    let r := finSumFinEquiv (Sum.inl j)
    dotProduct (zeta_admissible_scaled clock b 0 ch 0 c_zeta) (binomBasis (w + 1) (q + 1)) -
      (1 + (c_zeta - canonicalCZeta_admissible clock b 0 ch 0)) * (4 * (w + 1 : ℚ))⁻¹ *
        (∑ c : Fin (w + 1), binomBasis (w + 1) (q + 1) c) +
      (Q_reset (J_admissible_scaled clock b 0 ch 0 c_zeta) (M_coupled w) (B_mat (w + 1))
        (zeta_admissible_scaled clock b 0 ch 0 c_zeta)) r 0 <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      (ch * ((q + 1 : ℕ) : ℚ) + H0) →
    dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) (q + 1)) -
      ((J_admissible_scaled clock b H0 ch delta c_zeta * M_coupled w).mulVec (binomBasis (w + 1) (q + 1))) r +
      P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) r <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      dotProduct (h_row_lin w H0 ch) (binomBasis (w + 1) (q + 1)) := by
  intro r h_drift
  apply stage3_early_end_lt_of_H0_gt hw clock b H0 ch delta c_zeta c_P0 a_old L_C W_p q k hk j
  have h_cz_delta : canonicalCZeta_admissible clock b 0 ch delta ≤ c_zeta := by
    rw [canonicalCZeta_admissible_indep_of_delta clock b 0 ch delta]
    exact h_cz
  have hr_pos : 0 < r.val := by
    dsimp only [r, finSumFinEquiv, Equiv.coe_fn_mk, Fin.addCases]
    exact hj_pos
  have h_sub := stage3_end_inr_admissible_le_zeta_sub_of_pos clock b 0 ch 0 c_zeta c_P0 a_old L_C hLC
    h_cz (q + 1) r hr_pos
  dsimp only [r] at h_drift h_sub ⊢
  rw [zeta_admissible_scaled_indep_of_delta clock b 0 ch delta c_zeta]
  rw [J_admissible_scaled_indep_of_delta clock b 0 ch delta c_zeta]
  rw [P_admissible_scaled_indep_of_delta clock b 0 ch delta c_zeta c_P0 a_old L_C]
  linarith

/-- For any non-top late reset action `j.val < w`, `r = finSumFinEquiv (Sum.inr j)` satisfies `r.val < (w + 1) + w`,
    so the Stage 3 start late reset score is depressed below `zeta · p_q` by the strictly positive degree-`w`
    subdiagonal drift slack `(1 + (c_zeta - canonicalCZeta_admissible)) * (4 * (w + 1))⁻¹ * ∑ c, binomBasis (w + 1) q c`. -/
theorem stage3_late_start_lt_of_lt_top_drift_H0_gt {w : ℕ} (hw : 1 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ)
    (h_cz : canonicalCZeta_admissible clock b 0 ch 0 ≤ c_zeta)
    (W_p : List (Fin clock.m)) (q k : ℕ) (hk : k < W_p.length) (j : Fin (w + 1)) (hj_lt : j.val < w) :
    let r := finSumFinEquiv (Sum.inr j)
    dotProduct (zeta_admissible_scaled clock b 0 ch 0 c_zeta) (binomBasis (w + 1) q) -
      (1 + (c_zeta - canonicalCZeta_admissible clock b 0 ch 0)) * (4 * (w + 1 : ℚ))⁻¹ *
        (∑ c : Fin (w + 1), binomBasis (w + 1) q c) <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      (ch * ((q + 1 : ℕ) : ℚ) + H0) →
    ((V_reset (J_admissible_scaled clock b H0 ch delta c_zeta) (M_coupled w) (B_mat (w + 1))
      (zeta_admissible_scaled clock b H0 ch delta c_zeta)).mulVec (binomBasis (w + 1) (q + 1))) r <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      dotProduct (h_row_lin w H0 ch) (binomBasis (w + 1) (q + 1)) := by
  intro r h_drift
  apply stage3_late_start_lt_of_H0_gt hw clock b H0 ch delta c_zeta W_p q k hk j
  have hr_lt : r.val < (w + 1) + w := by
    change (Fin.natAdd (w + 1) j).val < (w + 1) + w
    rw [Fin.val_natAdd]
    omega
  have h_sub := V_reset_admissible_scaled_mulVec_binomBasis_le_zeta_sub_of_lt clock b 0 ch 0 c_zeta
    h_cz q r hr_lt
  dsimp only [r] at h_drift h_sub ⊢
  rw [J_admissible_scaled_indep_of_delta clock b 0 ch delta c_zeta]
  rw [zeta_admissible_scaled_indep_of_delta clock b 0 ch delta c_zeta]
  linarith

/-- For any positive reset action `0 < r.val` at the Stage 4 boundary, the reset score gains the strictly positive
    degree-`w` subdiagonal drift slack `(1 + (c_zeta - canonicalCZeta_admissible)) * (4 * (w + 1))⁻¹ * ∑ c, binomBasis (w + 1) (q + 1) c`. -/
theorem stage4_reset_bound_of_pos_drift_H0_le {w : ℕ} (hw : 1 ≤ w) (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (hLC : clock.C.transpose * L_C = 1)
    (h_cz : canonicalCZeta_admissible clock b 0 ch 0 ≤ c_zeta)
    (hdelta_pos : 0 < delta)
    (q : ℕ) (r : Fin ((w + 1) + (w + 1))) (hr_pos : 0 < r.val)
    (h_le :
      dotProduct (zeta_admissible_scaled clock b 0 ch 0 c_zeta) (binomBasis (w + 1) (q + 1)) -
        (1 + (c_zeta - canonicalCZeta_admissible clock b 0 ch 0)) * (4 * (w + 1 : ℚ))⁻¹ *
          (∑ c : Fin (w + 1), binomBasis (w + 1) (q + 1) c) +
        (Q_reset (J_admissible_scaled clock b 0 ch 0 c_zeta) (M_coupled w) (B_mat (w + 1))
          (zeta_admissible_scaled clock b 0 ch 0 c_zeta)) r 0 ≤
      (∑ σ ∈ Finset.range (q + 1), (clock.R.mulVec (binomBasis w (σ + 1))) b) +
        (ch * ((q + 1 : ℕ) : ℚ) + H0)) :
    dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) (q + 1)) -
      ((J_admissible_scaled clock b H0 ch delta c_zeta * M_coupled w).mulVec (binomBasis (w + 1) (q + 1))) r +
      P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) r <
    (shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1)) b +
      (clock.R.mulVec (binomBasis w (q + 1)) b - clock.R.mulVec (binomBasis w 0) b) +
      dotProduct (h_row_lin w H0 ch) (binomBasis (w + 1) (q + 1)) + delta := by
  apply stage4_reset_bound_of_H0_gt hw clock b H0 ch delta c_zeta c_P0 a_old L_C q r
  have h_sub := stage3_end_inr_admissible_le_zeta_sub_of_pos clock b 0 ch 0 c_zeta c_P0 a_old L_C hLC
    h_cz (q + 1) r hr_pos
  rw [zeta_admissible_scaled_indep_of_delta clock b 0 ch delta c_zeta]
  rw [J_admissible_scaled_indep_of_delta clock b 0 ch delta c_zeta]
  rw [P_admissible_scaled_indep_of_delta clock b 0 ch delta c_zeta c_P0 a_old L_C]
  rw [stage3_end_parent_score_base_eq_sum_succ clock.R q b]
  linarith

/-- **Boundary-vs-Interior Drift Stage 3–4 Admissible Chronology Specification (`BoundaryInteriorStage34AdmissibleSpec`)**:
    Sharpens `QResetCalibratedStage34AdmissibleSpec` by separating the boundary rows (`r = 0` at Stage 3 end / Stage 4
    and `r_top = 2w + 1` at Stage 3 start, where `-J*M` and `-Jᵀ*M` vanish identically) from all interior rows
    (`0 < r.val` at Stage 3 end / Stage 4 and `j.val < w` at Stage 3 start), where every inequality retains the explicit
    strictly positive degree-`w` subdiagonal drift slack
    `(1 + (c_zeta - canonicalCZeta_admissible)) * (4 * (w + 1))⁻¹ * ∑ c, binomBasis (w + 1) Q c`. -/
structure BoundaryInteriorStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hP_early_nonpos :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        x (finSumFinEquiv (Sum.inl j)) ≤ 0
  hP_late_nonneg :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (x : Fin (fc.clock.m + 1)),
      0 ≤ P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        x (finSumFinEquiv (Sum.inr j))
  hdelta_pos : 0 < delta d
  hdelta_lt_one : delta d < 1
  hstage3_parent : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let q := p + (d + 2)
    IsValidPriorityWord fc.clock.G
      ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)))
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1))
  hstage3_early_zero_H0_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length),
      dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (binomBasis (d + 3) (q + 1)) +
        (V_reset (J_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (M_coupled (d + 2)) (B_mat (d + 3))
          (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) ⟨0, by omega⟩ 0 -
          zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d) 0) <
      wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) +
        (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)
  hstage3_early_pos_drift_H0_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length) (j : Fin (d + 3)), 0 < j.val →
      let r := finSumFinEquiv (Sum.inl j)
      dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (binomBasis (d + 3) (q + 1)) -
        (1 + (c_zeta d - canonicalCZeta_admissible fc.clock b 0 (ch d) 0)) * (4 * (((d + 2 : ℕ) : ℚ) + 1))⁻¹ *
          (∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c) +
        (Q_reset (J_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (M_coupled (d + 2)) (B_mat (d + 3))
          (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d))) r 0 <
      wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) +
        (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)
  hstage3_late_top_H0_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length),
      dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (binomBasis (d + 3) q) <
      wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) +
        (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)
  hstage4_reset_zero_H0_le : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (binomBasis (d + 3) (q + 1)) +
      (V_reset (J_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (M_coupled (d + 2)) (B_mat (d + 3))
        (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) ⟨0, by omega⟩ 0 -
        zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d) 0) ≤
    (∑ σ ∈ Finset.range (q + 1), (fc.clock.R.mulVec (binomBasis (d + 2) (σ + 1))) b) +
      (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)
  hstage4_reset_pos_drift_H0_le : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    ∀ r : Fin ((d + 3) + (d + 3)), 0 < r.val →
      dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (binomBasis (d + 3) (q + 1)) -
        (1 + (c_zeta d - canonicalCZeta_admissible fc.clock b 0 (ch d) 0)) * (4 * (((d + 2 : ℕ) : ℚ) + 1))⁻¹ *
          (∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c) +
        (Q_reset (J_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (M_coupled (d + 2)) (B_mat (d + 3))
          (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d))) r 0 ≤
      (∑ σ ∈ Finset.range (q + 1), (fc.clock.R.mulVec (binomBasis (d + 2) (σ + 1))) b) +
        (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)

/-- Automatic conversion from `BoundaryInteriorStage34AdmissibleSpec` to `ParentReducedStage34AdmissibleSpec`. -/
def BoundaryInteriorStage34AdmissibleSpec.toParentReducedStage34AdmissibleSpec
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (d : ℕ) (spec : BoundaryInteriorStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d) :
    ParentReducedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d where
  hP_early_nonpos := spec.hP_early_nonpos
  hP_late_nonneg := spec.hP_late_nonneg
  hdelta_pos := spec.hdelta_pos
  hdelta_lt_one := spec.hdelta_lt_one
  hstage3_parent := spec.hstage3_parent
  hstage3_early_end_lt := fun p k hk j => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    have h_cz0 : canonicalCZeta_admissible fc.clock b 0 (ch d) 0 ≤ c_zeta d := by
      rw [← canonicalCZeta_admissible_indep_of_H0_delta fc.clock b (H0 d) (ch d) (delta d)]
      exact le_trans (canonicalCZeta_admissible_le_full fc.clock b (H0 d) (ch d) (delta d)) (h_cz d)
    by_cases hj : j.val = 0
    · apply stage3_early_end_lt_of_Q_reset_H0_gt (by omega) fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)
        (c_P0 d) (fun _ => 1) fc.L_C fc.hLC h_cz0 W_p q k hk j
      have hr0 : (finSumFinEquiv (Sum.inl j) : Fin ((d + 3) + (d + 3))) = ⟨0, by omega⟩ := by
        ext
        dsimp only [finSumFinEquiv, Equiv.coe_fn_mk, Fin.addCases]
        exact hj
      rw [hr0, Q_reset_admissible_scaled_row_zero_col_zero_eq]
      exact spec.hstage3_early_zero_H0_lt p k hk
    · have hj_pos : 0 < j.val := Nat.pos_of_ne_zero hj
      exact stage3_early_end_lt_of_pos_drift_H0_gt (by omega) fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)
        (c_P0 d) (fun _ => 1) fc.L_C fc.hLC h_cz0 W_p q k hk j hj_pos
        (spec.hstage3_early_pos_drift_H0_lt p k hk j hj_pos)
  hstage3_late_start_lt := fun p k hk j => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    have h_cz0 : canonicalCZeta_admissible fc.clock b 0 (ch d) 0 ≤ c_zeta d := by
      rw [← canonicalCZeta_admissible_indep_of_H0_delta fc.clock b (H0 d) (ch d) (delta d)]
      exact le_trans (canonicalCZeta_admissible_le_full fc.clock b (H0 d) (ch d) (delta d)) (h_cz d)
    exact stage3_late_start_lt_of_Q_reset_H0_gt (by omega) fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)
      h_cz0 W_p q k hk j (spec.hstage3_late_top_H0_lt p k hk)
  hstage4_reset_bound := fun p r => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    have h_cz0 : canonicalCZeta_admissible fc.clock b 0 (ch d) 0 ≤ c_zeta d := by
      rw [← canonicalCZeta_admissible_indep_of_H0_delta fc.clock b (H0 d) (ch d) (delta d)]
      exact le_trans (canonicalCZeta_admissible_le_full fc.clock b (H0 d) (ch d) (delta d)) (h_cz d)
    by_cases hr : r.val = 0
    · apply stage4_reset_bound_of_Q_reset_H0_le (by omega) fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)
        (c_P0 d) (fun _ => 1) fc.L_C fc.hLC h_cz0 spec.hdelta_pos q r
      have hr0 : r = ⟨0, by omega⟩ := Fin.ext hr
      rw [hr0, Q_reset_admissible_scaled_row_zero_col_zero_eq]
      exact spec.hstage4_reset_zero_H0_le p
    · have hr_pos : 0 < r.val := Nat.pos_of_ne_zero hr
      exact stage4_reset_bound_of_pos_drift_H0_le (by omega) fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)
        (c_P0 d) (fun _ => 1) fc.L_C fc.hLC h_cz0 spec.hdelta_pos q r hr_pos
        (spec.hstage4_reset_pos_drift_H0_le p r hr_pos)

/-- **All-Orders Boundary-vs-Interior Drift Stage 3–4 Admissible Karlin Theorem**:
    Polynomial duality gap scaling across all orders $k \ge 2$ from `BoundaryInteriorStage34AdmissibleSpec`,
    where row `0` is evaluated exactly via `V_reset ... 0 0 - zeta 0` and all positive rows `0 < r.val`
    retain the explicit degree-`w` subdiagonal drift slack from `J * M`. -/
theorem all_orders_boundary_interior_stage34_admissible_karlin_theorem
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (bi_lifts : ∀ d : ℕ, BoundaryInteriorStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  let parent_reduced_lifts : ∀ d : ℕ, ParentReducedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d :=
    fun d => (bi_lifts d).toParentReducedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 h_cz d
  exact all_orders_parent_reduced_stage34_admissible_karlin_theorem H0 ch delta c_zeta c_P0 h_cz parent_reduced_lifts k hk

/-! ## Section 15: Parent-vs-Gateway Separation of the `P_admissible_scaled` Sign Conditions -/

/-- `P_admissible_scaled` is completely independent of both `H0` and `delta`. -/
theorem P_admissible_scaled_indep_of_H0_delta {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) :
    P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C =
      P_admissible_scaled clock b 0 ch 0 c_zeta c_P0 a_old L_C := by
  rw [P_admissible_scaled_indep_of_H0 clock b H0 ch delta c_zeta c_P0 a_old L_C]
  exact P_admissible_scaled_indep_of_delta clock b 0 ch delta c_zeta c_P0 a_old L_C

/-- For any parent action `Sum.inl i` with positive projected cone weight
    `0 < a_old_proj clock a_old L_C (finSumFinEquiv (Sum.inl i))`, choosing `c_P0` above the explicit
    threshold guarantees `P_admissible_scaled ≤ 0` on all early reset columns and `0 ≤ P_admissible_scaled`
    on all late reset columns. -/
theorem P_admissible_scaled_parent_sign_of_a_old_proj_pos {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (i : Fin clock.m)
    (ha_pos : 0 < a_old_proj clock a_old L_C (finSumFinEquiv (Sum.inl i)))
    (hcP0 : ∀ r : Fin ((w + 1) + (w + 1)),
      |P_admissible_scaled clock b 0 ch 0 0 0 a_old L_C (finSumFinEquiv (Sum.inl i)) r +
        c_zeta * (L_X_gateway L_C * (Q_reset (J_coupled w) (M_coupled w) (B_mat (w + 1)) (zeta_coupled w)).transpose)
          (finSumFinEquiv (Sum.inl i)) r| /
        a_old_proj clock a_old L_C (finSumFinEquiv (Sum.inl i)) ≤ c_P0) :
    (∀ j : Fin (w + 1),
      P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ≤ 0) ∧
    (∀ j : Fin (w + 1),
      0 ≤ P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))) := by
  let x : Fin (clock.m + 1) := finSumFinEquiv (Sum.inl i)
  have hP_indep := P_admissible_scaled_indep_of_H0_delta clock b H0 ch delta 0 0 a_old L_C
  constructor
  · intro j
    let r : Fin ((w + 1) + (w + 1)) := finSumFinEquiv (Sum.inl j)
    have h_inl := P_admissible_scaled_inl_eq_proj clock b H0 ch delta c_zeta c_P0 a_old L_C x j
    rw [h_inl, hP_indep]
    have h_div := hcP0 r
    have h_mul : |P_admissible_scaled clock b 0 ch 0 0 0 a_old L_C x r +
        c_zeta * (L_X_gateway L_C * (Q_reset (J_coupled w) (M_coupled w) (B_mat (w + 1)) (zeta_coupled w)).transpose) x r| ≤
        c_P0 * a_old_proj clock a_old L_C x :=
      (div_le_iff₀ ha_pos).mp h_div
    have h_le := le_abs_self (P_admissible_scaled clock b 0 ch 0 0 0 a_old L_C x r +
        c_zeta * (L_X_gateway L_C * (Q_reset (J_coupled w) (M_coupled w) (B_mat (w + 1)) (zeta_coupled w)).transpose) x r)
    linarith
  · intro j
    let r : Fin ((w + 1) + (w + 1)) := finSumFinEquiv (Sum.inr j)
    have h_inr := P_admissible_scaled_inr_eq_proj clock b H0 ch delta c_zeta c_P0 a_old L_C x j
    rw [h_inr, hP_indep]
    have h_div := hcP0 r
    have h_mul : |P_admissible_scaled clock b 0 ch 0 0 0 a_old L_C x r +
        c_zeta * (L_X_gateway L_C * (Q_reset (J_coupled w) (M_coupled w) (B_mat (w + 1)) (zeta_coupled w)).transpose) x r| ≤
        c_P0 * a_old_proj clock a_old L_C x :=
      (div_le_iff₀ ha_pos).mp h_div
    have h_le := neg_abs_le (P_admissible_scaled clock b 0 ch 0 0 0 a_old L_C x r +
        c_zeta * (L_X_gateway L_C * (Q_reset (J_coupled w) (M_coupled w) (B_mat (w + 1)) (zeta_coupled w)).transpose) x r)
    linarith

/-- On the gateway row `gatewayOldAct clock.m`, the sign conditions of `P_admissible_scaled`
    reduce purely to the column-`0` signs of `Q_reset` (independent of `H0`, `delta`, `c_P0`, `a_old`, and `L_C`). -/
theorem P_admissible_scaled_gateway_sign_iff_Q_reset {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (hLC : clock.C.transpose * L_C = 1) :
    ((∀ j : Fin (w + 1),
      P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C
        (gatewayOldAct clock.m) (finSumFinEquiv (Sum.inl j)) ≤ 0) ∧
     (∀ j : Fin (w + 1),
      0 ≤ P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C
        (gatewayOldAct clock.m) (finSumFinEquiv (Sum.inr j)))) ↔
    ((∀ j : Fin (w + 1),
      Q_reset (J_admissible_scaled clock b 0 ch 0 c_zeta) (M_coupled w) (B_mat (w + 1))
        (zeta_admissible_scaled clock b 0 ch 0 c_zeta) (finSumFinEquiv (Sum.inl j)) 0 ≤ 0) ∧
     (∀ j : Fin (w + 1),
      0 ≤ Q_reset (J_admissible_scaled clock b 0 ch 0 c_zeta) (M_coupled w) (B_mat (w + 1))
        (zeta_admissible_scaled clock b 0 ch 0 c_zeta) (finSumFinEquiv (Sum.inr j)) 0)) := by
  have hP_indep := P_admissible_scaled_indep_of_H0_delta clock b H0 ch delta c_zeta c_P0 a_old L_C
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · intro j
      have h := h1 j
      rw [hP_indep, P_admissible_scaled_gateway_row_eq_Q_reset clock b 0 ch 0 c_zeta c_P0 a_old L_C hLC] at h
      exact h
    · intro j
      have h := h2 j
      rw [hP_indep, P_admissible_scaled_gateway_row_eq_Q_reset clock b 0 ch 0 c_zeta c_P0 a_old L_C hLC] at h
      exact h
  · rintro ⟨h1, h2⟩
    constructor
    · intro j
      rw [hP_indep, P_admissible_scaled_gateway_row_eq_Q_reset clock b 0 ch 0 c_zeta c_P0 a_old L_C hLC]
      exact h1 j
    · intro j
      rw [hP_indep, P_admissible_scaled_gateway_row_eq_Q_reset clock b 0 ch 0 c_zeta c_P0 a_old L_C hLC]
      exact h2 j

/-- Complete decomposition of the `P_admissible_scaled` early/late sign conditions into
    (1) parent rows `Sum.inl i` and (2) the gateway row `gatewayOldAct clock.m` via `Q_reset ... r 0`. -/
theorem P_admissible_scaled_sign_of_parent_and_gateway {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ) (a_old : Fin (clock.m + 1) → ℚ)
    (L_C : Matrix (Fin clock.m) (Fin w) ℚ) (hLC : clock.C.transpose * L_C = 1)
    (h_parent_early : ∀ (i : Fin clock.m) (j : Fin (w + 1)),
      P_admissible_scaled clock b 0 ch 0 c_zeta c_P0 a_old L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ≤ 0)
    (h_parent_late : ∀ (i : Fin clock.m) (j : Fin (w + 1)),
      0 ≤ P_admissible_scaled clock b 0 ch 0 c_zeta c_P0 a_old L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)))
    (h_gw_early : ∀ j : Fin (w + 1),
      Q_reset (J_admissible_scaled clock b 0 ch 0 c_zeta) (M_coupled w) (B_mat (w + 1))
        (zeta_admissible_scaled clock b 0 ch 0 c_zeta) (finSumFinEquiv (Sum.inl j)) 0 ≤ 0)
    (h_gw_late : ∀ j : Fin (w + 1),
      0 ≤ Q_reset (J_admissible_scaled clock b 0 ch 0 c_zeta) (M_coupled w) (B_mat (w + 1))
        (zeta_admissible_scaled clock b 0 ch 0 c_zeta) (finSumFinEquiv (Sum.inr j)) 0) :
    (∀ (j : Fin (w + 1)) (x : Fin (clock.m + 1)),
      P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C x (finSumFinEquiv (Sum.inl j)) ≤ 0) ∧
    (∀ (j : Fin (w + 1)) (x : Fin (clock.m + 1)),
      0 ≤ P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C x (finSumFinEquiv (Sum.inr j))) := by
  have hP_indep := P_admissible_scaled_indep_of_H0_delta clock b H0 ch delta c_zeta c_P0 a_old L_C
  constructor
  · intro j x
    rw [hP_indep]
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective x
    cases s with
    | inl i => exact h_parent_early i j
    | inr v =>
      have hv : v = 0 := Subsingleton.elim v 0
      subst hv
      change P_admissible_scaled clock b 0 ch 0 c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) (finSumFinEquiv (Sum.inl j)) ≤ 0
      rw [P_admissible_scaled_gateway_row_eq_Q_reset clock b 0 ch 0 c_zeta c_P0 a_old L_C hLC]
      exact h_gw_early j
  · intro j x
    rw [hP_indep]
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective x
    cases s with
    | inl i => exact h_parent_late i j
    | inr v =>
      have hv : v = 0 := Subsingleton.elim v 0
      subst hv
      change 0 ≤ P_admissible_scaled clock b 0 ch 0 c_zeta c_P0 a_old L_C (gatewayOldAct clock.m) (finSumFinEquiv (Sum.inr j))
      rw [P_admissible_scaled_gateway_row_eq_Q_reset clock b 0 ch 0 c_zeta c_P0 a_old L_C hLC]
      exact h_gw_late j

/-!
## Section 16: Sign-Separated & Q-Reset-Eliminated Stage 3–4 Admissible Specification (`SignSeparatedStage34AdmissibleSpec`)

In this section, we establish:
1. Two helper drift-elimination lemmas (`stage3_early_end_lt_of_pure_drift_H0_gt` and
   `stage4_reset_bound_of_pure_drift_H0_le`) showing that whenever `Q_reset ... (inl j) 0 ≤ 0`,
   the $Q_{\mathrm{reset}}$ term on early reset actions is purely non-positive and can be
   dropped entirely from the Stage 3 early waiting and Stage 4 reset upper bounds.
2. The sign-separated specification `SignSeparatedStage34AdmissibleSpec`, where:
   - Coupling signs are split between parent rows (`hP_parent_early_nonpos`, `hP_parent_late_nonneg`)
     and the gateway row (`hQ_gw_early_nonpos`, `hQ_gw_late_nonneg`),
   - Stage 3 early waiting and Stage 4 early reset bounds are completely freed of $Q_{\mathrm{reset}}$
     using `hQ_gw_early_nonpos`,
   - Row 0 boundary condition is formulated directly via `Q_reset ... 0 0`.
3. An automatic structure constructor `.toBoundaryInteriorStage34AdmissibleSpec` and the top-level
   synthesis theorem `all_orders_sign_separated_stage34_admissible_karlin_theorem`.
-/

/-- If `Q_reset ... (finSumFinEquiv (Sum.inl j)) 0 ≤ 0`, then the Stage 3 early reset waiting condition
    holds as long as the pure ceiling-minus-subdiagonal-drift term is strictly below the parent score. -/
theorem stage3_early_end_lt_of_pure_drift_H0_gt {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (ch c_zeta : ℚ)
    (W_p : List (Fin clock.m)) (q k : ℕ) (hk : k < W_p.length) (j : Fin (w + 1))
    (hQ_nonpos : (Q_reset (J_admissible_scaled clock b 0 ch 0 c_zeta) (M_coupled w) (B_mat (w + 1))
      (zeta_admissible_scaled clock b 0 ch 0 c_zeta)) (finSumFinEquiv (Sum.inl j)) 0 ≤ 0)
    (H0 : ℚ)
    (h_pure :
      dotProduct (zeta_admissible_scaled clock b 0 ch 0 c_zeta) (binomBasis (w + 1) (q + 1)) -
        (1 + (c_zeta - canonicalCZeta_admissible clock b 0 ch 0)) * (4 * (w + 1 : ℚ))⁻¹ *
          (∑ c : Fin (w + 1), binomBasis (w + 1) (q + 1) c) <
      wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
        (ch * ((q + 1 : ℕ) : ℚ) + H0)) :
    dotProduct (zeta_admissible_scaled clock b 0 ch 0 c_zeta) (binomBasis (w + 1) (q + 1)) -
      (1 + (c_zeta - canonicalCZeta_admissible clock b 0 ch 0)) * (4 * (w + 1 : ℚ))⁻¹ *
        (∑ c : Fin (w + 1), binomBasis (w + 1) (q + 1) c) +
      (Q_reset (J_admissible_scaled clock b 0 ch 0 c_zeta) (M_coupled w) (B_mat (w + 1))
        (zeta_admissible_scaled clock b 0 ch 0 c_zeta)) (finSumFinEquiv (Sum.inl j)) 0 <
    wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
      (ch * ((q + 1 : ℕ) : ℚ) + H0) := by
  linarith

/-- If `Q_reset ... r 0 ≤ 0`, then the Stage 4 reset bound holds as long as the pure
    ceiling-minus-subdiagonal-drift term is bounded by the accumulated parent score. -/
theorem stage4_reset_bound_of_pure_drift_H0_le {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (ch c_zeta : ℚ)
    (q : ℕ) (r : Fin ((w + 1) + (w + 1)))
    (hQ_nonpos : (Q_reset (J_admissible_scaled clock b 0 ch 0 c_zeta) (M_coupled w) (B_mat (w + 1))
      (zeta_admissible_scaled clock b 0 ch 0 c_zeta)) r 0 ≤ 0)
    (H0 : ℚ)
    (h_pure :
      dotProduct (zeta_admissible_scaled clock b 0 ch 0 c_zeta) (binomBasis (w + 1) (q + 1)) -
        (1 + (c_zeta - canonicalCZeta_admissible clock b 0 ch 0)) * (4 * (w + 1 : ℚ))⁻¹ *
          (∑ c : Fin (w + 1), binomBasis (w + 1) (q + 1) c) ≤
      (∑ σ ∈ Finset.range (q + 1), (clock.R.mulVec (binomBasis w (σ + 1))) b) +
        (ch * ((q + 1 : ℕ) : ℚ) + H0)) :
    dotProduct (zeta_admissible_scaled clock b 0 ch 0 c_zeta) (binomBasis (w + 1) (q + 1)) -
      (1 + (c_zeta - canonicalCZeta_admissible clock b 0 ch 0)) * (4 * (w + 1 : ℚ))⁻¹ *
        (∑ c : Fin (w + 1), binomBasis (w + 1) (q + 1) c) +
      (Q_reset (J_admissible_scaled clock b 0 ch 0 c_zeta) (M_coupled w) (B_mat (w + 1))
        (zeta_admissible_scaled clock b 0 ch 0 c_zeta)) r 0 ≤
    (∑ σ ∈ Finset.range (q + 1), (clock.R.mulVec (binomBasis w (σ + 1))) b) +
      (ch * ((q + 1 : ℕ) : ℚ) + H0) := by
  linarith

/-- **Sign-Separated Stage 3–4 Admissible Chronology Specification (`SignSeparatedStage34AdmissibleSpec`)**:
    Separates parent coupling rows from the gateway row, uses `Q_reset_admissible_scaled_row_zero_col_zero_eq`
    to formulate the boundary at row 0 directly via `Q_reset`, and eliminates `Q_reset` from all interior early
    Stage 3–4 conditions by virtue of gateway non-positivity `hQ_gw_early_nonpos`. -/
structure SignSeparatedStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  -- Parent rows coupling signs
  hP_parent_early_nonpos :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (i : Fin fc.clock.m),
      P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ≤ 0
  hP_parent_late_nonneg :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (i : Fin fc.clock.m),
      0 ≤ P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))
  -- Gateway row coupling signs (exact Q_reset equivalent)
  hQ_gw_early_nonpos :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)),
      (Q_reset (J_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (M_coupled (d + 2)) (B_mat (d + 3))
        (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d))) (finSumFinEquiv (Sum.inl j)) 0 ≤ 0
  hQ_gw_late_nonneg :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)),
      0 ≤ (Q_reset (J_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (M_coupled (d + 2)) (B_mat (d + 3))
        (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d))) (finSumFinEquiv (Sum.inr j)) 0
  hdelta_pos : 0 < delta d
  hdelta_lt_one : delta d < 1
  hstage3_parent : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let q := p + (d + 2)
    IsValidPriorityWord fc.clock.G
      ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)))
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1))
  -- Stage 3 early row 0 (boundary) with direct Q_reset
  hstage3_early_zero_H0_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length),
      dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (binomBasis (d + 3) (q + 1)) +
        (Q_reset (J_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (M_coupled (d + 2)) (B_mat (d + 3))
          (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d))) ⟨0, by omega⟩ 0 <
      wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) +
        (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)
  -- Stage 3 early interior: Q_reset is eliminated!
  hstage3_early_pos_pure_drift_H0_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length),
      dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (binomBasis (d + 3) (q + 1)) -
        (1 + (c_zeta d - canonicalCZeta_admissible fc.clock b 0 (ch d) 0)) * (4 * (((d + 2 : ℕ) : ℚ) + 1))⁻¹ *
          (∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c) <
      wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) +
        (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)
  -- Stage 3 late top (boundary)
  hstage3_late_top_H0_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length),
      dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (binomBasis (d + 3) q) <
      wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) +
        (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)
  -- Stage 4 reset row 0 (boundary) with direct Q_reset
  hstage4_reset_zero_H0_le : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (binomBasis (d + 3) (q + 1)) +
      (Q_reset (J_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (M_coupled (d + 2)) (B_mat (d + 3))
        (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d))) ⟨0, by omega⟩ 0 ≤
    (∑ σ ∈ Finset.range (q + 1), (fc.clock.R.mulVec (binomBasis (d + 2) (σ + 1))) b) +
      (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)
  -- Stage 4 reset interior: for early actions (Sum.inl), Q_reset is eliminated!
  hstage4_reset_pos_early_pure_drift_H0_le : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (binomBasis (d + 3) (q + 1)) -
      (1 + (c_zeta d - canonicalCZeta_admissible fc.clock b 0 (ch d) 0)) * (4 * (((d + 2 : ℕ) : ℚ) + 1))⁻¹ *
        (∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c) ≤
    (∑ σ ∈ Finset.range (q + 1), (fc.clock.R.mulVec (binomBasis (d + 2) (σ + 1))) b) +
      (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)
  -- Stage 4 reset interior for late actions (Sum.inr)
  hstage4_reset_pos_late_drift_H0_le : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    ∀ j : Fin (d + 3),
      let r := finSumFinEquiv (Sum.inr j)
      dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (binomBasis (d + 3) (q + 1)) -
        (1 + (c_zeta d - canonicalCZeta_admissible fc.clock b 0 (ch d) 0)) * (4 * (((d + 2 : ℕ) : ℚ) + 1))⁻¹ *
          (∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c) +
        (Q_reset (J_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (M_coupled (d + 2)) (B_mat (d + 3))
          (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d))) r 0 ≤
      (∑ σ ∈ Finset.range (q + 1), (fc.clock.R.mulVec (binomBasis (d + 2) (σ + 1))) b) +
        (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)

/-- Automatic conversion from `SignSeparatedStage34AdmissibleSpec` to `BoundaryInteriorStage34AdmissibleSpec`. -/
def SignSeparatedStage34AdmissibleSpec.toBoundaryInteriorStage34AdmissibleSpec
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (d : ℕ) (spec : SignSeparatedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d) :
    BoundaryInteriorStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d where
  hP_early_nonpos := fun j x => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    rcases (finSumFinEquiv : Fin fc.clock.m ⊕ Fin 1 ≃ Fin (fc.clock.m + 1)).surjective x with ⟨s, rfl⟩
    cases s with
    | inl i =>
      exact spec.hP_parent_early_nonpos j i
    | inr v =>
      have hv : v = 0 := Subsingleton.elim v 0
      subst hv
      change P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        (gatewayOldAct fc.clock.m) (finSumFinEquiv (Sum.inl j)) ≤ 0
      rw [P_admissible_scaled_gateway_row_eq_Q_reset fc.clock b (H0 d) (ch d) (delta d)
        (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C fc.hLC]
      rw [Q_reset_admissible_scaled_indep_of_H0_delta fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)]
      exact spec.hQ_gw_early_nonpos j
  hP_late_nonneg := fun j x => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    rcases (finSumFinEquiv : Fin fc.clock.m ⊕ Fin 1 ≃ Fin (fc.clock.m + 1)).surjective x with ⟨s, rfl⟩
    cases s with
    | inl i =>
      exact spec.hP_parent_late_nonneg j i
    | inr v =>
      have hv : v = 0 := Subsingleton.elim v 0
      subst hv
      change 0 ≤ P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        (gatewayOldAct fc.clock.m) (finSumFinEquiv (Sum.inr j))
      rw [P_admissible_scaled_gateway_row_eq_Q_reset fc.clock b (H0 d) (ch d) (delta d)
        (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C fc.hLC]
      rw [Q_reset_admissible_scaled_indep_of_H0_delta fc.clock b (H0 d) (ch d) (delta d) (c_zeta d)]
      exact spec.hQ_gw_late_nonneg j
  hdelta_pos := spec.hdelta_pos
  hdelta_lt_one := spec.hdelta_lt_one
  hstage3_parent := spec.hstage3_parent
  hstage3_early_zero_H0_lt := fun p k hk => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    have hQ := Q_reset_admissible_scaled_row_zero_col_zero_eq fc.clock b 0 (ch d) 0 (c_zeta d)
    have hspec := spec.hstage3_early_zero_H0_lt p k hk
    linarith
  hstage3_early_pos_drift_H0_lt := fun p k hk j _ => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    apply stage3_early_end_lt_of_pure_drift_H0_gt fc.clock b (ch d) (c_zeta d) W_p q k hk j
      (spec.hQ_gw_early_nonpos j) (H0 d)
    exact spec.hstage3_early_pos_pure_drift_H0_lt p k hk
  hstage3_late_top_H0_lt := spec.hstage3_late_top_H0_lt
  hstage4_reset_zero_H0_le := fun p => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    have hQ := Q_reset_admissible_scaled_row_zero_col_zero_eq fc.clock b 0 (ch d) 0 (c_zeta d)
    have hspec := spec.hstage4_reset_zero_H0_le p
    linarith
  hstage4_reset_pos_drift_H0_le := fun p r _ => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    rcases (finSumFinEquiv : Fin (d + 3) ⊕ Fin (d + 3) ≃ Fin ((d + 3) + (d + 3))).surjective r with ⟨s, rfl⟩
    cases s with
    | inl j_early =>
      apply stage4_reset_bound_of_pure_drift_H0_le fc.clock b (ch d) (c_zeta d) (p + (d + 2))
        (finSumFinEquiv (Sum.inl j_early)) (spec.hQ_gw_early_nonpos j_early) (H0 d)
      exact spec.hstage4_reset_pos_early_pure_drift_H0_le p
    | inr j_late =>
      exact spec.hstage4_reset_pos_late_drift_H0_le p j_late

/-- **All-Orders Sign-Separated Stage 3–4 Admissible Karlin Theorem**:
    Polynomial duality gap scaling across all orders $k \ge 2$ from `SignSeparatedStage34AdmissibleSpec`. -/
theorem all_orders_sign_separated_stage34_admissible_karlin_theorem
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_full_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (ss_lifts : ∀ d : ℕ, SignSeparatedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  let bi_lifts : ∀ d : ℕ, BoundaryInteriorStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d :=
    fun d => (ss_lifts d).toBoundaryInteriorStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d
  exact all_orders_boundary_interior_stage34_admissible_karlin_theorem H0 ch delta c_zeta c_P0 h_cz bi_lifts k hk

/-!
## Section 17: Gateway Q-Reset Dominance, Canonical Gateway Threshold (`canonicalCZeta_gw_admissible`), & Pure-Ceiling Stage 3–4 Admissible Specification (`PureCeilingStage34AdmissibleSpec`)

In this section, we establish:
1. The explicit threshold `canonicalCZeta_gw_admissible`, augmenting `canonicalCZeta_full_admissible`
   with `4 * ∑ r, |Q_reset (J_general) r 0|`.
2. Coercion bounds showing `canonicalCZeta_full_admissible ≤ canonicalCZeta_gw_admissible` and
   `4 * |Q_reset (J_general) r 0| ≤ canonicalCZeta_gw_admissible`.
3. Unconditional sign-definiteness and two-sided bounds on the gateway row of `Q_reset (J_admissible_scaled)` at column 0:
   - Early reset actions: `Q_reset ... (inl j) 0 ≤ 0` (and row 0: `Q_reset ... ⟨0, _⟩ 0 ≤ 0`),
   - Late reset actions: `0 ≤ Q_reset ... (inr j) 0 ≤ (5 / 2) * c_zeta`,
   whenever `canonicalCZeta_gw_admissible ≤ c_zeta`.
4. Phase monotonicity of the ceiling dot product (`dotProduct_zeta_admissible_scaled_mono_q`).
5. The pure-ceiling specification `PureCeilingStage34AdmissibleSpec`, which completely eliminates
   `hQ_gw_early_nonpos`, `hQ_gw_late_nonneg`, and all `Q_reset`/`V_reset` terms from Stage 3 and Stage 4,
   collapsing the 6 reset inequalities of `SignSeparatedStage34AdmissibleSpec` into just 2 scalar
   polynomial ceiling bounds (`hstage3_ceiling_H0_lt` and `hstage4_ceiling_H0_le`).
-/

/-- Explicit canonical ceiling scaling constant guaranteeing gateway row sign-definiteness
    for the scaled admissible lift: `Q_reset ... (inl j) 0 ≤ 0` and `0 ≤ Q_reset ... (inr j) 0`. -/
def canonicalCZeta_gw_admissible {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta : ℚ) : ℚ :=
  canonicalCZeta_full_admissible clock b H0 ch delta +
    4 * ∑ r : Fin ((w + 1) + (w + 1)),
      |Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
        (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) r 0|

/-- The gateway admissible ceiling threshold is at least the full admissible ceiling threshold. -/
theorem canonicalCZeta_full_le_gw_admissible {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta : ℚ) :
    canonicalCZeta_full_admissible clock b H0 ch delta ≤
      canonicalCZeta_gw_admissible clock b H0 ch delta := by
  unfold canonicalCZeta_gw_admissible
  have h_nonneg : 0 ≤ 4 * ∑ r : Fin ((w + 1) + (w + 1)),
      |Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
        (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) r 0| := by
    have h1 : 0 ≤ (4 : ℚ) := by norm_num
    have h2 : 0 ≤ ∑ r : Fin ((w + 1) + (w + 1)),
        |Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
          (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) r 0| :=
      Finset.sum_nonneg fun r _ => abs_nonneg _
    exact mul_nonneg h1 h2
  linarith

/-- The gateway admissible ceiling threshold dominates `4 * |Q_reset (J_general) r 0|` for every row `r`. -/
theorem four_mul_abs_Q_reset_general_le_canonicalCZeta_gw_admissible {w : ℕ}
    (clock : AlgebraicClock w) (b : Fin clock.m) (H0 ch delta : ℚ)
    (r : Fin ((w + 1) + (w + 1))) :
    4 * |Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
      (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) r 0| ≤
    canonicalCZeta_gw_admissible clock b H0 ch delta := by
  unfold canonicalCZeta_gw_admissible
  have h1 : 1 ≤ canonicalCZeta_admissible clock b H0 ch delta :=
    one_le_canonicalCZeta_admissible clock b H0 ch delta
  have h2 : canonicalCZeta_admissible clock b H0 ch delta ≤
      canonicalCZeta_full_admissible clock b H0 ch delta :=
    canonicalCZeta_admissible_le_full clock b H0 ch delta
  have h_full_pos : 0 ≤ canonicalCZeta_full_admissible clock b H0 ch delta := by
    linarith
  have h_sum : |Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
      (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) r 0| ≤
    ∑ r' : Fin ((w + 1) + (w + 1)),
      |Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
        (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) r' 0| :=
    Finset.single_le_sum
      (f := fun r' => |Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
        (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) r' 0|)
      (fun r' _ => abs_nonneg _) (Finset.mem_univ r)
  have h_mul : 4 * |Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
      (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) r 0| ≤
    4 * ∑ r' : Fin ((w + 1) + (w + 1)),
      |Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
        (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) r' 0| := by
    nlinarith
  linarith

/-- Early reset action gateway row sign-definiteness:
    `Q_reset (J_admissible_scaled) (inl j) 0 ≤ 0` whenever `canonicalCZeta_gw_admissible ≤ c_zeta`. -/
theorem Q_reset_admissible_scaled_inl_col_zero_nonpos_of_ge {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ)
    (h_cz : canonicalCZeta_gw_admissible clock b H0 ch delta ≤ c_zeta)
    (j : Fin (w + 1)) :
    (Q_reset (J_admissible_scaled clock b 0 ch 0 c_zeta) (M_coupled w) (B_mat (w + 1))
      (zeta_admissible_scaled clock b 0 ch 0 c_zeta)) (finSumFinEquiv (Sum.inl j)) 0 ≤ 0 := by
  have hdecomp := congr_fun (congr_fun
    (Q_reset_admissible_scaled_decomp clock b 0 ch 0 c_zeta) (finSumFinEquiv (Sum.inl j))) 0
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hdecomp
  rw [hdecomp]
  have hQ_coupled := Q_reset_coupled_inl_col_zero_le_neg_quarter w j
  have h_bound := four_mul_abs_Q_reset_general_le_canonicalCZeta_gw_admissible clock b H0 ch delta
    (finSumFinEquiv (Sum.inl j))
  have h_gen_le_abs : Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
      (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) (finSumFinEquiv (Sum.inl j)) 0 ≤
    |Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
      (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) (finSumFinEquiv (Sum.inl j)) 0| :=
    le_abs_self _
  have h_gen_le_cz : Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
      (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) (finSumFinEquiv (Sum.inl j)) 0 ≤
    c_zeta / 4 := by
    linarith
  have h1 := one_le_canonicalCZeta_admissible clock b H0 ch delta
  have h2 := canonicalCZeta_admissible_le_full clock b H0 ch delta
  have h3 := canonicalCZeta_full_le_gw_admissible clock b H0 ch delta
  have h_cz_nonneg : 0 ≤ c_zeta := by linarith
  have h_prod : c_zeta * Q_reset (J_coupled w) (M_coupled w) (B_mat (w + 1)) (zeta_coupled w)
      (finSumFinEquiv (Sum.inl j)) 0 ≤ c_zeta * (- (1 / 4 : ℚ)) :=
    mul_le_mul_of_nonneg_left hQ_coupled h_cz_nonneg
  linarith

/-- Late reset action gateway row sign-definiteness:
    `0 ≤ Q_reset (J_admissible_scaled) (inr j) 0` whenever `canonicalCZeta_gw_admissible ≤ c_zeta`. -/
theorem Q_reset_admissible_scaled_inr_col_zero_nonneg_of_ge {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ)
    (h_cz : canonicalCZeta_gw_admissible clock b H0 ch delta ≤ c_zeta)
    (j : Fin (w + 1)) :
    0 ≤ (Q_reset (J_admissible_scaled clock b 0 ch 0 c_zeta) (M_coupled w) (B_mat (w + 1))
      (zeta_admissible_scaled clock b 0 ch 0 c_zeta)) (finSumFinEquiv (Sum.inr j)) 0 := by
  have hdecomp := congr_fun (congr_fun
    (Q_reset_admissible_scaled_decomp clock b 0 ch 0 c_zeta) (finSumFinEquiv (Sum.inr j))) 0
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hdecomp
  rw [hdecomp]
  have hQ_coupled := Q_reset_coupled_inr_col_zero_ge_quarter clock j
  have h_bound := four_mul_abs_Q_reset_general_le_canonicalCZeta_gw_admissible clock b H0 ch delta
    (finSumFinEquiv (Sum.inr j))
  have h_gen_ge_neg_abs : - |Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
      (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) (finSumFinEquiv (Sum.inr j)) 0| ≤
    Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
      (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) (finSumFinEquiv (Sum.inr j)) 0 :=
    neg_abs_le _
  have h_gen_ge_neg_cz : - (c_zeta / 4) ≤
    Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
      (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) (finSumFinEquiv (Sum.inr j)) 0 := by
    linarith
  have h1 := one_le_canonicalCZeta_admissible clock b H0 ch delta
  have h2 := canonicalCZeta_admissible_le_full clock b H0 ch delta
  have h3 := canonicalCZeta_full_le_gw_admissible clock b H0 ch delta
  have h_cz_nonneg : 0 ≤ c_zeta := by linarith
  have h_prod : c_zeta * (1 / 4 : ℚ) ≤ c_zeta * Q_reset (J_coupled w) (M_coupled w) (B_mat (w + 1))
      (zeta_coupled w) (finSumFinEquiv (Sum.inr j)) 0 :=
    mul_le_mul_of_nonneg_left hQ_coupled h_cz_nonneg
  linarith

/-- Gateway row column 0 value of `Q_reset (J_admissible_scaled)` at row 0 is non-positive:
    `Q_reset ... ⟨0, _⟩ 0 ≤ 0` whenever `canonicalCZeta_gw_admissible ≤ c_zeta`. -/
theorem Q_reset_admissible_scaled_row_zero_col_zero_nonpos_of_ge {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ)
    (h_cz : canonicalCZeta_gw_admissible clock b H0 ch delta ≤ c_zeta) :
    (Q_reset (J_admissible_scaled clock b 0 ch 0 c_zeta) (M_coupled w) (B_mat (w + 1))
      (zeta_admissible_scaled clock b 0 ch 0 c_zeta)) ⟨0, by omega⟩ 0 ≤ 0 := by
  have h0 : (⟨0, by omega⟩ : Fin ((w + 1) + (w + 1))) = finSumFinEquiv (Sum.inl (0 : Fin (w + 1))) := by
    ext
    simp only [finSumFinEquiv_apply_left, Fin.val_castAdd, Fin.val_zero]
  rw [h0]
  exact Q_reset_admissible_scaled_inl_col_zero_nonpos_of_ge clock b H0 ch delta c_zeta h_cz 0

/-- Late reset action gateway row column 0 upper bound:
    `Q_reset (J_admissible_scaled) (inr j) 0 ≤ (5 / 2) * c_zeta` whenever `canonicalCZeta_gw_admissible ≤ c_zeta`. -/
theorem Q_reset_admissible_scaled_inr_col_zero_le_five_halves_c_zeta_of_ge {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ)
    (h_cz : canonicalCZeta_gw_admissible clock b H0 ch delta ≤ c_zeta)
    (j : Fin (w + 1)) :
    (Q_reset (J_admissible_scaled clock b 0 ch 0 c_zeta) (M_coupled w) (B_mat (w + 1))
      (zeta_admissible_scaled clock b 0 ch 0 c_zeta)) (finSumFinEquiv (Sum.inr j)) 0 ≤
    (5 / 2 : ℚ) * c_zeta := by
  have hdecomp := congr_fun (congr_fun
    (Q_reset_admissible_scaled_decomp clock b 0 ch 0 c_zeta) (finSumFinEquiv (Sum.inr j))) 0
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hdecomp
  rw [hdecomp]
  have hQ_coupled := Q_reset_coupled_inr_col_zero_le_nine_quarters clock j
  have h_bound := four_mul_abs_Q_reset_general_le_canonicalCZeta_gw_admissible clock b H0 ch delta
    (finSumFinEquiv (Sum.inr j))
  have h_gen_le_abs : Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
      (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) (finSumFinEquiv (Sum.inr j)) 0 ≤
    |Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
      (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) (finSumFinEquiv (Sum.inr j)) 0| :=
    le_abs_self _
  have h_gen_le_cz : Q_reset (J_general w (E_rank2 (F_admissible clock b 0 ch 0)))
      (M_coupled w) (B_mat (w + 1)) (zeta_admissible clock b 0 ch 0) (finSumFinEquiv (Sum.inr j)) 0 ≤
    c_zeta / 4 := by
    linarith
  have h1 := one_le_canonicalCZeta_admissible clock b H0 ch delta
  have h2 := canonicalCZeta_admissible_le_full clock b H0 ch delta
  have h3 := canonicalCZeta_full_le_gw_admissible clock b H0 ch delta
  have h_cz_nonneg : 0 ≤ c_zeta := by linarith
  have h_prod : c_zeta * Q_reset (J_coupled w) (M_coupled w) (B_mat (w + 1))
      (zeta_coupled w) (finSumFinEquiv (Sum.inr j)) 0 ≤ c_zeta * (9 / 4 : ℚ) :=
    mul_le_mul_of_nonneg_left hQ_coupled h_cz_nonneg
  linarith

/-- Monotonicity of the dot product `zeta_admissible_scaled · binomBasis (w + 1) q` in phase index `q`. -/
theorem dotProduct_zeta_admissible_scaled_mono_q {w : ℕ} (clock : AlgebraicClock w)
    (b : Fin clock.m) (H0 ch delta c_zeta : ℚ)
    (h_cz : canonicalCZeta_admissible clock b H0 ch delta ≤ c_zeta)
    (q : ℕ) :
    dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) q) ≤
    dotProduct (zeta_admissible_scaled clock b H0 ch delta c_zeta) (binomBasis (w + 1) (q + 1)) := by
  have h_zeta_ge_one : ∀ c : Fin (w + 1), 1 ≤ zeta_admissible_scaled clock b H0 ch delta c_zeta c := by
    intro c
    have h_diff : zeta_admissible_scaled clock b H0 ch delta c_zeta c =
        zeta_admissible_scaled clock b H0 ch delta (canonicalCZeta_admissible clock b H0 ch delta) c +
          (c_zeta - canonicalCZeta_admissible clock b H0 ch delta) := by
      unfold zeta_admissible_scaled zeta_coupled
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      ring
    rw [h_diff]
    have h_base := zeta_admissible_scaled_canonicalCZeta_ge_one clock b H0 ch delta c
    linarith
  have h_zeta_nonneg : ∀ c : Fin (w + 1), 0 ≤ zeta_admissible_scaled clock b H0 ch delta c_zeta c := by
    intro c
    linarith [h_zeta_ge_one c]
  simp only [dotProduct]
  refine Finset.sum_le_sum fun c _ => ?_
  exact mul_le_mul_of_nonneg_left (binomBasis_le_succ (w + 1) q c) (h_zeta_nonneg c)

/-- **Pure-Ceiling Stage 3–4 Admissible Chronology Specification (`PureCeilingStage34AdmissibleSpec`)**:
    Completely eliminates `hQ_gw_early_nonpos`, `hQ_gw_late_nonneg`, and all interior $Q_{\mathrm{reset}}$
    dependencies, collapsing Stage 3 into a single pure ceiling bound `hstage3_ceiling_H0_lt` and Stage 4
    into a single ceiling-plus-$(5/2)c_\zeta$ bound `hstage4_ceiling_H0_le`. -/
structure PureCeilingStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hP_parent_early_nonpos :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (i : Fin fc.clock.m),
      P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ≤ 0
  hP_parent_late_nonneg :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (i : Fin fc.clock.m),
      0 ≤ P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))
  hdelta_pos : 0 < delta d
  hdelta_lt_one : delta d < 1
  hstage3_parent : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let q := p + (d + 2)
    IsValidPriorityWord fc.clock.G
      ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)))
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1))
  hstage3_ceiling_H0_lt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length),
      dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (binomBasis (d + 3) (q + 1)) <
      wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) +
        (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)
  hstage4_ceiling_H0_le : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    dotProduct (zeta_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d)) (binomBasis (d + 3) (q + 1)) +
      (5 / 2 : ℚ) * c_zeta d ≤
    (∑ σ ∈ Finset.range (q + 1), (fc.clock.R.mulVec (binomBasis (d + 2) (σ + 1))) b) +
      (ch d * ((q + 1 : ℕ) : ℚ) + H0 d)

/-- Automatic conversion from `PureCeilingStage34AdmissibleSpec` to `SignSeparatedStage34AdmissibleSpec`. -/
def PureCeilingStage34AdmissibleSpec.toSignSeparatedStage34AdmissibleSpec
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_gw_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (d : ℕ) (spec : PureCeilingStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d) :
    SignSeparatedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d where
  hP_parent_early_nonpos := spec.hP_parent_early_nonpos
  hP_parent_late_nonneg := spec.hP_parent_late_nonneg
  hQ_gw_early_nonpos := fun j => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    exact Q_reset_admissible_scaled_inl_col_zero_nonpos_of_ge fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (h_cz d) j
  hQ_gw_late_nonneg := fun j => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    exact Q_reset_admissible_scaled_inr_col_zero_nonneg_of_ge fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (h_cz d) j
  hdelta_pos := spec.hdelta_pos
  hdelta_lt_one := spec.hdelta_lt_one
  hstage3_parent := spec.hstage3_parent
  hstage3_early_zero_H0_lt := fun p k hk => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    have hQ_nonpos := Q_reset_admissible_scaled_row_zero_col_zero_nonpos_of_ge fc.clock b
      (H0 d) (ch d) (delta d) (c_zeta d) (h_cz d)
    have h_ceil := spec.hstage3_ceiling_H0_lt p k hk
    linarith
  hstage3_early_pos_pure_drift_H0_lt := fun p k hk => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    have h_drift_nonneg : 0 ≤
        (1 + (c_zeta d - canonicalCZeta_admissible fc.clock b 0 (ch d) 0)) * (4 * (((d + 2 : ℕ) : ℚ) + 1))⁻¹ *
          (∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c) := by
      have h1 : 0 ≤ 1 + (c_zeta d - canonicalCZeta_admissible fc.clock b 0 (ch d) 0) := by
        have h_cz_base : canonicalCZeta_admissible fc.clock b 0 (ch d) 0 ≤ c_zeta d := by
          rw [← canonicalCZeta_admissible_indep_of_H0_delta fc.clock b (H0 d) (ch d) (delta d)]
          exact le_trans (canonicalCZeta_admissible_le_full fc.clock b (H0 d) (ch d) (delta d))
            (le_trans (canonicalCZeta_full_le_gw_admissible fc.clock b (H0 d) (ch d) (delta d)) (h_cz d))
        linarith
      have h2 : 0 ≤ (4 * (((d + 2 : ℕ) : ℚ) + 1))⁻¹ := by positivity
      have h3 : 0 ≤ ∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c := by
        have h_sum := one_le_sum_binomBasis (d + 3) (q + 1) (by omega)
        linarith
      exact mul_nonneg (mul_nonneg h1 h2) h3
    have h_ceil := spec.hstage3_ceiling_H0_lt p k hk
    linarith
  hstage3_late_top_H0_lt := fun p k hk => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    have h_cz_base : canonicalCZeta_admissible fc.clock b 0 (ch d) 0 ≤ c_zeta d := by
      rw [← canonicalCZeta_admissible_indep_of_H0_delta fc.clock b (H0 d) (ch d) (delta d)]
      exact le_trans (canonicalCZeta_admissible_le_full fc.clock b (H0 d) (ch d) (delta d))
        (le_trans (canonicalCZeta_full_le_gw_admissible fc.clock b (H0 d) (ch d) (delta d)) (h_cz d))
    have h_mono := dotProduct_zeta_admissible_scaled_mono_q fc.clock b 0 (ch d) 0 (c_zeta d) h_cz_base q
    have h_ceil := spec.hstage3_ceiling_H0_lt p k hk
    linarith
  hstage4_reset_zero_H0_le := fun p => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    have hQ_nonpos := Q_reset_admissible_scaled_row_zero_col_zero_nonpos_of_ge fc.clock b
      (H0 d) (ch d) (delta d) (c_zeta d) (h_cz d)
    have h_cz_pos : 0 ≤ c_zeta d := by
      have h1 := one_le_canonicalCZeta_admissible fc.clock b (H0 d) (ch d) (delta d)
      have h2 := canonicalCZeta_admissible_le_full fc.clock b (H0 d) (ch d) (delta d)
      have h3 := canonicalCZeta_full_le_gw_admissible fc.clock b (H0 d) (ch d) (delta d)
      linarith [h_cz d]
    have h_ceil := spec.hstage4_ceiling_H0_le p
    linarith
  hstage4_reset_pos_early_pure_drift_H0_le := fun p => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    have h_drift_nonneg : 0 ≤
        (1 + (c_zeta d - canonicalCZeta_admissible fc.clock b 0 (ch d) 0)) * (4 * (((d + 2 : ℕ) : ℚ) + 1))⁻¹ *
          (∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c) := by
      have h1 : 0 ≤ 1 + (c_zeta d - canonicalCZeta_admissible fc.clock b 0 (ch d) 0) := by
        have h_cz_base : canonicalCZeta_admissible fc.clock b 0 (ch d) 0 ≤ c_zeta d := by
          rw [← canonicalCZeta_admissible_indep_of_H0_delta fc.clock b (H0 d) (ch d) (delta d)]
          exact le_trans (canonicalCZeta_admissible_le_full fc.clock b (H0 d) (ch d) (delta d))
            (le_trans (canonicalCZeta_full_le_gw_admissible fc.clock b (H0 d) (ch d) (delta d)) (h_cz d))
        linarith
      have h2 : 0 ≤ (4 * (((d + 2 : ℕ) : ℚ) + 1))⁻¹ := by positivity
      have h3 : 0 ≤ ∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c := by
        have h_sum := one_le_sum_binomBasis (d + 3) (q + 1) (by omega)
        linarith
      exact mul_nonneg (mul_nonneg h1 h2) h3
    have h_cz_pos : 0 ≤ c_zeta d := by
      have h1 := one_le_canonicalCZeta_admissible fc.clock b (H0 d) (ch d) (delta d)
      have h2 := canonicalCZeta_admissible_le_full fc.clock b (H0 d) (ch d) (delta d)
      have h3 := canonicalCZeta_full_le_gw_admissible fc.clock b (H0 d) (ch d) (delta d)
      linarith [h_cz d]
    have h_ceil := spec.hstage4_ceiling_H0_le p
    linarith
  hstage4_reset_pos_late_drift_H0_le := fun p j => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    have h_drift_nonneg : 0 ≤
        (1 + (c_zeta d - canonicalCZeta_admissible fc.clock b 0 (ch d) 0)) * (4 * (((d + 2 : ℕ) : ℚ) + 1))⁻¹ *
          (∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c) := by
      have h1 : 0 ≤ 1 + (c_zeta d - canonicalCZeta_admissible fc.clock b 0 (ch d) 0) := by
        have h_cz_base : canonicalCZeta_admissible fc.clock b 0 (ch d) 0 ≤ c_zeta d := by
          rw [← canonicalCZeta_admissible_indep_of_H0_delta fc.clock b (H0 d) (ch d) (delta d)]
          exact le_trans (canonicalCZeta_admissible_le_full fc.clock b (H0 d) (ch d) (delta d))
            (le_trans (canonicalCZeta_full_le_gw_admissible fc.clock b (H0 d) (ch d) (delta d)) (h_cz d))
        linarith
      have h2 : 0 ≤ (4 * (((d + 2 : ℕ) : ℚ) + 1))⁻¹ := by positivity
      have h3 : 0 ≤ ∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c := by
        have h_sum := one_le_sum_binomBasis (d + 3) (q + 1) (by omega)
        linarith
      exact mul_nonneg (mul_nonneg h1 h2) h3
    have h_Q_le := Q_reset_admissible_scaled_inr_col_zero_le_five_halves_c_zeta_of_ge fc.clock b
      (H0 d) (ch d) (delta d) (c_zeta d) (h_cz d) j
    have h_ceil := spec.hstage4_ceiling_H0_le p
    linarith

/-- **All-Orders Pure-Ceiling Stage 3–4 Admissible Karlin Theorem**:
    Polynomial duality gap scaling across all orders $k \ge 2$ from `PureCeilingStage34AdmissibleSpec`. -/
theorem all_orders_pure_ceiling_stage34_admissible_karlin_theorem
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_gw_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (pc_lifts : ∀ d : ℕ, PureCeilingStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  let ss_lifts : ∀ d : ℕ, SignSeparatedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d :=
    fun d => (pc_lifts d).toSignSeparatedStage34AdmissibleSpec H0 ch delta c_zeta c_P0 h_cz d
  exact all_orders_sign_separated_stage34_admissible_karlin_theorem H0 ch delta c_zeta c_P0
    (fun d => le_trans (canonicalCZeta_full_le_gw_admissible _ _ _ _ _) (h_cz d))
    ss_lifts k hk

/-!
## Section 18: Explicit Linear-Binomial Stage 3–4 Admissible Specification (`ExplicitLinearBinomialStage34AdmissibleSpec`)

In this section, we establish:
1. Lemma `stage3_ceiling_lt_of_linear_binomial_H0_gt`: reduces Stage 3 pure-ceiling waiting to
   $$(d_c - c_h)(q + 1) + c_\zeta \sum_c \text{binomBasis}(q + 1)_c - \text{wordScore} < H_0.$$
2. Lemma `stage4_ceiling_le_of_linear_binomial_H0_ge`: reduces Stage 4 pure-ceiling reset bound to
   $$(d_c - c_h)(q + 1) + c_\zeta \left(\sum_c \text{binomBasis}(q + 1)_c + \frac{5}{2}\right) - \sum_{\sigma \le q} R p_w(\sigma + 1)_b \le H_0.$$
3. The explicit linear-binomial specification `ExplicitLinearBinomialStage34AdmissibleSpec`, its
   automatic conversion `.toPureCeilingStage34AdmissibleSpec`, and the top-level synthesis theorem
   `all_orders_explicit_linear_binomial_stage34_admissible_karlin_theorem`.
-/

/-- Reduction of Stage 3 pure-ceiling waiting to explicit linear-binomial drift against $H_0$. -/
theorem stage3_ceiling_lt_of_linear_binomial_H0_gt {w : ℕ} (hw : 1 ≤ w)
    (clock : AlgebraicClock w) (b : Fin clock.m) (ch c_zeta : ℚ)
    (W_p : List (Fin clock.m)) (q k : ℕ) (hk : k < W_p.length) (H0 : ℚ)
    (h_gt : (dc_admissible clock b 0 ch 0 - ch) * ((q + 1 : ℕ) : ℚ) +
        c_zeta * (∑ c : Fin (w + 1), binomBasis (w + 1) (q + 1) c) -
        wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) < H0) :
    dotProduct (zeta_admissible_scaled clock b 0 ch 0 c_zeta) (binomBasis (w + 1) (q + 1)) <
      wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) +
        (ch * ((q + 1 : ℕ) : ℚ) + H0) := by
  have h_dot := dotProduct_zeta_admissible_scaled_binomBasis_eq hw clock b 0 ch 0 c_zeta (q + 1)
  rw [h_dot]
  linarith

/-- Reduction of Stage 4 pure-ceiling reset bound to explicit linear-binomial drift against $H_0$. -/
theorem stage4_ceiling_le_of_linear_binomial_H0_ge {w : ℕ} (hw : 1 ≤ w)
    (clock : AlgebraicClock w) (b : Fin clock.m) (ch c_zeta : ℚ)
    (q : ℕ) (H0 : ℚ)
    (h_le : (dc_admissible clock b 0 ch 0 - ch) * ((q + 1 : ℕ) : ℚ) +
        c_zeta * ((∑ c : Fin (w + 1), binomBasis (w + 1) (q + 1) c) + (5 / 2 : ℚ)) -
        (∑ σ ∈ Finset.range (q + 1), (clock.R.mulVec (binomBasis w (σ + 1))) b) ≤ H0) :
    dotProduct (zeta_admissible_scaled clock b 0 ch 0 c_zeta) (binomBasis (w + 1) (q + 1)) +
      (5 / 2 : ℚ) * c_zeta ≤
    (∑ σ ∈ Finset.range (q + 1), (clock.R.mulVec (binomBasis w (σ + 1))) b) +
      (ch * ((q + 1 : ℕ) : ℚ) + H0) := by
  have h_dot := dotProduct_zeta_admissible_scaled_binomBasis_eq hw clock b 0 ch 0 c_zeta (q + 1)
  rw [h_dot]
  linarith

/-- **Explicit Linear-Binomial Stage 3–4 Admissible Specification (`ExplicitLinearBinomialStage34AdmissibleSpec`)**:
    Expresses the Stage 3 waiting and Stage 4 reset inequalities in exact affine-linear-binomial form
    in terms of the effective slope `(dc_admissible - ch)` and binomial coefficient sums. -/
structure ExplicitLinearBinomialStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hP_parent_early_nonpos :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (i : Fin fc.clock.m),
      P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ≤ 0
  hP_parent_late_nonneg :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (i : Fin fc.clock.m),
      0 ≤ P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))
  hdelta_pos : 0 < delta d
  hdelta_lt_one : delta d < 1
  hstage3_parent : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let q := p + (d + 2)
    IsValidPriorityWord fc.clock.G
      ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)))
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1))
  hstage3_linear_binomial_H0_gt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length),
      (dc_admissible fc.clock b 0 (ch d) 0 - ch d) * ((q + 1 : ℕ) : ℚ) +
        c_zeta d * (∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c) -
        wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) < H0 d
  hstage4_linear_binomial_H0_ge : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    (dc_admissible fc.clock b 0 (ch d) 0 - ch d) * ((q + 1 : ℕ) : ℚ) +
      c_zeta d * ((∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c) + (5 / 2 : ℚ)) -
      (∑ σ ∈ Finset.range (q + 1), (fc.clock.R.mulVec (binomBasis (d + 2) (σ + 1))) b) ≤ H0 d

/-- Automatic conversion from `ExplicitLinearBinomialStage34AdmissibleSpec` to `PureCeilingStage34AdmissibleSpec`. -/
def ExplicitLinearBinomialStage34AdmissibleSpec.toPureCeilingStage34AdmissibleSpec
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (d : ℕ) (spec : ExplicitLinearBinomialStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d) :
    PureCeilingStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d where
  hP_parent_early_nonpos := spec.hP_parent_early_nonpos
  hP_parent_late_nonneg := spec.hP_parent_late_nonneg
  hdelta_pos := spec.hdelta_pos
  hdelta_lt_one := spec.hdelta_lt_one
  hstage3_parent := spec.hstage3_parent
  hstage3_ceiling_H0_lt := fun p k hk => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    apply stage3_ceiling_lt_of_linear_binomial_H0_gt (by omega) fc.clock b (ch d) (c_zeta d) W_p q k hk (H0 d)
    exact spec.hstage3_linear_binomial_H0_gt p k hk
  hstage4_ceiling_H0_le := fun p => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    apply stage4_ceiling_le_of_linear_binomial_H0_ge (by omega) fc.clock b (ch d) (c_zeta d) q (H0 d)
    exact spec.hstage4_linear_binomial_H0_ge p

/-- **All-Orders Explicit Linear-Binomial Stage 3–4 Admissible Karlin Theorem**:
    Polynomial duality gap scaling across all orders $k \ge 2$ from `ExplicitLinearBinomialStage34AdmissibleSpec`. -/
theorem all_orders_explicit_linear_binomial_stage34_admissible_karlin_theorem
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_gw_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (lin_lifts : ∀ d : ℕ, ExplicitLinearBinomialStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  let pc_lifts : ∀ d : ℕ, PureCeilingStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d :=
    fun d => (lin_lifts d).toPureCeilingStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d
  exact all_orders_pure_ceiling_stage34_admissible_karlin_theorem H0 ch delta c_zeta c_P0 h_cz pc_lifts k hk

/-!
## Section 19: Zero-Baseline Slope Stage 3–4 Admissible Specification (`ZeroBaselineSlopeStage34AdmissibleSpec`)

In this section, we establish:
1. `stage3_linear_binomial_lt_of_zero_baseline_slope_H0_gt`: simplifies the effective slope
   `(dc_admissible - ch)` in the Stage 3 waiting bound to the zero-baseline form
   `dc_admissible clock b 0 0 0 - ch * (1 + topColSum_X_gateway clock / (4 * (w + 1)))`.
2. `stage4_linear_binomial_le_of_zero_baseline_slope_H0_ge`: simplifies the effective slope
   `(dc_admissible - ch)` in the Stage 4 reset bound to the same zero-baseline form.
3. The specification `ZeroBaselineSlopeStage34AdmissibleSpec`, its automatic conversion
   `.toExplicitLinearBinomialStage34AdmissibleSpec`, and the top-level synthesis theorem
   `all_orders_zero_baseline_slope_stage34_admissible_karlin_theorem`.
-/

/-- Reduction of the Stage 3 linear-binomial condition using the zero-baseline slope decomposition. -/
theorem stage3_linear_binomial_lt_of_zero_baseline_slope_H0_gt {w : ℕ} (hw : 1 ≤ w)
    (clock : AlgebraicClock w) (b : Fin clock.m) (ch c_zeta : ℚ)
    (W_p : List (Fin clock.m)) (q k : ℕ) (hk : k < W_p.length) (H0 : ℚ)
    (h_gt : (dc_admissible clock b 0 0 0 - ch * (1 + topColSum_X_gateway clock / (4 * (w + 1 : ℚ)))) * ((q + 1 : ℕ) : ℚ) +
        c_zeta * (∑ c : Fin (w + 1), binomBasis (w + 1) (q + 1) c) -
        wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) < H0) :
    (dc_admissible clock b 0 ch 0 - ch) * ((q + 1 : ℕ) : ℚ) +
      c_zeta * (∑ c : Fin (w + 1), binomBasis (w + 1) (q + 1) c) -
      wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) < H0 := by
  have hslope := dc_admissible_sub_ch_eq hw clock b 0 ch 0
  rw [hslope]
  exact h_gt

/-- Reduction of the Stage 4 linear-binomial condition using the zero-baseline slope decomposition. -/
theorem stage4_linear_binomial_le_of_zero_baseline_slope_H0_ge {w : ℕ} (hw : 1 ≤ w)
    (clock : AlgebraicClock w) (b : Fin clock.m) (ch c_zeta : ℚ)
    (q : ℕ) (H0 : ℚ)
    (h_le : (dc_admissible clock b 0 0 0 - ch * (1 + topColSum_X_gateway clock / (4 * (w + 1 : ℚ)))) * ((q + 1 : ℕ) : ℚ) +
        c_zeta * ((∑ c : Fin (w + 1), binomBasis (w + 1) (q + 1) c) + (5 / 2 : ℚ)) -
        (∑ σ ∈ Finset.range (q + 1), (clock.R.mulVec (binomBasis w (σ + 1))) b) ≤ H0) :
    (dc_admissible clock b 0 ch 0 - ch) * ((q + 1 : ℕ) : ℚ) +
      c_zeta * ((∑ c : Fin (w + 1), binomBasis (w + 1) (q + 1) c) + (5 / 2 : ℚ)) -
      (∑ σ ∈ Finset.range (q + 1), (clock.R.mulVec (binomBasis w (σ + 1))) b) ≤ H0 := by
  have hslope := dc_admissible_sub_ch_eq hw clock b 0 ch 0
  rw [hslope]
  exact h_le

/-- **Zero-Baseline Slope Stage 3–4 Admissible Specification (`ZeroBaselineSlopeStage34AdmissibleSpec`)**:
    Evaluates the effective slope `(dc_admissible - ch)` in terms of the pure baseline coefficient
    `dc_admissible clock b 0 0 0` and the positive feedback factor `1 + topColSum / 4(w+1)`. -/
structure ZeroBaselineSlopeStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hP_parent_early_nonpos :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (i : Fin fc.clock.m),
      P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ≤ 0
  hP_parent_late_nonneg :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (i : Fin fc.clock.m),
      0 ≤ P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))
  hdelta_pos : 0 < delta d
  hdelta_lt_one : delta d < 1
  hstage3_parent : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let q := p + (d + 2)
    IsValidPriorityWord fc.clock.G
      ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)))
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1))
  hstage3_zero_baseline_slope_H0_gt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length),
      (dc_admissible fc.clock b 0 0 0 - ch d * (1 + topColSum_X_gateway fc.clock / (4 * (((d + 2 : ℕ) : ℚ) + 1)))) *
        ((q + 1 : ℕ) : ℚ) +
        c_zeta d * (∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c) -
        wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) < H0 d
  hstage4_zero_baseline_slope_H0_ge : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    (dc_admissible fc.clock b 0 0 0 - ch d * (1 + topColSum_X_gateway fc.clock / (4 * (((d + 2 : ℕ) : ℚ) + 1)))) *
      ((q + 1 : ℕ) : ℚ) +
      c_zeta d * ((∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c) + (5 / 2 : ℚ)) -
      (∑ σ ∈ Finset.range (q + 1), (fc.clock.R.mulVec (binomBasis (d + 2) (σ + 1))) b) ≤ H0 d

/-- Automatic conversion from `ZeroBaselineSlopeStage34AdmissibleSpec` to `ExplicitLinearBinomialStage34AdmissibleSpec`. -/
def ZeroBaselineSlopeStage34AdmissibleSpec.toExplicitLinearBinomialStage34AdmissibleSpec
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (d : ℕ) (spec : ZeroBaselineSlopeStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d) :
    ExplicitLinearBinomialStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d where
  hP_parent_early_nonpos := spec.hP_parent_early_nonpos
  hP_parent_late_nonneg := spec.hP_parent_late_nonneg
  hdelta_pos := spec.hdelta_pos
  hdelta_lt_one := spec.hdelta_lt_one
  hstage3_parent := spec.hstage3_parent
  hstage3_linear_binomial_H0_gt := fun p k hk => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    apply stage3_linear_binomial_lt_of_zero_baseline_slope_H0_gt (by omega) fc.clock b (ch d) (c_zeta d) W_p q k hk (H0 d)
    exact spec.hstage3_zero_baseline_slope_H0_gt p k hk
  hstage4_linear_binomial_H0_ge := fun p => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    apply stage4_linear_binomial_le_of_zero_baseline_slope_H0_ge (by omega) fc.clock b (ch d) (c_zeta d) q (H0 d)
    exact spec.hstage4_zero_baseline_slope_H0_ge p

/-- **All-Orders Zero-Baseline Slope Stage 3–4 Admissible Karlin Theorem**:
    Polynomial duality gap scaling across all orders $k \ge 2$ from `ZeroBaselineSlopeStage34AdmissibleSpec`. -/
theorem all_orders_zero_baseline_slope_stage34_admissible_karlin_theorem
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_gw_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (zb_lifts : ∀ d : ℕ, ZeroBaselineSlopeStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  let lin_lifts : ∀ d : ℕ, ExplicitLinearBinomialStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d :=
    fun d => (zb_lifts d).toExplicitLinearBinomialStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d
  exact all_orders_explicit_linear_binomial_stage34_admissible_karlin_theorem H0 ch delta c_zeta c_P0 h_cz lin_lifts k hk

/-!
## Section 20: Early Coupling Stage 3–4 Admissible Specification (`EarlyCouplingStage34AdmissibleSpec`)

In this section, we establish:
1. `sum_inl_inr`: the column-sum matrix `P(x, inl j) + P(x, inr j)`.
2. `mul_M_coupled_eq_sum_inl_inr_mul_W_coupled`: exact factorization of any matrix product
   `P * M_coupled w` through `sum_inl_inr P * W_coupled w`.
3. `mul_M_coupled_mul_W_coupled_inv_apply`: right-multiplication by `W_coupled_inv w` yields the
   exact entrywise column sum `P(x, inl j) + P(x, inr j)`.
4. `P_admissible_scaled_early_nonpos_of_le_min`: reduction of early parent coupling nonpositivity
   from the upper bound $P(x, \text{inl } j) \le \min(0, (D W^{-1})_{x, j})$.
5. `P_admissible_scaled_late_nonneg_of_le_min`: reduction of late parent coupling nonnegativity
   from the same upper bound via entrywise conservation (`P_admissible_scaled_sum_inl_inr_zero_eq`).
6. The specification `EarlyCouplingStage34AdmissibleSpec`, its automatic conversion
   `.toZeroBaselineSlopeStage34AdmissibleSpec`, and the top-level synthesis theorem
   `all_orders_early_coupling_stage34_admissible_karlin_theorem`.
-/

/-- Sum of early and late reset columns of a coupling matrix `P`. -/
def sum_inl_inr {α : Type*} [Fintype α] {w : ℕ} (P : Matrix α (Fin ((w + 1) + (w + 1))) ℚ) :
    Matrix α (Fin (w + 1)) ℚ :=
  Matrix.of fun x i => P x (finSumFinEquiv (Sum.inl i)) + P x (finSumFinEquiv (Sum.inr i))

/-- Multiplication by `M_coupled w` factors through the column sum `sum_inl_inr P * W_coupled w`. -/
theorem mul_M_coupled_eq_sum_inl_inr_mul_W_coupled {α : Type*} [Fintype α] {w : ℕ}
    (P : Matrix α (Fin ((w + 1) + (w + 1))) ℚ) :
    P * M_coupled w = sum_inl_inr P * W_coupled w := by
  ext x c
  simp only [Matrix.mul_apply, sum_inl_inr, Matrix.of_apply]
  have hcomp :=
    (Equiv.sum_comp finSumFinEquiv fun y : Fin ((w + 1) + (w + 1)) =>
      P x y * M_coupled w y c).symm
  rw [hcomp, Fintype.sum_sum_type]
  have h_inl : (∑ i : Fin (w + 1), P x (finSumFinEquiv (Sum.inl i)) *
      M_coupled w (finSumFinEquiv (Sum.inl i)) c) =
      ∑ i : Fin (w + 1), P x (finSumFinEquiv (Sum.inl i)) * W_coupled w i c := by
    simp only [M_coupled, Matrix.of_apply, Equiv.symm_apply_apply]
  have h_inr : (∑ i : Fin (w + 1), P x (finSumFinEquiv (Sum.inr i)) *
      M_coupled w (finSumFinEquiv (Sum.inr i)) c) =
      ∑ i : Fin (w + 1), P x (finSumFinEquiv (Sum.inr i)) * W_coupled w i c := by
    simp only [M_coupled, Matrix.of_apply, Equiv.symm_apply_apply]
  rw [h_inl, h_inr, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Action of `P * M_coupled w * W_coupled_inv w` at column `j` equals `P(inl j) + P(inr j)`. -/
theorem mul_M_coupled_mul_W_coupled_inv_apply {α : Type*} [Fintype α] {w : ℕ}
    (P : Matrix α (Fin ((w + 1) + (w + 1))) ℚ) (x : α) (j : Fin (w + 1)) :
    (P * M_coupled w * W_coupled_inv w) x j =
      P x (finSumFinEquiv (Sum.inl j)) + P x (finSumFinEquiv (Sum.inr j)) := by
  rw [mul_M_coupled_eq_sum_inl_inr_mul_W_coupled, Matrix.mul_assoc, W_coupled_mul_inv,
    Matrix.mul_one]
  rfl

/-- Reduction of early parent coupling sign to the min-coupling upper bound. -/
theorem P_admissible_scaled_early_nonpos_of_le_min {w : ℕ}
    (clock : AlgebraicClock w) (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ)
    (a_old : Fin (clock.m + 1) → ℚ) (L_C : Matrix (Fin clock.m) (Fin w) ℚ)
    (i : Fin clock.m) (j : Fin (w + 1))
    (h_le : P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ≤
      min 0 ((D_admissible clock b 0 ch 0 * W_coupled_inv w) (finSumFinEquiv (Sum.inl i)) j)) :
    P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ≤ 0 :=
  le_trans h_le (min_le_left 0 _)

/-- Reduction of late parent coupling sign to the min-coupling upper bound. -/
theorem P_admissible_scaled_late_nonneg_of_le_min {w : ℕ} (hw : 2 ≤ w)
    (clock : AlgebraicClock w) (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ)
    (a_old : Fin (clock.m + 1) → ℚ) (L_C : Matrix (Fin clock.m) (Fin w) ℚ)
    (i : Fin clock.m) (j : Fin (w + 1))
    (h_le : P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ≤
      min 0 ((D_admissible clock b 0 ch 0 * W_coupled_inv w) (finSumFinEquiv (Sum.inl i)) j)) :
    0 ≤ P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) := by
  have h_sum := P_admissible_scaled_sum_inl_inr_zero_eq hw clock b H0 ch delta c_zeta c_P0 a_old L_C
    (finSumFinEquiv (Sum.inl i)) j
  have h_bound : P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C
      (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ≤
    (D_admissible clock b 0 ch 0 * W_coupled_inv w) (finSumFinEquiv (Sum.inl i)) j :=
    le_trans h_le (min_le_right 0 _)
  linarith

/-- **Early Coupling Stage 3–4 Admissible Specification (`EarlyCouplingStage34AdmissibleSpec`)**:
    Collapses both parent coupling sign conditions (`hP_parent_early_nonpos` and `hP_parent_late_nonneg`)
    into a single upper bound `P_admissible_scaled ... ≤ min 0 (D_admissible * W_coupled_inv)` on early reset columns. -/
structure EarlyCouplingStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hP_parent_early_le_min :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (i : Fin fc.clock.m),
      P_admissible_scaled fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ≤
      min 0 ((D_admissible fc.clock b 0 (ch d) 0 * W_coupled_inv (d + 2)) (finSumFinEquiv (Sum.inl i)) j)
  hdelta_pos : 0 < delta d
  hdelta_lt_one : delta d < 1
  hstage3_parent : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let q := p + (d + 2)
    IsValidPriorityWord fc.clock.G
      ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)))
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1))
  hstage3_zero_baseline_slope_H0_gt : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length),
      (dc_admissible fc.clock b 0 0 0 - ch d * (1 + topColSum_X_gateway fc.clock / (4 * (((d + 2 : ℕ) : ℚ) + 1)))) *
        ((q + 1 : ℕ) : ℚ) +
        c_zeta d * (∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c) -
        wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) < H0 d
  hstage4_zero_baseline_slope_H0_ge : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    (dc_admissible fc.clock b 0 0 0 - ch d * (1 + topColSum_X_gateway fc.clock / (4 * (((d + 2 : ℕ) : ℚ) + 1)))) *
      ((q + 1 : ℕ) : ℚ) +
      c_zeta d * ((∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c) + (5 / 2 : ℚ)) -
      (∑ σ ∈ Finset.range (q + 1), (fc.clock.R.mulVec (binomBasis (d + 2) (σ + 1))) b) ≤ H0 d

/-- Automatic conversion from `EarlyCouplingStage34AdmissibleSpec` to `ZeroBaselineSlopeStage34AdmissibleSpec`. -/
def EarlyCouplingStage34AdmissibleSpec.toZeroBaselineSlopeStage34AdmissibleSpec
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (d : ℕ) (spec : EarlyCouplingStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d) :
    ZeroBaselineSlopeStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d where
  hP_parent_early_nonpos := fun j i => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    exact P_admissible_scaled_early_nonpos_of_le_min fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d)
      (fun _ => 1) fc.L_C i j (spec.hP_parent_early_le_min j i)
  hP_parent_late_nonneg := fun j i => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    exact P_admissible_scaled_late_nonneg_of_le_min (by omega) fc.clock b (H0 d) (ch d) (delta d) (c_zeta d) (c_P0 d)
      (fun _ => 1) fc.L_C i j (spec.hP_parent_early_le_min j i)
  hdelta_pos := spec.hdelta_pos
  hdelta_lt_one := spec.hdelta_lt_one
  hstage3_parent := spec.hstage3_parent
  hstage3_zero_baseline_slope_H0_gt := spec.hstage3_zero_baseline_slope_H0_gt
  hstage4_zero_baseline_slope_H0_ge := spec.hstage4_zero_baseline_slope_H0_ge

/-- **All-Orders Early Coupling Stage 3–4 Admissible Karlin Theorem**:
    Polynomial duality gap scaling across all orders $k \ge 2$ from `EarlyCouplingStage34AdmissibleSpec`. -/
theorem all_orders_early_coupling_stage34_admissible_karlin_theorem
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_gw_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (ec_lifts : ∀ d : ℕ, EarlyCouplingStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  let zb_lifts : ∀ d : ℕ, ZeroBaselineSlopeStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d :=
    fun d => (ec_lifts d).toZeroBaselineSlopeStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d
  exact all_orders_zero_baseline_slope_stage34_admissible_karlin_theorem H0 ch delta c_zeta c_P0 h_cz zb_lifts k hk

/-!
## Section 21: Stage 3 Score-Gap Dominance & Explicit Deficit Stage 3–4 Admissible Specification (`Stage3GapDomStage34AdmissibleSpec`)

In this section, we establish:
1. `stage3_zero_baseline_slope_lt_of_stage4_and_gap`: because Stage 3 and Stage 4 share the exact same
   effective slope term `(dc_admissible - ch * (1 + ...)) * (q + 1)` and binomial sum `c_zeta * ∑ binomBasis`,
   while Stage 4 includes the positive buffer `+(5 / 2) * c_zeta`, the Stage 3 upper bound (`< H0`)
   follows automatically from the Stage 4 upper bound (`≤ H0`) whenever the parent score gap satisfies
   `(∑ σ, R p_w(σ + 1) b) - wordScore G ... < (5 / 2) * c_zeta`.
   This completely eliminates `H0`, `ch`, `dc_admissible`, and `topColSum_X_gateway` from Stage 3!
2. `P_admissible_scaled_early_le_min_of_explicit_deficit`: evaluates `(D_admissible * W_coupled_inv)` on
   parent rows explicitly as `(R i 0 + ch + G b i + v i) * (1_{0=j} - (w + 1)⁻¹)` and removes `H0` and `delta`
   from `P_admissible_scaled`.
3. The specification `Stage3GapDomStage34AdmissibleSpec`, its automatic conversion
   `.toEarlyCouplingStage34AdmissibleSpec`, and the top-level synthesis theorem
   `all_orders_stage3_gap_dom_stage34_admissible_karlin_theorem`.
-/

/-- Elimination of `H0`, `ch`, `dc_admissible`, and the binomial sum from the Stage 3 waiting condition
    via comparison against the Stage 4 upper bound. -/
theorem stage3_zero_baseline_slope_lt_of_stage4_and_gap {w : ℕ}
    (clock : AlgebraicClock w) (b : Fin clock.m) (ch c_zeta : ℚ)
    (W_p : List (Fin clock.m)) (q k : ℕ) (hk : k < W_p.length) (H0 : ℚ)
    (h4 : (dc_admissible clock b 0 0 0 - ch * (1 + topColSum_X_gateway clock / (4 * (w + 1 : ℚ)))) *
        ((q + 1 : ℕ) : ℚ) +
        c_zeta * ((∑ c : Fin (w + 1), binomBasis (w + 1) (q + 1) c) + (5 / 2 : ℚ)) -
        (∑ σ ∈ Finset.range (q + 1), (clock.R.mulVec (binomBasis w (σ + 1))) b) ≤ H0)
    (hgap : (∑ σ ∈ Finset.range (q + 1), (clock.R.mulVec (binomBasis w (σ + 1))) b) -
        wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) <
      (5 / 2 : ℚ) * c_zeta) :
    (dc_admissible clock b 0 0 0 - ch * (1 + topColSum_X_gateway clock / (4 * (w + 1 : ℚ)))) *
        ((q + 1 : ℕ) : ℚ) +
        c_zeta * (∑ c : Fin (w + 1), binomBasis (w + 1) (q + 1) c) -
        wordScore clock.G ((shiftRightCount clock.R).mulVec (binomBasis (w + 1) (q + 1))) (W_p.take k) (W_p[k]) < H0 := by
  linarith

/-- Reduction of the early coupling min-bound to the explicit parent-row deficit formula at zero baseline `(0, ch, 0)`. -/
theorem P_admissible_scaled_early_le_min_of_explicit_deficit {w : ℕ} (hw : 1 ≤ w)
    (clock : AlgebraicClock w) (b : Fin clock.m) (H0 ch delta c_zeta c_P0 : ℚ)
    (a_old : Fin (clock.m + 1) → ℚ) (L_C : Matrix (Fin clock.m) (Fin w) ℚ)
    (i : Fin clock.m) (j : Fin (w + 1))
    (h_le : P_admissible_scaled clock b 0 ch 0 c_zeta c_P0 a_old L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ≤
      min 0 ((clock.R i ⟨0, hw⟩ + ch + clock.G b i + clock.v i) *
        ((if (0 : Fin (w + 1)) = j then 1 else 0) - (w + 1 : ℚ)⁻¹))) :
    P_admissible_scaled clock b H0 ch delta c_zeta c_P0 a_old L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ≤
      min 0 ((D_admissible clock b 0 ch 0 * W_coupled_inv w) (finSumFinEquiv (Sum.inl i)) j) := by
  rw [P_admissible_scaled_indep_of_H0_delta clock b H0 ch delta c_zeta c_P0 a_old L_C]
  rw [D_admissible_mul_W_coupled_inv_inl_eq hw clock b 0 ch 0 i j]
  exact h_le

/-- **Stage 3 Score-Gap Dominance & Explicit Deficit Stage 3–4 Admissible Specification (`Stage3GapDomStage34AdmissibleSpec`)**:
    Eliminates `H0`, `ch`, `dc_admissible`, and `binomBasis` sums from Stage 3 by comparing Stage 3 against Stage 4,
    and substitutes the explicit parent-row deficit formula `(R i 0 + ch + G b i + v i) * (1_{0=j} - (d+3)⁻¹)`. -/
structure Stage3GapDomStage34AdmissibleSpec (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hP_parent_early_le_explicit_min :
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    ∀ (j : Fin (d + 3)) (i : Fin fc.clock.m),
      P_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ≤
      min 0 ((fc.clock.R i ⟨0, by omega⟩ + ch d + fc.clock.G b i + fc.clock.v i) *
        ((if (0 : Fin (d + 3)) = j then 1 else 0) - (((d + 2 : ℕ) : ℚ) + 1)⁻¹))
  hdelta_pos : 0 < delta d
  hdelta_lt_one : delta d < 1
  hstage3_parent : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let q := p + (d + 2)
    IsValidPriorityWord fc.clock.G
      ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1)))
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      (W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1))
  hstage3_score_gap_lt_cz : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    ∀ (k : ℕ) (hk : k < W_p.length),
      (∑ σ ∈ Finset.range (q + 1), (fc.clock.R.mulVec (binomBasis (d + 2) (σ + 1))) b) -
        wordScore fc.clock.G ((shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))) (W_p.take k) (W_p[k]) <
      (5 / 2 : ℚ) * c_zeta d
  hstage4_zero_baseline_slope_H0_ge : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    (dc_admissible fc.clock b 0 0 0 - ch d * (1 + topColSum_X_gateway fc.clock / (4 * (((d + 2 : ℕ) : ℚ) + 1)))) *
      ((q + 1 : ℕ) : ℚ) +
      c_zeta d * ((∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c) + (5 / 2 : ℚ)) -
      (∑ σ ∈ Finset.range (q + 1), (fc.clock.R.mulVec (binomBasis (d + 2) (σ + 1))) b) ≤ H0 d

/-- Automatic conversion from `Stage3GapDomStage34AdmissibleSpec` to `EarlyCouplingStage34AdmissibleSpec`. -/
def Stage3GapDomStage34AdmissibleSpec.toEarlyCouplingStage34AdmissibleSpec
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (d : ℕ) (spec : Stage3GapDomStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d) :
    EarlyCouplingStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d where
  hP_parent_early_le_min := fun j i => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    exact P_admissible_scaled_early_le_min_of_explicit_deficit (by omega) fc.clock b (H0 d) (ch d) (delta d)
      (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C i j (spec.hP_parent_early_le_explicit_min j i)
  hdelta_pos := spec.hdelta_pos
  hdelta_lt_one := spec.hdelta_lt_one
  hstage3_parent := spec.hstage3_parent
  hstage3_zero_baseline_slope_H0_gt := fun p k hk => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_p := W_bundle_word (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d) (q + 1)
    exact stage3_zero_baseline_slope_lt_of_stage4_and_gap fc.clock b (ch d) (c_zeta d) W_p q k hk (H0 d)
      (spec.hstage4_zero_baseline_slope_H0_ge p) (spec.hstage3_score_gap_lt_cz p k hk)
  hstage4_zero_baseline_slope_H0_ge := spec.hstage4_zero_baseline_slope_H0_ge

/-- **All-Orders Stage 3 Score-Gap Dominance Stage 3–4 Admissible Karlin Theorem**:
    Polynomial duality gap scaling across all orders $k \ge 2$ from `Stage3GapDomStage34AdmissibleSpec`. -/
theorem all_orders_stage3_gap_dom_stage34_admissible_karlin_theorem
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_gw_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (sg_lifts : ∀ d : ℕ, Stage3GapDomStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  let ec_lifts : ∀ d : ℕ, EarlyCouplingStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d :=
    fun d => (sg_lifts d).toEarlyCouplingStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d
  exact all_orders_early_coupling_stage34_admissible_karlin_theorem H0 ch delta c_zeta c_P0 h_cz ec_lifts k hk

/-!
## Section 22: Subphase Stage 3–4 Admissible Specification (`SubphaseStage34AdmissibleSpec`)

In `Stage3GapDomStage34AdmissibleSpec`, both `hstage3_parent` and `hstage3_score_gap_lt_cz`
quantify over the concatenated Stage 3 parent bundle `W_bundle_word (admissiblePhaseWordFamily ... d) (q + 1)`
starting from the degree-shifted score `(shiftRightCount fc.clock.R).mulVec (binomBasis (d + 3) (q + 1))`.

By `isValidPriorityWord_W_bundle_word_of_subphase_valid` (Section 15 of `AdmissibleLift.lean`)
and `stage3_bundle_score_gap_lt_of_subphase` (Section 25 of `AdmissibleLift.lean`), both premises
reduce cleanly to single subphases `idx < q + 1` of the parent word `admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d idx`
starting from the native subphase score `fc.clock.R.mulVec (binomBasis (d + 2) idx)`.
-/

/-- Stage 3–4 admissible specification where both Stage 3 parent priority validity and
    the Stage 3 score-gap bound are reduced from `W_bundle_word` and `shiftRightCount`
    to single-subphase statements on `admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d idx`. -/
structure SubphaseStage34AdmissibleSpec
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ) (d : ℕ) where
  hP_parent_early_le_explicit_min : ∀ (j : Fin (d + 3))
    (i : Fin (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock.m),
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    P_admissible_scaled fc.clock b 0 (ch d) 0 (c_zeta d) (c_P0 d) (fun _ => 1) fc.L_C
      (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ≤
    min 0 ((fc.clock.R i ⟨0, by omega⟩ + ch d + fc.clock.G b i + fc.clock.v i) *
      ((if (0 : Fin (d + 3)) = j then (1 : ℚ) else 0) - (((d + 2 : ℕ) : ℚ) + 1)⁻¹))
  hdelta_pos : 0 < delta d
  hdelta_lt_one : delta d < 1
  hstage3_subphase_parent : ∀ (p idx : ℕ) (_ : idx < (p + (d + 2)) + 1),
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let q := p + (d + 2)
    IsValidPriorityWord fc.clock.G
      (fun i => (fc.clock.R.mulVec (binomBasis (d + 2) idx)) i +
        ∑ σ ∈ Finset.range q, (fc.clock.R.mulVec (binomBasis (d + 2) (σ + 1))) i)
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d idx)
  hstage3_subphase_score_gap_lt_cz : ∀ (p idx : ℕ) (_ : idx < (p + (d + 2)) + 1),
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    let W_sub := admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d idx
    ∀ (k : ℕ) (hk : k < W_sub.length),
      let act := W_sub[k]
      (∑ σ ∈ Finset.range q,
        ((fc.clock.R.mulVec (binomBasis (d + 2) (σ + 1))) b -
         (fc.clock.R.mulVec (binomBasis (d + 2) (σ + 1))) act)) +
      ((fc.clock.R.mulVec (binomBasis (d + 2) (q + 1))) b -
        wordScore fc.clock.G (fc.clock.R.mulVec (binomBasis (d + 2) idx)) (W_sub.take k) act) <
      (5 / 2 : ℚ) * c_zeta d
  hstage4_zero_baseline_slope_H0_ge : ∀ p : ℕ,
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    (dc_admissible fc.clock b 0 0 0 - ch d * (1 + topColSum_X_gateway fc.clock / (4 * (((d + 2 : ℕ) : ℚ) + 1)))) *
      ((q + 1 : ℕ) : ℚ) +
      c_zeta d * ((∑ c : Fin (d + 3), binomBasis (d + 3) (q + 1) c) + (5 / 2 : ℚ)) -
      (∑ σ ∈ Finset.range (q + 1), (fc.clock.R.mulVec (binomBasis (d + 2) (σ + 1))) b) ≤ H0 d

/-- Automatic conversion from `SubphaseStage34AdmissibleSpec` to `Stage3GapDomStage34AdmissibleSpec`. -/
def SubphaseStage34AdmissibleSpec.toStage3GapDomStage34AdmissibleSpec
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (d : ℕ) (spec : SubphaseStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d) :
    Stage3GapDomStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d where
  hP_parent_early_le_explicit_min := spec.hP_parent_early_le_explicit_min
  hdelta_pos := spec.hdelta_pos
  hdelta_lt_one := spec.hdelta_lt_one
  hstage3_parent := fun p => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let q := p + (d + 2)
    exact isValidPriorityWord_W_bundle_word_of_subphase_valid fc.clock
      (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d)
      (admissiblePriorityRankFamily H0 ch delta c_zeta c_P0 d)
      (wordCountVec_admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d)
      q (fun idx hidx => spec.hstage3_subphase_parent p idx hidx)
  hstage3_score_gap_lt_cz := fun p k hk => by
    let fc := admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d
    let b : Fin fc.clock.m := ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
    let q := p + (d + 2)
    exact stage3_bundle_score_gap_lt_of_subphase fc.clock b
      (admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d)
      (wordCountVec_admissiblePhaseWordFamily H0 ch delta c_zeta c_P0 d)
      q ((5 / 2 : ℚ) * c_zeta d)
      (fun idx hidx k' hk' => spec.hstage3_subphase_score_gap_lt_cz p idx hidx k' hk')
      k hk
  hstage4_zero_baseline_slope_H0_ge := spec.hstage4_zero_baseline_slope_H0_ge

/-- **All-Orders Subphase Stage 3–4 Admissible Karlin Theorem**:
    Polynomial duality gap scaling across all orders $k \ge 2$ from `SubphaseStage34AdmissibleSpec`. -/
theorem all_orders_subphase_stage34_admissible_karlin_theorem
    (H0 ch delta c_zeta c_P0 : ℕ → ℚ)
    (h_cz : ∀ d : ℕ, canonicalCZeta_gw_admissible
      (admissibleFullRankClockFamily H0 ch delta c_zeta c_P0 d).clock
      ⟨0, admissibleFullRankClockFamily_pos H0 ch delta c_zeta c_P0 d⟩
      (H0 d) (ch d) (delta d) ≤ c_zeta d)
    (sub_lifts : ∀ d : ℕ, SubphaseStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) := by
  let sg_lifts : ∀ d : ℕ, Stage3GapDomStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d :=
    fun d => (sub_lifts d).toStage3GapDomStage34AdmissibleSpec H0 ch delta c_zeta c_P0 d
  exact all_orders_stage3_gap_dom_stage34_admissible_karlin_theorem H0 ch delta c_zeta c_P0 h_cz sg_lifts k hk

/-- Unconditional all-orders realized clock theorem for Karlin's conjecture across all orders k ≥ 2. -/
theorem all_orders_unconditional_karlin_theorem (k : ℕ) (hk : 2 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) :=
  unconditional_karlin_theorem k hk

/-- Unconditional refutation of Karlin's conjecture for all orders k ≥ 3 with ZERO parameters. -/
theorem karlin_conjecture_false_all_orders_unconditional (k : ℕ) (hk : 3 ≤ k) :
    ∃ (rc : RealizedClock k),
      rc.fc.clock.m = (k + 1) ^ 2 - 6 ∧
      Fintype.card (Option (Fin rc.fc.clock.m)) = (k + 1) ^ 2 - 5 ∧
      IsSkewSymmetric rc.gameMatrix ∧
      rc.fc.clock.C.transpose * rc.fc.L_C = 1 ∧
      rc.trajectory 0 = none ∧
      IsStrictFPTrajectory rc.gameMatrix rc.trajectory ∧
      IsStrictTwoPlayerFPTrajectory rc.gameMatrix rc.trajectory rc.trajectory ∧
      (∀ rowPlay colPlay : ℕ → Option (Fin rc.fc.clock.m),
        IsWeakTwoPlayerFPTrajectory rc.gameMatrix rowPlay colPlay →
        rowPlay 0 = none → colPlay 0 = none →
        ∀ t : ℕ, rowPlay t = rc.trajectory t ∧ colPlay t = rc.trajectory t) ∧
      0 < rc.c_low ∧
      0 < rc.c_high ∧
      (∀ t : ℕ, 1 ≤ t →
        rc.c_low ≤
          standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ∧
        standardDualityGap rc.gameMatrix rc.trajectory rc.trajectory t ^ k * (t : ℚ) ≤
          rc.c_high) :=
  all_orders_unconditional_karlin_theorem k (by omega)

end Karlin

#print axioms Karlin.bundle_c_high_gen_pos
#print axioms Karlin.admissible_c_high_gen_pos
#print axioms Karlin.dotProduct_zeta_bundle_scaled_le
#print axioms Karlin.dotProduct_zeta_admissible_scaled_le
#print axioms Karlin.bundleBiasedScoreShift_nonneg
#print axioms Karlin.admissibleBiasedScoreShift_nonneg
#print axioms Karlin.bundle_hgap_low_unconditional
#print axioms Karlin.score_upper_bound
#print axioms Karlin.bundle_hgap_high_unconditional
#print axioms Karlin.score_upper_bound_admissible
#print axioms Karlin.admissible_hgap_low_unconditional
#print axioms Karlin.admissible_hgap_high_unconditional
#print axioms Karlin.all_orders_admissible_chronology_karlin_theorem
#print axioms Karlin.wordCountVec_admissiblePhaseWordFamily
#print axioms Karlin.all_orders_pure_admissible_karlin_theorem
#print axioms Karlin.wordCountVec_bundlePhaseWordFamily
#print axioms Karlin.all_orders_pure_bundle_karlin_theorem
#print axioms Karlin.one_le_sum_binomBasis
#print axioms Karlin.mulVec_binomBasis_lt_dotProduct_zeta
#print axioms Karlin.admissible_stage1_old_below_ceiling_all_q
#print axioms Karlin.admissible_stage2_old_below_ceiling_all_q
#print axioms Karlin.isValidPriorityStep_congr_rank_val
#print axioms Karlin.isValidPriorityWord_congr_rank_val
#print axioms Karlin.bundle_stage1_old_below_ceiling_all_q
#print axioms Karlin.bundle_stage2_old_below_ceiling_all_q
#print axioms Karlin.canonicalCZeta_admissible_le_full
#print axioms Karlin.stage1_dom_of_ge_canonicalCZeta_full_admissible
#print axioms Karlin.stage2_dom_of_ge_canonicalCZeta_full_admissible
#print axioms Karlin.admissible_stage1_old_below_ceiling_unconditional
#print axioms Karlin.admissible_stage2_old_below_ceiling_unconditional
#print axioms Karlin.canonicalCZeta_bundle_le_full
#print axioms Karlin.stage1_dom_of_ge_canonicalCZeta_full_bundle
#print axioms Karlin.stage2_dom_of_ge_canonicalCZeta_full_bundle
#print axioms Karlin.bundle_stage1_old_below_ceiling_unconditional
#print axioms Karlin.bundle_stage2_old_below_ceiling_unconditional
#print axioms Karlin.J_admissible_scaled_subdiag_pos_of_ge
#print axioms Karlin.J_bundle_subdiag_pos_of_ge
#print axioms Karlin.admissible_stage1_priority_valid_unconditional
#print axioms Karlin.admissible_stage2_priority_valid_unconditional
#print axioms Karlin.admissible_reset_stages_priority_valid_unconditional
#print axioms Karlin.admissible_cone_reset_stages_priority_valid_unconditional
#print axioms Karlin.wordScore_after_reset_stages_bundle_inl
#print axioms Karlin.bundle_stage1_priority_valid_unconditional
#print axioms Karlin.bundle_stage2_priority_valid_unconditional
#print axioms Karlin.bundle_reset_stages_priority_valid_unconditional
#print axioms Karlin.admissibleStageRank_val_eq_paperPriorityRank_val
#print axioms Karlin.isValidPriorityWord_admissibleStageRank_iff_paperPriorityRank
#print axioms Karlin.isValidPriorityWord_admissiblePhaseWordFamily_zero
#print axioms Karlin.isValidPriorityWord_bundlePhaseWordFamily_zero
#print axioms Karlin.ceiling_admissible_ge_choose_of_ge
#print axioms Karlin.ceiling_bundle_ge_choose_of_ge
#print axioms Karlin.admissible_hgap_low_of_ge
#print axioms Karlin.admissible_hgap_high_of_ge
#print axioms Karlin.bundle_hgap_low_of_ge
#print axioms Karlin.bundle_hgap_high_of_ge
#print axioms Karlin.all_orders_stage34_admissible_karlin_theorem
#print axioms Karlin.all_orders_stage34_bundle_karlin_theorem
#print axioms Karlin.canonicalCZeta_full_le_cone_admissible
#print axioms Karlin.canonicalCP0_le_cone_admissible
#print axioms Karlin.admissible_stage3_reset_waits_of_endpoint_bounds
#print axioms Karlin.all_orders_reduced_stage34_admissible_karlin_theorem
#print axioms Karlin.admissible_stage3_reset_waits_of_ceiling_bounds
#print axioms Karlin.admissible_stage4_gw_of_parent_and_ceiling_bounds
#print axioms Karlin.all_orders_simplified_stage34_admissible_karlin_theorem
#print axioms Karlin.liftedScoreMat_admissible_scaled_inr_mulVec_binomBasis_le_zeta
#print axioms Karlin.admissibleScaledLiftClock_leader_zero_dom
#print axioms Karlin.admissibleFullRankClockFamily_leader_zero_dom
#print axioms Karlin.admissibleFullRankClockFamily_stage4_parent_bound_unconditional
#print axioms Karlin.all_orders_minimal_stage34_admissible_karlin_theorem
#print axioms Karlin.admissiblePhaseWordFamily_take_v_dot_nonpos
#print axioms Karlin.admissiblePhaseWordFamily_full_v_dot_eq_one
#print axioms Karlin.admissibleFullRankClockFamily_stage3_v_bound_unconditional
#print axioms Karlin.isValidPriorityWord_stage3_old_of_parent_and_v_bound
#print axioms Karlin.admissibleFullRankClockFamily_stage3_old_of_parent_priority
#print axioms Karlin.all_orders_parent_reduced_stage34_admissible_karlin_theorem
#print axioms Karlin.stage3_early_end_lt_of_H0_gt
#print axioms Karlin.stage3_late_start_lt_of_H0_gt
#print axioms Karlin.stage4_reset_bound_of_H0_gt
#print axioms Karlin.stage3_early_end_lt_of_ceiling_H0_gt
#print axioms Karlin.stage3_late_start_lt_of_ceiling_H0_gt
#print axioms Karlin.stage4_reset_bound_of_ceiling_H0_gt
#print axioms Karlin.all_orders_H0_calibrated_stage34_admissible_karlin_theorem
#print axioms Karlin.stage3_early_end_lt_of_Q_reset_H0_gt
#print axioms Karlin.stage3_late_start_lt_of_Q_reset_H0_gt
#print axioms Karlin.stage4_reset_bound_of_Q_reset_H0_le
#print axioms Karlin.all_orders_Q_reset_calibrated_stage34_admissible_karlin_theorem
#print axioms Karlin.stage3_early_end_lt_of_pos_drift_H0_gt
#print axioms Karlin.stage3_late_start_lt_of_lt_top_drift_H0_gt
#print axioms Karlin.stage4_reset_bound_of_pos_drift_H0_le
#print axioms Karlin.all_orders_boundary_interior_stage34_admissible_karlin_theorem
#print axioms Karlin.P_admissible_scaled_indep_of_H0_delta
#print axioms Karlin.P_admissible_scaled_parent_sign_of_a_old_proj_pos
#print axioms Karlin.P_admissible_scaled_gateway_sign_iff_Q_reset
#print axioms Karlin.P_admissible_scaled_sign_of_parent_and_gateway
#print axioms Karlin.stage3_early_end_lt_of_pure_drift_H0_gt
#print axioms Karlin.stage4_reset_bound_of_pure_drift_H0_le
#print axioms Karlin.all_orders_sign_separated_stage34_admissible_karlin_theorem
#print axioms Karlin.canonicalCZeta_full_le_gw_admissible
#print axioms Karlin.four_mul_abs_Q_reset_general_le_canonicalCZeta_gw_admissible
#print axioms Karlin.Q_reset_admissible_scaled_inl_col_zero_nonpos_of_ge
#print axioms Karlin.Q_reset_admissible_scaled_inr_col_zero_nonneg_of_ge
#print axioms Karlin.Q_reset_admissible_scaled_row_zero_col_zero_nonpos_of_ge
#print axioms Karlin.Q_reset_admissible_scaled_inr_col_zero_le_five_halves_c_zeta_of_ge
#print axioms Karlin.dotProduct_zeta_admissible_scaled_mono_q
#print axioms Karlin.all_orders_pure_ceiling_stage34_admissible_karlin_theorem
#print axioms Karlin.stage3_ceiling_lt_of_linear_binomial_H0_gt
#print axioms Karlin.stage4_ceiling_le_of_linear_binomial_H0_ge
#print axioms Karlin.all_orders_explicit_linear_binomial_stage34_admissible_karlin_theorem
#print axioms Karlin.stage3_linear_binomial_lt_of_zero_baseline_slope_H0_gt
#print axioms Karlin.stage4_linear_binomial_le_of_zero_baseline_slope_H0_ge
#print axioms Karlin.all_orders_zero_baseline_slope_stage34_admissible_karlin_theorem
#print axioms Karlin.mul_M_coupled_eq_sum_inl_inr_mul_W_coupled
#print axioms Karlin.mul_M_coupled_mul_W_coupled_inv_apply
#print axioms Karlin.P_admissible_scaled_early_nonpos_of_le_min
#print axioms Karlin.P_admissible_scaled_late_nonneg_of_le_min
#print axioms Karlin.all_orders_early_coupling_stage34_admissible_karlin_theorem
#print axioms Karlin.stage3_zero_baseline_slope_lt_of_stage4_and_gap
#print axioms Karlin.P_admissible_scaled_early_le_min_of_explicit_deficit
#print axioms Karlin.all_orders_stage3_gap_dom_stage34_admissible_karlin_theorem
#print axioms Karlin.all_orders_subphase_stage34_admissible_karlin_theorem

#print axioms Karlin.all_orders_unconditional_karlin_theorem
#print axioms Karlin.karlin_conjecture_false_all_orders_unconditional
