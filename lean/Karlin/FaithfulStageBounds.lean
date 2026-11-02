import Karlin.FaithfulController
import Karlin.FaithfulGateway
import Karlin.FaithfulChronologyAlgebra

/-! Literal old/reset stage bounds derived from the parent clock and the actual
scale/onset conditions. No trajectory of the successor is assumed. -/
namespace Karlin.FaithfulStageBounds
open scoped BigOperators Matrix
open FaithfulClock FaithfulTables FaithfulAdmissible FaithfulController
open FaithfulGain.AdmissibleGain FaithfulParameters.AdmissibleParameters
open FaithfulResetEquations FaithfulChronologyAlgebra
set_option maxHeartbeats 1200000

variable {k : ℕ} (P : Clock k)

theorem old_word_count (tau q : ℕ) (hq : P.Q ≤ tau * q) :
    wordCountVec (FaithfulGateway.oldWord P (tau * q) (tau * q)) =
      (X P tau).mulVec (binomBasis (k + 1) q) := by
  funext i
  cases i with
  | inl i =>
      rw [FaithfulGateway.oldWord_parent_count]
      simpa [X, Matrix.mulVec, dotProduct, FaithfulWindow.dyadicWord]
        using congrFun (P.dyadic_compatible tau q hq).2.2 i
  | inr i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rw [FaithfulGateway.oldWord_gateway_count, X_eval_gateway]

theorem old_table_score (tau q : ℕ) (c H delta : ℚ) (hq : P.Q ≤ tau * q) :
    wordScore (FaithfulGateway.game P)
      (FaithfulGateway.initial P (tau * q) (tau * q) (parentTranslation P tau c H q) delta)
      (FaithfulGateway.oldWord P (tau * q) (tau * q)) =
      (S P tau c H delta + oldGame P * X P tau).mulVec (binomBasis (k + 1) q) := by
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← old_word_count P tau q hq, S_eval]
  rfl

/-- Parent entry leadership and delta<1 bound every old action at the next
outer entrance by the current outer height. -/
theorem old_endpoint_le (tau q : ℕ) (c H delta : ℚ) (htau : 1 ≤ tau)
    (hq : P.Q ≤ tau * (q + 1)) (hdelta : delta ≤ 1) (i : OldAct P) :
    (S P tau c H delta).mulVec (binomBasis (k + 1) (q + 1)) i ≤
      heightValue P tau c H q := by
  rw [S_eval, parentTranslation_step]
  cases i with
  | inl i =>
      have hp : P.entry (tau * (q + 1)) i ≤ P.entry (tau * (q + 1)) P.b := by
        have hh := le_height P.b (P.entry (tau * (q + 1))) i
        rw [P.entry_height _ hq] at hh
        exact hh
      simp only [Sum.elim_inl]
      linarith
  | inr i =>
      have ht : (1 : ℚ) ≤ (tau * (q + 1) : ℕ) := by
        exact_mod_cast (show 1 ≤ tau * (q + 1) by nlinarith)
      simp only [Sum.elim_inr]
      linarith

theorem parent_endpoint_height (tau q : ℕ) (c H : ℚ) (hq : 1 ≤ q) :
    P.entry (tau * q + tau * q) P.b + parentTranslation P tau c H q =
      heightValue P tau c H q - c := by
  have ht := parentTranslation_step P tau (q - 1) c H
  have hh := heightValue_step P tau (q - 1) c H
  rw [Nat.sub_add_cancel hq] at ht hh
  have he : tau * q + tau * q = 2 * tau * q := by ring
  rw [he, ht]
  linarith

/-- The exact post-gateway parent and gateway scores are strictly below the
reset ceiling because c>0 and delta<c. -/
theorem old_post_lt_height (tau q : ℕ) (c H delta : ℚ)
    (hq : 1 ≤ q) (hparent : P.Q ≤ tau * q) (hc : 0 < c) (hdelta : delta < c)
    (i : OldAct P) :
    (S P tau c H delta + oldGame P * X P tau).mulVec (binomBasis (k + 1) q) i <
      heightValue P tau c H q := by
  rw [← old_table_score P tau q c H delta hparent]
  have hh := parent_endpoint_height P tau q c H hq
  cases i with
  | inl i =>
      have hp := (FaithfulGateway.after_gateway_parent_max P (tau * q) hparent
        (tau * q) (parentTranslation P tau c H q) delta).1 i
      linarith
  | inr i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rw [FaithfulGateway.after_gateway_score P (tau * q) hparent]
      linarith

variable {P} (A : Admissible P)

theorem actual_parent_onset (T1 T2 q : ℕ) (hq : outerOnset A T1 T2 ≤ q) :
    P.Q ≤ A.tau * q := by
  have heps : 0 < FaithfulSynthesis.minimumWeight A / 4 :=
    div_pos (FaithfulSynthesis.minimumWeight_pos A) (by norm_num)
  exact (P.threshold_onset _ heps).trans ((le_max_left _ _).trans
    (outerOnset_bundle A T1 T2 q hq))

theorem actual_old_endpoint_le (T1 T2 : ℕ) (hv : ValidParameters A T1 T2)
    (q : ℕ) (hq : outerOnset A T1 T2 ≤ q) (i : OldAct P) :
    (S P A.tau (selectedGain A (lam A) T1) (baseline P)
      (FaithfulSynthesis.endpointMargin A (lam A) T1)).mulVec (binomBasis (k + 1) (q + 1)) i ≤
      heightValue P A.tau (selectedGain A (lam A) T1) (baseline P) q := by
  apply old_endpoint_le P _ _ _ _ _ A.tau_pos
  · have h := actual_parent_onset A T1 T2 q hq
    exact h.trans (Nat.mul_le_mul_left _ (by omega))
  · exact le_of_lt (hv.margin_lt_gain.trans hv.gain_lt_one)

theorem actual_old_post_lt_height (T1 T2 : ℕ) (hv : ValidParameters A T1 T2)
    (q : ℕ) (hq : outerOnset A T1 T2 ≤ q) (i : OldAct P) :
    (S P A.tau (selectedGain A (lam A) T1) (baseline P)
      (FaithfulSynthesis.endpointMargin A (lam A) T1) + oldGame P * X P A.tau).mulVec
      (binomBasis (k + 1) q) i <
      heightValue P A.tau (selectedGain A (lam A) T1) (baseline P) q :=
  old_post_lt_height P _ _ _ _ _ ((outerOnset_pos A T1 T2).trans hq)
    (actual_parent_onset A T1 T2 q hq) hv.gain_pos hv.margin_lt_gain i

#print axioms old_endpoint_le
#print axioms old_post_lt_height
#print axioms actual_old_endpoint_le
#print axioms actual_old_post_lt_height
end Karlin.FaithfulStageBounds
