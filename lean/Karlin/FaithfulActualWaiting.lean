import Karlin.FaithfulNextClock
import Karlin.FaithfulController
import Karlin.FaithfulChronologyAlgebra

/-! Actual old-word validity for the fixed v15 controller. All early and late
reset comparisons are discharged from its tables and parameter bounds. -/

namespace Karlin.FaithfulActualWaiting
open scoped BigOperators Matrix
open FaithfulClock FaithfulAdmissible FaithfulParameters.AdmissibleParameters
open FaithfulGain.AdmissibleGain FaithfulNextClock.Lift

variable {k : ℕ} {P : Clock k} (A : Admissible P)

abbrev Nested := FaithfulGateway.Act P ⊕ Res (k := k)

def middle : Nested (P := P) ≃ Act (P := P) :=
  Equiv.sumCongr oldEquiv (Equiv.refl _)

noncomputable def pullCoupling (T1 T2 : ℕ) : Matrix (FaithfulGateway.Act P) (Res (k := k)) ℚ :=
  fun i j => coupling A T1 T2 (oldEquiv i) j

noncomputable def pullState (T1 T2 q : ℕ) : Nested (P := P) → ℚ :=
  fun i => (entryTable A T1 T2).mulVec (binomBasis (k + 1) q) (middle i)

def pullRank : Nested (P := P) → Fin (P.m + 2 * (k + 1) + 1) :=
  fun i => paperPriorityRank P.m k P.rank (middle i)

theorem pull_old_state (T1 T2 q : ℕ) (x : FaithfulGateway.Act P) :
    pullState A T1 T2 q (Sum.inl x) =
      FaithfulGateway.initial P (A.tau * q) (A.tau * q)
        (FaithfulTables.parentTranslation P A.tau (selectedGain A (lam A) T1)
          (baseline P) q) (FaithfulSynthesis.endpointMargin A (lam A) T1) x := by
  change (FaithfulTables.S P A.tau _ _ _).mulVec (binomBasis (k + 1) q)
    (oldEquiv.symm (oldEquiv x)) = _
  rw [Equiv.symm_apply_apply, FaithfulTables.S_eval]
  rfl

theorem pull_old_count (q : ℕ) (hq : P.Q ≤ A.tau * q) :
    wordCountVec (FaithfulGateway.oldWord P (A.tau * q) (A.tau * q)) =
      (FaithfulTables.X P A.tau).mulVec (binomBasis (k + 1) q) := by
  funext i
  have h := congrFun (old_count A q hq) (oldEquiv i)
  simpa only [old, wordCountVec_map_equiv, Equiv.symm_apply_apply,
    oldX, Matrix.mulVec, Matrix.submatrix_apply, id_eq] using h

theorem pull_interpolation (T1 T2 : ℕ) (hv : FaithfulController.ValidParameters A T1 T2) :
    (pullCoupling A T1 T2)ᵀ * FaithfulTables.X P A.tau =
      Q_reset (J A T1 T2) (countRat A T1 T2) (B_mat (k + 1)) (zeta A T1) := by
  rw [← (interpolation A T1 T2 hv).2]
  ext i j
  change (∑ x : FaithfulGateway.Act P,
    coupling A T1 T2 (oldEquiv x) i * FaithfulTables.X P A.tau x j) =
      ∑ x : Fin (P.m + 1), coupling A T1 T2 x i * FaithfulTables.X P A.tau (oldEquiv.symm x) j
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.sum_comp oldEquiv (fun x => coupling A T1 T2 x i *
      FaithfulTables.X P A.tau (oldEquiv.symm x) j))

theorem pull_reset_initial (T1 T2 q : ℕ) (hv : FaithfulController.ValidParameters A T1 T2)
    (hq : P.Q ≤ A.tau * q) :
    ∀ j, pullState A T1 T2 q (Sum.inr j) =
      FaithfulTables.heightValue P A.tau (selectedGain A (lam A) T1) (baseline P) q -
        ((J A T1 T2 * countRat A T1 T2).mulVec (binomBasis (k + 1) q)) j +
        pullCoupling A T1 T2 (Sum.inr 0) j +
        ∑ i : Fin P.m, pullCoupling A T1 T2 (Sum.inl i) j *
          wordCountVec (FaithfulWindow.consecutiveWord P.word (A.tau * q) (A.tau * q)) i := by
  apply FaithfulWaiting.reset_initial_of_count_table P (pullCoupling A T1 T2)
    (FaithfulTables.X P A.tau) (binomBasis (k + 1) q) _ _ _ _ _ (pull_old_count A q hq)
  intro j
  exact FaithfulChronologyAlgebra.V_reset_initial_identity (pullCoupling A T1 T2)
    (FaithfulTables.X P A.tau) (J A T1 T2) (countRat A T1 T2) (B_mat (k + 1))
    (zeta A T1) (binomBasis (k + 1) q) (pull_interpolation A T1 T2 hv) j

theorem parent_endpoint (T1 q : ℕ) (hq : 1 ≤ q) :
    P.entry (A.tau * q + A.tau * q) P.b +
      FaithfulTables.parentTranslation P A.tau (selectedGain A (lam A) T1) (baseline P) q =
      FaithfulTables.heightValue P A.tau (selectedGain A (lam A) T1) (baseline P) q -
        selectedGain A (lam A) T1 := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  exact FaithfulInheritance.parent_endpoint_height P A.tau p _ _

theorem current_counts_nonneg (T1 T2 q : ℕ) (hv : FaithfulController.ValidParameters A T1 T2)
    (hq : FaithfulController.outerOnset A T1 T2 ≤ q) (i : Res (k := k)) :
    0 ≤ (countRat A T1 T2).mulVec (binomBasis (k + 1) q) i := by
  rw [← count_cast_outer A T1 T2 q hv hq i]
  positivity

theorem previous_counts_nonneg (T1 T2 q : ℕ) (hv : FaithfulController.ValidParameters A T1 T2)
    (hq : FaithfulController.outerOnset A T1 T2 ≤ q) (i : Res (k := k)) :
    0 ≤ (countRat A T1 T2).mulVec (binomBasis (k + 1) (q - 1)) i := by
  have hh := (phaseCount_outer A T1 T2 q hv hq i).2
  have hc := FaithfulParameters.phaseCounts_cast (countInt A T1 T2) (q - 1) i
  change (FaithfulParameters.phaseCounts (countInt A T1 T2) (q - 1) i : ℚ) =
    (countRat A T1 T2).mulVec (binomBasis (k + 1) (q - 1)) i at hc
  rw [← hc]
  exact_mod_cast (show 0 ≤ FaithfulParameters.phaseCounts (countInt A T1 T2) (q - 1) i by omega)

theorem reset_product_nonneg (T1 T2 q : ℕ) (hv : FaithfulController.ValidParameters A T1 T2)
    (hq : FaithfulController.outerOnset A T1 T2 ≤ q) (i : Res (k := k)) :
    0 ≤ (J A T1 T2 * countRat A T1 T2).mulVec (binomBasis (k + 1) q) i := by
  rw [← Matrix.mulVec_mulVec]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (J_nonnegative A T1 T2 hv i j)
    (current_counts_nonneg A T1 T2 q hv hq j))

theorem reset_initial_le_parent (T1 T2 q : ℕ) (hv : FaithfulController.ValidParameters A T1 T2)
    (hq : FaithfulController.outerOnset A T1 T2 ≤ q) (j : Res (k := k)) :
    pullState A T1 T2 q (Sum.inr j) ≤ P.entry (A.tau * q) P.b +
      FaithfulTables.parentTranslation P A.tau (selectedGain A (lam A) T1) (baseline P) q := by
  have hq1 : 1 ≤ q := (FaithfulController.outerOnset_pos A T1 T2).trans hq
  have hh := FaithfulChronologyAlgebra.V_reset_eval_le_previous
    (J A T1 T2) (countRat A T1 T2) (zeta A T1) q hq1 (J_nonnegative A T1 T2 hv)
    (previous_counts_nonneg A T1 T2 q hv hq) j
  have hp := FaithfulInheritance.parentTranslation_next P A.tau (q - 1)
    (selectedGain A (lam A) T1) (baseline P)
  rw [Nat.sub_add_cancel hq1] at hp
  change pullState A T1 T2 q (Sum.inr j) ≤
    FaithfulTables.heightValue P A.tau (selectedGain A (lam A) T1) (baseline P) (q - 1) at hh
  linarith

theorem pull_early_sign (T1 T2 : ℕ) (hv : FaithfulController.ValidParameters A T1 T2)
    (j : Res (k := k)) (hj : j.val < k + 1) (i : FaithfulGateway.Act P) :
    pullCoupling A T1 T2 i j < -(FaithfulSynthesis.minimumWeight A / 4) := by
  obtain ⟨x, rfl⟩ := resetEquiv.surjective j
  cases x with
  | inl x => simpa [pullCoupling, coupling] using (hv.coupling_signs i x).1
  | inr x => simp only [resetEquiv, finSumFinEquiv_apply_right, Fin.val_natAdd] at hj; omega

theorem pull_late_sign (T1 T2 : ℕ) (hv : FaithfulController.ValidParameters A T1 T2)
    (j : Res (k := k)) (hj : k + 1 ≤ j.val) (i : FaithfulGateway.Act P) :
    FaithfulSynthesis.minimumWeight A / 4 < pullCoupling A T1 T2 i j := by
  obtain ⟨x, rfl⟩ := resetEquiv.surjective j
  cases x with
  | inl x => simp only [resetEquiv, finSumFinEquiv_apply_left, Fin.val_castAdd] at hj; omega
  | inr x => simpa [pullCoupling, coupling] using (hv.coupling_signs i x).2

theorem pull_early_reserve (T1 T2 : ℕ) (hv : FaithfulController.ValidParameters A T1 T2)
    (j : Res (k := k)) (hj : j.val < k + 1) :
    0 < -pullCoupling A T1 T2 (Sum.inr 0) j - selectedGain A (lam A) T1 - P.Arem := by
  obtain ⟨x, rfl⟩ := resetEquiv.surjective j
  cases x with
  | inl x =>
      have hh := hv.early_reserve x
      have he : pullCoupling A T1 T2 (Sum.inr 0) (resetEquiv (Sum.inl x)) =
          FaithfulSynthesis.coupling A (lam A) T1 T2
            (FaithfulResetEquations.leftInverseLX P A.tau) (Sum.inr 0) (Sum.inl x) := by
        simp [pullCoupling, coupling]
      rw [he]
      linarith
  | inr x => simp only [resetEquiv, finSumFinEquiv_apply_right, Fin.val_natAdd] at hj; omega

theorem pull_parent_priority (i j : Fin P.m) (hij : (P.rank i).val < (P.rank j).val) :
    (pullRank (P := P) (Sum.inl (Sum.inl i))).val <
      (pullRank (P := P) (Sum.inl (Sum.inl j))).val := by
  simpa [pullRank, middle, paperPriorityRank, oldEquiv] using hij

theorem pull_parent_reset_priority (i : Fin P.m) (j : Res (k := k)) :
    (pullRank (P := P) (Sum.inl (Sum.inl i))).val < (pullRank (P := P) (Sum.inr j)).val := by
  simp only [pullRank, middle, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    Equiv.refl_apply, paperPriorityRank, oldEquiv, Equiv.symm_apply_apply]
  have := (P.rank i).isLt
  omega

theorem pull_oldWord_valid (T1 T2 q : ℕ) (hv : FaithfulController.ValidParameters A T1 T2)
    (hq : FaithfulController.outerOnset A T1 T2 ≤ q) :
    IsValidPriorityWord
      (liftedGameMat (FaithfulGateway.game P) (pullCoupling A T1 T2) (J A T1 T2))
      (pullState A T1 T2 q) (pullRank (P := P))
      ((FaithfulGateway.oldWord P (A.tau * q) (A.tau * q)).map Sum.inl) := by
  have heps : 0 < FaithfulSynthesis.minimumWeight A / 4 :=
    div_pos (FaithfulSynthesis.minimumWeight_pos A) (by norm_num)
  have ha := FaithfulController.outerOnset_bundle A T1 T2 q hq
  have hQ : P.Q ≤ A.tau * q :=
    (P.threshold_onset _ heps).trans ((le_max_left _ _).trans ha)
  apply FaithfulWaiting.oldWord_valid_from_data P (pullCoupling A T1 T2) (J A T1 T2)
    (pullState A T1 T2 q) (pullRank (P := P)) (A.tau * q) (A.tau * q) (k + 1)
    (FaithfulTables.parentTranslation P A.tau (selectedGain A (lam A) T1) (baseline P) q)
    (FaithfulSynthesis.endpointMargin A (lam A) T1)
    (FaithfulTables.heightValue P A.tau (selectedGain A (lam A) T1) (baseline P) q)
    (selectedGain A (lam A) T1) (FaithfulSynthesis.minimumWeight A / 4)
    ((J A T1 T2 * countRat A T1 T2).mulVec (binomBasis (k + 1) q))
    heps ha hv.margin_pos hv.margin_lt_parent (pull_old_state A T1 T2 q)
    (parent_endpoint A T1 q ((FaithfulController.outerOnset_pos A T1 T2).trans hq))
    (pull_reset_initial A T1 T2 q hv hQ)
  · intro j _
    exact reset_product_nonneg A T1 T2 q hv hq j
  · exact pull_early_reserve A T1 T2 hv
  · intro j hj i
    have hh := pull_early_sign A T1 T2 hv j hj (Sum.inl i)
    linarith
  · intro j _
    exact reset_initial_le_parent A T1 T2 q hv hq j
  · intro j hj i
    exact le_trans heps.le (pull_late_sign A T1 T2 hv j hj (Sum.inl i)).le
  · exact pull_parent_priority
  · exact pull_parent_reset_priority

theorem push_game (T1 T2 : ℕ) :
    FaithfulReindex.matrix (middle (P := P)) middle
      (liftedGameMat (FaithfulGateway.game P) (pullCoupling A T1 T2) (J A T1 T2)) =
      game A T1 T2 := by
  ext i j
  cases i <;> cases j <;>
    simp [FaithfulReindex.matrix, middle, game, liftedGameMat, G, pullCoupling,
      FaithfulGateway.game, FaithfulTables.oldGame]

theorem push_state (T1 T2 q : ℕ) :
    FaithfulReindex.vec (middle (P := P)) (pullState A T1 T2 q) =
      (entryTable A T1 T2).mulVec (binomBasis (k + 1) q) := by
  funext i
  change (entryTable A T1 T2).mulVec (binomBasis (k + 1) q) (middle (middle.symm i)) = _
  rw [Equiv.apply_symm_apply]

theorem push_rank : FaithfulReindex.vec (middle (P := P)) (pullRank (P := P)) =
    paperPriorityRank P.m k P.rank := by
  funext i
  change paperPriorityRank P.m k P.rank (middle (middle.symm i)) = _
  rw [Equiv.apply_symm_apply]

theorem push_word (q : ℕ) :
    (((FaithfulGateway.oldWord P (A.tau * q) (A.tau * q)).map Sum.inl).map
      (middle (P := P))) = (old A q).map Sum.inl := by
  simp [old, List.map_map, middle, Function.comp_def]

/-- Every old phase is valid in the actual complete game, including all early
and late reset competitors and the single terminal gateway play. -/
theorem actual_oldWord_valid (T1 T2 q : ℕ) (hv : FaithfulController.ValidParameters A T1 T2)
    (hq : FaithfulController.outerOnset A T1 T2 ≤ q) :
    IsValidPriorityWord (game A T1 T2)
      ((entryTable A T1 T2).mulVec (binomBasis (k + 1) q))
      (paperPriorityRank P.m k P.rank) ((old A q).map Sum.inl) := by
  have hh := FaithfulReindex.priority_valid (middle (P := P))
    (liftedGameMat (FaithfulGateway.game P) (pullCoupling A T1 T2) (J A T1 T2))
    (pullState A T1 T2 q) (pullRank (P := P))
    ((FaithfulGateway.oldWord P (A.tau * q) (A.tau * q)).map Sum.inl)
    (pull_oldWord_valid A T1 T2 q hv hq)
  rw [push_game, push_state, push_rank, push_word] at hh
  exact hh

end Karlin.FaithfulActualWaiting
