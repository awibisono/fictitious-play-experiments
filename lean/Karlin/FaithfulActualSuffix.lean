import Karlin.FaithfulActualWaiting
import Karlin.FaithfulGatewaySuffix

/-! The inherited suffix estimate on the actual normalized child game/word.
Only reset chronology and its exact endpoint identities remain external. -/
namespace Karlin.FaithfulActualSuffix
open scoped BigOperators Matrix
open FaithfulClock FaithfulAdmissible FaithfulParameters.AdmissibleParameters
open FaithfulGain.AdmissibleGain FaithfulNextClock.Lift FaithfulActualWaiting
open FaithfulReindex FaithfulInheritance

variable {k : ℕ} {P : Clock k} (A : Admissible P)

noncomputable def pullScore (T1 T2 q : ℕ) : Nested (P := P) → ℚ :=
  fun i => (scoreTable A T1 T2).mulVec (binomBasis (k + 1) q) (middle i)

def pullReset (T1 T2 q : ℕ) : List (Nested (P := P)) :=
  (FaithfulChronology.resetWord (m := P.m + 1) (count A T1 T2 q)).map middle.symm

theorem pull_game (T1 T2 : ℕ) :
    matrix (middle (P := P)).symm middle.symm (game A T1 T2) =
      liftedGameMat (FaithfulGateway.game P) (pullCoupling A T1 T2) (J A T1 T2) := by
  rw [← push_game A T1 T2]
  ext i j
  simp [matrix]

theorem push_score (T1 T2 q : ℕ) :
    vec (middle (P := P)) (pullScore A T1 T2 q) =
      (scoreTable A T1 T2).mulVec (binomBasis (k + 1) q) := by
  ext i
  change (scoreTable A T1 T2).mulVec (binomBasis (k + 1) q) (middle (middle.symm i)) = _
  rw [Equiv.apply_symm_apply]

theorem push_reset (T1 T2 q : ℕ) : (pullReset A T1 T2 q).map middle =
    FaithfulChronology.resetWord (m := P.m + 1) (count A T1 T2 q) := by
  simp [pullReset, List.map_map, Function.comp_def]

theorem push_rotated_word (T1 T2 q : ℕ) :
    ((pullReset A T1 T2 q ++
      (FaithfulGateway.oldWord P (A.tau * (q + 1)) (A.tau * (q + 1))).map Sum.inl).map middle) =
      word A T1 T2 q := by
  rw [List.map_append, push_reset, push_word]
  rfl

theorem pull_score_height_entry (T1 T2 q : ℕ) :
    FaithfulTables.heightValue P A.tau (selectedGain A (lam A) T1) (baseline P) q ≤
      scoreHeight (Sum.inr (0 : Res (k := k))) (pullScore A T1 T2 q) := by
  have hh := le_scoreHeight (Sum.inr (0 : Res (k := k))) (pullScore A T1 T2 q) (Sum.inr 0)
  have hs : pullScore A T1 T2 q (Sum.inr 0) =
      FaithfulTables.heightValue P A.tau (selectedGain A (lam A) T1) (baseline P) q := by
    change dotProduct (scoreTable A T1 T2 (Sum.inr 0)) (binomBasis (k + 1) q) = _
    rw [score_reset_zero]
    rfl
  rwa [hs] at hh

theorem pull_reset_valid (T1 T2 q : ℕ)
    (hreset : IsValidPriorityWord (game A T1 T2)
      ((scoreTable A T1 T2).mulVec (binomBasis (k + 1) q))
      (paperPriorityRank P.m k P.rank)
      (FaithfulChronology.resetWord (m := P.m + 1) (count A T1 T2 q))) :
    IsValidPriorityWord
      (liftedGameMat (FaithfulGateway.game P) (pullCoupling A T1 T2) (J A T1 T2))
      (pullScore A T1 T2 q) (pullRank (P := P)) (pullReset A T1 T2 q) := by
  have hh := priority_valid (middle (P := P)).symm (game A T1 T2)
    ((scoreTable A T1 T2).mulVec (binomBasis (k + 1) q)) (paperPriorityRank P.m k P.rank)
    (FaithfulChronology.resetWord (m := P.m + 1) (count A T1 T2 q)) hreset
  rw [pull_game] at hh
  exact hh

theorem pull_post_reset (T1 T2 q : ℕ)
    (hpost : wordScore (game A T1 T2)
      ((scoreTable A T1 T2).mulVec (binomBasis (k + 1) q))
      (FaithfulChronology.resetWord (m := P.m + 1) (count A T1 T2 q)) =
        (entryTable A T1 T2).mulVec (binomBasis (k + 1) (q + 1))) :
    wordScore (liftedGameMat (FaithfulGateway.game P) (pullCoupling A T1 T2) (J A T1 T2))
      (pullScore A T1 T2 q) (pullReset A T1 T2 q) = pullState A T1 T2 (q + 1) := by
  have hh := wordScore_eq (middle (P := P)).symm (game A T1 T2)
    ((scoreTable A T1 T2).mulVec (binomBasis (k + 1) q))
    (FaithfulChronology.resetWord (m := P.m + 1) (count A T1 T2 q))
  rw [pull_game, hpost] at hh
  exact hh

theorem prefix_height_transport (T1 T2 q r : ℕ) :
    scoreHeight (Sum.inr (0 : Res (k := k)))
      (wordScore (liftedGameMat (FaithfulGateway.game P) (pullCoupling A T1 T2) (J A T1 T2))
        (pullScore A T1 T2 q)
        ((pullReset A T1 T2 q ++
          (FaithfulGateway.oldWord P (A.tau * (q + 1)) (A.tau * (q + 1))).map Sum.inl).take r)) =
    scoreHeight (Sum.inr (0 : Res (k := k)))
      (wordScore (game A T1 T2) ((scoreTable A T1 T2).mulVec (binomBasis (k + 1) q))
        ((word A T1 T2 q).take r)) := by
  have hh := FaithfulReindex.wordScore_eq (middle (P := P))
    (liftedGameMat (FaithfulGateway.game P) (pullCoupling A T1 T2) (J A T1 T2))
    (pullScore A T1 T2 q)
    ((pullReset A T1 T2 q ++
      (FaithfulGateway.oldWord P (A.tau * (q + 1)) (A.tau * (q + 1))).map Sum.inl).take r)
  rw [push_game, push_score, List.map_take, push_rotated_word] at hh
  rw [scoreHeight_equiv (middle (P := P))]
  exact congrArg (scoreHeight (Sum.inr (0 : Res (k := k)))) hh.symm

/-- Condition III for the literal normalized rotated child word. All epsilon
dependence is confined to the inherited threshold, never its additive constant. -/
theorem actual_suffix (T1 T2 q : ℕ) (hv : FaithfulController.ValidParameters A T1 T2)
    (eps : ℚ) (heps : 0 < eps)
    (hq : inheritedThreshold P A.tau (FaithfulController.outerOnset A T1 T2)
      (selectedGain A (lam A) T1) (baseline P) eps ≤ q)
    (hreset : IsValidPriorityWord (game A T1 T2)
      ((scoreTable A T1 T2).mulVec (binomBasis (k + 1) q))
      (paperPriorityRank P.m k P.rank)
      (FaithfulChronology.resetWord (m := P.m + 1) (count A T1 T2 q)))
    (hpost : wordScore (game A T1 T2)
      ((scoreTable A T1 T2).mulVec (binomBasis (k + 1) q))
      (FaithfulChronology.resetWord (m := P.m + 1) (count A T1 T2 q)) =
        (entryTable A T1 T2).mulVec (binomBasis (k + 1) (q + 1)))
    (hfinal : scoreHeight (Sum.inr (0 : Res (k := k)))
      (wordScore (game A T1 T2) ((scoreTable A T1 T2).mulVec (binomBasis (k + 1) q))
        (word A T1 T2 q)) =
      FaithfulTables.heightValue P A.tau (selectedGain A (lam A) T1) (baseline P) (q + 1))
    (r : ℕ) (hr : r ≤ (word A T1 T2 q).length) :
    FaithfulTables.heightValue P A.tau (selectedGain A (lam A) T1) (baseline P) (q + 1) -
      scoreHeight (Sum.inr (0 : Res (k := k)))
        (wordScore (game A T1 T2) ((scoreTable A T1 T2).mulVec (binomBasis (k + 1) q))
          ((word A T1 T2 q).take r)) ≤
      eps * (((word A T1 T2 q).length - r : ℕ) : ℚ) + (P.Arem + 1) := by
  -- The PDF treats this terminal proper prefix separately: the gateway is
  -- currently maximal and its unchanged endpoint score gives exactly c-delta.
  by_cases hterminal : r = (word A T1 T2 q).length - 1
  · subst r
    have honset : FaithfulController.outerOnset A T1 T2 ≤ q :=
      (inheritedThreshold_onset P A.tau (FaithfulController.outerOnset A T1 T2)
        (selectedGain A (lam A) T1) (baseline P) eps).trans hq
    have hgain := FaithfulGatewaySuffix.actual_pre_gateway_gain A T1 T2 q hv honset hreset hpost
    dsimp only [base] at hgain
    have hstrict := hgain.2.2
    rw [hgain.1] at hstrict
    rw [hgain.1]
    have hrem : 0 ≤ eps * (((word A T1 T2 q).length -
        ((word A T1 T2 q).length - 1) : ℕ) : ℚ) := by positivity
    linarith [P.remainder_nonneg]
  let W := pullReset A T1 T2 q ++
    (FaithfulGateway.oldWord P (A.tau * (q + 1)) (A.tau * (q + 1))).map Sum.inl
  have hlen : W.length = (word A T1 T2 q).length := by
    have hh := congrArg List.length (push_rotated_word A T1 T2 q)
    simpa only [List.length_map] using hh
  have hfinalraw : scoreHeight (Sum.inr (0 : Res (k := k)))
      (wordScore (liftedGameMat (FaithfulGateway.game P) (pullCoupling A T1 T2) (J A T1 T2))
        (pullScore A T1 T2 q) W) =
      FaithfulTables.heightValue P A.tau (selectedGain A (lam A) T1) (baseline P) (q + 1) := by
    have hh := prefix_height_transport A T1 T2 q W.length
    change scoreHeight _ (wordScore _ _ (W.take W.length)) = _ at hh
    rw [List.take_length, hlen, List.take_length] at hh
    exact hh.trans hfinal
  have hG : IsSkewSymmetric
      (liftedGameMat (FaithfulGateway.game P) (pullCoupling A T1 T2) (J A T1 T2)) := by
    rw [← pull_game]
    exact FaithfulReindex.skew middle.symm (game_skew A T1 T2)
  have hs : ∀ x, wordScore
      (liftedGameMat (FaithfulGateway.game P) (pullCoupling A T1 T2) (J A T1 T2))
      (pullScore A T1 T2 q) (pullReset A T1 T2 q) (Sum.inl x) =
      FaithfulGateway.initial P (A.tau * (q + 1)) (A.tau * (q + 1))
        (FaithfulTables.parentTranslation P A.tau (selectedGain A (lam A) T1)
          (baseline P) (q + 1)) (FaithfulSynthesis.endpointMargin A (lam A) T1) x := by
    rw [pull_post_reset A T1 T2 q hpost]
    exact pull_old_state A T1 T2 (q + 1)
  have hh := rotated_tables_suffix P (pullCoupling A T1 T2) (J A T1 T2)
    (Sum.inr (0 : Res (k := k))) (pullScore A T1 T2 q) (pullRank (P := P))
    (pullReset A T1 T2 q) A.tau (FaithfulController.outerOnset A T1 T2) q A.tau_pos
    (selectedGain A (lam A) T1) (baseline P) (FaithfulSynthesis.endpointMargin A (lam A) T1)
    eps heps hq hv.gain_lt_one.le hG (pull_reset_valid A T1 T2 q hreset)
    (pull_score_height_entry A T1 T2 q) hs hfinalraw r (by change r ≤ W.length; rwa [hlen])
  rw [prefix_height_transport] at hh
  change _ ≤ eps * ((W.length - r : ℕ) : ℚ) + _ at hh
  rwa [hlen] at hh

end Karlin.FaithfulActualSuffix
