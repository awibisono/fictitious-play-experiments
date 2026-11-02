import Karlin.FaithfulActualWaiting

/-!
# The terminal pre-gateway suffix, below next-clock assembly

The final scheduled gateway is a maximizer immediately before it is played.
Its own score is unchanged by that play. Combining these two facts with the
actual endpoint row gives remaining gain exactly `c - delta`, strictly below
one. This is the separate terminal-prefix calculation in v15 pp. 56–57.
-/

namespace Karlin.FaithfulGatewaySuffix

open scoped BigOperators Matrix
open FaithfulClock FaithfulAdmissible FaithfulController FaithfulNextClock
open FaithfulNextClock.Lift FaithfulWindow FaithfulInheritance
open FaithfulGain.AdmissibleGain FaithfulParameters.AdmissibleParameters

/-- Raw validity and the gateway endpoint coordinate determine the exact
maximum immediately before the terminal play. No assembled clock is used. -/
theorem terminal_prefix_gain {ι : Type*} [Fintype ι] [DecidableEq ι] {rnk : ℕ}
    (G : Matrix ι ι ℚ) (hG : IsSkewSymmetric G) (s : ι → ℚ)
    (rank : ι → Fin rnk) (b g : ι) (pre : List ι) (H c delta : ℚ)
    (hvalid : IsValidPriorityWord G s rank (pre ++ [g]))
    (hend : wordScore G s (pre ++ [g]) g = H - (c - delta)) :
    H - scoreHeight b (wordScore G s pre) = c - delta := by
  have hlast := ((isValidPriorityWord_append _ _ _ _ _).mp hvalid).2
  have hmax : ∀ i, wordScore G s pre i ≤ wordScore G s pre g := by
    intro i
    have hi := (hlast 0 (by simp) i).1
    simpa only [List.take_zero, wordScore_nil, List.getElem_cons_zero] using hi
  rw [scoreHeight_eq b _ g hmax]
  rw [wordScore_append, wordScore_singleton, skew_diag_zero hG, add_zero] at hend
  linarith

variable {k : ℕ} {P : Clock k} (A : Admissible P)

/-- Endpoint computation from the existing interpolation equations. It is
placed before assembly so suffix inheritance need not import the next clock. -/
theorem actual_old_endpoint (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) :
    wordScore (game A T1 T2)
      ((entryTable A T1 T2).mulVec (binomBasis (k + 1) q)) ((old A q).map Sum.inl) =
      (scoreTable A T1 T2).mulVec (binomBasis (k + 1) q) := by
  have heps : 0 < FaithfulSynthesis.minimumWeight A / 4 :=
    div_pos (FaithfulSynthesis.minimumWeight_pos A) (by norm_num)
  have hparent : P.Q ≤ A.tau * q := (P.threshold_onset _ heps).trans
    ((le_max_left _ _).trans (outerOnset_bundle A T1 T2 q hq))
  exact FaithfulChronologyAlgebra.post_old (G (P := P)) (coupling A T1 T2) (J A T1 T2)
    (oldS A T1) (oldX A) (countRat A T1 T2) (B_mat (k + 1)) (zeta A T1)
    (binomBasis (k + 1) q) (old A q) (old_count A q hparent)
    (interpolation A T1 T2 hv).2

/-- The exact pre-gateway gain on the actual rotated word. Reset validity and
its endpoint are precisely the already available raw chronology premises. -/
theorem actual_pre_gateway_gain (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q)
    (hreset : IsValidPriorityWord (game A T1 T2)
      ((scoreTable A T1 T2).mulVec (binomBasis (k + 1) q))
      (paperPriorityRank P.m k P.rank)
      (FaithfulChronology.resetWord (m := P.m + 1) (count A T1 T2 q)))
    (hpost : wordScore (game A T1 T2)
      ((scoreTable A T1 T2).mulVec (binomBasis (k + 1) q))
      (FaithfulChronology.resetWord (m := P.m + 1) (count A T1 T2 q)) =
        (entryTable A T1 T2).mulVec (binomBasis (k + 1) (q + 1))) :
    let d := FaithfulTables.heightValue P A.tau (selectedGain A (lam A) T1)
      (baseline P) (q + 1) - scoreHeight (base (P := P))
        (wordScore (game A T1 T2) ((scoreTable A T1 T2).mulVec (binomBasis (k + 1) q))
          ((word A T1 T2 q).take ((word A T1 T2 q).length - 1)))
    d = selectedGain A (lam A) T1 - FaithfulSynthesis.endpointMargin A (lam A) T1 ∧
      0 < d ∧ d < 1 := by
  dsimp only
  have hvalid : IsValidPriorityWord (game A T1 T2)
      ((scoreTable A T1 T2).mulVec (binomBasis (k + 1) q))
      (paperPriorityRank P.m k P.rank) (word A T1 T2 q) := by
    change IsValidPriorityWord _ _ _
      (FaithfulChronology.resetWord (count A T1 T2 q) ++ (old A (q + 1)).map Sum.inl)
    apply (isValidPriorityWord_append _ _ _ _ _).2
    refine ⟨hreset, ?_⟩
    rw [hpost]
    exact FaithfulActualWaiting.actual_oldWord_valid A T1 T2 (q + 1) hv (by omega)
  have hend : wordScore (game A T1 T2)
      ((scoreTable A T1 T2).mulVec (binomBasis (k + 1) q)) (word A T1 T2 q) =
      (scoreTable A T1 T2).mulVec (binomBasis (k + 1) (q + 1)) := by
    change wordScore _ _
      (FaithfulChronology.resetWord (count A T1 T2 q) ++ (old A (q + 1)).map Sum.inl) = _
    rw [wordScore_append, hpost, actual_old_endpoint A T1 T2 (q + 1) hv (by omega)]
  have hgateway : wordScore (game A T1 T2)
      ((scoreTable A T1 T2).mulVec (binomBasis (k + 1) q)) (word A T1 T2 q)
        (gateway (P := P)) =
      FaithfulTables.heightValue P A.tau (selectedGain A (lam A) T1) (baseline P) (q + 1) -
        (selectedGain A (lam A) T1 - FaithfulSynthesis.endpointMargin A (lam A) T1) := by
    rw [hend]
    change dotProduct (scoreTable A T1 T2 (gateway (P := P))) _ = _
    rw [score_gateway_row, sub_dotProduct, smul_dotProduct]
    simp [FaithfulTables.heightValue, zeta, dotProduct, e0_row, binomBasis]
  obtain ⟨pre, hp⟩ := word_terminal A T1 T2 q
  have htake : (word A T1 T2 q).take ((word A T1 T2 q).length - 1) = pre := by
    rw [hp]
    simp
  rw [hp] at hvalid hgateway
  rw [htake]
  have heq := terminal_prefix_gain (game A T1 T2) (game_skew A T1 T2)
    ((scoreTable A T1 T2).mulVec (binomBasis (k + 1) q))
    (paperPriorityRank P.m k P.rank) base gateway pre _ _ _ hvalid hgateway
  exact ⟨heq, by linarith [hv.margin_lt_gain], by linarith [hv.gain_lt_one, hv.margin_pos]⟩

end Karlin.FaithfulGatewaySuffix
