import Karlin.FaithfulResetPlateau

/-! Exact score formulas used in the PDF chronology and inheritance proofs.
These strengthen the exported deficit inequalities without changing the word.+-/
namespace Karlin.FaithfulPaperChronology
open scoped BigOperators Matrix
open FaithfulClock FaithfulAdmissible FaithfulController FaithfulNextClock
open FaithfulNextClock.Lift FaithfulNextClockAssembly FaithfulWindow
open FaithfulGain.AdmissibleGain FaithfulParameters.AdmissibleParameters

/-- The algebraic run prefix is literally a prefix of the prescribed reset
word whenever the active run has not been exceeded. -/
theorem reset_run_is_prefix {m n : ℕ} (count : Fin n → ℕ) (j : Fin n)
    (h : ℕ) (hh : h ≤ count j) :
    ∃ tail : List (Fin m ⊕ Fin n), FaithfulChronology.resetWord count =
      (FaithfulChronology.resetPrefix count j.val ++ List.replicate h (Sum.inr j)) ++ tail := by
  let rest := ((List.finRange n).drop (j.val + 1)).flatMap
    (fun a => List.replicate (count a) (Sum.inr a : Fin m ⊕ Fin n))
  refine ⟨List.replicate (count j - h) (Sum.inr j) ++ rest, ?_⟩
  have hj : j.val < (List.finRange n).length := by simp
  have hsplit : List.finRange n = (List.finRange n).take j.val ++
      [j] ++ (List.finRange n).drop (j.val + 1) := by
    conv_lhs => rw [← List.take_append_drop (j.val + 1) (List.finRange n)]
    rw [List.take_succ_eq_append_getElem hj]
    simp
  unfold FaithfulChronology.resetWord FaithfulChronology.resetPrefix
  conv_lhs => rw [hsplit]
  simp only [List.flatMap_append, List.flatMap_singleton]
  simp only [List.append_assoc, rest]
  rw [← List.append_assoc (List.replicate h (Sum.inr j)),
    List.replicate_append_replicate, Nat.add_sub_of_le hh]

/-- The exact future-reset deficit, including all intervening runs. -/
theorem future_reset_deficit {n : ℕ} (J : Matrix (Fin n) (Fin n) ℚ)
    (m : Fin n → ℚ) (z h : ℚ) (j i : Fin n) (hij : j.val < i.val)
    (hlower : ∀ a b : Fin n, a.val ≤ b.val → J a b = 0) :
    z - scoreVec (J - J.transpose) (resetEntryScore J m z)
      (resetPrefixCount j m h) i =
      J i j * (m j - h) +
        ∑ ell : Fin n, if j.val < ell.val ∧ ell.val < i.val then J i ell * m ell else 0 := by
  have hs : z - scoreVec (J - J.transpose) (resetEntryScore J m z)
      (resetPrefixCount j m h) i =
      ∑ ell : Fin n, (J i ell * m ell -
        (J i ell - J ell i) * resetPrefixCount j m h ell) := by
    simp only [scoreVec, resetEntryScore, Matrix.sub_apply, Matrix.transpose_apply,
      Finset.sum_sub_distrib]
    ring
  rw [hs]
  have hterm (ell : Fin n) :
      J i ell * m ell - (J i ell - J ell i) * resetPrefixCount j m h ell =
      (if ell = j then J i j * (m j - h) else 0) +
      (if j.val < ell.val ∧ ell.val < i.val then J i ell * m ell else 0) := by
    by_cases he : ell = j
    · subst ell
      simp [resetPrefixCount, hlower j i hij.le]
      ring
    by_cases hj : ell.val < j.val
    · simp [resetPrefixCount, hj, he, hlower ell i (by omega), show ¬ j.val < ell.val by omega]
    · have hj' : j.val < ell.val := by
        have hn : ell.val ≠ j.val := fun h => he (Fin.ext h)
        omega
      by_cases hi : ell.val < i.val
      · simp [resetPrefixCount, hj, he, hj', hi]
      · simp [resetPrefixCount, hj, he, hj', hi, hlower i ell (by omega)]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp

/-- The exact deficit of a previously played reset, with the intervening
completed runs retained rather than discarded as nonnegative. -/
theorem earlier_reset_deficit {n : ℕ} (J : Matrix (Fin n) (Fin n) ℚ)
    (m : Fin n → ℚ) (z h : ℚ) (j i : Fin n) (hij : i.val < j.val)
    (hlower : ∀ a b : Fin n, a.val ≤ b.val → J a b = 0) :
    z - scoreVec (J - J.transpose) (resetEntryScore J m z)
      (resetPrefixCount j m h) i =
      J j i * h +
        ∑ ell : Fin n, if i.val < ell.val ∧ ell.val < j.val then J ell i * m ell else 0 := by
  have hs : z - scoreVec (J - J.transpose) (resetEntryScore J m z)
      (resetPrefixCount j m h) i =
      ∑ ell : Fin n, (J i ell * m ell -
        (J i ell - J ell i) * resetPrefixCount j m h ell) := by
    simp only [scoreVec, resetEntryScore, Matrix.sub_apply, Matrix.transpose_apply,
      Finset.sum_sub_distrib]
    ring
  rw [hs]
  have hterm (ell : Fin n) :
      J i ell * m ell - (J i ell - J ell i) * resetPrefixCount j m h ell =
      (if ell = j then J j i * h else 0) +
      (if i.val < ell.val ∧ ell.val < j.val then J ell i * m ell else 0) := by
    by_cases he : ell = j
    · subst ell
      simp [resetPrefixCount, hlower i j hij.le]
    by_cases hj : ell.val < j.val
    · by_cases hi : i.val < ell.val
      · simp [resetPrefixCount, hj, he, hi, hlower i ell hi.le]
      · simp [resetPrefixCount, hj, he, hi, hlower ell i (by omega)]
    · simp [resetPrefixCount, hj, he, hlower i ell (by omega)]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp

/-- Counts and scores at a literal reset-run prefix, with `h` actual plays of
the active action. This connects the algebraic deficit formulas to the word. -/
theorem reset_run_score {m n : ℕ}
    (G : Matrix (Fin m) (Fin m) ℚ) (C : Matrix (Fin m) (Fin n) ℚ)
    (J : Matrix (Fin n) (Fin n) ℚ) (s : Fin m ⊕ Fin n → ℚ)
    (count : Fin n → ℕ) (z : ℚ)
    (hs : ∀ i, s (Sum.inr i) = resetEntryScore J (fun j => (count j : ℚ)) z i)
    (j i : Fin n) (h : ℕ) :
    wordScore (liftedGameMat G C J) s
      (FaithfulChronology.resetPrefix count j.val ++ List.replicate h (Sum.inr j))
      (Sum.inr i) =
    scoreVec (J - J.transpose) (resetEntryScore J (fun a => (count a : ℚ)) z)
      (resetPrefixCount j (fun a => (count a : ℚ)) (h : ℚ)) i := by
  rw [FaithfulChronology.reset_score_affine, wordScore_append, wordScore_replicate,
    FaithfulChronology.resetPrefix_score_reset G C J s count z hs j i]
  simp only [liftedGameMat, Matrix.fromBlocks_apply₂₂, Matrix.sub_apply,
    Matrix.transpose_apply]
  ring

variable {k : ℕ} {P : Clock k} (A : Admissible P)

/-- The literal word-prefix version of the PDF's future-reset formula, on
the synthesized matrices and actual integer run counts. -/
theorem actual_future_reset_deficit (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) (j i : Res (k := k)) (hij : j.val < i.val)
    (h : ℕ) :
    dotProduct (zeta A T1) (binomBasis (k + 1) q) -
      wordScore (game A T1 T2) (rotatedScore A T1 T2 q)
        (FaithfulChronology.resetPrefix (count A T1 T2 q) j.val ++
          List.replicate h (Sum.inr j)) (Sum.inr i) =
      J A T1 T2 i j * ((count A T1 T2 q j : ℚ) - h) +
        ∑ ell : Res (k := k), if j.val < ell.val ∧ ell.val < i.val then
          J A T1 T2 i ell * (count A T1 T2 q ell : ℚ) else 0 := by
  rw [show game A T1 T2 = liftedGameMat (G (P := P)) (coupling A T1 T2) (J A T1 T2)
    by rfl, reset_run_score _ _ _ _ _ _ (reset_start_scores A T1 T2 q hv hq)]
  exact future_reset_deficit _ _ _ _ j i hij (Lift.J_lower A T1 T2)

/-- The literal word-prefix version of the earlier-reset formula. -/
theorem actual_earlier_reset_deficit (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) (j i : Res (k := k)) (hij : i.val < j.val)
    (h : ℕ) :
    dotProduct (zeta A T1) (binomBasis (k + 1) q) -
      wordScore (game A T1 T2) (rotatedScore A T1 T2 q)
        (FaithfulChronology.resetPrefix (count A T1 T2 q) j.val ++
          List.replicate h (Sum.inr j)) (Sum.inr i) =
      J A T1 T2 j i * h +
        ∑ ell : Res (k := k), if i.val < ell.val ∧ ell.val < j.val then
          J A T1 T2 ell i * (count A T1 T2 q ell : ℚ) else 0 := by
  rw [show game A T1 T2 = liftedGameMat (G (P := P)) (coupling A T1 T2) (J A T1 T2)
    by rfl, reset_run_score _ _ _ _ _ _ (reset_start_scores A T1 T2 q hv hq)]
  exact earlier_reset_deficit _ _ _ _ j i hij (Lift.J_lower A T1 T2)

/-- The endpoint action occurs exactly once in the constructed rotated word. -/
theorem word_gateway_count (T1 T2 q : ℕ) :
    wordCountVec (word A T1 T2 q) (gateway (P := P)) = 1 := by
  simp only [word, rotatedWord, wordCountVec_append,
    FaithfulChronology.resetWord_count, gateway, Sum.elim_inl,
    wordCountVec_map_inl_inl, zero_add, old]
  rw [wordCountVec_map_equiv]
  simp only [Equiv.symm_apply_apply]
  exact FaithfulGateway.oldWord_gateway_count P _ _

/-- At every proper prefix, precisely the one terminal gateway play remains. -/
theorem remaining_marker_eq_one (T1 T2 q r : ℕ)
    (hr : r < (word A T1 T2 q).length) :
    dotProduct counter (wordCountVec ((word A T1 T2 q).drop r)) = 1 := by
  rw [counter, gatewayCounter_dot]
  obtain ⟨pre, hp⟩ := word_terminal A T1 T2 q
  have hlo := terminal_gateway_remaining pre (gateway (P := P)) r (by rwa [← hp])
  rw [← hp] at hlo
  have hs := wordCountVec_take_add_drop (word A T1 T2 q) r (gateway (P := P))
  rw [word_gateway_count] at hs
  have hn : 0 ≤ wordCountVec ((word A T1 T2 q).take r) (gateway (P := P)) :=
    Nat.cast_nonneg _
  linarith

/-- Immediately before the one terminal gateway play, the exact remaining
height gain is `c - delta`, hence strictly less than one. This is the separate
last-prefix case in the PDF's inheritance proof. -/
theorem pre_gateway_gain (T1 T2 q : ℕ) (hv : ValidParameters A T1 T2)
    (hq : outerOnset A T1 T2 ≤ q) :
    let H := FaithfulInheritance.scoreHeight base
      (wordScore (game A T1 T2) (rotatedScore A T1 T2 q)
        ((word A T1 T2 q).take ((word A T1 T2 q).length - 1)))
    (dotProduct (zeta A T1) (binomBasis (k + 1) (q + 1)) - H =
      selectedGain A (lam A) T1 - FaithfulSynthesis.endpointMargin A (lam A) T1) ∧
    (0 < dotProduct (zeta A T1) (binomBasis (k + 1) (q + 1)) - H) ∧
    (dotProduct (zeta A T1) (binomBasis (k + 1) (q + 1)) - H < 1) := by
  dsimp only
  obtain ⟨pre, hp⟩ := word_terminal A T1 T2 q
  have htake : (word A T1 T2 q).take ((word A T1 T2 q).length - 1) = pre := by
    rw [hp]
    simp
  rw [htake]
  have hvalid := word_valid A T1 T2 q hv hq
  rw [hp] at hvalid
  have hlast := ((isValidPriorityWord_append _ _ _ _ _).mp hvalid).2
  have hmax : ∀ i, wordScore (game A T1 T2) (rotatedScore A T1 T2 q) pre i ≤
      wordScore (game A T1 T2) (rotatedScore A T1 T2 q) pre (gateway (P := P)) := by
    intro i
    have hi := (hlast 0 (by simp) i).1
    simpa only [List.take_zero, wordScore_nil, List.getElem_cons_zero] using hi
  rw [FaithfulInheritance.scoreHeight_eq base _ (gateway (P := P)) hmax]
  have he := congrFun (rotated_end A T1 T2 q hv hq) (gateway (P := P))
  rw [hp, wordScore_append, wordScore_singleton, skew_diag_zero (game_skew A T1 T2),
    add_zero] at he
  rw [he]
  have hg : rotatedScore A T1 T2 (q + 1) (gateway (P := P)) =
      dotProduct (zeta A T1) (binomBasis (k + 1) (q + 1)) -
        (selectedGain A (lam A) T1 - FaithfulSynthesis.endpointMargin A (lam A) T1) := by
    change dotProduct (scoreTable A T1 T2 (gateway (P := P))) _ = _
    rw [score_gateway_row, sub_dotProduct, smul_dotProduct]
    simp [dotProduct, e0_row, binomBasis]
  rw [hg]
  refine ⟨by ring, ?_, ?_⟩
  · linarith [hv.margin_lt_gain]
  · linarith [hv.gain_lt_one, hv.margin_pos]

end Karlin.FaithfulPaperChronology
