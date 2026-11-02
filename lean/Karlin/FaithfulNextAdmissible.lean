import Karlin.FaithfulNextTables
import Karlin.FaithfulScaleClock
import Karlin.FaithfulAdmissible
import Karlin.FaithfulReindex

/-!
# Admissibility of the literal next tables

This interface consumes an actual order-(k+1) Clock with exact reindexed score
and count tables and the first-reset entry action. It does not assume summary
invariance, a next correction solving tests, or positive next weights: all
three are discharged from the literal v15 construction. Constructing the Clock
and proving these table equalities is the separate chronology/inheritance step.
-/

namespace Karlin.FaithfulNextAdmissible
open scoped BigOperators Matrix
open FaithfulClock FaithfulTables FaithfulNextTables FaithfulAdmissible

variable {k : ℕ} (P : Clock k)

/-- Exact finite reindexing interface for the output of the chronology step. -/
structure TableMatch (Q : Clock (k + 1)) (tau : ℕ) (c cref H delta T1 lam : ℚ)
    (ellStar : Fin (k + 1) → ℚ) (E Lr : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) where
  equiv : (OldAct P ⊕ (Fin (k + 1) ⊕ Fin (k + 1))) ≃ Fin Q.m
  score : Q.R = FaithfulReindex.rows equiv
    (nextScores (S_mid P tau c H delta) (zeta (P.R P.b) tau c H)
      (resetInteractions k T1 (prescribedT2 P tau c cref H delta T1 lam ellStar E) lam
        (zeta (P.R P.b) tau cref H) ellStar E Lr)
      (resetCounts k T1 (prescribedT2 P tau c cref H delta T1 lam ellStar E) lam
        (zeta (P.R P.b) tau cref H) ellStar))
  count : Q.countTable = FaithfulReindex.rows equiv
    (nextCounts (X P tau)
      (resetCounts k T1 (prescribedT2 P tau c cref H delta T1 lam ellStar E) lam
        (zeta (P.R P.b) tau cref H) ellStar))
  entry : Q.b = equiv (Sum.inr (Sum.inl 0))

/-- The next Clock inherits the exact deterministic scale and correction
chosen before T2; equality follows from actual tables, not summary premises. -/
theorem chosen_pair (Q : Clock (k + 1)) (tau : ℕ) (htau : 0 < tau)
    (c cref H delta T1 lam : ℚ) (hT1 : 0 < T1) (hlam : 0 < lam)
    (ellStar : Fin (k + 1) → ℚ) (E Lr : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hL : ∀ j, Lr 0 j = 0)
    (hearly : 0 < T1 * lam * zeta (P.R P.b) tau cref H (lastIdx k) + ellStar (lastIdx k))
    (hd : 1 + dotProduct ellStar (Matrix.mulVec
      (Winv_concrete k T1 (prescribedT2 P tau c cref H delta T1 lam ellStar E) lam
        (zeta (P.R P.b) tau cref H)) (Faithful.earlyUnit k)) ≠ 0)
    (matchTables : TableMatch P Q tau c cref H delta T1 lam ellStar E Lr) :
    FaithfulScaleClock.chosenScale Q (1 / 2) =
      nextScale k (by have := P.order_ge_two; omega) (S_mid P tau c H delta) (X P tau)
        (zeta (P.R P.b) tau c H) (zeta (P.R P.b) tau cref H) ellStar T1 lam E ∧
    FaithfulScaleClock.chosenCorrection Q (1 / 2) =
      nextCorrection k (by have := P.order_ge_two; omega) (S_mid P tau c H delta) (X P tau)
        (zeta (P.R P.b) tau c H) (zeta (P.R P.b) tau cref H) ellStar T1 lam E := by
  have hspec := prescribedT2_weights_spec P tau htau c cref H delta T1 lam hT1 hlam ellStar E hearly
  have hT2 : (prescribedT2 P tau c cref H delta T1 lam ellStar E : ℚ) ≠ 0 :=
    ne_of_gt (lt_trans (by norm_num) hspec.2.2.1)
  have hz0 : zeta (P.R P.b) tau cref H (lastIdx k) ≠ 0 :=
    ne_of_gt (zeta_leading_pos P.order_ge_two _ tau htau P.leading_height cref H)
  let Rplus := nextScores (S_mid P tau c H delta) (zeta (P.R P.b) tau c H)
    (resetInteractions k T1 (prescribedT2 P tau c cref H delta T1 lam ellStar E) lam
      (zeta (P.R P.b) tau cref H) ellStar E Lr)
    (resetCounts k T1 (prescribedT2 P tau c cref H delta T1 lam ellStar E) lam
      (zeta (P.R P.b) tau cref H) ellStar)
  let Cplus := nextCounts (X P tau)
    (resetCounts k T1 (prescribedT2 P tau c cref H delta T1 lam ellStar E) lam
      (zeta (P.R P.b) tau cref H) ellStar)
  have hm : FaithfulScaleClock.momentSummary Q = Rplusᵀ * Cplus := by
    rw [FaithfulScaleClock.momentSummary, matchTables.score, matchTables.count,
      FaithfulReindex.transpose_rows_mul_rows]
  have hl : FaithfulScaleClock.lengthSummary Q = Matrix.vecMul (fun _ => 1) Cplus := by
    rw [FaithfulScaleClock.lengthSummary, matchTables.count]
    exact FaithfulReindex.vecMul_rows matchTables.equiv (fun _ => 1) Cplus
  have hc : FaithfulScaleClock.scoreSummary Q = zeta (P.R P.b) tau c H := by
    rw [FaithfulScaleClock.scoreSummary, matchTables.score, matchTables.entry]
    change Rplus (matchTables.equiv.symm (matchTables.equiv (Sum.inr (Sum.inl 0)))) = _
    rw [Equiv.symm_apply_apply]
    exact nextScores_first_reset _ _ _ _ _
      (resetInteractions_first_row k T1 _ lam _ ellStar E Lr hL)
  unfold FaithfulScaleClock.chosenScale FaithfulScaleClock.correctionPolynomials
    FaithfulScaleClock.chosenCorrection
  rw [hm, hl, hc]
  exact actual_next_pair_eq_fixed k Q.order_ge_two (S_mid P tau c H delta) (X P tau)
    (zeta (P.R P.b) tau c H) (zeta (P.R P.b) tau cref H) ellStar T1
    (prescribedT2 P tau c cref H delta T1 lam ellStar E) lam
    (ne_of_gt hT1) hT2 (ne_of_gt hlam) hz0 hd E Lr

/-- All additional data are constructed, with the mandated next reference
gain 1/2 and next baseline Q.Arem+3. Only the exact chronological Clock/table
identification and the inverse denominator remain inputs. -/
noncomputable def admissible (Q : Clock (k + 1)) (tau : ℕ) (htau : 0 < tau)
    (c cref H delta T1 lam : ℚ) (hT1 : 0 < T1) (hlam : 0 < lam)
    (ellStar : Fin (k + 1) → ℚ) (E Lr : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hL : ∀ j, Lr 0 j = 0)
    (hearly : 0 < T1 * lam * zeta (P.R P.b) tau cref H (lastIdx k) + ellStar (lastIdx k))
    (hd : 1 + dotProduct ellStar (Matrix.mulVec
      (Winv_concrete k T1 (prescribedT2 P tau c cref H delta T1 lam ellStar E) lam
        (zeta (P.R P.b) tau cref H)) (Faithful.earlyUnit k)) ≠ 0)
    (matchTables : TableMatch P Q tau c cref H delta T1 lam ellStar E Lr) : Admissible Q := by
  let tauNext := nextScale k (by have := P.order_ge_two; omega)
    (S_mid P tau c H delta) (X P tau) (zeta (P.R P.b) tau c H)
    (zeta (P.R P.b) tau cref H) ellStar T1 lam E
  let ellNext := nextCorrection k (by have := P.order_ge_two; omega)
    (S_mid P tau c H delta) (X P tau) (zeta (P.R P.b) tau c H)
    (zeta (P.R P.b) tau cref H) ellStar T1 lam E
  let a := prescribedWeights P tau c cref H delta T1 lam ellStar E
  let aP := FaithfulReindex.vec matchTables.equiv a
  have hpair := chosen_pair P Q tau htau c cref H delta T1 lam hT1 hlam ellStar E Lr hL hearly hd matchTables
  have hspec := prescribedT2_weights_spec P tau htau c cref H delta T1 lam hT1 hlam ellStar E hearly
  have ht : 0 < tauNext := nextScale_pos _ _ _ _ _ _ _ _ _ _
  have hc : Q.R Q.b = zeta (P.R P.b) tau c H := by
    funext j
    rw [matchTables.score, matchTables.entry, FaithfulReindex.rows_apply, Equiv.symm_apply_apply]
    exact congrFun (nextScores_first_reset _ _ _ _ _
      (resetInteractions_first_row k T1 _ lam _ ellStar E Lr hL)) j
  refine {
    tau := tauNext
    tau_pos := ht
    cref := 1 / 2
    cref_pos := by norm_num
    cref_lt_one := by norm_num
    ellStar := ellNext
    aP := aP
    weights_pos := fun i => hspec.2.2.2.1 (matchTables.equiv.symm i)
    higher_tests := ?_
    cone := ?_ }
  · intro h hkh hht heven
    have hh := FaithfulScaleClock.chosenCorrection_higher_tests Q (1 / 2) (baseline Q) 0 h hkh hht heven
    rw [hpair.1, hpair.2] at hh
    exact hh
  · apply (target_cone_iff Q tauNext ht (1 / 2) (baseline Q) aP).mp
    rw [matchTables.count, FaithfulReindex.vecMul_rows, hc]
    exact hspec.2.2.2.2 (baseline Q)

#print axioms chosen_pair
#print axioms admissible

end Karlin.FaithfulNextAdmissible
