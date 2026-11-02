import Karlin.FaithfulWaiting
import Karlin.FaithfulChronology
import Karlin.FaithfulTables

/-! Remaining-height inheritance for the literal rotated phase.
The parent additive constant is charged once and the gateway costs at most one.
The reset-prefix threshold uses the actual count and height tables. -/

namespace Karlin.FaithfulInheritance

open scoped BigOperators
open FaithfulClock FaithfulWindow

def scoreHeight {α : Type*} [Fintype α] (b : α) (s : α → ℚ) : ℚ :=
  Finset.univ.sup' ⟨b, Finset.mem_univ b⟩ s

theorem le_scoreHeight {α : Type*} [Fintype α] (b : α) (s : α → ℚ) (i : α) :
    s i ≤ scoreHeight b s := Finset.le_sup' s (Finset.mem_univ i)

theorem scoreHeight_eq {α : Type*} [Fintype α] (b : α) (s : α → ℚ) (i : α)
    (hi : ∀ j, s j ≤ s i) : scoreHeight b s = s i := by
  exact le_antisymm (Finset.sup'_le _ _ (fun j _ => hi j)) (le_scoreHeight b s i)

theorem scoreHeight_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (b : α) (s : α → ℚ) :
    scoreHeight b s = scoreHeight (e b) (fun j => s (e.symm j)) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    simpa using le_scoreHeight (e b) (fun j => s (e.symm j)) (e i)
  · apply Finset.sup'_le
    intro i _
    exact le_scoreHeight b s (e.symm i)

theorem scoreHeight_fin {m : ℕ} (b : Fin m) (s : Fin m → ℚ) :
    scoreHeight b s = height b s := rfl

theorem scoreHeight_prefix_ge {α : Type*} [Fintype α] [DecidableEq α] {rnk : ℕ}
    (b : α) (G : Matrix α α ℚ) (hG : IsSkewSymmetric G) (s : α → ℚ)
    (rank : α → Fin rnk) (W : List α) (hW : IsValidPriorityWord G s rank W)
    (r : ℕ) (hr : r ≤ W.length) :
    scoreHeight b s ≤ scoreHeight b (wordScore G s (W.take r)) := by
  induction r with
  | zero => simp [wordScore_nil]
  | succ r ih =>
      have hr' : r < W.length := by omega
      have hp := ih (by omega)
      rw [scoreHeight_eq b _ (W[r]) (fun j => (hW r hr' j).1)] at hp
      have hn := le_scoreHeight b (wordScore G s (W.take (r + 1))) (W[r])
      have htake : W.take (r + 1) = W.take r ++ [W[r]] := by
        rw [List.take_add_one]
        simp [hr']
      rw [htake, wordScore_append, wordScore_singleton] at hn
      have hd : G (W[r]) (W[r]) = 0 := by have hh := hG (W[r]) (W[r]); linarith
      rw [hd, add_zero] at hn
      simpa only [← wordScore_append, ← htake] using hp.trans hn

variable {k nR : ℕ} (P : Clock k)

/-- The parent maximum is a lower bound for the maximum in the actual lifted
game, after exactly the same parent prefix. No waiting inequality is assumed. -/
theorem parent_height_le
    (C : Matrix (FaithfulGateway.Act P) (Fin nR) ℚ) (J : Matrix (Fin nR) (Fin nR) ℚ)
    (b : FaithfulWaiting.Act (nR := nR) P)
    (s : FaithfulWaiting.Act (nR := nR) P → ℚ) (a n : ℕ) (h delta : ℚ)
    (hs : ∀ x, s (Sum.inl x) = FaithfulGateway.initial P a n h delta x)
    (W : List (Fin P.m)) :
    height P.b (wordScore P.A (P.entry a) W) + h ≤
      scoreHeight b (wordScore (liftedGameMat (FaithfulGateway.game P) C J) s
        (FaithfulWaiting.parentStage P W)) := by
  apply add_le_of_le_sub_right
  apply Finset.sup'_le
  intro i _
  have hi := le_scoreHeight b
    (wordScore (liftedGameMat (FaithfulGateway.game P) C J) s
      (FaithfulWaiting.parentStage P W)) (Sum.inl (Sum.inl i))
  rw [FaithfulWaiting.parent_score P C J s a n h delta hs W i] at hi
  linarith

/-- All prefixes of `reset ++ oldWord` inherit `Aparent+1`. Structural inputs
are actual reset validity, reset endpoint, and the two scalar phase heights.
The only reset growth input is a whole polynomial increment bound. -/
theorem rotated_suffix
    (C : Matrix (FaithfulGateway.Act P) (Fin nR) ℚ) (J : Matrix (Fin nR) (Fin nR) ℚ)
    (b : FaithfulWaiting.Act (nR := nR) P)
    (s : FaithfulWaiting.Act (nR := nR) P → ℚ)
    {rnk : ℕ} (rank : FaithfulWaiting.Act (nR := nR) P → Fin rnk)
    (reset : List (FaithfulWaiting.Act (nR := nR) P))
    (a n : ℕ) (h delta zeta next c eps : ℚ)
    (heps : 0 < eps) (ha : FaithfulGrowth.Clock.bundleThreshold P eps ≤ a)
    (hc : c ≤ 1)
    (hG : IsSkewSymmetric (liftedGameMat (FaithfulGateway.game P) C J))
    (hreset : IsValidPriorityWord (liftedGameMat (FaithfulGateway.game P) C J) s rank reset)
    (hentry : zeta ≤ scoreHeight b s)
    (hs : ∀ x, wordScore (liftedGameMat (FaithfulGateway.game P) C J) s reset (Sum.inl x) =
      FaithfulGateway.initial P a n h delta x)
    (hend : P.entry (a + n) P.b + h = next - c)
    (hfinal : scoreHeight b (wordScore (liftedGameMat (FaithfulGateway.game P) C J) s
      (reset ++ (FaithfulGateway.oldWord P a n).map Sum.inl)) = next)
    (hgrowth : next - zeta ≤ eps * ((FaithfulGateway.oldWord P a n).length : ℚ))
    (r : ℕ) (hr : r ≤ (reset ++ (FaithfulGateway.oldWord P a n).map Sum.inl).length) :
    next - scoreHeight b (wordScore (liftedGameMat (FaithfulGateway.game P) C J) s
      ((reset ++ (FaithfulGateway.oldWord P a n).map Sum.inl).take r)) ≤
      eps * (((reset ++ (FaithfulGateway.oldWord P a n).map Sum.inl).length - r : ℕ) : ℚ) +
        (P.Arem + 1) := by
  let W := consecutiveWord P.word a n
  let old : List (FaithfulWaiting.Act (nR := nR) P) :=
    (FaithfulGateway.oldWord P a n).map Sum.inl
  have hlen : old.length = W.length + 1 := by simp [old, FaithfulGateway.oldWord, W]
  have hrem : 0 ≤ P.Arem + 1 := by linarith [P.remainder_nonneg]
  by_cases hfull : r = (reset ++ old).length
  · change next - scoreHeight b (wordScore _ s ((reset ++ old).take r)) ≤ _
    rw [hfull, List.take_length]
    change next - scoreHeight b (wordScore _ s (reset ++ (FaithfulGateway.oldWord P a n).map Sum.inl)) ≤ _
    rw [hfinal]
    simpa [hfull, old] using hrem
  by_cases hsmall : r ≤ reset.length
  · have hm := hentry.trans (scoreHeight_prefix_ge b _ hG s rank reset hreset r hsmall)
    have hl : (FaithfulGateway.oldWord P a n).length ≤ (reset ++ old).length - r := by
      simp only [List.length_append] at *
      have ho : old.length = (FaithfulGateway.oldWord P a n).length := by simp [old]
      omega
    have he := mul_le_mul_of_nonneg_left (show ((FaithfulGateway.oldWord P a n).length : ℚ) ≤
      ((reset ++ old).length - r : ℕ) by exact_mod_cast hl) heps.le
    change next - scoreHeight b (wordScore _ s ((reset ++ old).take r)) ≤ _
    rw [List.take_append_of_le_length hsmall]
    dsimp only [old] at he
    linarith
  · let u := r - reset.length
    have hu : u ≤ W.length := by
      change r ≤ (reset ++ old).length at hr
      simp only [List.length_append] at hr hfull
      omega
    have htake : (reset ++ old).take r = reset ++ FaithfulWaiting.parentStage P (W.take u) := by
      rw [List.take_append, List.take_of_length_le (by omega : reset.length ≤ r)]
      congr 1
      change (((W.map Sum.inl) ++ [Sum.inr (0 : Fin 1)]).map Sum.inl).take u = _
      rw [List.map_append, List.take_append_of_le_length (by simpa using hu)]
      simp [FaithfulWaiting.parentStage, List.map_take]
    have hp := parent_height_le P C J b (wordScore _ s reset) a n h delta hs (W.take u)
    have hQ : P.Q ≤ a := (P.threshold_onset eps heps).trans ((le_max_left _ _).trans ha)
    have hsuf := FaithfulGrowth.Clock.consecutive_suffix P heps a n u ha hu
    rw [P.entry_height (a + n) (by omega)] at hsuf
    have hl : W.length - u ≤ (reset ++ old).length - r := by
      simp only [List.length_append]
      omega
    have he := mul_le_mul_of_nonneg_left (show ((W.length - u : ℕ) : ℚ) ≤
      ((reset ++ old).length - r : ℕ) by exact_mod_cast hl) heps.le
    change next - scoreHeight b (wordScore _ s ((reset ++ old).take r)) ≤ _
    rw [htake, wordScore_append]
    dsimp only [old] at he
    change P.entry (a + n) P.b - height P.b (wordScore P.A (P.entry a) (W.take u)) ≤ _ at hsuf
    linarith

open FaithfulGrowth FaithfulTables

/-- The length row of the actual dyadic parent bundle followed by one gateway. -/
def oldLengthRow (tau : ℕ) : Fin (k + 1) → ℚ :=
  Matrix.vecMul (FaithfulGrowth.Clock.totalCountCoeff P) (F_tau_mat k tau) + e0_row (k + 1)

def nextOldLengthRow (tau : ℕ) : Fin (k + 1) → ℚ :=
  Matrix.vecMul (oldLengthRow P tau) (T_mat (k + 1))

def resetGainRow (tau : ℕ) (c H : ℚ) : Fin (k + 1) → ℚ :=
  Matrix.vecMul (zeta (P.R P.b) tau c H) (N_mat (k + 1))

theorem oldLengthRow_eval (tau q : ℕ) (hq : P.Q ≤ tau * q) :
    dotProduct (oldLengthRow P tau) (binomBasis (k + 1) q) =
      ((FaithfulGateway.oldWord P (tau * q) (tau * q)).length : ℚ) := by
  have hc := dyadicWord_count_table P.countTable P.word P.Q P.counts tau q hq
  rw [oldLengthRow, add_dotProduct, ← Matrix.dotProduct_mulVec]
  have he : dotProduct (e0_row (k + 1)) (binomBasis (k + 1) q) = 1 := by
    simp [dotProduct, e0_row, binomBasis]
  rw [he]
  simp only [FaithfulGateway.oldWord, List.length_append, List.length_map,
    List.length_singleton, Nat.cast_add, Nat.cast_one]
  congr 1
  rw [list_length_eq_sum_wordCountVec]
  change _ = ∑ i : Fin P.m, wordCountVec (dyadicWord P.word tau q) i
  rw [hc, ← Matrix.mulVec_mulVec]
  simp only [FaithfulGrowth.Clock.totalCountCoeff, dotProduct, Matrix.mulVec,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem nextOldLengthRow_eval (tau q : ℕ) (hq : P.Q ≤ tau * (q + 1)) :
    (rowPoly (nextOldLengthRow P tau)).eval (q : ℚ) =
      ((FaithfulGateway.oldWord P (tau * (q + 1)) (tau * (q + 1))).length : ℚ) := by
  rw [rowPoly_eval_nat]
  change dotProduct (nextOldLengthRow P tau) (binomBasis (k + 1) q) = _
  rw [nextOldLengthRow, ← Matrix.dotProduct_mulVec, ← binomBasis_succ]
  exact oldLengthRow_eval P tau (q + 1) hq

theorem oldLengthRow_last_pos (tau : ℕ) (htau : 0 < tau) :
    0 < oldLengthRow P tau (Fin.last k) := by
  have hk : 2 ≤ k := P.order_ge_two
  have hval := FaithfulPolynomialRoutes.bundle_row_top_coefficient hk
    (FaithfulGrowth.Clock.totalCountCoeff P) tau htau
  change oldLengthRow P tau (Fin.last k) = _ at hval
  rw [hval]
  apply mul_pos
  · apply mul_pos (FaithfulGrowth.Clock.leading_total_count_pos P)
    exact pow_pos (by exact_mod_cast htau : (0 : ℚ) < tau) _
  · exact sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega))

theorem nextOldLengthRow_top_pos (tau : ℕ) (htau : 0 < tau) :
    0 < (rowPoly (nextOldLengthRow P tau)).coeff k := by
  have htop := rowPoly_top_coeff (by omega : 0 < k + 1) (nextOldLengthRow P tau)
  simp only [Nat.add_sub_cancel] at htop
  rw [htop]
  apply div_pos _ (by positivity)
  change 0 < Matrix.vecMul (oldLengthRow P tau) (T_mat (k + 1)) (Fin.last k)
  rw [FaithfulTables.vecMul_T_apply, dif_neg (by simp), add_zero]
  exact oldLengthRow_last_pos P tau htau

theorem resetGainRow_degree (tau : ℕ) (c H : ℚ) :
    (rowPoly (resetGainRow P tau c H)).natDegree ≤ k - 1 := by
  apply rowPoly_natDegree_le_of_vanishing
  intro j hj
  have hjeq : j = Fin.last k := Fin.ext (by have := j.isLt; simp; omega)
  subst j
  simp only [resetGainRow, Matrix.vecMul, dotProduct]
  apply Finset.sum_eq_zero
  intro i _
  have hi : i.val ≠ k + 1 := by have := i.isLt; omega
  simp [N_mat, hi]

theorem resetGainRow_eval (tau q : ℕ) (c H : ℚ) :
    (rowPoly (resetGainRow P tau c H)).eval (q : ℚ) =
      heightValue P tau c H (q + 1) - heightValue P tau c H q := by
  rw [rowPoly_eval_nat]
  change dotProduct (resetGainRow P tau c H) (binomBasis (k + 1) q) = _
  rw [resetGainRow, ← Matrix.dotProduct_mulVec, ← binomBasis_succ_sub]
  simp only [dotProduct_sub, heightValue]

/-- A finite rational coefficient computation; all parameters precede eps. -/
def resetPrefixThreshold (tau : ℕ) (c H eps : ℚ) : ℕ :=
  rowDominationThreshold (nextOldLengthRow P tau) (resetGainRow P tau c H) k eps

theorem reset_prefix_gain_le (tau : ℕ) (htau : 0 < tau) (c H eps : ℚ)
    (heps : 0 < eps) (q : ℕ) (hq : resetPrefixThreshold P tau c H eps ≤ q)
    (hQ : P.Q ≤ tau * (q + 1)) :
    heightValue P tau c H (q + 1) - heightValue P tau c H q ≤
      eps * ((FaithfulGateway.oldWord P (tau * (q + 1)) (tau * (q + 1))).length : ℚ) := by
  rw [← resetGainRow_eval, ← nextOldLengthRow_eval P tau q hQ]
  apply polynomial_domination
    (rowPoly (nextOldLengthRow P tau)) (rowPoly (resetGainRow P tau c H))
    (by have := P.order_ge_two; omega)
    (by simpa using rowPoly_natDegree_le (nextOldLengthRow P tau))
    (resetGainRow_degree P tau c H) (nextOldLengthRow_top_pos P tau htau) heps
  simpa only [resetPrefixThreshold, rowDominationThreshold_eq] using hq

theorem parentTranslation_next (tau q : ℕ) (c H : ℚ) :
    parentTranslation P tau c H (q + 1) = heightValue P tau c H q -
      P.entry (tau * (q + 1)) P.b := by
  rw [parentTranslation, translation, sub_dotProduct,
    ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec,
    B_mat_mulVec_binomBasis, E_tau_mat_mulVec_binomBasis]
  rfl

theorem parent_endpoint_height (tau q : ℕ) (c H : ℚ) :
    P.entry (tau * (q + 1) + tau * (q + 1)) P.b +
      parentTranslation P tau c H (q + 1) = heightValue P tau c H (q + 1) - c := by
  rw [parentTranslation_next]
  have hh := heightValue_step P tau q c H
  have he : tau * (q + 1) + tau * (q + 1) = 2 * tau * (q + 1) := by ring
  rw [he]
  linarith

/-- Exact terminating threshold of the inheritance proof: outer onset,
reset-prefix coefficient bound, and the scaled parent bundle onset. -/
def inheritedThreshold (tau Qout : ℕ) (c H eps : ℚ) : ℕ :=
  max Qout (max (resetPrefixThreshold P tau c H eps)
    ⌈(FaithfulGrowth.Clock.bundleThreshold P eps : ℚ) / (tau : ℚ)⌉₊)

theorem inheritedThreshold_onset (tau Qout : ℕ) (c H eps : ℚ) :
    Qout ≤ inheritedThreshold P tau Qout c H eps := le_max_left _ _

theorem inheritedThreshold_bundle (tau Qout : ℕ) (htau : 0 < tau) (c H eps : ℚ)
    (q : ℕ) (hq : inheritedThreshold P tau Qout c H eps ≤ q) :
    FaithfulGrowth.Clock.bundleThreshold P eps ≤ tau * (q + 1) := by
  have hb : ⌈(FaithfulGrowth.Clock.bundleThreshold P eps : ℚ) / (tau : ℚ)⌉₊ ≤ q :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hq)
  have ht : (0 : ℚ) < tau := by exact_mod_cast htau
  have hdiv : (FaithfulGrowth.Clock.bundleThreshold P eps : ℚ) / (tau : ℚ) ≤ (q : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hb)
  have he := (div_le_iff₀ ht).mp hdiv
  have hnat : FaithfulGrowth.Clock.bundleThreshold P eps ≤ q * tau := by exact_mod_cast he
  exact hnat.trans (by nlinarith)

/-- The actual rotated-word suffix statement with all growth estimates proved
from the fixed parent tables. The structural premises describe chronology and
phase scores, never an assumed inherited suffix bound. -/
theorem rotated_tables_suffix
    (C : Matrix (FaithfulGateway.Act P) (Fin nR) ℚ) (J : Matrix (Fin nR) (Fin nR) ℚ)
    (b : FaithfulWaiting.Act (nR := nR) P)
    (s : FaithfulWaiting.Act (nR := nR) P → ℚ)
    {rnk : ℕ} (rank : FaithfulWaiting.Act (nR := nR) P → Fin rnk)
    (reset : List (FaithfulWaiting.Act (nR := nR) P))
    (tau Qout q : ℕ) (htau : 0 < tau) (c H delta eps : ℚ)
    (heps : 0 < eps) (hq : inheritedThreshold P tau Qout c H eps ≤ q) (hc : c ≤ 1)
    (hG : IsSkewSymmetric (liftedGameMat (FaithfulGateway.game P) C J))
    (hreset : IsValidPriorityWord (liftedGameMat (FaithfulGateway.game P) C J) s rank reset)
    (hentry : heightValue P tau c H q ≤ scoreHeight b s)
    (hs : ∀ x, wordScore (liftedGameMat (FaithfulGateway.game P) C J) s reset (Sum.inl x) =
      FaithfulGateway.initial P (tau * (q + 1)) (tau * (q + 1))
        (parentTranslation P tau c H (q + 1)) delta x)
    (hfinal : scoreHeight b (wordScore (liftedGameMat (FaithfulGateway.game P) C J) s
      (reset ++ (FaithfulGateway.oldWord P (tau * (q + 1)) (tau * (q + 1))).map Sum.inl)) =
      heightValue P tau c H (q + 1))
    (r : ℕ) (hr : r ≤
      (reset ++ (FaithfulGateway.oldWord P (tau * (q + 1)) (tau * (q + 1))).map Sum.inl).length) :
    heightValue P tau c H (q + 1) - scoreHeight b
      (wordScore (liftedGameMat (FaithfulGateway.game P) C J) s
        ((reset ++ (FaithfulGateway.oldWord P (tau * (q + 1)) (tau * (q + 1))).map Sum.inl).take r)) ≤
      eps * (((reset ++ (FaithfulGateway.oldWord P (tau * (q + 1)) (tau * (q + 1))).map Sum.inl).length - r : ℕ) : ℚ) +
        (P.Arem + 1) := by
  have ha := inheritedThreshold_bundle P tau Qout htau c H eps q hq
  have hQ : P.Q ≤ tau * (q + 1) :=
    (P.threshold_onset eps heps).trans ((le_max_left _ _).trans ha)
  apply rotated_suffix P C J b s rank reset _ _ _ delta _ _ c eps heps ha hc
    hG hreset hentry hs (parent_endpoint_height P tau q c H) hfinal _ r hr
  apply reset_prefix_gain_le P tau htau c H eps heps q _ hQ
  exact (le_max_left _ _).trans ((le_max_right _ _).trans hq)

end Karlin.FaithfulInheritance
