import Karlin.FaithfulWaiting
import Karlin.FaithfulChronology
import Karlin.FaithfulTables
import Karlin.FaithfulNextTables
import Karlin.FaithfulParameters
import Karlin.FaithfulResetEquations
import Karlin.FaithfulSynthesis
import Karlin.FaithfulReindex
import Karlin.FaithfulInheritance
import Karlin.FaithfulController

/-! Literal rotated words and structural clock inheritance. -/
namespace Karlin.FaithfulNextClock
open scoped BigOperators Matrix
open FaithfulClock

/-- Gateway unit counter, fixed independently of the phase. -/
def gatewayCounter {α : Type*} [DecidableEq α] (g : α) : α → ℚ :=
  fun i => if i = g then 1 else 0

@[simp] theorem gatewayCounter_self {α : Type*} [DecidableEq α] (g : α) :
    gatewayCounter g g = 1 := by simp [gatewayCounter]

@[simp] theorem gatewayCounter_other {α : Type*} [DecidableEq α] (g i : α) (hi : i ≠ g) :
    gatewayCounter g i = 0 := by simp [gatewayCounter, hi]

theorem gatewayCounter_dot {α : Type*} [Fintype α] [DecidableEq α]
    (g : α) (x : α → ℚ) : dotProduct (gatewayCounter g) x = x g := by
  simp [dotProduct, gatewayCounter]

/-- At every proper pre the literal last gateway play remains. -/
theorem terminal_gateway_remaining {α : Type*} [DecidableEq α]
    (W : List α) (g : α) (r : ℕ) (hr : r < (W ++ [g]).length) :
    1 ≤ wordCountVec ((W ++ [g]).drop r) g := by
  have hr' : r ≤ W.length := by simp only [List.length_append, List.length_singleton] at hr; omega
  rw [List.drop_append, Nat.sub_eq_zero_of_le hr', List.drop_zero, wordCountVec_append]
  have hn : 0 ≤ wordCountVec (W.drop r) g := Nat.cast_nonneg _
  simp only [wordCountVec, List.count_singleton, beq_self_eq_true, ite_true, Nat.cast_one]
  exact le_add_of_nonneg_left hn

/-- Marker one follows from the actual terminal gateway, without signs on
parent counters or assumptions about the score maximum. -/
theorem terminal_gateway_marker {m : ℕ} (G : Matrix (Fin m) (Fin m) ℚ)
    (s : Fin m → ℚ) (b g : Fin m) (W : List (Fin m))
    (r : ℕ) (hr : r < (W ++ [g]).length) :
    1 ≤ height b (wordScore G s ((W ++ [g]).take r)) -
      wordScore G s ((W ++ [g]).take r) b +
      dotProduct (gatewayCounter g) (wordCountVec ((W ++ [g]).drop r)) := by
  rw [gatewayCounter_dot]
  have hc := terminal_gateway_remaining W g r hr
  have hm := le_height b (wordScore G s ((W ++ [g]).take r)) b
  linarith

/-- The literal inherited word is resets(q), then the next old word. -/
def rotatedWord {m n : ℕ} (counts : ℕ → Fin n → ℕ)
    (old : ℕ → List (Fin m)) (q : ℕ) : List (Fin m ⊕ Fin n) :=
  FaithfulChronology.resetWord (counts q) ++ (old (q + 1)).map Sum.inl

theorem rotatedWord_begins_twice {m n : ℕ} (hn : 0 < n)
    (counts : ℕ → Fin n → ℕ) (old : ℕ → List (Fin m)) (q : ℕ)
    (hc : 2 ≤ counts q ⟨0, hn⟩) :
    ∃ tail, rotatedWord counts old q = Sum.inr ⟨0, hn⟩ :: Sum.inr ⟨0, hn⟩ :: tail := by
  obtain ⟨tail, ht⟩ := FaithfulChronology.resetWord_begins_twice (m := m) hn (counts q) hc
  refine ⟨tail ++ (old (q + 1)).map Sum.inl, ?_⟩
  simp only [rotatedWord, ht, List.cons_append]

/-- Exact counts on the same rotated word. -/
theorem rotatedWord_counts {m n w : ℕ} (counts : ℕ → Fin n → ℕ)
    (old : ℕ → List (Fin m)) (X : Matrix (Fin m) (Fin w) ℚ)
    (M : Matrix (Fin n) (Fin w) ℚ) (q : ℕ)
    (hold : wordCountVec (old (q + 1)) = X.mulVec (binomBasis w (q + 1)))
    (hcount : ∀ j, (counts q j : ℚ) = M.mulVec (binomBasis w q) j) :
    wordCountVec (rotatedWord counts old q) =
      (Matrix.fromRows (X * T_mat w) M).mulVec (binomBasis w q) := by
  funext i
  rw [rotatedWord, wordCountVec_append]
  cases i with
  | inl i =>
    rw [FaithfulChronology.resetWord_count, wordCountVec_map_inl_inl, hold]
    simp only [Sum.elim_inl, zero_add, Matrix.fromRows_mulVec, Sum.elim_inl]
    rw [← Matrix.mulVec_mulVec, ← binomBasis_succ]
  | inr j =>
    rw [FaithfulChronology.resetWord_count, wordCountVec_map_inl_inr]
    simpa using hcount j

/-- The first reset is safe against the sole counter-supported gateway. -/
theorem gateway_support_safe {α : Type*} [Fintype α] [DecidableEq α]
    (G : Matrix α α ℚ) (s : α → ℚ) (b g : α) (hbg : b ≠ g)
    (zeta c delta : ℚ) (hb : s b = zeta) (hg : s g = zeta - c + delta)
    (hdiag : G b b = 0) (hc : delta < c) (hcoupling : G g b < 0) :
    ∀ i, gatewayCounter g i ≠ 0 →
      s i + G i b - gatewayCounter g i < s b + G b b - gatewayCounter g b := by
  intro i hi
  have hig : i = g := by
    by_contra hne
    exact hi (gatewayCounter_other g i hne)
  subst i
  rw [gatewayCounter_self, gatewayCounter_other g b hbg, hb, hg, hdiag]
  linarith

/-- Reorder parent/gateway/reset coordinates into parent/reset/gateway rank blocks. -/
def rankBlocks (m n : ℕ) : (Fin m ⊕ Fin 1) ⊕ Fin n ≃ (Fin m ⊕ Fin n) ⊕ Fin 1 where
  toFun := fun x => match x with
    | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl i)
    | Sum.inl (Sum.inr g) => Sum.inr g
    | Sum.inr j => Sum.inl (Sum.inr j)
  invFun := fun x => match x with
    | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl i)
    | Sum.inl (Sum.inr j) => Sum.inr j
    | Sum.inr g => Sum.inl (Sum.inr g)
  left_inv := by intro x; rcases x with (i | g) | j <;> rfl
  right_inv := by intro x; rcases x with (i | j) | g <;> rfl

/-- An explicit bijective paper rank, with reverse reset order. -/
def priorityEquiv (m n : ℕ) (parentRank : Equiv.Perm (Fin m)) :
    Fin (m + 1) ⊕ Fin n ≃ Fin ((m + 1) + n) :=
  (Equiv.sumCongr (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).symm (Equiv.refl _)).trans
  ((rankBlocks m n).trans
    ((Equiv.sumCongr (Equiv.sumCongr parentRank (Fin.revPerm : Equiv.Perm (Fin n)))
      (Equiv.refl (Fin 1))).trans
      ((Equiv.sumCongr (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)) (Equiv.refl _)).trans
        ((finSumFinEquiv : Fin (m + n) ⊕ Fin 1 ≃ Fin ((m + n) + 1)).trans
          (finCongr (by omega))))))

theorem priorityEquiv_paper_val (m w : ℕ) (parentRank : Equiv.Perm (Fin m))
    (i : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1))) :
    (priorityEquiv m ((w + 1) + (w + 1)) parentRank i).val =
      (paperPriorityRank m w parentRank i).val := by
  cases i with
  | inl i =>
    obtain ⟨x, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)).surjective i
    cases x with
    | inl x => simp [priorityEquiv, rankBlocks, paperPriorityRank]
    | inr x =>
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp [priorityEquiv, rankBlocks, paperPriorityRank]
      omega
  | inr j =>
    simp [priorityEquiv, rankBlocks, paperPriorityRank, Fin.rev]
    omega

/-- Convert the numerical paper rank into an actual permutation after the
canonical Sum-to-Fin action reindexing. -/
def nextRank (m n : ℕ) (parentRank : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin ((m + 1) + n)) :=
  (finSumFinEquiv : Fin (m + 1) ⊕ Fin n ≃ Fin ((m + 1) + n)).symm.trans
    (priorityEquiv m n parentRank)

theorem priority_valid_reindex (m w : ℕ) (parentRank : Equiv.Perm (Fin m))
    (G : Matrix (Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)))
      (Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1))) ℚ)
    (s : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) → ℚ)
    (W : List (Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1))))
    (hW : IsValidPriorityWord G s (paperPriorityRank m w parentRank) W) :
    let e := (finSumFinEquiv : Fin (m + 1) ⊕ Fin ((w + 1) + (w + 1)) ≃
      Fin ((m + 1) + ((w + 1) + (w + 1))))
    IsValidPriorityWord (fun i j => G (e.symm i) (e.symm j)) (fun i => s (e.symm i))
      (nextRank m ((w + 1) + (w + 1)) parentRank) (W.map e) := by
  intro e
  have hm := isValidPriorityWord_map_equiv e G s (paperPriorityRank m w parentRank) W hW
  intro r hr i
  obtain ⟨hle, htie⟩ := hm r hr i
  refine ⟨hle, ?_⟩
  intro hne heq
  have hh := htie hne heq
  simpa only [nextRank, Equiv.trans_apply, priorityEquiv_paper_val] using hh

namespace Lift
open FaithfulAdmissible FaithfulParameters FaithfulParameters.AdmissibleParameters
open FaithfulGain.AdmissibleGain FaithfulResetEquations
variable {k : ℕ} {P : Clock k} (A : Admissible P)

abbrev Res := Fin ((k + 1) + (k + 1))
abbrev Act := Fin (P.m + 1) ⊕ Res (k := k)

def oldEquiv : FaithfulTables.OldAct P ≃ Fin (P.m + 1) := finSumFinEquiv

def resetEquiv : Fin (k + 1) ⊕ Fin (k + 1) ≃ Res (k := k) := finSumFinEquiv

def countInt (T1 T2 : ℕ) : Matrix (Res (k := k)) (Fin (k + 1)) ℤ :=
  (resetTable A T1 T2).submatrix resetEquiv.symm id

def countRat (T1 T2 : ℕ) : Matrix (Res (k := k)) (Fin (k + 1)) ℚ :=
  fun i j => (countInt A T1 T2 i j : ℚ)

def count (T1 T2 q : ℕ) : Res (k := k) → ℕ :=
  fun i => (phaseCounts (countInt A T1 T2) q i).toNat

def old (q : ℕ) : List (Fin (P.m + 1)) :=
  (FaithfulGateway.oldWord P (A.tau * q) (A.tau * q)).map oldEquiv

def word (T1 T2 q : ℕ) : List (Act (P := P)) :=
  rotatedWord (count A T1 T2) (old A) q

def oldX : Matrix (Fin (P.m + 1)) (Fin (k + 1)) ℚ :=
  (FaithfulTables.X P A.tau).submatrix oldEquiv.symm id

def oldS (T1 : ℕ) : Matrix (Fin (P.m + 1)) (Fin (k + 1)) ℚ :=
  (FaithfulTables.S P A.tau (selectedGain A (lam A) T1) (baseline P)
    (FaithfulSynthesis.endpointMargin A (lam A) T1)).submatrix oldEquiv.symm id

def zeta (T1 : ℕ) : Fin (k + 1) → ℚ :=
  FaithfulTables.zeta (P.R P.b) A.tau (selectedGain A (lam A) T1) (baseline P)

noncomputable def coupling (T1 T2 : ℕ) : Matrix (Fin (P.m + 1)) (Res (k := k)) ℚ :=
  (FaithfulSynthesis.coupling A (lam A) T1 T2 (leftInverseLX P A.tau)).submatrix
    oldEquiv.symm resetEquiv.symm

noncomputable def J (T1 T2 : ℕ) : Matrix (Res (k := k)) (Res (k := k)) ℚ :=
  resetJFin k T1 T2 (lam A) A.referenceHeight A.correction (momentTable A (lam A) T1)

def G : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℚ :=
  (FaithfulTables.oldGame P).submatrix oldEquiv.symm oldEquiv.symm

noncomputable def game (T1 T2 : ℕ) : Matrix (Act (P := P)) (Act (P := P)) ℚ :=
  liftedGameMat (G (P := P)) (coupling A T1 T2) (J A T1 T2)

noncomputable def entryTable (T1 T2 : ℕ) : Matrix (Act (P := P)) (Fin (k + 1)) ℚ :=
  Matrix.fromRows (oldS A T1)
    (V_reset (J A T1 T2) (countRat A T1 T2) (B_mat (k + 1)) (zeta A T1))

noncomputable def scoreTable (T1 T2 : ℕ) : Matrix (Act (P := P)) (Fin (k + 1)) ℚ :=
  FaithfulNextTables.nextScores (oldS A T1 + G (P := P) * oldX A)
    (zeta A T1) (J A T1 T2) (countRat A T1 T2)

def countTable (T1 T2 : ℕ) : Matrix (Act (P := P)) (Fin (k + 1)) ℚ :=
  FaithfulNextTables.nextCounts (oldX A) (countRat A T1 T2)

theorem countRat_eq (T1 T2 : ℕ) :
    countRat A T1 T2 =
      (resetM k T1 T2 (lam A) A.referenceHeight A.correction).submatrix resetEquiv.symm id := by
  ext i j
  exact congrFun (congrFun (resetTable_cast A T1 T2) (resetEquiv.symm i)) j

theorem count_leading (T1 T2 : ℕ)
    (hv : FaithfulSynthesis.ValidScales A (lam A) T1 T2 (leftInverseLX P A.tau))
    (i : Res (k := k)) : 0 < countInt A T1 T2 i (Fin.last k) := by
  have he := congrFun (congrFun (countRat_eq A T1 T2) i) (Fin.last k)
  have hp : 0 < countRat A T1 T2 i (Fin.last k) := by
    rw [he]
    change 0 < resetM k T1 T2 (lam A) A.referenceHeight A.correction (resetEquiv.symm i) (Fin.last k)
    cases h : resetEquiv.symm i with
    | inl j => exact (hv.reset_leading j).1
    | inr j => exact (hv.reset_leading j).2
  change (0 : ℚ) < (countInt A T1 T2 i (Fin.last k) : ℚ) at hp
  exact_mod_cast hp

theorem count_ge_two (T1 T2 q : ℕ)
    (hv : FaithfulSynthesis.ValidScales A (lam A) T1 T2 (leftInverseLX P A.tau))
    (hq : resetOnset (countInt A T1 T2) ≤ q) (i : Res (k := k)) :
    2 ≤ count A T1 T2 q i := by
  have hc := resetCounts_ge_two (by have := P.order_ge_two; omega)
    (countInt A T1 T2) (count_leading A T1 T2 hv) q hq i
  unfold count
  omega

theorem count_cast (T1 T2 q : ℕ)
    (hv : FaithfulSynthesis.ValidScales A (lam A) T1 T2 (leftInverseLX P A.tau))
    (hq : resetOnset (countInt A T1 T2) ≤ q) (i : Res (k := k)) :
    (count A T1 T2 q i : ℚ) = (countRat A T1 T2).mulVec (binomBasis (k + 1) q) i := by
  have hc := resetCounts_ge_two (by have := P.order_ge_two; omega)
    (countInt A T1 T2) (count_leading A T1 T2 hv) q hq i
  have hn : (count A T1 T2 q i : ℤ) = phaseCounts (countInt A T1 T2) q i :=
    Int.toNat_of_nonneg (by omega)
  have he := congrArg (fun z : ℤ => (z : ℚ)) hn
  simpa only [Int.cast_natCast, phaseCounts_cast] using he

theorem old_count (q : ℕ) (hq : P.Q ≤ A.tau * q) :
    wordCountVec (old A q) = (oldX A).mulVec (binomBasis (k + 1) q) := by
  funext i
  rw [old, wordCountVec_map_equiv]
  obtain ⟨j, rfl⟩ := oldEquiv.surjective i
  simp only [Equiv.symm_apply_apply]
  cases j with
  | inl j =>
    rw [FaithfulGateway.oldWord_parent_count]
    simpa [oldX, Matrix.mulVec, dotProduct, FaithfulTables.X, FaithfulWindow.dyadicWord]
      using congrFun (P.dyadic_compatible A.tau q hq).2.2 j
  | inr j =>
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rw [FaithfulGateway.oldWord_gateway_count]
    simp [oldX, oldEquiv, FaithfulTables.X, Matrix.mulVec, dotProduct, e0_row, binomBasis]

theorem word_count (T1 T2 q : ℕ)
    (hv : FaithfulSynthesis.ValidScales A (lam A) T1 T2 (leftInverseLX P A.tau))
    (hq : resetOnset (countInt A T1 T2) ≤ q) (hparent : P.Q ≤ A.tau * (q + 1)) :
    wordCountVec (word A T1 T2 q) = (countTable A T1 T2).mulVec (binomBasis (k + 1) q) :=
  rotatedWord_counts (count A T1 T2) (old A) (oldX A) (countRat A T1 T2) q
    (old_count A (q + 1) hparent) (count_cast A T1 T2 q hv hq)

theorem word_begins_twice (T1 T2 q : ℕ)
    (hv : FaithfulSynthesis.ValidScales A (lam A) T1 T2 (leftInverseLX P A.tau))
    (hq : resetOnset (countInt A T1 T2) ≤ q) :
    ∃ tail, word A T1 T2 q = Sum.inr 0 :: Sum.inr 0 :: tail :=
  rotatedWord_begins_twice (by omega) (count A T1 T2) (old A) q
    (count_ge_two A T1 T2 q hv hq 0)

theorem phaseCount_outer (T1 T2 q : ℕ)
    (hv : FaithfulController.ValidParameters A T1 T2)
    (hq : FaithfulController.outerOnset A T1 T2 ≤ q) (i : Res (k := k)) :
    2 ≤ phaseCounts (countInt A T1 T2) q i ∧
      2 ≤ phaseCounts (countInt A T1 T2) (q - 1) i :=
  FaithfulController.outerOnset_counts A T1 T2 hv q hq (resetEquiv.symm i)

theorem count_ge_two_outer (T1 T2 q : ℕ)
    (hv : FaithfulController.ValidParameters A T1 T2)
    (hq : FaithfulController.outerOnset A T1 T2 ≤ q) (i : Res (k := k)) :
    2 ≤ count A T1 T2 q i := by
  have h := (phaseCount_outer A T1 T2 q hv hq i).1
  unfold count
  omega

theorem count_cast_outer (T1 T2 q : ℕ)
    (hv : FaithfulController.ValidParameters A T1 T2)
    (hq : FaithfulController.outerOnset A T1 T2 ≤ q) (i : Res (k := k)) :
    (count A T1 T2 q i : ℚ) = (countRat A T1 T2).mulVec (binomBasis (k + 1) q) i := by
  have hc := (phaseCount_outer A T1 T2 q hv hq i).1
  have hn : (count A T1 T2 q i : ℤ) = phaseCounts (countInt A T1 T2) q i :=
    Int.toNat_of_nonneg (by omega)
  have he := congrArg (fun z : ℤ => (z : ℚ)) hn
  simpa only [Int.cast_natCast, phaseCounts_cast] using he


open FaithfulReindex

theorem game_skew (T1 T2 : ℕ) : IsSkewSymmetric (game A T1 T2) :=
  liftedGameMat_skew _ _ _ (FaithfulReindex.skew oldEquiv (FaithfulTables.oldGame_skew P))

theorem J_lower (T1 T2 : ℕ) (i j : Res (k := k)) (hij : i.val ≤ j.val) :
    J A T1 T2 i j = 0 :=
  resetJFin_lower k T1 T2 (lam A) A.referenceHeight A.correction
    (momentTable A (lam A) T1) i j hij

theorem J_positive (T1 T2 : ℕ)
    (hv : FaithfulSynthesis.ValidScales A (lam A) T1 T2 (leftInverseLX P A.tau))
    (i j : Res (k := k)) (hij : j.val < i.val) : 0 < J A T1 T2 i j := by
  apply resetJFin_positive k T1 T2 (lam A) A.referenceHeight A.correction
    (momentTable A (lam A) T1)
  · exact_mod_cast hv.first_pos
  · exact_mod_cast hv.second_pos
  · exact hv.cross_positive
  · exact hij

theorem J_nonnegative (T1 T2 : ℕ)
    (hv : FaithfulSynthesis.ValidScales A (lam A) T1 T2 (leftInverseLX P A.tau))
    (i j : Res (k := k)) : 0 ≤ J A T1 T2 i j := by
  by_cases h : i.val ≤ j.val
  · rw [J_lower A T1 T2 i j h]
  · exact (J_positive A T1 T2 hv i j (by omega)).le

theorem interpolation (T1 T2 : ℕ)
    (hv : FaithfulSynthesis.ValidScales A (lam A) T1 T2 (leftInverseLX P A.tau)) :
    coupling A T1 T2 * countRat A T1 T2 = oldS A T1 * N_mat (k + 1) - G * oldX A ∧
      (coupling A T1 T2)ᵀ * oldX A =
        Q_reset (J A T1 T2) (countRat A T1 T2) (B_mat (k + 1)) (zeta A T1) := by
  have he := actualCoupling_equations_of_moment A (lam A) T1 T2
    (FaithfulSynthesis.endpointMargin A (lam A) T1) hv.first_pos hv.second_pos (lam_pos A)
    (ne_of_gt (lt_trans (by norm_num) hv.inverse_denominator))
    (hv.moment (FaithfulSynthesis.endpointMargin A (lam A) T1))
  dsimp only at he
  constructor
  · rw [countRat_eq]
    change matrix oldEquiv resetEquiv (actualCoupling A (lam A) T1 T2) *
      rows resetEquiv (resetM k T1 T2 (lam A) A.referenceHeight A.correction) = _
    rw [matrix_mul_rows, he.1]
    change rows oldEquiv (FaithfulTables.S P A.tau _ _ _ * N_mat (k+1) -
      FaithfulTables.oldGame P * FaithfulTables.X P A.tau) = _
    have hg := matrix_mul_rows oldEquiv oldEquiv (FaithfulTables.oldGame P) (FaithfulTables.X P A.tau)
    change rows oldEquiv _ = rows oldEquiv _ * _ -
      matrix oldEquiv oldEquiv (FaithfulTables.oldGame P) * rows oldEquiv (FaithfulTables.X P A.tau)
    rw [hg]
    rfl
  · rw [countRat_eq]
    change matrix resetEquiv oldEquiv (actualCoupling A (lam A) T1 T2)ᵀ *
      rows oldEquiv (FaithfulTables.X P A.tau) = _
    rw [matrix_mul_rows, he.2]
    change rows resetEquiv (Q_reset _ _ _ _) =
      Q_reset (matrix resetEquiv resetEquiv _) (rows resetEquiv _) _ _
    exact rows_Q_reset resetEquiv _ _ _ _

theorem clock_equation (T1 T2 : ℕ)
    (hv : FaithfulSynthesis.ValidScales A (lam A) T1 T2 (leftInverseLX P A.tau)) :
    game A T1 T2 * countTable A T1 T2 = scoreTable A T1 T2 * N_mat (k + 1) :=
  FaithfulNextTables.next_clock_eq G (coupling A T1 T2) (J A T1 T2)
    (oldS A T1) (oldX A) (countRat A T1 T2) (zeta A T1)
    (interpolation A T1 T2 hv).1 (interpolation A T1 T2 hv).2

theorem reset_full_rank (T1 T2 : ℕ)
    (hv : FaithfulSynthesis.ValidScales A (lam A) T1 T2 (leftInverseLX P A.tau)) :
    Function.Injective (countRat A T1 T2).mulVec := by
  rw [countRat_eq]
  apply FaithfulReindex.rows_full_column_rank resetEquiv
  have hm := resetRM_mul_resetM k T1 T2 (lam A) A.referenceHeight A.correction
    (by exact_mod_cast hv.first_pos.ne') (by exact_mod_cast hv.second_pos.ne')
    (by exact_mod_cast (show 0 < lam A from lam_pos A).ne') A.reference_leading_pos.ne'
  intro x y hxy
  have h := congrArg (resetRM k T1 T2 (lam A) A.referenceHeight).mulVec hxy
  change (resetRM k T1 T2 (lam A) A.referenceHeight).mulVec
    ((resetM k T1 T2 (lam A) A.referenceHeight A.correction).mulVec x) =
    (resetRM k T1 T2 (lam A) A.referenceHeight).mulVec
    ((resetM k T1 T2 (lam A) A.referenceHeight A.correction).mulVec y) at h
  simpa only [Matrix.mulVec_mulVec, hm, Matrix.one_mulVec] using h

theorem count_full_rank (T1 T2 : ℕ)
    (hv : FaithfulSynthesis.ValidScales A (lam A) T1 T2 (leftInverseLX P A.tau)) :
    Function.Injective (countTable A T1 T2).mulVec :=
  FaithfulNextTables.nextCounts_full_column_rank (oldX A) (countRat A T1 T2)
    (reset_full_rank A T1 T2 hv)

theorem score_reset_zero (T1 T2 : ℕ) : scoreTable A T1 T2 (Sum.inr 0) = zeta A T1 :=
  FaithfulNextTables.nextScores_first_reset _ _ _ _ 0
    (fun j => J_lower A T1 T2 0 j (Nat.zero_le _))

theorem score_leading_positive (T1 T2 : ℕ) :
    0 < scoreTable A T1 T2 (Sum.inr 0) (Fin.last k) := by
  rw [score_reset_zero]
  exact FaithfulTables.zeta_leading_pos P.order_ge_two (P.R P.b) A.tau A.tau_pos
    P.leading_height _ _


/-- Integral Pascal shift, with the same coefficient orientation as T_mat. -/
def shiftInt (w : ℕ) : Matrix (Fin w) (Fin w) ℤ :=
  (1 : Matrix (Fin w) (Fin w) ℤ) + (Matrix.of fun i j => if i.val = j.val + 1 then 1 else 0)

theorem shiftInt_cast (w : ℕ) (i j : Fin w) :
    (shiftInt w i j : ℚ) = T_mat w i j := by
  simp only [shiftInt, Matrix.add_apply, Int.cast_add, Matrix.one_apply,
    T_mat, N_mat, Matrix.of_apply]
  split_ifs <;> norm_num

def oldCountInt : Matrix (Fin (P.m + 1)) (Fin (k + 1)) ℤ :=
  (oldTable A).submatrix oldEquiv.symm id

def nextCountInt (T1 T2 : ℕ) : Matrix (Act (P := P)) (Fin (k + 1)) ℤ :=
  Matrix.fromRows (oldCountInt A * shiftInt (k + 1)) (countInt A T1 T2)

theorem nextCountInt_cast (T1 T2 : ℕ) :
    (fun i j => (nextCountInt A T1 T2 i j : ℚ)) = countTable A T1 T2 := by
  ext i j
  cases i with
  | inl i =>
    change ((∑ l, oldCountInt A i l * shiftInt (k + 1) l j : ℤ) : ℚ) = _
    simp only [Int.cast_sum, Int.cast_mul, shiftInt_cast]
    apply Finset.sum_congr rfl
    intro l _
    rw [show (oldCountInt A i l : ℚ) = oldX A i l from oldTable_cast A (oldEquiv.symm i) l]
  | inr i => rfl

def base : Act (P := P) := Sum.inr 0

def gateway : Act (P := P) := Sum.inl (oldEquiv (Sum.inr 0))

def counter : Act (P := P) → ℚ := gatewayCounter (gateway (P := P))

theorem counter_base : counter (P := P) (base (P := P)) = 0 := by
  simp [counter, base, gateway, gatewayCounter]

theorem count_gateway (T1 T2 : ℕ) : countTable A T1 T2 (gateway (P := P)) = e0_row (k + 1) := by
  change Matrix.vecMul (oldX A (oldEquiv (Sum.inr 0))) (T_mat (k + 1)) = _
  have hx : oldX A (oldEquiv (Sum.inr 0)) = e0_row (k + 1) := by
    funext j
    change FaithfulTables.X P A.tau (oldEquiv.symm (oldEquiv (Sum.inr 0))) j = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [hx, T_mat, Matrix.vecMul_add, Matrix.vecMul_one, e0_row_mul_N_mat, add_zero]

theorem counter_table (T1 T2 : ℕ) : Matrix.vecMul (counter (P := P)) (countTable A T1 T2) =
    e0_row (k + 1) := by
  have h : Matrix.vecMul (counter (P := P)) (countTable A T1 T2) =
      countTable A T1 T2 (gateway (P := P)) := by
    ext j
    exact gatewayCounter_dot _ _
  rw [h, count_gateway]

theorem word_terminal (T1 T2 q : ℕ) :
    ∃ pre, word A T1 T2 q = pre ++ [gateway (P := P)] := by
  refine ⟨FaithfulChronology.resetWord (count A T1 T2 q) ++
    ((FaithfulWindow.consecutiveWord P.word (A.tau * (q + 1)) (A.tau * (q + 1))).map
      (fun i => Sum.inl (oldEquiv (Sum.inl i)))), ?_⟩
  simp only [word, rotatedWord, old, FaithfulGateway.oldWord, List.map_append,
    List.map_singleton, List.map_map, List.append_assoc, gateway]
  rfl

/-- Marker one on the exact rotated word, before action reindexing. -/
theorem word_marker (T1 T2 q r : ℕ) (s : Act (P := P) → ℚ)
    (hr : r < (word A T1 T2 q).length) :
    1 ≤ FaithfulInheritance.scoreHeight base (wordScore (game A T1 T2) s ((word A T1 T2 q).take r)) -
      wordScore (game A T1 T2) s ((word A T1 T2 q).take r) base +
      dotProduct counter (wordCountVec ((word A T1 T2 q).drop r)) := by
  obtain ⟨pre, hp⟩ := word_terminal A T1 T2 q
  rw [hp] at hr ⊢
  rw [counter, gatewayCounter_dot]
  have hc := terminal_gateway_remaining pre gateway r hr
  have hm := FaithfulInheritance.le_scoreHeight base
    (wordScore (game A T1 T2) s ((pre ++ [gateway]).take r)) base
  linarith

theorem score_old_row (T1 T2 : ℕ) (i : FaithfulTables.OldAct P) :
    scoreTable A T1 T2 (Sum.inl (oldEquiv i)) =
      FaithfulTables.S_mid P A.tau (selectedGain A (lam A) T1) (baseline P)
        (FaithfulSynthesis.endpointMargin A (lam A) T1) i := by
  have hg := matrix_mul_rows oldEquiv oldEquiv (FaithfulTables.oldGame P) (FaithfulTables.X P A.tau)
  change (oldS A T1 + G (P := P) * oldX A) (oldEquiv i) = _
  change (rows oldEquiv (FaithfulTables.S P A.tau _ _ _) +
    matrix oldEquiv oldEquiv (FaithfulTables.oldGame P) * rows oldEquiv (FaithfulTables.X P A.tau)) _ = _
  rw [hg]
  funext j
  simp only [Matrix.add_apply, rows_apply, Equiv.symm_apply_apply]
  rfl

theorem score_gateway_row (T1 T2 : ℕ) :
    scoreTable A T1 T2 (gateway (P := P)) = zeta A T1 -
      (selectedGain A (lam A) T1 - FaithfulSynthesis.endpointMargin A (lam A) T1) • e0_row (k + 1) := by
  rw [gateway, score_old_row, FaithfulTables.S_mid_gateway_row]
  rfl

theorem gateway_base_coupling (T1 T2 : ℕ)
    (hv : FaithfulController.ValidParameters A T1 T2) :
    game A T1 T2 (gateway (P := P)) (base (P := P)) < 0 := by
  have h := (hv.coupling_signs (Sum.inr 0) 0).1
  have hm := FaithfulSynthesis.minimumWeight_pos A
  have he : (resetEquiv (k := k)).symm 0 = Sum.inl 0 := by
    apply resetEquiv.injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    rfl
  change coupling A T1 T2 (oldEquiv (Sum.inr 0)) 0 < 0
  simp only [coupling, Matrix.submatrix_apply, Equiv.symm_apply_apply, he]
  linarith

theorem support_safe (T1 T2 q : ℕ)
    (hv : FaithfulController.ValidParameters A T1 T2) :
    ∀ i, counter (P := P) i ≠ 0 →
      (scoreTable A T1 T2).mulVec (binomBasis (k + 1) q) i + game A T1 T2 i base - counter i <
      (scoreTable A T1 T2).mulVec (binomBasis (k + 1) q) base + game A T1 T2 base base - counter (P := P) (base (P := P)) := by
  apply gateway_support_safe (game A T1 T2) _ base gateway (by simp [base, gateway])
    (dotProduct (zeta A T1) (binomBasis (k + 1) q)) (selectedGain A (lam A) T1)
    (FaithfulSynthesis.endpointMargin A (lam A) T1)
  · change dotProduct (scoreTable A T1 T2 (Sum.inr 0)) _ = _
    rw [score_reset_zero]
  · change dotProduct (scoreTable A T1 T2 gateway) _ = _
    rw [score_gateway_row, sub_dotProduct, smul_dotProduct, e0_row_dot_binomBasis (by omega)]
    simp only [smul_eq_mul, mul_one]
    ring
  · exact skew_diag_zero (game_skew A T1 T2) base
  · exact hv.margin_lt_gain
  · exact gateway_base_coupling A T1 T2 hv


end Lift
end Karlin.FaithfulNextClock
