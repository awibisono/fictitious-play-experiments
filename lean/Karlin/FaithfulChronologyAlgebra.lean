import Karlin.FaithfulChronology
import Karlin.FaithfulResetEquations

/-! Score identities for the literal old/reset stages, independent of validity
and signs. All count equalities refer to the same actual words. -/
namespace Karlin.FaithfulChronologyAlgebra
open scoped BigOperators Matrix
set_option maxHeartbeats 1200000

theorem one_zeta_eq_outer {n w : Type*} (zeta : w → ℚ) :
    one_zeta n zeta = outerProd (fun _ => 1) zeta := by
  ext i j
  simp [one_zeta, outerProd]

def rawEntry {m n w : Type*} [Fintype n] [Fintype w]
    (S : Matrix m w ℚ) (J : Matrix n n ℚ) (M : Matrix n w ℚ)
    (B : Matrix w w ℚ) (zeta : w → ℚ) :=
  Matrix.fromRows S (V_reset J M B zeta)

def rotatedEntry {m n w : Type*} [Fintype m] [Fintype n]
    (G : Matrix m m ℚ) (S X : Matrix m w ℚ) (J : Matrix n n ℚ)
    (M : Matrix n w ℚ) (zeta : w → ℚ) :=
  Matrix.fromRows (S + G * X) (outerProd (fun _ => 1) zeta - J * M)

/-- Backward binomial evaluation of the entrance reset scores. -/
theorem V_reset_eval_succ {n : Type*} [Fintype n] {w : ℕ}
    (J : Matrix n n ℚ) (M : Matrix n (Fin w) ℚ) (zeta : Fin w → ℚ)
    (q : ℕ) (j : n) :
    (V_reset J M (B_mat w) zeta).mulVec (binomBasis w (q + 1)) j =
      dotProduct zeta (binomBasis w q) -
        Jᵀ.mulVec (M.mulVec (binomBasis w q)) j := by
  simp only [V_reset, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    B_mat_mulVec_binomBasis, Pi.sub_apply]
  rfl

theorem V_reset_eval_previous {n : Type*} [Fintype n] {w : ℕ}
    (J : Matrix n n ℚ) (M : Matrix n (Fin w) ℚ) (zeta : Fin w → ℚ)
    (q : ℕ) (hq : 1 ≤ q) (j : n) :
    (V_reset J M (B_mat w) zeta).mulVec (binomBasis w q) j =
      dotProduct zeta (binomBasis w (q - 1)) -
        Jᵀ.mulVec (M.mulVec (binomBasis w (q - 1))) j := by
  have hh := V_reset_eval_succ J M zeta (q - 1) j
  simpa only [Nat.sub_add_cancel hq] using hh

theorem V_reset_eval_le_previous {n : Type*} [Fintype n] {w : ℕ}
    (J : Matrix n n ℚ) (M : Matrix n (Fin w) ℚ) (zeta : Fin w → ℚ)
    (q : ℕ) (hq : 1 ≤ q) (hJ : ∀ i j, 0 ≤ J i j)
    (hM : ∀ j, 0 ≤ M.mulVec (binomBasis w (q - 1)) j) (j : n) :
    (V_reset J M (B_mat w) zeta).mulVec (binomBasis w q) j ≤
      dotProduct zeta (binomBasis w (q - 1)) := by
  rw [V_reset_eval_previous J M zeta q hq]
  have hh : 0 ≤ Jᵀ.mulVec (M.mulVec (binomBasis w (q - 1))) j :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hJ i j) (hM i))
  linarith

/-- The reset entrance decomposes into its post-old score plus the old-count
coupling. This is exactly the identity used in backwards waiting estimates. -/
theorem V_reset_initial_identity {m n w : Type*} [Fintype m] [Fintype n] [Fintype w]
    (C : Matrix m n ℚ) (X : Matrix m w ℚ) (J : Matrix n n ℚ)
    (M : Matrix n w ℚ) (B : Matrix w w ℚ) (zeta v : w → ℚ)
    (hCX : Cᵀ * X = Q_reset J M B zeta) (j : n) :
    (V_reset J M B zeta).mulVec v j =
      dotProduct zeta v - (J * M).mulVec v j + (Cᵀ * X).mulVec v j := by
  have h := congrArg (fun A : Matrix n w ℚ => A.mulVec v j)
    (rotated_reset_score_identity J M B zeta)
  simp only [Matrix.sub_mulVec, Pi.sub_apply] at h
  rw [hCX]
  change (V_reset J M B zeta).mulVec v j - (Q_reset J M B zeta).mulVec v j =
    dotProduct zeta v - (J * M).mulVec v j at h
  linarith

theorem post_old {m n w : Type*} [Fintype m] [Fintype n] [Fintype w]
    [DecidableEq m] [DecidableEq n]
    (G : Matrix m m ℚ) (C : Matrix m n ℚ) (J : Matrix n n ℚ)
    (S X : Matrix m w ℚ) (M : Matrix n w ℚ) (B : Matrix w w ℚ)
    (zeta v : w → ℚ) (W : List m) (hcount : wordCountVec W = X.mulVec v)
    (hCX : Cᵀ * X = Q_reset J M B zeta) :
    wordScore (liftedGameMat G C J) ((rawEntry S J M B zeta).mulVec v) (W.map Sum.inl) =
      (rotatedEntry G S X J M zeta).mulVec v := by
  funext i
  cases i with
  | inl i =>
      rw [liftedGameMat, wordScore_map_inl_old]
      change S.mulVec v i + G.mulVec (wordCountVec W) i = (S + G * X).mulVec v i
      rw [hcount, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
      rfl
  | inr j =>
      rw [liftedGameMat, wordScore_map_inl_new]
      change (V_reset J M B zeta).mulVec v j - Cᵀ.mulVec (wordCountVec W) j =
        (outerProd (fun _ => 1) zeta - J * M).mulVec v j
      rw [hcount, Matrix.mulVec_mulVec, hCX, ← Pi.sub_apply, ← Matrix.sub_mulVec,
        rotated_reset_score_identity, one_zeta_eq_outer]

theorem raw_clock_equation {m n w : Type*} [Fintype m] [Fintype n] [Fintype w]
    [DecidableEq w]
    (G : Matrix m m ℚ) (C : Matrix m n ℚ) (J : Matrix n n ℚ)
    (S X : Matrix m w ℚ) (M : Matrix n w ℚ) (B N : Matrix w w ℚ) (zeta : w → ℚ)
    (hBT : B * (1 + N) = 1) (hCM : C * M = S * N - G * X)
    (hCX : Cᵀ * X = Q_reset J M B zeta) :
    liftedGameMat G C J * Matrix.fromRows X M = rawEntry S J M B zeta * N := by
  obtain ⟨ho, hr⟩ := (reset_identity_iff G C J S X M B N zeta hBT).mpr ⟨hCM, hCX⟩
  rw [liftedGameMat, rawEntry, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, ho, hr]

theorem raw_word_count {m n w : Type*} [Fintype m] [Fintype n] [Fintype w]
    [DecidableEq m] [DecidableEq n]
    (X : Matrix m w ℚ) (M : Matrix n w ℚ) (v : w → ℚ)
    (WO : List m) (WR : List (m ⊕ n))
    (hO : wordCountVec WO = X.mulVec v)
    (hR : wordCountVec WR = Sum.elim (fun _ => 0) (M.mulVec v)) :
    wordCountVec (WO.map Sum.inl ++ WR) = (Matrix.fromRows X M).mulVec v := by
  funext i
  rw [wordCountVec_append, hR]
  cases i with
  | inl i => simp only [wordCountVec_map_inl_inl, Sum.elim_inl, add_zero,
      Matrix.fromRows_mulVec]; exact congrFun hO i
  | inr i => simp only [wordCountVec_map_inl_inr, Sum.elim_inr, zero_add,
      Matrix.fromRows_mulVec]

theorem raw_end {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {w : ℕ}
    (G : Matrix m m ℚ) (C : Matrix m n ℚ) (J : Matrix n n ℚ)
    (S X : Matrix m (Fin w) ℚ) (M : Matrix n (Fin w) ℚ) (zeta : Fin w → ℚ)
    (q : ℕ) (WO : List m) (WR : List (m ⊕ n))
    (hO : wordCountVec WO = X.mulVec (binomBasis w q))
    (hR : wordCountVec WR = Sum.elim (fun _ => 0) (M.mulVec (binomBasis w q)))
    (hCM : C * M = S * N_mat w - G * X)
    (hCX : Cᵀ * X = Q_reset J M (B_mat w) zeta) :
    wordScore (liftedGameMat G C J) ((rawEntry S J M (B_mat w) zeta).mulVec (binomBasis w q))
      (WO.map Sum.inl ++ WR) = (rawEntry S J M (B_mat w) zeta).mulVec (binomBasis w (q + 1)) := by
  unfold wordScore
  rw [raw_word_count X M _ WO WR hO hR]
  exact clock_phase_transition _ _ _
    (raw_clock_equation G C J S X M (B_mat w) (N_mat w) zeta (B_mat_mul_T_mat w).1 hCM hCX) q

theorem post_reset {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {w : ℕ}
    (G : Matrix m m ℚ) (C : Matrix m n ℚ) (J : Matrix n n ℚ)
    (S X : Matrix m (Fin w) ℚ) (M : Matrix n (Fin w) ℚ) (zeta : Fin w → ℚ)
    (q : ℕ) (WO : List m) (WR : List (m ⊕ n))
    (hO : wordCountVec WO = X.mulVec (binomBasis w q))
    (hR : wordCountVec WR = Sum.elim (fun _ => 0) (M.mulVec (binomBasis w q)))
    (hCM : C * M = S * N_mat w - G * X)
    (hCX : Cᵀ * X = Q_reset J M (B_mat w) zeta) :
    wordScore (liftedGameMat G C J) ((rotatedEntry G S X J M zeta).mulVec (binomBasis w q)) WR =
      (rawEntry S J M (B_mat w) zeta).mulVec (binomBasis w (q + 1)) := by
  have h := raw_end G C J S X M zeta q WO WR hO hR hCM hCX
  rw [wordScore_append, post_old G C J S X M (B_mat w) zeta _ WO hO hCX] at h
  exact h

#print axioms V_reset_eval_le_previous
#print axioms V_reset_initial_identity
#print axioms post_old
#print axioms raw_end
#print axioms post_reset
end Karlin.FaithfulChronologyAlgebra
