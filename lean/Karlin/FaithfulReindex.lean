import Karlin.FaithfulClock
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Action reindexing for the literal v15 game and tables.
All results concern the given matrices and words; no Clock or realized lift is assumed. -/

namespace Karlin.FaithfulReindex

open scoped BigOperators
open Matrix

variable {α β γ α' β' γ' : Type*}

def vec {R : Type*} (e : α ≃ α') (v : α → R) : α' → R := fun i => v (e.symm i)

def matrix {R : Type*} (e : α ≃ α') (f : β ≃ β') (M : Matrix α β R) : Matrix α' β' R :=
  fun i j => M (e.symm i) (f.symm j)

def rows {R : Type*} (e : α ≃ α') (M : Matrix α β R) : Matrix α' β R :=
  fun i j => M (e.symm i) j

@[simp] theorem vec_apply {R : Type*} (e : α ≃ α') (v : α → R) (i : α') :
    vec e v i = v (e.symm i) := rfl

@[simp] theorem matrix_apply {R : Type*} (e : α ≃ α') (f : β ≃ β')
    (M : Matrix α β R) (i : α') (j : β') :
    matrix e f M i j = M (e.symm i) (f.symm j) := rfl

@[simp] theorem rows_apply {R : Type*} (e : α ≃ α') (M : Matrix α β R)
    (i : α') (j : β) : rows e M i j = M (e.symm i) j := rfl

@[simp] theorem matrix_transpose {R : Type*} (e : α ≃ α') (f : β ≃ β')
    (M : Matrix α β R) : (matrix e f M)ᵀ = matrix f e Mᵀ := rfl

theorem matrix_mul [Fintype β] [Fintype β']
    (e : α ≃ α') (f : β ≃ β') (g : γ ≃ γ')
    (M : Matrix α β ℚ) (N : Matrix β γ ℚ) :
    matrix e f M * matrix f g N = matrix e g (M * N) := by
  ext i j
  simp only [Matrix.mul_apply, matrix]
  exact Equiv.sum_comp f.symm (fun a => M (e.symm i) a * N a (g.symm j))

theorem matrix_mulVec [Fintype β] [Fintype β']
    (e : α ≃ α') (f : β ≃ β') (M : Matrix α β ℚ) (v : β → ℚ) :
    (matrix e f M).mulVec (vec f v) = vec e (M.mulVec v) := by
  ext i
  exact Equiv.sum_comp f.symm (fun j => M (e.symm i) j * v j)

@[simp] theorem rows_mulVec [Fintype β] (e : α ≃ α')
    (M : Matrix α β ℚ) (v : β → ℚ) :
    (rows e M).mulVec v = vec e (M.mulVec v) := rfl

theorem vecMul_rows [Fintype α] [Fintype α'] (e : α ≃ α')
    (v : α → ℚ) (M : Matrix α β ℚ) :
    Matrix.vecMul (vec e v) (rows e M) = Matrix.vecMul v M := by
  ext j
  exact Equiv.sum_comp e.symm (fun i => v i * M i j)

theorem dotProduct_vec [Fintype α] [Fintype α'] (e : α ≃ α') (u v : α → ℚ) :
    dotProduct (vec e u) (vec e v) = dotProduct u v :=
  Equiv.sum_comp e.symm (fun i => u i * v i)

@[simp] theorem rows_mul [Fintype β] (e : α ≃ α')
    (M : Matrix α β ℚ) (N : Matrix β γ ℚ) :
    rows e M * N = rows e (M * N) := rfl

theorem matrix_mul_rows [Fintype β] [Fintype β']
    (e : α ≃ α') (f : β ≃ β') (M : Matrix α β ℚ) (N : Matrix β γ ℚ) :
    matrix e f M * rows f N = rows e (M * N) :=
  matrix_mul e f (Equiv.refl γ) M N

theorem transpose_rows_mul_rows [Fintype α] [Fintype α']
    (e : α ≃ α') (M : Matrix α β ℚ) (N : Matrix α γ ℚ) :
    (rows e M)ᵀ * rows e N = Mᵀ * N := by
  ext i j
  exact Equiv.sum_comp e.symm (fun a => M a i * N a j)

theorem skew (e : α ≃ α') {M : Matrix α α ℚ} (hM : IsSkewSymmetric M) :
    IsSkewSymmetric (matrix e e M) := fun i j => hM (e.symm i) (e.symm j)

theorem rows_full_column_rank [Fintype β] (e : α ≃ α') (C : Matrix α β ℚ)
    (hC : Function.Injective C.mulVec) : Function.Injective (rows e C).mulVec := by
  intro x y hxy
  apply hC
  funext i
  simpa only [rows_mulVec, vec_apply, Equiv.symm_apply_apply] using congrFun hxy (e i)

@[simp] theorem rows_intCast (e : α ≃ α') (C : Matrix α β ℤ) :
    (fun i j => ((rows e C i j : ℤ) : ℚ)) = rows e (fun i j => (C i j : ℚ)) := rfl

theorem clock_equation [Fintype α] [Fintype α'] [Fintype β]
    (e : α ≃ α') (A : Matrix α α ℚ) (C R : Matrix α β ℚ)
    (N : Matrix β β ℚ) (h : A * C = R * N) :
    matrix e e A * rows e C = rows e R * N := by
  rw [matrix_mul_rows, rows_mul, h]

theorem counts [DecidableEq α] [DecidableEq α'] [Fintype β]
    (e : α ≃ α') (W : List α) (C : Matrix α β ℚ) (p : β → ℚ)
    (h : wordCountVec W = C.mulVec p) :
    wordCountVec (W.map e) = (rows e C).mulVec p := by
  funext i
  rw [wordCountVec_map_equiv, h]
  rfl

theorem wordScore_eq [Fintype α] [Fintype α'] [DecidableEq α] [DecidableEq α']
    (e : α ≃ α') (A : Matrix α α ℚ) (s : α → ℚ) (W : List α) :
    wordScore (matrix e e A) (vec e s) (W.map e) = vec e (wordScore A s W) := by
  funext i
  exact wordScore_map_equiv e A s W i

theorem priority_valid [Fintype α] [Fintype α'] [DecidableEq α] [DecidableEq α']
    {r : ℕ} (e : α ≃ α') (A : Matrix α α ℚ) (s : α → ℚ)
    (rank : α → Fin r) (W : List α) (hW : IsValidPriorityWord A s rank W) :
    IsValidPriorityWord (matrix e e A) (vec e s) (vec e rank) (W.map e) :=
  isValidPriorityWord_map_equiv e A s rank W hW

@[simp] theorem rows_fromRows (e : α ≃ α') (f : β ≃ β')
    (U : Matrix α γ ℚ) (V : Matrix β γ ℚ) :
    rows (Equiv.sumCongr e f) (Matrix.fromRows U V) =
      Matrix.fromRows (rows e U) (rows f V) := by
  ext i j
  cases i <;> rfl

/-- The maximum is unchanged, with nonemptiness witnessed by the same action. -/
theorem maximum_eq [Fintype α] [Fintype α'] (e : α ≃ α') (b : α) (s : α → ℚ) :
    Finset.univ.sup' ⟨e b, Finset.mem_univ (e b)⟩ (vec e s) =
      Finset.univ.sup' ⟨b, Finset.mem_univ b⟩ s := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun i _ => Finset.le_sup' s (Finset.mem_univ (e.symm i)))
  · apply Finset.sup'_le _ _
    intro i _
    simpa only [vec_apply, Equiv.symm_apply_apply] using
      (Finset.le_sup' (vec e s) (Finset.mem_univ (e i)))

/-- The anchored finite maximum becomes the exact height used in Clock fields. -/
theorem height_to_fin [Fintype α] {m : ℕ} (e : α ≃ Fin m) (b : α) (s : α → ℚ) :
    FaithfulClock.height (e b) (vec e s) = Finset.univ.sup' ⟨b, Finset.mem_univ b⟩ s :=
  maximum_eq e b s

/-- The full lifted payoff matrix commutes with separate old/reset action reindexing. -/
theorem liftedGameMat_sumCongr (e : α ≃ α') (f : β ≃ β')
    (G : Matrix α α ℚ) (P : Matrix α β ℚ) (J : Matrix β β ℚ) :
    matrix (Equiv.sumCongr e f) (Equiv.sumCongr e f) (liftedGameMat G P J) =
      liftedGameMat (matrix e e G) (matrix e f P) (matrix f f J) := by
  ext i j
  cases i <;> cases j <;> rfl

theorem liftedCountMat_sumCongr [Fintype γ] [DecidableEq γ]
    (e : α ≃ α') (f : β ≃ β')
    (X : Matrix α γ ℚ) (M : Matrix β γ ℚ) (N : Matrix γ γ ℚ) :
    rows (Equiv.sumCongr e f) (liftedCountMat X M N) =
      liftedCountMat (rows e X) (rows f M) N := by
  ext i j
  cases i <;> rfl

theorem liftedScoreMat_sumCongr [Fintype α] [Fintype α'] [Fintype β] [Fintype β']
    (e : α ≃ α') (f : β ≃ β') (G : Matrix α α ℚ) (J : Matrix β β ℚ)
    (S X : Matrix α γ ℚ) (M : Matrix β γ ℚ) (zeta : γ → ℚ) :
    rows (Equiv.sumCongr e f) (liftedScoreMat G J S X M zeta) =
      liftedScoreMat (matrix e e G) (matrix f f J) (rows e S) (rows e X) (rows f M) zeta := by
  have hg := matrix_mul_rows e e G X
  have hj := matrix_mul_rows f f J M
  ext i j
  cases i with
  | inl i =>
    change S (e.symm i) j + (G * X) (e.symm i) j =
      S (e.symm i) j + (matrix e e G * rows e X) i j
    rw [hg]
    rfl
  | inr i =>
    change zeta j - (J * M) (f.symm i) j =
      zeta j - (matrix f f J * rows f M) i j
    rw [hj]
    rfl

theorem rows_V_reset [Fintype α] [Fintype α'] [Fintype β]
    (e : α ≃ α') (J : Matrix α α ℚ) (M : Matrix α β ℚ)
    (B : Matrix β β ℚ) (zeta : β → ℚ) :
    rows e (V_reset J M B zeta) = V_reset (matrix e e J) (rows e M) B zeta := by
  unfold V_reset
  rw [matrix_transpose, matrix_mul_rows, rows_mul]
  rfl

theorem rows_Q_reset [Fintype α] [Fintype α'] [Fintype β]
    (e : α ≃ α') (J : Matrix α α ℚ) (M : Matrix α β ℚ)
    (B : Matrix β β ℚ) (zeta : β → ℚ) :
    rows e (Q_reset J M B zeta) = Q_reset (matrix e e J) (rows e M) B zeta := by
  unfold Q_reset
  rw [matrix_transpose, matrix_mul_rows, matrix_mul_rows, rows_mul]
  rfl

theorem rows_D_deficit [Fintype α] [Fintype α'] [Fintype β]
    (e : α ≃ α') (G : Matrix α α ℚ) (S X : Matrix α β ℚ) (N : Matrix β β ℚ) :
    rows e (D_deficit G S X N) = D_deficit (matrix e e G) (rows e S) (rows e X) N := by
  unfold D_deficit
  rw [matrix_mul_rows, rows_mul]
  rfl

/-- Both exact coupling equations hold after the same independent block reindexings. -/
theorem coupling_equations [Fintype α] [Fintype α'] [Fintype β] [Fintype β']
    (e : α ≃ α') (f : β ≃ β') (P : Matrix α β ℚ)
    (M Q : Matrix β γ ℚ) (X D : Matrix α γ ℚ)
    (hPM : P * M = D) (hPTX : Pᵀ * X = Q) :
    matrix e f P * rows f M = rows e D ∧
      (matrix e f P)ᵀ * rows e X = rows f Q := by
  constructor
  · rw [matrix_mul_rows, hPM]
  · rw [matrix_transpose, matrix_mul_rows, hPTX]

end Karlin.FaithfulReindex
