import Karlin.FaithfulTables

/-! The literal additional data of v15 Definition `def:admissible`.
The positive-weight condition uses the paper's equivalent old-block cone identity.
The reference baseline is fixed from the parent's suffix constant before any scale.
-/

namespace Karlin.FaithfulAdmissible

open FaithfulClock
open scoped BigOperators

def baseline {k : ℕ} (P : Clock k) : ℚ := P.Arem + 3

def oldWeight {k : ℕ} (P : Clock k) (aP : Fin P.m → ℚ) (cref : ℚ) :
    FaithfulTables.OldAct P → ℚ :=
  Sum.elim aP (fun _ => 2 * baseline P - cref)

structure Admissible {k : ℕ} (P : Clock k) where
  tau : ℕ
  tau_pos : 1 ≤ tau
  cref : ℚ
  cref_pos : 0 < cref
  cref_lt_one : cref < 1
  ellStar : Fin (k + 1) → ℤ
  aP : Fin P.m → ℚ
  weights_pos : ∀ i, 0 < aP i
  higher_tests : ∀ h : ℕ, k < h → h ≤ 2 * k → Even h →
    matInnerProd (Z_binom_concrete (k + 1) h)
      ((FaithfulTables.D P tau cref (baseline P) 0).transpose * FaithfulTables.X P tau -
        outerProd (fun i => (ellStar i : ℚ))
          (FaithfulTables.psi (P.R P.b) tau cref (baseline P))) = 0
  cone : Matrix.vecMul (oldWeight P aP cref) (FaithfulTables.X P tau) =
    FaithfulTables.zeta (P.R P.b) tau cref (baseline P) +
      Matrix.vecMul (FaithfulTables.zeta (P.R P.b) tau cref (baseline P)) (B_mat (k + 1))

namespace Admissible

variable {k : ℕ} {P : Clock k} (D : Admissible P)

def correction : Fin (k + 1) → ℚ := fun i => (D.ellStar i : ℚ)

def weights : FaithfulTables.OldAct P → ℚ := oldWeight P D.aP D.cref

def referenceHeight : Fin (k + 1) → ℚ :=
  FaithfulTables.zeta (P.R P.b) D.tau D.cref (baseline P)

theorem weights_positive (i : FaithfulTables.OldAct P) : 0 < D.weights i := by
  cases i with
  | inl i => exact D.weights_pos i
  | inr i =>
      change 0 < 2 * (P.Arem + 3) - D.cref
      have := P.remainder_nonneg
      have := D.cref_lt_one
      linarith

/-- The endpoint reference weight exceeds the entire waiting reserve. -/
theorem gateway_weight_margin : P.Arem + 1 < D.weights (Sum.inr 0) := by
  change P.Arem + 1 < 2 * (P.Arem + 3) - D.cref
  have := P.remainder_nonneg
  have := D.cref_lt_one
  linarith

theorem reference_leading_pos : 0 < D.referenceHeight (Fin.last k) := by
  apply FaithfulTables.zeta_leading_pos P.order_ge_two (P.R P.b) D.tau
  · have := D.tau_pos
    omega
  · exact P.leading_height

theorem reference_cone : Matrix.vecMul D.weights (FaithfulTables.X P D.tau) =
    D.referenceHeight + Matrix.vecMul D.referenceHeight (B_mat (k + 1)) := D.cone

end Admissible

end Karlin.FaithfulAdmissible
