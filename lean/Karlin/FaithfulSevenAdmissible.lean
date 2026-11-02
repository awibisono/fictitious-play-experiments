import Karlin.FaithfulAdmissible
import Karlin.FaithfulSevenData
import Karlin.FaithfulSevenSeed

/-! The note's exact integer correction and positive weights, checked against
literal old tables before attaching them to the actual order-three Clock. -/
namespace Karlin.FaithfulSevenAdmissible
open scoped BigOperators Matrix
open FaithfulClock FaithfulTables FaithfulAdmissible FaithfulSevenData
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def correction : Fin 4 → ℤ := ![0, -6376, -12752, 0]
def oldX : Matrix (Fin 6 ⊕ Fin 1) (Fin 4) ℚ :=
  Matrix.fromRows (C_seven * F_tau_mat 3 1) (fun _ => e0_row 4)
def oldGame : Matrix (Fin 6 ⊕ Fin 1) (Fin 6 ⊕ Fin 1) ℚ :=
  Matrix.fromBlocks M_seven (fun i _ => -(M_seven 0 i + v_seven i))
    (fun _ j => M_seven 0 j + v_seven j) 0
def oldS : Matrix (Fin 6 ⊕ Fin 1) (Fin 4) ℚ :=
  Matrix.fromRows
    (R_seven * E_tau_mat 3 1 + outerProd (fun _ => 1)
      (Matrix.vecMul zeta_seven (B_mat 4) - Matrix.vecMul (R_seven 0) (E_tau_mat 3 1)))
    (fun _ : Fin 1 => Matrix.vecMul zeta_seven (B_mat 4) - Matrix.vecMul v_seven (C_seven * F_tau_mat 3 1))
def oldD := oldS * N_mat 4 - oldGame * oldX
def difference : Fin 4 → ℚ := Matrix.vecMul zeta_seven (B_mat 4) - zeta_seven

theorem reference_height : zeta (R_seven 0) 1 (1/2) 4 = zeta_seven := by
  decide +kernel

theorem actual_corrected_rhs : oldD.transpose * oldX -
    outerProd (fun j => (correction j : ℚ)) difference = RHS_seven := by
  decide +kernel

theorem literal_tests (h : ℕ) (hlo : 3 < h) (hhi : h ≤ 6) (he : Even h) :
    matInnerProd (Z_binom_concrete 4 h) RHS_seven = 0 := by
  obtain ⟨r, hr⟩ := he
  have hh : h = 4 ∨ h = 6 := by omega
  rcases hh with rfl | rfl <;> decide +kernel

theorem literal_cone : Matrix.vecMul (Sum.elim aP_seven (fun _ : Fin 1 => (15/2 : ℚ))) oldX =
    zeta_seven + Matrix.vecMul zeta_seven (B_mat 4) := by
  decide +kernel



/-- Identification with the tables of the actual constructed Clock, rather
than only an equality between the two displayed constant matrices. -/
theorem clock_corrected_rhs :
    (D FaithfulSevenSeed.sevenClock 1 (1/2) (baseline FaithfulSevenSeed.sevenClock) 0).transpose *
        X FaithfulSevenSeed.sevenClock 1 -
      outerProd (fun j => (correction j : ℚ))
        (psi (FaithfulSevenSeed.sevenClock.R FaithfulSevenSeed.sevenClock.b) 1 (1/2)
          (baseline FaithfulSevenSeed.sevenClock)) = RHS_seven := by
  decide +kernel

theorem clock_tests (h : ℕ) (hlo : 3 < h) (hhi : h ≤ 6) (he : Even h) :
    matInnerProd (Z_binom_concrete 4 h)
      ((D FaithfulSevenSeed.sevenClock 1 (1/2) (baseline FaithfulSevenSeed.sevenClock) 0).transpose *
          X FaithfulSevenSeed.sevenClock 1 -
        outerProd (fun j => (correction j : ℚ))
          (psi (FaithfulSevenSeed.sevenClock.R FaithfulSevenSeed.sevenClock.b) 1 (1/2)
            (baseline FaithfulSevenSeed.sevenClock))) = 0 := by
  rw [clock_corrected_rhs]
  exact literal_tests h hlo hhi he

theorem clock_cone :
    Matrix.vecMul (oldWeight FaithfulSevenSeed.sevenClock aP_seven (1/2))
      (X FaithfulSevenSeed.sevenClock 1) =
    zeta (FaithfulSevenSeed.sevenClock.R FaithfulSevenSeed.sevenClock.b) 1 (1/2)
      (baseline FaithfulSevenSeed.sevenClock) +
    Matrix.vecMul
      (zeta (FaithfulSevenSeed.sevenClock.R FaithfulSevenSeed.sevenClock.b) 1 (1/2)
        (baseline FaithfulSevenSeed.sevenClock)) (B_mat 4) := by
  decide +kernel

/-- A generic data match; all dynamical clock fields remain unrestricted. -/
structure DataMatch (P : Clock 3) : Prop where
  m : P.m = 6
  game : HEq P.A M_seven
  score : HEq P.R R_seven
  count : HEq P.C CInteger
  entry : HEq P.b (0 : Fin 6)
  counter : HEq P.v v_seven
  remainder : P.Arem = 1

/-- The literal witness works for any Clock with these recurrent tables. -/
def admissible_of_data (P : Clock 3) (h : DataMatch P) : Admissible P := by
  rcases h with ⟨hm, hA, hR, hC, hb, hv, hrem⟩
  cases P
  cases hm
  cases hA
  cases hR
  cases hC
  cases hb
  cases hv
  cases hrem
  refine { tau := 1
           tau_pos := by decide
           cref := 1/2
           cref_pos := by norm_num
           cref_lt_one := by norm_num
           ellStar := correction
           aP := aP_seven
           weights_pos := seven_admissible_weights.1
           higher_tests := ?_
           cone := ?_ }
  · intro h hlo hhi he
    exact clock_tests h hlo hhi he
  · exact clock_cone

/-- The fully constructed six-action recurrent Clock is admissible with the
note's scale one, fixed correction, and six strictly positive weights. -/
def sevenAdmissible : Admissible FaithfulSevenSeed.sevenClock where
  tau := 1
  tau_pos := by decide
  cref := 1/2
  cref_pos := by norm_num
  cref_lt_one := by norm_num
  ellStar := correction
  aP := aP_seven
  weights_pos := seven_admissible_weights.1
  higher_tests := clock_tests
  cone := clock_cone

@[simp] theorem sevenAdmissible_tau : sevenAdmissible.tau = 1 := rfl
@[simp] theorem sevenAdmissible_cref : sevenAdmissible.cref = 1/2 := rfl
@[simp] theorem sevenAdmissible_correction : sevenAdmissible.ellStar = correction := rfl
@[simp] theorem sevenAdmissible_weights : sevenAdmissible.aP = aP_seven := rfl

/-- The displayed E is a solution for the actual constructed clock's tables. -/
theorem clock_moment_solution : E_seven - E_seven.transpose * B_mat 4 =
    (D FaithfulSevenSeed.sevenClock 1 (1/2) (baseline FaithfulSevenSeed.sevenClock) 0).transpose *
        X FaithfulSevenSeed.sevenClock 1 -
      outerProd (fun j => (correction j : ℚ))
        (psi (FaithfulSevenSeed.sevenClock.R FaithfulSevenSeed.sevenClock.b) 1 (1/2)
          (baseline FaithfulSevenSeed.sevenClock)) := by
  rw [clock_corrected_rhs, show B_mat 4 = B4 by decide +kernel]
  exact seven_moment_equation

#print axioms actual_corrected_rhs
#print axioms clock_corrected_rhs
#print axioms admissible_of_data
#print axioms sevenAdmissible
#print axioms clock_moment_solution

end Karlin.FaithfulSevenAdmissible
