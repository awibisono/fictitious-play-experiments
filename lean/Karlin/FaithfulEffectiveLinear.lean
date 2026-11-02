import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Logic.Encodable.Pi
import Mathlib.Data.Rat.Encodable

/-! Executable finite rational search for a fixed linear section. The search
predicate is a finite family of rational equalities. Its existence proof is
erased at runtime; no classical choice is used to select runtime data. -/
namespace Karlin.FaithfulEffectiveLinear
open scoped BigOperators Matrix

abbrev Mat (w : ℕ) := Matrix (Fin w) (Fin w) ℚ
abbrev Coeff (w : ℕ) := Fin w → Fin w → Fin w → Fin w → ℚ

instance (w : ℕ) : Encodable (Coeff w) := inferInstanceAs (Encodable
  (Fin w → Fin w → Fin w → Fin w → ℚ))

def unit (w : ℕ) (i j : Fin w) : Mat w :=
  fun a b => if a = i ∧ b = j then 1 else 0

theorem expansion {w : ℕ} (F : Mat w) :
    (∑ i, ∑ j, F i j • unit w i j) = F := by
  ext a b
  simp [unit, ite_and, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_ite]

def operator {w : ℕ} (C : Coeff w) : Mat w →ₗ[ℚ] Mat w where
  toFun F a b := ∑ i, ∑ j, C a b i j * F i j
  map_add' F G := by
    ext a b
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c F := by
    ext a b
    simp only [RingHom.id_apply, Matrix.smul_apply, smul_eq_mul]
    simp_rw [← mul_assoc, mul_comm (C a b _ _) c, mul_assoc]
    simp only [← Finset.mul_sum]

def coefficients {w : ℕ} (S : Mat w →ₗ[ℚ] Mat w) : Coeff w :=
  fun a b i j => S (unit w i j) a b

theorem operator_coefficients {w : ℕ} (S : Mat w →ₗ[ℚ] Mat w) :
    operator (coefficients S) = S := by
  apply LinearMap.ext
  intro F
  conv_rhs => rw [← expansion F]
  simp only [map_sum, map_smul]
  ext a b
  simp only [operator, coefficients, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

def Certificate {w : ℕ} (L : Mat w →ₗ[ℚ] Mat w) (C : Coeff w) : Prop :=
  ∀ i j, L (operator C (L (unit w i j))) = L (unit w i j)

instance {w : ℕ} (L : Mat w →ₗ[ℚ] Mat w) : DecidablePred (Certificate L) :=
  fun C => decidable_of_iff (∀ i j : Fin w,
    ∀ a b : Fin w, L (operator C (L (unit w i j))) a b = L (unit w i j) a b)
    (by
      constructor
      · intro h i j; ext a b; exact h i j a b
      · intro h i j a b; exact congrFun (congrFun (h i j) a) b)

theorem certificate_exists {w : ℕ} (L : Mat w →ₗ[ℚ] Mat w)
    (h : ∃ S : Mat w →ₗ[ℚ] Mat w, ∀ F ∈ LinearMap.range L, L (S F) = F) :
    ∃ C : Coeff w, Certificate L C := by
  obtain ⟨S, hS⟩ := h
  refine ⟨coefficients S, ?_⟩
  intro i j
  rw [operator_coefficients]
  exact hS _ ⟨unit w i j, rfl⟩

def sectionCoefficients {w : ℕ} (L : Mat w →ₗ[ℚ] Mat w)
    (h : ∃ S : Mat w →ₗ[ℚ] Mat w, ∀ F ∈ LinearMap.range L, L (S F) = F) : Coeff w :=
  Encodable.choose (certificate_exists L h)

def linearSection {w : ℕ} (L : Mat w →ₗ[ℚ] Mat w)
    (h : ∃ S : Mat w →ₗ[ℚ] Mat w, ∀ F ∈ LinearMap.range L, L (S F) = F) :
    Mat w →ₗ[ℚ] Mat w := operator (sectionCoefficients L h)

theorem section_certificate {w : ℕ} (L : Mat w →ₗ[ℚ] Mat w)
    (h : ∃ S : Mat w →ₗ[ℚ] Mat w, ∀ F ∈ LinearMap.range L, L (S F) = F) :
    ∀ i j, L (linearSection L h (L (unit w i j))) = L (unit w i j) :=
  Encodable.choose_spec (certificate_exists L h)

theorem section_on_range {w : ℕ} (L : Mat w →ₗ[ℚ] Mat w)
    (h : ∃ S : Mat w →ₗ[ℚ] Mat w, ∀ F ∈ LinearMap.range L, L (S F) = F)
    (F : Mat w) (hF : F ∈ LinearMap.range L) : L (linearSection L h F) = F := by
  obtain ⟨E, rfl⟩ := hF
  conv_lhs => rw [← expansion E]
  simp only [map_sum, map_smul]
  simp_rw [section_certificate]
  simpa only [map_sum, map_smul] using congrArg L (expansion E)

end Karlin.FaithfulEffectiveLinear
