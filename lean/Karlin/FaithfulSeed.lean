import Karlin.FaithfulClock

/-!
# The literal v15 RPS seed

This constructs all fields of the order-two clock on the paper's exact RPS
matrix, coefficient tables and three-run phase words. In particular the suffix
constant is one, fixed before epsilon, and its threshold rule is the constant one.
-/

namespace Karlin.FaithfulSeed

open scoped BigOperators
open FaithfulClock

/-- The manuscript's integer count table, before its rational cast. -/
def C2Integer : Matrix (Fin 3) (Fin 2) ℤ := !![5, 3; 6, 3; 7, 3]

theorem ratCount_C2Integer : ratCount C2Integer = C2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem C2_mulVec_injective : Function.Injective (fun x : Fin 2 → ℚ => C2.mulVec x) := by
  intro x y hxy
  have h0 := congr_fun hxy 0
  have h1 := congr_fun hxy 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, C2] at h0 h1
  funext i
  fin_cases i
  · change x 0 = y 0
    linarith
  · change x 1 = y 1
    linarith

theorem rps_height (q : ℕ) :
    height (0 : Fin 3) (R2.mulVec (binomBasis 2 q)) = (q : ℚ) + 1 := by
  have h := height_eq (0 : Fin 3) (R2.mulVec (binomBasis 2 q)) 0
    (rps_leader_dom_all q)
  rw [h, ← r2Vec_eq_R2_mulVec]
  rfl

theorem rps_word_transition (q : ℕ) :
    wordScore A_RPS (R2.mulVec (binomBasis 2 q)) (rpsPhaseWord q) =
      R2.mulVec (binomBasis 2 (q + 1)) := by
  unfold wordScore
  rw [wordCountVec_rpsPhaseWord]
  exact clock_phase_transition A_RPS R2 C2 rpsAlgebraicClock.hclock q

theorem rps_word_begins_twice (q : ℕ) :
    ∃ tail, rpsPhaseWord q = (0 : Fin 3) :: 0 :: tail := by
  refine ⟨List.replicate (3 * q + 3) 0 ++
    List.replicate (3 * q + 6) 1 ++ List.replicate (3 * q + 7) 2, ?_⟩
  unfold rpsPhaseWord
  have he : 3 * q + 5 = (3 * q + 3) + 1 + 1 := by omega
  rw [he]
  simp only [List.replicate_succ, List.cons_append]

theorem rps_counter_remaining (q r : ℕ) (hr : r < (rpsPhaseWord q).length) :
    1 ≤ dotProduct v_RPS (wordCountVec ((rpsPhaseWord q).drop r)) := by
  have hp := rpsPhaseWord_take_v_dot_nonpos q r hr
  change dotProduct v_RPS (wordCountVec ((rpsPhaseWord q).take r)) ≤ 0 at hp
  have hsplit : dotProduct v_RPS (wordCountVec ((rpsPhaseWord q).take r)) +
      dotProduct v_RPS (wordCountVec ((rpsPhaseWord q).drop r)) = 1 := by
    calc
      _ = ∑ i, v_RPS i * (wordCountVec ((rpsPhaseWord q).take r) i +
          wordCountVec ((rpsPhaseWord q).drop r) i) := by
        simp only [dotProduct, mul_add, Finset.sum_add_distrib]
      _ = dotProduct v_RPS (wordCountVec (rpsPhaseWord q)) := by
        unfold dotProduct
        apply Finset.sum_congr rfl
        intro i _
        rw [wordCountVec_take_add_drop]
      _ = 1 := by
        rw [wordCountVec_rpsPhaseWord]
        exact clock_endpoint_increment_eq_one (by decide) v_RPS C2 rpsAlgebraicClock.hvC q
  linarith

theorem rps_marker (q r : ℕ) (hr : r < (rpsPhaseWord q).length) :
    1 ≤ height (0 : Fin 3)
        (wordScore A_RPS (R2.mulVec (binomBasis 2 q)) ((rpsPhaseWord q).take r)) -
      wordScore A_RPS (R2.mulVec (binomBasis 2 q)) ((rpsPhaseWord q).take r) 0 +
      dotProduct v_RPS (wordCountVec ((rpsPhaseWord q).drop r)) := by
  have hh := le_height (0 : Fin 3)
    (wordScore A_RPS (R2.mulVec (binomBasis 2 q)) ((rpsPhaseWord q).take r)) 0
  linarith [rps_counter_remaining q r hr]

theorem rps_support_safe (q : ℕ) (hq : 1 ≤ q) (i : Fin 3) (hi : v_RPS i ≠ 0) :
    R2.mulVec (binomBasis 2 q) i + A_RPS i 0 - v_RPS i <
      R2.mulVec (binomBasis 2 q) 0 + A_RPS 0 0 - v_RPS 0 := by
  rw [← r2Vec_eq_R2_mulVec]
  have hs := rps_entry_support_safety (q := (q : ℚ)) (by exact_mod_cast hq)
  fin_cases i <;> norm_num [r2Vec, A_RPS, v_RPS] at * <;> linarith

/-- Fixed-A form of the seed suffix bound, including the complete prefix. -/
theorem rps_suffix (eps : ℚ) (heps : 0 < eps) (q r : ℕ)
    (hr : r ≤ (rpsPhaseWord q).length) :
    height (0 : Fin 3) (R2.mulVec (binomBasis 2 (q + 1))) -
      height (0 : Fin 3)
        (wordScore A_RPS (R2.mulVec (binomBasis 2 q)) ((rpsPhaseWord q).take r)) ≤
      eps * ((rpsPhaseWord q).length - r : ℕ) + 1 := by
  rcases lt_or_eq_of_le hr with hr | rfl
  · have ha := rps_active_score_ge_sigma_add_one q r hr
    have hh := le_height (0 : Fin 3)
      (wordScore A_RPS (R2.mulVec (binomBasis 2 q)) ((rpsPhaseWord q).take r))
      ((rpsPhaseWord q)[r])
    have hn : 0 ≤ eps * ((rpsPhaseWord q).length - r : ℕ) := by positivity
    rw [rps_height]
    push_cast
    linarith
  · rw [List.take_length, rps_word_transition]
    simp

/-- Proposition seed of v15, with every Clock field closed on the literal RPS data. -/
def rpsClock : Clock 2 where
  order_ge_two := by decide
  m := 3
  A := A_RPS
  skew := A_RPS_skew
  rank := Equiv.refl (Fin 3)
  R := R2
  C := C2Integer
  b := 0
  v := v_RPS
  Q := 1
  onset_pos := by decide
  word := rpsPhaseWord
  delta0 := 1
  marker_pos := by norm_num
  Arem := 1
  remainder_nonneg := by norm_num
  threshold := fun _ => 1
  threshold_onset := by intros; exact le_refl 1
  clock_eq := by rw [ratCount_C2Integer]; exact rpsAlgebraicClock.hclock
  full_column_rank := by rw [ratCount_C2Integer]; exact C2_mulVec_injective
  leading_height := by norm_num [R2]
  valid := by intro q _; exact isValidPriorityWord_rpsPhaseWord q (Equiv.refl (Fin 3))
  counts := by intro q _; rw [ratCount_C2Integer]; exact wordCountVec_rpsPhaseWord q
  begins_twice := by intro q _; exact rps_word_begins_twice q
  counter_entry := rfl
  counter_table := by rw [ratCount_C2Integer]; exact rpsAlgebraicClock.hvC
  marker := by intro q _ r hr; exact rps_marker q r hr
  support_safe := rps_support_safe
  suffix := by intro eps heps q _ r hr; exact rps_suffix eps heps q r hr

theorem rpsClock_constants : rpsClock.Q = 1 ∧ rpsClock.delta0 = 1 ∧
    rpsClock.Arem = 1 ∧ ∀ eps, rpsClock.threshold eps = 1 := by
  exact ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem rpsClock_strict (q : ℕ) :
    IsValidStrictWord rpsClock.A (rpsClock.entry q) (rpsClock.word q) :=
  isValidStrictWord_rpsPhaseWord q

end Karlin.FaithfulSeed
