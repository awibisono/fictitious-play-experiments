import Karlin.FaithfulWindow

/-!
# The v15 clock interface

This record states the manuscript's clock conditions without a realized trajectory,
strictness, gap estimate, grounded constructor, or extra sign assumptions on the
counter and coefficient table. Constructors must supply an actual threshold rule.
These fields express its mathematical specification. Computational preservation
for executable parent data and closed executable family programs are supplied by
`FaithfulEffectiveLift`; the function-valued fields alone do not assert that
every possible inhabitant of this mathematical record is computable.
-/

namespace Karlin.FaithfulClock

open scoped BigOperators

/-- A finite maximum whose nonemptiness is supplied by the clock's entry action. -/
def height {m : ℕ} (b : Fin m) (s : Fin m → ℚ) : ℚ :=
  Finset.univ.sup' ⟨b, Finset.mem_univ b⟩ s

theorem le_height {m : ℕ} (b : Fin m) (s : Fin m → ℚ) (i : Fin m) :
    s i ≤ height b s := Finset.le_sup' s (Finset.mem_univ i)

theorem height_eq {m : ℕ} (b : Fin m) (s : Fin m → ℚ) (i : Fin m)
    (hi : ∀ j, s j ≤ s i) : height b s = s i := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun j _ => hi j)
  · exact le_height b s i

/-- The maximum score never falls along a priority-valid word, including its
complete prefix. Only the maximizing part of priority validity is used. -/
theorem height_prefix_ge {m rnk : ℕ} (b : Fin m) (A : Matrix (Fin m) (Fin m) ℚ)
    (hA : IsSkewSymmetric A) (s : Fin m → ℚ) (rank : Fin m → Fin rnk)
    (W : List (Fin m)) (hW : IsValidPriorityWord A s rank W)
    (r : ℕ) (hr : r ≤ W.length) :
    height b s ≤ height b (wordScore A s (W.take r)) := by
  induction r with
  | zero => simp [wordScore_nil]
  | succ r ih =>
      have hr' : r < W.length := by omega
      have hp := ih (by omega)
      have hm := height_eq b (wordScore A s (W.take r)) (W[r]) (fun j => (hW r hr' j).1)
      rw [hm] at hp
      have hs := wordScore_take_succ_self_of_skew A hA s W r hr'
      have hn := le_height b (wordScore A s (W.take (r + 1))) (W[r])
      rw [hs] at hn
      exact hp.trans hn

def ratCount {m k : ℕ} (C : Matrix (Fin m) (Fin k) ℤ) :
    Matrix (Fin m) (Fin k) ℚ := fun i j => (C i j : ℚ)

/-- Literal conditions I--III of `master_v15`, lines 829--855. Full column rank
is expressed as injectivity of the linear map represented by the count table. -/
structure Clock (k : ℕ) where
  order_ge_two : 2 ≤ k
  m : ℕ
  A : Matrix (Fin m) (Fin m) ℚ
  skew : IsSkewSymmetric A
  rank : Equiv.Perm (Fin m)
  R : Matrix (Fin m) (Fin k) ℚ
  C : Matrix (Fin m) (Fin k) ℤ
  b : Fin m
  v : Fin m → ℚ
  Q : ℕ
  onset_pos : 1 ≤ Q
  word : ℕ → List (Fin m)
  delta0 : ℚ
  marker_pos : 0 < delta0
  Arem : ℚ
  remainder_nonneg : 0 ≤ Arem
  threshold : ℚ → ℕ
  threshold_onset : ∀ eps, 0 < eps → Q ≤ threshold eps
  clock_eq : A * ratCount C = R * N_mat k
  full_column_rank : Function.Injective
    (fun x : Fin k → ℚ => (ratCount C).mulVec x)
  leading_height : 0 < R b ⟨k - 1, by omega⟩
  valid : ∀ q, Q ≤ q →
    IsValidPriorityWord A (R.mulVec (binomBasis k q)) rank (word q)
  counts : ∀ q, Q ≤ q → wordCountVec (word q) =
    (ratCount C).mulVec (binomBasis k q)
  begins_twice : ∀ q, Q ≤ q → ∃ tail, word q = b :: b :: tail
  counter_entry : v b = 0
  counter_table : Matrix.vecMul v (ratCount C) = e0_row k
  marker : ∀ q, Q ≤ q → ∀ r, r < (word q).length →
    delta0 ≤ height b (wordScore A (R.mulVec (binomBasis k q)) ((word q).take r)) -
      wordScore A (R.mulVec (binomBasis k q)) ((word q).take r) b +
      dotProduct v (wordCountVec ((word q).drop r))
  support_safe : ∀ q, Q ≤ q → ∀ i, v i ≠ 0 →
    R.mulVec (binomBasis k q) i + A i b - v i <
      R.mulVec (binomBasis k q) b + A b b - v b
  suffix : ∀ eps, 0 < eps → ∀ q, threshold eps ≤ q →
    ∀ r, r ≤ (word q).length →
      height b (R.mulVec (binomBasis k (q + 1))) -
        height b (wordScore A (R.mulVec (binomBasis k q)) ((word q).take r)) ≤
          eps * ((word q).length - r : ℕ) + Arem

namespace Clock

variable {k : ℕ} (P : Clock k)

def countTable : Matrix (Fin P.m) (Fin k) ℚ := fun i j => (P.C i j : ℚ)

def entry (q : ℕ) : Fin P.m → ℚ := P.R.mulVec (binomBasis k q)

theorem phase_transition (q : ℕ) (hq : P.Q ≤ q) :
    wordScore P.A (P.entry q) (P.word q) = P.entry (q + 1) := by
  unfold wordScore entry
  rw [P.counts q hq]
  exact clock_phase_transition P.A P.R P.countTable P.clock_eq q

theorem count_nonneg (q : ℕ) (hq : P.Q ≤ q) (i : Fin P.m) :
    0 ≤ P.countTable.mulVec (binomBasis k q) i := by
  change 0 ≤ (ratCount P.C).mulVec (binomBasis k q) i
  rw [← P.counts q hq]
  exact Nat.cast_nonneg _

theorem word_length_pos (q : ℕ) (hq : P.Q ≤ q) : 0 < (P.word q).length := by
  obtain ⟨tail, ht⟩ := P.begins_twice q hq
  simp [ht]

theorem entry_height (q : ℕ) (hq : P.Q ≤ q) :
    height P.b (P.entry q) = P.entry q P.b := by
  obtain ⟨tail, ht⟩ := P.begins_twice q hq
  apply height_eq
  intro j
  have hv := (P.valid q hq) 0 (P.word_length_pos q hq) j
  simpa [ht, entry, wordScore_nil] using hv.1

/-- The required two initial entry plays imply leadership after one such play. -/
theorem second_entry_leader (q : ℕ) (hq : P.Q ≤ q) (i : Fin P.m) :
    P.entry q i + P.A i P.b ≤ P.entry q P.b := by
  obtain ⟨tail, ht⟩ := P.begins_twice q hq
  have hlen : 1 < (P.word q).length := by simp [ht]
  have hv := ((P.valid q hq) 1 hlen i).1
  have htake : (P.word q).take 1 = [P.b] := by simp [ht]
  have hget : (P.word q)[1] = P.b := by simp [ht]
  rw [htake, hget, FaithfulWindow.wordScore_singleton,
    FaithfulWindow.wordScore_singleton, skew_diag_zero P.skew, add_zero] at hv
  exact hv

theorem counter_increment (q : ℕ) (hq : P.Q ≤ q) :
    dotProduct P.v (wordCountVec (P.word q)) = 1 := by
  rw [P.counts q hq]
  exact clock_endpoint_increment_eq_one (by have := P.order_ge_two; omega)
    P.v P.countTable P.counter_table q

theorem consecutive_counter (a : ℕ) (ha : P.Q ≤ a) (n : ℕ) :
    dotProduct P.v (wordCountVec (FaithfulWindow.consecutiveWord P.word a n)) = n := by
  induction n with
  | zero => simp [FaithfulWindow.consecutiveWord, wordCountVec, dotProduct]
  | succ n ih =>
      rw [FaithfulWindow.consecutiveWord, FaithfulWindow.dotCount_append, ih,
        P.counter_increment (a + n) (by omega)]
      simp

/-- Endpoint detection propagates through a consecutive bundle even when the
parent counter has negative coordinates. Later complete phases each add one. -/
theorem consecutive_marker (a : ℕ) (ha : P.Q ≤ a) (n r : ℕ)
    (hr : r < (FaithfulWindow.consecutiveWord P.word a n).length) :
    P.delta0 ≤
      height P.b (wordScore P.A (P.entry a)
        ((FaithfulWindow.consecutiveWord P.word a n).take r)) -
      wordScore P.A (P.entry a)
        ((FaithfulWindow.consecutiveWord P.word a n).take r) P.b +
      dotProduct P.v (wordCountVec ((FaithfulWindow.consecutiveWord P.word a n).drop r)) := by
  obtain ⟨j, hj, u, hu, _, htake⟩ :=
    FaithfulWindow.consecutiveWord_prefix P.word a n r hr
  have hq : P.Q ≤ a + j := by omega
  have hend := (FaithfulWindow.consecutiveWord_valid_score P.A P.rank P.word P.entry P.Q
    P.valid P.phase_transition a ha j).2
  have hscore : wordScore P.A (P.entry a)
      ((FaithfulWindow.consecutiveWord P.word a n).take r) =
      wordScore P.A (P.entry (a + j)) ((P.word (a + j)).take u) := by
    rw [htake, wordScore_append, hend]
  have hprefix : dotProduct P.v
      (wordCountVec ((FaithfulWindow.consecutiveWord P.word a n).take r)) =
      j + dotProduct P.v (wordCountVec ((P.word (a + j)).take u)) := by
    rw [htake, FaithfulWindow.dotCount_append, P.consecutive_counter a ha j]
  have hbundle := FaithfulWindow.dotCount_take_add_drop P.v
    (FaithfulWindow.consecutiveWord P.word a n) r
  rw [hprefix, P.consecutive_counter a ha n] at hbundle
  have hphase := FaithfulWindow.dotCount_take_add_drop P.v (P.word (a + j)) u
  rw [P.counter_increment (a + j) hq] at hphase
  have hmarker := P.marker (a + j) hq u hu
  have hj' : (j : ℚ) + 1 ≤ n := by exact_mod_cast hj
  rw [hscore]
  change P.delta0 ≤ height P.b (wordScore P.A (P.entry (a + j)) _) - _ + _ at hmarker
  dsimp only [entry] at hmarker ⊢
  linarith

/-- The compatible witness is literally the dyadic window of this clock's words. -/
theorem dyadic_compatible (tau q : ℕ) (hq : P.Q ≤ tau * q) :
    IsValidPriorityWord P.A (P.entry (tau * q)) P.rank
        (FaithfulWindow.dyadicWord P.word tau q) ∧
    wordScore P.A (P.entry (tau * q)) (FaithfulWindow.dyadicWord P.word tau q) =
        P.entry (2 * tau * q) ∧
    wordCountVec (FaithfulWindow.dyadicWord P.word tau q) =
        (P.countTable * F_tau_mat k tau).mulVec (binomBasis (k + 1) q) := by
  have hs := FaithfulWindow.dyadicWord_valid_score P.A P.rank P.word P.entry P.Q
    P.valid P.phase_transition tau q hq
  exact ⟨hs.1, hs.2, FaithfulWindow.dyadicWord_count_table P.countTable P.word P.Q
    P.counts tau q hq⟩

end Clock

end Karlin.FaithfulClock
