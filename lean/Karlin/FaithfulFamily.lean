import Karlin.FaithfulSeedAdmissible
import Karlin.FaithfulRealization

/-! Generic recursion and exact dimensions for admissible faithful clocks.
The step is explicit in these helper statements. The unconditional family
will instantiate it with the literal v15 lift after its record is assembled.
-/
namespace Karlin.FaithfulFamily
open FaithfulClock FaithfulAdmissible

structure Bundle (k : ℕ) where
  clock : Clock k
  data : Admissible clock

def seed : Bundle 2 := ⟨FaithfulSeed.rpsClock, FaithfulSeedAdmissible.rpsAdmissible⟩

noncomputable def iterate (step : ∀ k : ℕ, Bundle k → Bundle (k+1)) :
    (n : ℕ) → Bundle (n+2)
  | 0 => seed
  | n+1 => step (n+2) (iterate step n)

theorem iterate_dimension
    (step : ∀ k : ℕ, Bundle k → Bundle (k+1))
    (hdim : ∀ k (B : Bundle k), (step k B).clock.m = B.clock.m + 2*k + 3) :
    ∀ n : ℕ, (iterate step n).clock.m + 6 = (n+3)^2 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (step (n+2) (iterate step n)).clock.m + 6 = (n+1+3)^2
    rw [hdim]
    nlinarith

theorem iterate_total_dimension
    (step : ∀ k : ℕ, Bundle k → Bundle (k+1))
    (hdim : ∀ k (B : Bundle k), (step k B).clock.m = B.clock.m + 2*k + 3)
    (n : ℕ) : (iterate step n).clock.m + 1 = (n+3)^2 - 5 := by
  have h := iterate_dimension step hdim n
  omega

noncomputable def atOrder (step : ∀ k : ℕ, Bundle k → Bundle (k+1))
    (k : ℕ) (hk : 2 ≤ k) : Bundle k :=
  (show k - 2 + 2 = k by omega) ▸ iterate step (k-2)

theorem transport_dimension {a b : ℕ} (h : a = b) (B : Bundle a) :
    (h ▸ B).clock.m = B.clock.m := by cases h; rfl

theorem atOrder_dimension
    (step : ∀ k : ℕ, Bundle k → Bundle (k+1))
    (hdim : ∀ k (B : Bundle k), (step k B).clock.m = B.clock.m + 2*k + 3)
    (k : ℕ) (hk : 2 ≤ k) : (atOrder step k hk).clock.m + 1 = (k+1)^2 - 5 := by
  have h := iterate_total_dimension step hdim (k-2)
  have he : k - 2 + 2 = k := by omega
  have hn : k - 2 + 3 = k + 1 := by omega
  rw [hn] at h
  change ((he ▸ iterate step (k-2)).clock.m) + 1 = _
  rw [transport_dimension]
  exact h

#print axioms atOrder_dimension
end Karlin.FaithfulFamily
