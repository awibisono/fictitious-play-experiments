import Karlin.FaithfulV15
import Karlin.FaithfulRPS
import Karlin.FaithfulScaleClock
import Lean.Util.CollectAxioms

namespace IndependentGate
open scoped BigOperators
open Filter Topology Karlin

def tally {n : ℕ} (a : ℕ → Fin n) (t : ℕ) (i : Fin n) : ℚ :=
  ∑ s ∈ Finset.range t, if a s = i then 1 else 0

theorem tally_zero {n : ℕ} (a : ℕ → Fin n) (i : Fin n) : tally a 0 i = 0 := by
  simp [tally]

theorem tally_update {n : ℕ} (a : ℕ → Fin n) (t : ℕ) (i : Fin n) :
    tally a (t+1) i = tally a t i + if a t = i then 1 else 0 := by
  simp only [tally, Finset.sum_range_succ]

theorem tally_total {n : ℕ} (a : ℕ → Fin n) (t : ℕ) :
    ∑ i, tally a t i = (t : ℚ) := by
  simp only [tally]
  rw [Finset.sum_comm]
  simp

theorem tally_nonneg {n : ℕ} (a : ℕ → Fin n) (t : ℕ) (i : Fin n) :
    0 ≤ tally a t i := by
  apply Finset.sum_nonneg
  intro s _
  split_ifs <;> norm_num

noncomputable def rawGap {m : ℕ} (M : Matrix (Fin (m+1)) (Fin (m+1)) ℚ)
    (a : ℕ → Fin (m+1)) (t : ℕ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, M i j * (tally a t j / t)) -
  Finset.univ.inf' Finset.univ_nonempty (fun j => ∑ i, (tally a t i / t) * M i j)

theorem rawGap_eq {m : ℕ} (M : Matrix (Fin (m+1)) (Fin (m+1)) ℚ)
    (a : ℕ → Fin (m+1)) (t : ℕ) : rawGap M a t = standardDualityGap M a a t := rfl

/-- Independent statement with literal cumulative sums and empirical gap,
not the implementation's FP predicate as an opaque semantic assumption. -/
theorem raw_main (k : ℕ) (hk : 2 ≤ k) :
    ∃ (m : ℕ) (M : Matrix (Fin (m+1)) (Fin (m+1)) ℚ)
      (a : ℕ → Fin (m+1)) (c : ℝ),
      m+1 = (k+1)^2-5 ∧ (∀ i j, M i j = -M j i) ∧ a 0 = 0 ∧
      (∀ t : ℕ, 1 ≤ t →
        (∀ i, i ≠ a t → (∑ s ∈ Finset.range t, M i (a s)) <
          ∑ s ∈ Finset.range t, M (a t) (a s)) ∧
        (∀ j, j ≠ a t → (∑ s ∈ Finset.range t, M (a s) (a t)) <
          ∑ s ∈ Finset.range t, M (a s) j)) ∧
      0 < c ∧
      Tendsto (fun t : ℕ => (rawGap M a t : ℝ) * (t : ℝ) ^ (1/(k : ℝ)))
        atTop (𝓝 c) ∧
      ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
        (c/2) * (t : ℝ) ^ (-(1/(k : ℝ))) ≤ (rawGap M a t : ℝ) ∧
        (rawGap M a t : ℝ) ≤ (2*c) * (t : ℝ) ^ (-(1/(k : ℝ))) := by
  obtain ⟨m, M, a, c, hdim, hskew, hinit, _, hstrict, _, hc, hlim, _, htheta⟩ :=
    FaithfulMain.main_theorem k hk
  exact ⟨m, M, a, c, hdim, hskew, hinit, hstrict, hc, hlim, htheta⟩

end IndependentGate

namespace IndependentSevenGate
open scoped BigOperators
open Filter Topology Karlin

def tally {n : ℕ} (a : ℕ → Fin n) (t : ℕ) (i : Fin n) : ℚ :=
  ∑ s ∈ Finset.range t, if a s = i then 1 else 0

theorem tally_zero {n : ℕ} (a : ℕ → Fin n) (i : Fin n) : tally a 0 i = 0 := by
  simp [tally]

theorem tally_update {n : ℕ} (a : ℕ → Fin n) (t : ℕ) (i : Fin n) :
    tally a (t+1) i = tally a t i + if a t = i then 1 else 0 := by
  simp only [tally, Finset.sum_range_succ]

theorem tally_total {n : ℕ} (a : ℕ → Fin n) (t : ℕ) :
    ∑ i, tally a t i = (t : ℚ) := by
  simp only [tally]
  rw [Finset.sum_comm]
  simp

theorem tally_nonneg {n : ℕ} (a : ℕ → Fin n) (t : ℕ) (i : Fin n) :
    0 ≤ tally a t i := by
  apply Finset.sum_nonneg
  intro s _
  split_ifs <;> norm_num

noncomputable def rawGap {m : ℕ} (M : Matrix (Fin (m+1)) (Fin (m+1)) ℚ)
    (a : ℕ → Fin (m+1)) (t : ℕ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, M i j * (tally a t j / t)) -
  Finset.univ.inf' Finset.univ_nonempty (fun j => ∑ i, (tally a t i / t) * M i j)

theorem rawGap_eq {m : ℕ} (M : Matrix (Fin (m+1)) (Fin (m+1)) ℚ)
    (a : ℕ → Fin (m+1)) (t : ℕ) : rawGap M a t = standardDualityGap M a a t := rfl

/-- Independent statement with literal cumulative sums and empirical gap,
not the implementation's FP predicate as an opaque semantic assumption. -/
theorem raw_main (k : ℕ) (hk : 3 ≤ k) :
    ∃ (m : ℕ) (M : Matrix (Fin (m+1)) (Fin (m+1)) ℚ)
      (a : ℕ → Fin (m+1)) (c : ℝ),
      m+1 = (k+1)^2-9 ∧ (∀ i j, M i j = -M j i) ∧ a 0 = 0 ∧
      (∀ t : ℕ, 1 ≤ t →
        (∀ i, i ≠ a t → (∑ s ∈ Finset.range t, M i (a s)) <
          ∑ s ∈ Finset.range t, M (a t) (a s)) ∧
        (∀ j, j ≠ a t → (∑ s ∈ Finset.range t, M (a s) (a t)) <
          ∑ s ∈ Finset.range t, M (a s) j)) ∧
      0 < c ∧
      Tendsto (fun t : ℕ => (rawGap M a t : ℝ) * (t : ℝ) ^ (1/(k : ℝ)))
        atTop (𝓝 c) ∧
      ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
        (c/2) * (t : ℝ) ^ (-(1/(k : ℝ))) ≤ (rawGap M a t : ℝ) ∧
        (rawGap M a t : ℝ) ≤ (2*c) * (t : ℝ) ^ (-(1/(k : ℝ))) := by
  obtain ⟨m, M, a, c, hdim, hskew, hinit, _, hstrict, _, hc, hlim, _, htheta⟩ :=
    FaithfulSevenFamily.main_theorem k hk
  exact ⟨m, M, a, c, hdim, hskew, hinit, hstrict, hc, hlim, htheta⟩

end IndependentSevenGate

-- These ordinary definitions independently require executable code for the
-- full original family APIs after loading their verified compiler bridges.
def integrationRPSBundle (k : ℕ) (hk : 2 ≤ k) := Karlin.FaithfulMain.bundle k hk
def integrationRPSMatrix (k : ℕ) (hk : 2 ≤ k) := Karlin.FaithfulMain.matrix k hk
def integrationRPSWord (k : ℕ) (hk : 2 ≤ k) (q : ℕ) := (Karlin.FaithfulMain.clock k hk).word q
def integrationRPSThreshold (k : ℕ) (hk : 2 ≤ k) (eps : ℚ) := (Karlin.FaithfulMain.clock k hk).threshold eps
def integrationSevenBundle (k : ℕ) (hk : 3 ≤ k) := Karlin.FaithfulSevenFamily.bundle k hk
def integrationSevenMatrix (k : ℕ) (hk : 3 ≤ k) := Karlin.FaithfulSevenFamily.matrix k hk
def integrationSevenWord (k : ℕ) (hk : 3 ≤ k) (q : ℕ) := (Karlin.FaithfulSevenFamily.clock k hk).word q
def integrationSevenThreshold (k : ℕ) (hk : 3 ≤ k) (eps : ℚ) := (Karlin.FaithfulSevenFamily.clock k hk).threshold eps

open Lean in
run_cmd do
  let env ← getEnv
  let permitted := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #["groundedBundleTower", "GroundedClockBundle",
    "unconditionalRealizedClock", "all_orders_unconditional_karlin_theorem",
    "unconditional_karlin_theorem", "paper_thm_1_1_main", "grounded", "Grounded",
    "all_orders", "unconditional", "RealizedClock", "seven_unrolled_strict_fp_trajectory",
    "seven_all_integer_time_cubic_gap"]
  for root in #[`Karlin.FaithfulMain.main_theorem, `Karlin.FaithfulSevenFamily.main_theorem] do
    let (_, state) := ((Lean.CollectAxioms.collect root).run env).run {}
    for ax in state.axioms do
      unless permitted.contains ax do throwError m!"DISALLOWED AXIOM {root}: {ax}"
    for dep in state.visited do
      let s := dep.toString
      let owner := match env.getModuleIdxFor? dep with
        | some idx => env.header.moduleNames[idx.toNat]!
        | none => Name.anonymous
      if owner.toString.startsWith "Karlin." then
        for term in forbidden do
          if (s.splitOn term).length > 1 then throwError m!"FORBIDDEN {root}: {dep}"
        if let some info := env.find? dep then
          if info.isUnsafe then throwError m!"UNSAFE {root}: {dep}"
          if let .opaqueInfo _ := info then throwError m!"OPAQUE PROJECT DEPENDENCY {root}: {dep}"
    let required := #[`Karlin.FaithfulLift.nextAdmissible,
      `Karlin.FaithfulNextClockAssembly.nextRaw,
      `Karlin.FaithfulActualWaiting.actual_oldWord_valid,
      `Karlin.FaithfulNextClockAssembly.reset_valid,
      `Karlin.FaithfulController.chosen_valid,
      `Karlin.FaithfulEffectiveParameters.canonicalFirstScale,
      `Karlin.FaithfulNextTables.prescribedT2,
      `Karlin.FaithfulCokernel.momentSection,
      `Karlin.FaithfulEffectiveLinear.linearSection,
      `Karlin.FaithfulActualSuffix.actual_suffix,
      `Karlin.FaithfulBiasSetup.gridDenominator,
      `Karlin.FaithfulBiasSetup.shift,
      `Karlin.FaithfulRealization.exact_gap_limit,
      `Karlin.FaithfulRateError.standard_gap_from_phase_tables_relative_error]
    for req in required do
      unless state.visited.contains req do throwError m!"MISSING REQUIRED {root}: {req}"
      logInfo m!"REQUIRED {root}: {req} present"
    let seed := if root == `Karlin.FaithfulMain.main_theorem then
      `Karlin.FaithfulSeedAdmissible.rpsAdmissible else `Karlin.FaithfulSevenAdmissible.sevenAdmissible
    unless state.visited.contains seed do throwError m!"MISSING SEED {seed}"
    logInfo m!"FINAL_ENTRY {root}: visited={state.visited.size}; axioms={state.axioms.toList}; seed={seed}; forbidden_unsafe_opaque=false"
  let mut total := 0
  let mut thms := 0
  let mut moduleCounts : Std.HashMap Name Nat := {}
  let mut state : Lean.CollectAxioms.State := {}
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => Name.anonymous
    if owner.toString.startsWith "Karlin.Faithful" then
      total := total + 1
      if let .thmInfo _ := info then thms := thms + 1
      moduleCounts := moduleCounts.insert owner (moduleCounts.getD owner 0 + 1)
      let (_, next) := ((Lean.CollectAxioms.collect name).run env).run state
      state := next
  for ax in state.axioms do
    unless permitted.contains ax do throwError m!"MODULE-CLOSURE DISALLOWED AXIOM {ax}"
  for dep in state.visited do
    let s := dep.toString
    let owner := match env.getModuleIdxFor? dep with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => Name.anonymous
    if owner.toString.startsWith "Karlin." then
      for term in forbidden do
        if (s.splitOn term).length > 1 then throwError m!"MODULE-CLOSURE FORBIDDEN {dep}"
      if let some info := env.find? dep then
        if info.isUnsafe then throwError m!"MODULE-CLOSURE UNSAFE {dep}"
        if let .opaqueInfo _ := info then throwError m!"MODULE-CLOSURE OPAQUE {dep}"
  for (mod, n) in moduleCounts.toList do logInfo m!"OWNED_MODULE {mod}: declarations={n}"
  logInfo m!"ALL_OWNED_MODULES modules={moduleCounts.size}; declarations={total}; theorems={thms}; visited={state.visited.size}; axioms={state.axioms.toList}; forbidden_unsafe_opaque=false"

#print axioms IndependentGate.raw_main
#print axioms IndependentSevenGate.raw_main
#print axioms integrationRPSBundle
#print axioms integrationSevenBundle
#check @Karlin.FaithfulMain.main_theorem
#check @Karlin.FaithfulSevenFamily.main_theorem
#check @Karlin.FaithfulScaleEffective.compute_correct
#check @Karlin.FaithfulEffectiveLift.familySuffix
#check @Karlin.FaithfulStartPhase.realization_at_any_phase
#check @Karlin.FaithfulProcessSetup.rational_bias_realizes_priority
#check @Karlin.FaithfulProcessSetup.actual_setup_process
#check @Karlin.FaithfulGrowthRecurrences.polynomial_height_expansion
#check @Karlin.FaithfulResetPlateau.chosen_reset_prefix_height
#check @Karlin.FaithfulConsequences.no_universal_polynomial_exponent
#check @Karlin.FaithfulConsequences.normalized_constant_power
#check @Karlin.FaithfulAppendix.Actual.actual_coupling_bound
#check @Karlin.FaithfulAppendix.Actual.candidate_equations
#check @Karlin.FaithfulAppendix.Actual.candidate_validScales
#check @Karlin.FaithfulAppendix.Search.candidate_after_canonicalOnset
#check @Karlin.FaithfulAppendix.Search.canonicalSuccessiveScale_spec
#check @Karlin.FaithfulAppendix.Search.canonicalDoublingScale_spec
#check @Karlin.FaithfulAppendix.Search.canonicalDoublingScale_valid
#check @Karlin.FaithfulAppendix.Search.canonicalSuccessiveScale_valid

#eval ((Karlin.FaithfulEffectiveLift.familyClock 2 (by decide)).m,
  Karlin.FaithfulEffectiveLift.familyThreshold 2 (by decide) (1/100),
  (Karlin.FaithfulSevenFamily.clock 3 (by decide)).m,
  Karlin.FaithfulSevenFamily.threshold 3 (by decide) (1/100))
