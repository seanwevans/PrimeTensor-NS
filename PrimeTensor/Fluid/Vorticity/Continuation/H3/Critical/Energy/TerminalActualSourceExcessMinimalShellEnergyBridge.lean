import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessQuarterCubicEnergyOuterEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEFirstCrossingLastShell244
import Mathlib.Tactic

/-!
# The actual minimal first-crossing shell, physical H3 energy and PDE window

The exact-anchor constructor uses the least integer outer cutoff, yet the
previously exported no-trace disjoint certificates discarded its predecessor
inequality. Here that inequality, the strictly positive raw kinetic mass in
the *last integer Fourier shell*, the overshoot, the original source maximum,
exact quadratic-sharp PDE window and physical H3 energy burden are assembled
on one and the same snapshot. They are then selected cofinally and on disjoint
windows without terminal full-H3 dissipation integrability.

The last-shell overshoot is merely strictly positive. There is NO fixed
quarter-cubic lower bound for one last shell and no upper cutoff cap.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

-- The shell's physical raw Fourier mass needs the same local point-measure
-- instances as its defining first-crossing module.
noncomputable local instance axisFintypeMinimalShellEnergyBridge
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMinimalShellEnergyBridge :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A single actual preterminal window carries the minimal crossing,
last-shell kinetic witness, exact PDE clock, certified integral cost and
anchor H3 energy burden simultaneously. -/
def h3CriticalMinimalShellEnergyWindow
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (n N m : ℕ) (C δ : ℝ) : Prop :=
  N = m + 1 ∧ n ≤ m ∧
  0 ≤ C ∧
  C = h3PathActualProjectedSourceWindowEnvelope244 hH3
    t (t + (T - t) / 2) ∧
  0 < δ ∧ t + δ < T ∧
  δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 ((T - t) / 2)
    ((h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) -
      ((n : ℝ) + 1) ^ 3 / 2)
    (h3PathFiniteAnnulusPDEVariationCoefficient244
      ((n : ℝ) + 1) ((N : ℝ) + 1)
      ‖h3AuditActualSpectralVelocityTotal hH3 t‖ C)
    (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
      ((n : ℝ) + 1) ((N : ℝ) + 1) C) ∧
  ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2 ≤
    velocityH3EnergyAt u t ∧
  ((n : ℝ) + 1) ^ 3 / 4 <
    (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) -
      ((n : ℝ) + 1) ^ 3 / 2 ∧
  (∀ j : ℕ, n ≤ j → j < N →
    h3PathActualLowRadialDissipation244 ((j : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) ≤
      3 * (((n : ℝ) + 1) ^ 3) / 4) ∧
  (∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
    ((n : ℝ) + 1) ^ 3 / 2 <
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
  δ * (((n : ℝ) + 1) ^ 3 / 2) ≤
    ∫ s in t..(t + δ),
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s) ∧
  ((n : ℝ) + 1) ^ 3 <
    4 * ((N : ℝ) + 2) ^ 2 * velocityH3EnergyAt u t ∧
  0 < h3PathActualBandRawKineticMass244
    ((m : ℝ) + 1) ((N : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 t) ∧
  (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 t) -
    h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 t)) -
    3 * (((n : ℝ) + 1) ^ 3) / 4 ≤
  4 * (((N : ℝ) + 2) ^ 8) *
    h3PathActualBandRawKineticMass244
      ((m : ℝ) + 1) ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)

/-- Reassemble the *same* canonical N, C and delta with last-shell mass,
rather than extracting an unrelated annulus from a separate witness. -/
theorem h3Critical_highSnapshot_minimalShellEnergyExactClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (n : ℕ)
    (hCube : ((n : ℝ) + 1) ^ 3 <
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) :
    ∃ N m : ℕ, ∃ C δ : ℝ,
      h3CriticalMinimalShellEnergyWindow hH3 t n N m C δ := by
  obtain ⟨N, C, δ, hnN, hC, hEnvelope, _hMax,
    hδ, hEnd, hExact, hFloor, hEnergy, _hProduct,
    hQuarter, hMinimal⟩ :=
    h3Path_cubicHighSnapshot_has_exactAnchorCanonicalClock244
      hH3 hClass t ht n hCube
  have hCross : 3 * (((n : ℝ) + 1) ^ 3) / 4 <
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) := by
    linarith only [hQuarter]
  obtain ⟨m, hmN, hnm, _hJump, hMass, hOvershoot⟩ :=
    h3Path_physicalFirstCrossing_lastShellKineticOvershoot244
      hH3 hClass t ht n N hnN hCross hMinimal
  have hR : 1 ≤ (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith only [hn]
  have hRQ : (n : ℝ) + 1 ≤ (N : ℝ) + 1 := by
    have hn : (n : ℝ) ≤ N := by exact_mod_cast hnN
    linarith only [hn]
  have hPhysical :=
    h3Critical_quarterCubicPhysicalAnchor_forces_energyOuter
      hH3 t ((n : ℝ) + 1) ((N : ℝ) + 1)
      hR hRQ hQuarter hEnergy
  let B : ℝ → ℝ := fun s =>
    h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 s) -
    h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 s)
  have hR0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hQ0 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  have hSub : Set.Icc t (t + δ) ⊆ Set.Ioo a T := by
    intro s hs
    exact ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hContinuous : ContinuousOn B (Set.Ioo a T) :=
    h3Path_finiteAnnularDissipation_continuousOn244
      hH3 hClass ((n : ℝ) + 1) ((N : ℝ) + 1) hR0 hQ0
  have hIntegrable : IntervalIntegrable B volume t (t + δ) :=
    (hContinuous.mono hSub).intervalIntegrable_of_Icc
      (le_add_of_nonneg_right hδ.le)
  have hCost : δ * (((n : ℝ) + 1) ^ 3 / 2) ≤
      ∫ s in t..(t + δ), B s := by
    have hFloorCost := h3Path_localPositiveHeight_forces_integratedCost244
      B t (t + δ) (((n : ℝ) + 1) ^ 3 / 2)
      (by linarith only [hδ]) hIntegrable
      (fun s hs => (hFloor s hs).le)
    calc
      δ * (((n : ℝ) + 1) ^ 3 / 2) =
          ((t + δ) - t) * (((n : ℝ) + 1) ^ 3 / 2) := by ring
      _ ≤ ∫ s in t..(t + δ), B s := hFloorCost
  refine ⟨N, m, C, δ, ?_⟩
  dsimp only [h3CriticalMinimalShellEnergyWindow]
  refine ⟨hmN, hnm, hC, hEnvelope, hδ, hEnd,
    hExact, hEnergy, hQuarter, hMinimal, hFloor, ?_, ?_, hMass, hOvershoot⟩
  · simpa only [B] using hCost
  · simpa only [show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]
      using hPhysical

/-- Every strict preterminal tail has the complete minimal-shell witness
at each chosen natural inner cutoff. In particular the shell is not an
artifact of enlarging the outer cutoff. No terminal L1 dissipation bound. -/
theorem h3Critical_noL2Trace_everyTail_minimalShellEnergyExactClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (b : ℝ) (hb : b ∈ Set.Ioo a T) (n : ℕ) :
    ∃ t : ℝ, t ∈ Set.Ioo b T ∧
      ∃ N m : ℕ, ∃ C δ : ℝ,
        h3CriticalMinimalShellEnergyWindow hH3 t n N m C δ := by
  obtain ⟨t, ht, hSpike⟩ :=
    h3Critical_noL2Trace_highRadialDissipation_spikes_everyFixedRadius
      hH3 hClass hNoTrace b hb ((n : ℝ) + 1)
      (by positivity) (((n : ℝ) + 1) ^ 3)
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  obtain ⟨N, m, C, δ, hWindow⟩ :=
    h3Critical_highSnapshot_minimalShellEnergyExactClock
      hH3 hClass t htClass n hSpike
  exact ⟨t, ht, N, m, C, δ, hWindow⟩

/-- Cofinal minimal-shell witnesses preserve the same exact physical
PDE interval and strictly positive last-shell raw kinetic mass. -/
theorem h3Critical_noL2Trace_cofinal_minimalShellEnergyExactClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N m : ℕ → ℕ, ∃ C δ : ℕ → ℝ,
      (∀ n : ℕ, t n ∈ Set.Ioo a T) ∧
      Tendsto t atTop (𝓝 T) ∧
      (∀ n : ℕ, h3CriticalMinimalShellEnergyWindow
        hH3 (t n) n (N n) (m n) (C n) (δ n)) := by
  let P : ℕ → ℝ → Prop := fun n t =>
    ∃ N m : ℕ, ∃ C δ : ℝ,
      h3CriticalMinimalShellEnergyWindow hH3 t n N m C δ
  have hEvery (n : ℕ) (b : ℝ) (hb : b ∈ Set.Ioo a T) :
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧ P n t := by
    simpa only [P] using
      (h3Critical_noL2Trace_everyTail_minimalShellEnergyExactClock
        hH3 hClass hNoTrace b hb n)
  obtain ⟨t, ht, _hDist, hLimit⟩ :=
    h3Critical_scalar_everyTailWitness_cofinalDiagonal
      a T hClass.terminal_start.2 P hEvery
  have hWitness (n : ℕ) : P n (t n) := (ht n).2
  choose N m C δ hData using hWitness
  exact ⟨t, N, m, C, δ, (fun n => (ht n).1), hLimit, hData⟩

/-- The literal last integer shell, the minimal first crossing, physical
anchor energy and exact quadratic-sharp PDE source clock all survive one
strictly monotone, pairwise separated cofinal selection. -/
theorem h3Critical_noL2Trace_disjoint_minimalShellEnergyExactClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N m : ℕ → ℕ, ∃ C δ : ℕ → ℝ,
      ∃ v : ℕ → ℕ,
        StrictMono v ∧
        Tendsto (fun k => t (v k)) atTop (𝓝 T) ∧
        (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
        (∀ k : ℕ, h3CriticalMinimalShellEnergyWindow
          hH3 (t (v k)) (v k) (N (v k)) (m (v k))
          (C (v k)) (δ (v k))) := by
  obtain ⟨t, N, m, C, δ, _hTimes, hLimit, hWindows⟩ :=
    h3Critical_noL2Trace_cofinal_minimalShellEnergyExactClock
      hH3 hClass hNoTrace
  have hδ (n : ℕ) : 0 < δ n := by
    have h := hWindows n
    rcases h with ⟨_, _, _, _, hp, _⟩
    exact hp
  have hEnd (n : ℕ) : t n + δ n < T := by
    have h := hWindows n
    rcases h with ⟨_, _, _, _, _, he, _⟩
    exact he
  obtain ⟨v, hv, hCofinal, hSeparated⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      t δ T hLimit hδ hEnd
  exact ⟨t, N, m, C, δ, v, hv, hCofinal,
    hSeparated, fun k => hWindows (v k)⟩

end
end PrimeTensor.Bridge.Euclidean
