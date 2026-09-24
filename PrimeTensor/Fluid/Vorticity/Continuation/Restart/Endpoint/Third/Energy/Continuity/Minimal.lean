import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Late.Restart.Pressure.Free.Closure

/-!
# Minimal scalar-energy continuity interface for the pressure-free restart

The pressure-free endpoint argument no longer needs the complete
`CanonicalH3EnergyDataOnTail` package.  It uses only continuity of the scalar
canonical H³ energy on compact terminal subintervals.

This file isolates exactly that property.

For an energy-class tail `[a,T)`, define

    CanonicalH3EnergyContinuousOnTail u a T

to mean that `velocityH3EnergyAt u` is continuous on every compact interval
`[a,b]` with `b < T`.

The direct late-restart theorem then needs only

* `H3SeedProducesEnergyClass`;
* `EnergyClassProducesCanonicalH3EnergyContinuity`.

The older `EnergyClassProducesCanonicalH3Data` remains a sufficient condition,
because its local-C¹ field immediately implies the weaker continuity property.
No integrability or differentiated-energy analytic package from that structure
is consumed by the continuation topology anymore.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3MinimalEnergyContinuityClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Minimal scalar-energy regularity used by the pressure-free endpoint proof:
continuity of the canonical H³ energy on each compact terminal subinterval. -/
def CanonicalH3EnergyContinuousOnTail
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  ∀ b : ℝ,
    b ∈ Set.Ico a T →
      ContinuousOn
        (velocityH3EnergyAt u)
        (Set.Icc a b)

/-- Minimal energy-class closure obligation needed by continuation. -/
def EnergyClassProducesCanonicalH3EnergyContinuity : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ),
      PreterminalH3EnergyClass u a T →
      CanonicalH3EnergyContinuousOnTail u a T

/-- The older full canonical-data closure implies the new minimal continuity
interface by projecting its local-C¹ component. -/
theorem energyClassProducesCanonicalH3EnergyContinuity_of_canonicalData
    (hCanonical : EnergyClassProducesCanonicalH3Data) :
    EnergyClassProducesCanonicalH3EnergyContinuity := by
  intro u a T hClass
  have hData :
      CanonicalH3EnergyDataOnTail u a T :=
    hCanonical u a T hClass
  intro b hb
  exact
    (hData.2.1 b hb).continuousOn

/-- Scalar-energy continuity restricts to every later terminal-tail start. -/
theorem canonicalH3EnergyContinuousOnTail_mono_start
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a t T : ℝ}
    (hat : a ≤ t)
    (htT : t < T)
    (hCont : CanonicalH3EnergyContinuousOnTail u a T) :
    CanonicalH3EnergyContinuousOnTail u t T := by
  intro b hb

  have hbOld :
      b ∈ Set.Ico a T := by
    exact
      ⟨
        le_trans hat hb.1,
        hb.2
      ⟩

  have hOld :
      ContinuousOn
        (velocityH3EnergyAt u)
        (Set.Icc a b) :=
    hCont b hbOld

  exact
    hOld.mono
      (by
        intro s hs
        exact
          ⟨
            le_trans hat hs.1,
            hs.2
          ⟩)

/-- Minimal tail continuity gives the exact elapsed scalar-energy continuity
predicate used by the pressure-free spectral argument. -/
theorem h3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed_of_energyContinuousOnTail
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hCont :
      CanonicalH3EnergyContinuousOnTail u t T) :
    H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed
      hNS ht hEnd hTail := by
  unfold H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed

  have hRight :
      t + tau ∈ Set.Ico t T := by
    constructor
    · linarith
    · exact hEnd

  have hClosed :
      ContinuousOn
        (velocityH3EnergyAt u)
        (Set.Icc t (t + tau)) :=
    hCont (t + tau) hRight

  have hRestricted :
      Continuous
        ((Set.Icc t (t + tau)).domRestrict
          (velocityH3EnergyAt u)) :=
    hClosed.domRestrict

  have hShift :
      Continuous
        (h3ElapsedToPhysicalClosedInterval
          t tau (le_of_lt htau)) :=
    continuous_h3ElapsedToPhysicalClosedInterval
      t tau (le_of_lt htau)

  have hComp :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          ((Set.Icc t (t + tau)).domRestrict
            (velocityH3EnergyAt u))
            (h3ElapsedToPhysicalClosedInterval
              t tau (le_of_lt htau) q)) :=
    hRestricted.comp hShift

  simpa only [
    h3ElapsedToPhysicalClosedInterval,
    Set.domRestrict_apply
  ] using hComp

/-- Minimal scalar-energy continuity closes the complete radius-wide endpoint
continuity frontier at one retained tail, pressure-free. -/
theorem h3PreterminalTailUnitViscosityEndpointContinuityOnRestartRadius_of_energyContinuity_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hCont :
      CanonicalH3EnergyContinuousOnTail u t T) :
    H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
      E u T t hNS ht hE hTail := by
  intro q hqPos hEnd

  have hPhysical :
      H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed
        hNS ht hEnd hTail :=
    h3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed_of_energyContinuousOnTail
      hNS ht hqPos hEnd hTail hCont

  exact
    h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_physicalEnergy_pressureFree
      hNS ht hEnd hE hTail hPhysical

/-- One sufficiently late restart carrying only the retained H³ bound and the
minimal scalar-energy continuity required by endpoint topology. -/
def H3PreterminalTailUnitViscosityLateEnergyContinuousRestartData
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) : Prop :=
  ∃
    (E t : ℝ),
      1 ≤ E
        ∧
      t ∈ Set.Ioo (0 : ℝ) T
        ∧
      CanonicalH3TailDataFrom u t T E
        ∧
      CanonicalH3EnergyContinuousOnTail u t T
        ∧
      T - t < h3FinHeatLerayRestartRadius (1 : ℝ) E

/-- Terminal H³ control, smoothing into the high-order class, and only scalar
energy continuity on that class provide one late restart crossing `T`. -/
theorem h3PreterminalTailUnitViscosityLateEnergyContinuousRestartData_of_smoothing
    (hSmooth : H3SeedProducesEnergyClass)
    (hEnergyCont : EnergyClassProducesCanonicalH3EnergyContinuity)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hControl : TerminalTailH3Control u T) :
    H3PreterminalTailUnitViscosityLateEnergyContinuousRestartData
      u T := by
  rcases hControl with
    ⟨a₀, M, ha₀, hM, hBound⟩

  have hSeed :
      PreterminalH3Seed u T := by
    exact
      ⟨
        a₀,
        M,
        ha₀,
        hM,
        hBound a₀ ⟨le_rfl, ha₀.2⟩
      ⟩

  rcases hSmooth u T hNS hSeed with
    ⟨a₁, hClass⟩

  have ha₁ :
      a₁ ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

  have hCont₁ :
      CanonicalH3EnergyContinuousOnTail
        u a₁ T :=
    hEnergyCont u a₁ T hClass

  let E : ℝ :=
    velocityH3CoordinateBudget M

  have hE :
      1 ≤ E := by
    dsimp only [E]
    exact one_le_velocityH3CoordinateBudget hM

  have hR :
      0 <
        h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
      (one_pos : (0 : ℝ) < 1)
      hE

  let b : ℝ :=
    max a₀ a₁

  have hbT :
      b < T := by
    dsimp only [b]
    exact max_lt ha₀.2 ha₁.2

  have ha₀b :
      a₀ ≤ b := by
    dsimp only [b]
    exact le_max_left _ _

  have ha₁b :
      a₁ ≤ b := by
    dsimp only [b]
    exact le_max_right _ _

  have hTb :
      0 < T - b := by
    linarith

  let ε : ℝ :=
    min
      ((T - b) / 2)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E / 2)

  have hHalfTail :
      0 < (T - b) / 2 := by
    linarith

  have hHalfRadius :
      0 <
        h3FinHeatLerayRestartRadius (1 : ℝ) E / 2 := by
    linarith

  have hε :
      0 < ε := by
    dsimp only [ε]
    exact lt_min hHalfTail hHalfRadius

  have hεTail :
      ε ≤ (T - b) / 2 := by
    dsimp only [ε]
    exact min_le_left _ _

  have hεRadius :
      ε ≤
        h3FinHeatLerayRestartRadius (1 : ℝ) E / 2 := by
    dsimp only [ε]
    exact min_le_right _ _

  let t₀ : ℝ :=
    T - ε

  have ht₀T :
      t₀ < T := by
    dsimp only [t₀]
    linarith

  have hb₀ :
      b ≤ t₀ := by
    dsimp only [t₀]
    linarith

  have ht₀Pos :
      0 < t₀ := by
    exact
      lt_of_lt_of_le
        ha₀.1
        (le_trans ha₀b hb₀)

  have ht₀ :
      t₀ ∈ Set.Ioo (0 : ℝ) T :=
    ⟨ht₀Pos, ht₀T⟩

  have hTail₀ :
      CanonicalH3TailDataFrom
        u t₀ T E := by
    intro s hs

    have hsOld :
        s ∈ Set.Ico a₀ T := by
      exact
        ⟨
          le_trans
            (le_trans ha₀b hb₀)
            hs.1,
          hs.2
        ⟩

    have hsBound :
        VelocityH3BoundAt u s M :=
      hBound s hsOld

    exact
      ⟨
        velocityH3IntegrableAt_of_bound
          hsBound,
        by
          dsimp only [E]
          exact
            velocityH3EnergyAt_le_coordinateBudget_of_bound
              hsBound
      ⟩

  have hCont₀ :
      CanonicalH3EnergyContinuousOnTail
        u t₀ T :=
    canonicalH3EnergyContinuousOnTail_mono_start
      (le_trans ha₁b hb₀)
      ht₀T
      hCont₁

  have hCross :
      T - t₀ <
        h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    have hεLtRadius :
        ε <
          h3FinHeatLerayRestartRadius (1 : ℝ) E := by
      have hHalfLt :
          h3FinHeatLerayRestartRadius (1 : ℝ) E / 2
            <
          h3FinHeatLerayRestartRadius (1 : ℝ) E := by
        linarith
      exact lt_of_le_of_lt hεRadius hHalfLt

    dsimp only [t₀]
    linarith

  exact
    ⟨
      E,
      t₀,
      hE,
      ht₀,
      hTail₀,
      hCont₀,
      hCross
    ⟩

/-- The direct real-restart theorem now depends only on smoothing plus minimal
scalar H³-energy continuity in the resulting energy class. -/
theorem h3ControlProducesRealRestart_of_unitViscositySmoothingEnergyContinuity
    (hSmooth : H3SeedProducesEnergyClass)
    (hEnergyCont : EnergyClassProducesCanonicalH3EnergyContinuity) :
    H3ControlProducesRealRestart := by
  intro u T hNS hControl

  obtain
    ⟨
      E,
      t,
      hE,
      ht,
      hTail,
      hCont,
      hCross
    ⟩ :=
    h3PreterminalTailUnitViscosityLateEnergyContinuousRestartData_of_smoothing
      hSmooth
      hEnergyCont
      hNS
      hControl

  have hEndpoint :
      H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    h3PreterminalTailUnitViscosityEndpointContinuityOnRestartRadius_of_energyContinuity_pressureFree
      hNS ht hE hTail hCont

  have hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ) E
        (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail :=
    h3PreterminalTailPhysicalEvolutionOnRestartRadius_of_unitViscosity_endpointContinuity
      hNS ht hE hTail hEndpoint

  have hLocalPDE :
      H3PreterminalTailUnitViscosityLocalPDEAt
        hNS ht hE hTail :=
    h3PreterminalTailUnitViscosityLocalPDEAt_closed_of_evolution
      hNS ht hE hTail hEvolution

  exact
    h3PreterminalTailUnitViscosityRealRestartAt_of_localPDE
      hNS ht hE hTail
      hEvolution
      hCross
      hLocalPDE

/-- Minimal pressure-free continuation closure. -/
theorem h3ControlProducesExtension_of_unitViscositySmoothingEnergyContinuity
    (hSmooth : H3SeedProducesEnergyClass)
    (hEnergyCont : EnergyClassProducesCanonicalH3EnergyContinuity) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_realRestart
      (h3ControlProducesRealRestart_of_unitViscositySmoothingEnergyContinuity
        hSmooth hEnergyCont)

/-- Compatibility corollary: the old full canonical-data hypothesis still
discharges the smaller scalar-continuity obligation. -/
theorem h3ControlProducesExtension_of_unitViscositySmoothingCanonicalEnergy_via_minimal
    (hSmooth : H3SeedProducesEnergyClass)
    (hCanonical : EnergyClassProducesCanonicalH3Data) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscositySmoothingEnergyContinuity
      hSmooth
      (energyClassProducesCanonicalH3EnergyContinuity_of_canonicalData
        hCanonical)

end

end Euclidean
end Bridge
end PrimeTensor
