import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Selected.Old.H3.Path.Admissible
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Continuity.Minimal

/-!
# Direct pressure-free restart from an H³ path

The corrected strong-solution class

    LoggedPreterminalH3PathAdmissible u T

already carries continuity of the canonical scalar H³ energy at every strict
preterminal time.

The pressure-free endpoint continuation tree only needs that scalar continuity,
together with terminal-tail H³ control.  It does not need the full
`CanonicalH3EnergyDataOnTail` package.

Therefore the continuation half of the H³-path BKM theorem can be closed
directly:

    H³ path
      + TerminalTailH3Control
      -> sufficiently late canonical H³ tail
      -> scalar energy continuity on that tail
      -> pressure-free endpoint continuity
      -> physical selected/old evolution
      -> real restart beyond T
      -> SmoothContinuationExtension.

No energy-class smoothing theorem and no canonical-analysis hypothesis is used
in this restart route.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathDirectRestart
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Scalar energy continuity supplied directly by the H³ path -/

/--
Pointwise continuity of the canonical H³ energy on `(0,T)` gives continuity on
every compact terminal subinterval whose left endpoint is strict preterminal.
-/
theorem LoggedPreterminalH3PathAdmissible.canonicalH3EnergyContinuousOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ha : a ∈ Set.Ioo (0 : ℝ) T) :
    CanonicalH3EnergyContinuousOnTail u a T := by

  intro b hb
  intro s hs

  have hsAbs :
      s ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · exact
        lt_of_lt_of_le
          ha.1
          hs.1
    · exact
        lt_of_le_of_lt
          hs.2
          hb.2

  exact
    (hH3.energy_continuousAt s hsAbs).continuousWithinAt

/-! ## Late restart directly from terminal H³ control -/

/--
On an H³ path, terminal-tail H³ control alone supplies the complete late
energy-continuous restart datum.

The restart anchor is chosen directly inside the controlled H³ tail; no
intermediate high-order energy-class tail is needed for the continuation
topology.
-/
theorem h3PreterminalTailUnitViscosityLateEnergyContinuousRestartData_of_h3Path_tailControl
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hControl : TerminalTailH3Control u T) :
    H3PreterminalTailUnitViscosityLateEnergyContinuousRestartData
      u T := by

  rcases hControl with
    ⟨
      a,
      M,
      ha,
      hM,
      hBound
    ⟩

  let E : ℝ :=
    velocityH3CoordinateBudget M

  have hE :
      1 ≤ E := by
    dsimp only [E]
    exact
      one_le_velocityH3CoordinateBudget hM

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  have hR :
      0 < R := by
    dsimp only [R]
    exact
      h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
        (one_pos : (0 : ℝ) < 1)
        hE

  let ε : ℝ :=
    min
      ((T - a) / 2)
      (R / 2)

  have hHalfTail :
      0 < (T - a) / 2 := by
    linarith [ha.2]

  have hHalfRadius :
      0 < R / 2 := by
    linarith

  have hε :
      0 < ε := by
    dsimp only [ε]
    exact
      lt_min hHalfTail hHalfRadius

  have hεTail :
      ε ≤ (T - a) / 2 := by
    dsimp only [ε]
    exact
      min_le_left _ _

  have hεRadius :
      ε ≤ R / 2 := by
    dsimp only [ε]
    exact
      min_le_right _ _

  let t₀ : ℝ :=
    T - ε

  have hat₀ :
      a ≤ t₀ := by
    dsimp only [t₀]
    linarith

  have ht₀T :
      t₀ < T := by
    dsimp only [t₀]
    linarith

  have ht₀Pos :
      0 < t₀ :=
    lt_of_lt_of_le
      ha.1
      hat₀

  have ht₀ :
      t₀ ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      ht₀Pos,
      ht₀T
    ⟩

  have hTail :
      CanonicalH3TailDataFrom
        u t₀ T E := by

    intro s hs

    have hsOld :
        s ∈ Set.Ico a T :=
      ⟨
        le_trans hat₀ hs.1,
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

  have hCont :
      CanonicalH3EnergyContinuousOnTail
        u t₀ T :=
    hH3.canonicalH3EnergyContinuousOnTail
      ht₀

  have hCross :
      T - t₀ <
        h3FinHeatLerayRestartRadius
          (1 : ℝ) E := by

    have hεLtR :
        ε < R := by
      have hHalfLt :
          R / 2 < R := by
        linarith

      exact
        lt_of_le_of_lt
          hεRadius
          hHalfLt

    dsimp only [t₀, R] at hεLtR ⊢
    linarith

  exact
    ⟨
      E,
      t₀,
      hE,
      ht₀,
      hTail,
      hCont,
      hCross
    ⟩

/--
An H³ path plus terminal-tail H³ control gives a complete real restart beyond
the old terminal time.
-/
theorem h3PathRealRestart_of_tailControl
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hControl : TerminalTailH3Control u T) :
    ∃
      (v : SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
      (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
      (S : ℝ),
        T < S
          ∧
        RealRestartAgreesBeforeT u v T
          ∧
        PreterminalNavierStokes3 v p S
          ∧
        RealVelocitySpatialC3 v
          ∧
        (∀ x : Point3,
          RealVelocityThirdJetContinuousAt v T x) := by

  let hNS :
      LoggedPreterminalNavierStokesAdmissible u T :=
    hH3.navier_stokes

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
    h3PreterminalTailUnitViscosityLateEnergyContinuousRestartData_of_h3Path_tailControl
      hH3
      hControl

  have hEndpoint :
      H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    h3PreterminalTailUnitViscosityEndpointContinuityOnRestartRadius_of_energyContinuity_pressureFree
      hNS
      ht
      hE
      hTail
      hCont

  have hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ)
        E
        (one_pos : (0 : ℝ) < 1)
        u
        T
        t
        hNS
        ht
        hE
        hTail :=
    h3PreterminalTailPhysicalEvolutionOnRestartRadius_of_unitViscosity_endpointContinuity
      hNS
      ht
      hE
      hTail
      hEndpoint

  have hLocalPDE :
      H3PreterminalTailUnitViscosityLocalPDEAt
        hNS ht hE hTail :=
    h3PreterminalTailUnitViscosityLocalPDEAt_closed_of_evolution
      hNS
      ht
      hE
      hTail
      hEvolution

  exact
    h3PreterminalTailUnitViscosityRealRestartAt_of_localPDE
      hNS
      ht
      hE
      hTail
      hEvolution
      hCross
      hLocalPDE

/--
Path-specific continuation interface at the terminal-H³ stage.
-/
def H3PathH3ControlProducesExtension : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      TerminalTailH3Control u T →
      ∃
        w : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u w T

/--
The H³-path continuation half is completely closed from terminal-tail H³
control.  Scalar energy continuity comes directly from the path class.
-/
theorem h3PathH3ControlProducesExtension :
    H3PathH3ControlProducesExtension := by

  intro u T hH3 hControl

  have hTPositive :
      0 < T := by
    rcases hControl with
      ⟨a, M, ha, hM, hBound⟩
    exact
      lt_trans ha.1 ha.2

  obtain
    ⟨
      v,
      p,
      S,
      hTS,
      hAgree,
      hPDE,
      hSpatial,
      hThird
    ⟩ :=
    h3PathRealRestart_of_tailControl
      hH3
      hControl

  refine
    ⟨
      nativeSpaceTimeVectorFieldOfReal v,
      smoothContinuationExtension_of_realRestart
        hAgree
        hPDE
        ?_
        hSpatial
        hThird
    ⟩

  exact
    ⟨
      hTPositive,
      hTS
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
