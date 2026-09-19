import PrimeTensor.Fluid.Vorticity.Continuation.Restart.EnergyLifespan
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Preterminal.Canonical.Energy.Restart.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Spatial.Five
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.Selected.C4
import PrimeTensor.Fluid.Vorticity.H3.Energy.Regularity

/-!
# Selected high-order regularity directly from one H³ seed anchor

The selected positive-time restart is already spatially much smoother than the
old preterminal solution.  Earlier high-order packaging routed this fact
through

    CanonicalH3TailDataFrom u t T E,

which contains H³ information at every later old time.

That full future-tail hypothesis is not needed to launch the selected restart.
At one interior old time `t`, a single `VelocityH3BoundAt u t M` gives:

* H³ integrability at the anchor;
* the canonical Fourier-compatible spectral state;
* a normalized scalar ceiling `velocityH3CoordinateBudget M`;
* the corresponding positive spectral restart radius.

The generic selected-mild regularity theorems then give spatial `C⁵` velocity
and spatial `C⁴` pressure throughout the positive restart window.

This file packages exactly that anchor-only statement.  It deliberately does
not transfer the selected regularity back to the old solution.  After this
increment the remaining smoothing obstruction is therefore localized to
selected/old agreement (and its iteration), not to construction of the smooth
selected restart itself.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedHighOrderSeed
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Canonical spectral anchor from one H³ bound -/

/--
The canonical spectral state at one H³-bounded interior old slice.

Unlike the older tail anchor, this definition consumes no future-tail data.
-/
noncomputable def h3PreterminalH3BoundAnchorSpectralState
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t M : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hBound : VelocityH3BoundAt u t M) :
    H3SpectralVelocityState :=
  let hInt : VelocityH3IntegrableAt u t :=
    velocityH3IntegrableAt_of_bound hBound
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS ht
  let hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS ht hInt
  velocityH3SpectralStateAt
    u t hInt hMeas hFourier

/--
The coordinate budget attached to the single H³ bound controls the canonical
spectral anchor norm.
-/
theorem norm_h3PreterminalH3BoundAnchorSpectralState_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t M : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hM : 0 ≤ M)
    (hBound : VelocityH3BoundAt u t M) :
    ‖h3PreterminalH3BoundAnchorSpectralState
        hNS ht hBound‖
      ≤
    velocityH3CoordinateBudget M := by

  let hInt : VelocityH3IntegrableAt u t :=
    velocityH3IntegrableAt_of_bound hBound

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS ht

  let hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS ht hInt

  change
    ‖velocityH3SpectralStateAt
        u t hInt hMeas hFourier‖
      ≤
    velocityH3CoordinateBudget M

  exact
    norm_velocityH3SpectralStateAt_le_energyCeiling
      hFourier
      (one_le_velocityH3CoordinateBudget hM)
      (velocityH3EnergyAt_le_coordinateBudget_of_bound
        hBound)

/-! ## High-order selected restart from the anchor -/

/--
One anchor H³ bound is enough to obtain the selected velocity's exact
`VelocitySpatialC5OnTail` local shape at every positive time inside its
unit-viscosity restart radius.
-/
theorem h3PreterminalH3Bound_selectedVelocity_secondPartial_spatialC3
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t M q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hM : 0 ≤ M)
    (hBound : VelocityH3BoundAt u t M)
    (hq0 : 0 < q)
    (hqR :
      q ≤
        h3FinHeatLerayRestartRadius
          (1 : ℝ)
          (velocityH3CoordinateBudget M))
    (j i k : PrimeTensor.Axis Depth.three) :
    let E : ℝ :=
      velocityH3CoordinateBudget M
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalH3BoundAnchorSpectralState
        hNS ht hBound
    let hE : 1 ≤ E :=
      one_le_velocityH3CoordinateBudget hM
    let hEpos : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalH3BoundAnchorSpectralState_le
        hNS ht hM hBound
    SpatialC3
      (spatial3.d i
        (spatial3.d k
          (fun y =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              U₀
              hEpos
              hU₀
              q
              y).component j))) := by

  dsimp only

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_secondPartial_spatialC3At
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalH3BoundAnchorSpectralState
        hNS ht hBound)
      (lt_of_lt_of_le
        zero_lt_one
        (one_le_velocityH3CoordinateBudget hM))
      (norm_h3PreterminalH3BoundAnchorSpectralState_le
        hNS ht hM hBound)
      hq0
      hqR
      j i k

/--
The same single anchor H³ bound gives the selected pressure's exact
`PressureSpatialC4OnTail` local shape throughout the positive restart window.
-/
theorem h3PreterminalH3Bound_selectedPressure_spatialDerivative_spatialC3
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t M q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hM : 0 ≤ M)
    (hBound : VelocityH3BoundAt u t M)
    (hq0 : 0 < q)
    (hqR :
      q ≤
        h3FinHeatLerayRestartRadius
          (1 : ℝ)
          (velocityH3CoordinateBudget M))
    (i : PrimeTensor.Axis Depth.three) :
    let E : ℝ :=
      velocityH3CoordinateBudget M
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalH3BoundAnchorSpectralState
        hNS ht hBound
    let hE : 1 ≤ E :=
      one_le_velocityH3CoordinateBudget hM
    let hEpos : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalH3BoundAnchorSpectralState_le
        hNS ht hM hBound
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1)
        U₀
        hEpos
        hU₀
    SpatialC3
      (spatial3.d i
        (h3RawFinPressureRealC1OfPath W q)) := by

  dsimp only

  exact
    h3RawFinPressureRealC1OfPath_selectedRestart_spatialDerivative_spatialC3
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalH3BoundAnchorSpectralState
        hNS ht hBound)
      (lt_of_lt_of_le
        zero_lt_one
        (one_le_velocityH3CoordinateBudget hM))
      (norm_h3PreterminalH3BoundAnchorSpectralState_le
        hNS ht hM hBound)
      hq0
      hqR
      i

/--
Package both selected high-order conclusions on the complete positive
unit-viscosity restart window issued from one H³-bounded old slice.
-/
def H3SelectedHighOrderOnRestartFromBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t M : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hM : 0 ≤ M)
    (hBound : VelocityH3BoundAt u t M) : Prop :=
  let E : ℝ :=
    velocityH3CoordinateBudget M
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalH3BoundAnchorSpectralState
      hNS ht hBound
  let hE : 1 ≤ E :=
    one_le_velocityH3CoordinateBudget hM
  let hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE
  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalH3BoundAnchorSpectralState_le
      hNS ht hM hBound
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀
      hEpos
      hU₀
  (
    ∀ q : ℝ,
      q ∈ Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
      ∀ j i k : PrimeTensor.Axis Depth.three,
        SpatialC3
          (spatial3.d i
            (spatial3.d k
              (fun y =>
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                  (one_pos : (0 : ℝ) < 1)
                  U₀
                  hEpos
                  hU₀
                  q
                  y).component j)))
  )
    ∧
  (
    ∀ q : ℝ,
      q ∈ Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
      ∀ i : PrimeTensor.Axis Depth.three,
        SpatialC3
          (spatial3.d i
            (h3RawFinPressureRealC1OfPath W q))
  )

/--
Every single H³-bounded interior old slice therefore launches a selected
high-order restart.  No future H³ tail is used.
-/
theorem h3PreterminalH3Bound_selectedHighOrderOnRestart
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t M : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hM : 0 ≤ M)
    (hBound : VelocityH3BoundAt u t M) :
    H3SelectedHighOrderOnRestartFromBound
      hNS ht hM hBound := by

  unfold H3SelectedHighOrderOnRestartFromBound
  dsimp only

  constructor

  · intro q hq j i k
    exact
      h3PreterminalH3Bound_selectedVelocity_secondPartial_spatialC3
        hNS
        ht
        hM
        hBound
        hq.1
        hq.2
        j i k

  · intro q hq i
    exact
      h3PreterminalH3Bound_selectedPressure_spatialDerivative_spatialC3
        hNS
        ht
        hM
        hBound
        hq.1
        hq.2
        i

/--
Consequently every `PreterminalH3Seed` already supplies a selected high-order
restart at its seed anchor.

The remaining step toward `H3SeedProducesEnergyClass` is to identify this smooth
selected restart with the old preterminal branch on successive overlap
intervals.
-/
theorem h3PreterminalH3Seed_selectedHighOrderRestart
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hSeed : PreterminalH3Seed u T) :
    ∃
      (t M : ℝ)
      (ht : t ∈ Set.Ioo (0 : ℝ) T)
      (hM : 0 ≤ M)
      (hBound : VelocityH3BoundAt u t M),
        H3SelectedHighOrderOnRestartFromBound
          hNS ht hM hBound := by

  rcases hSeed with
    ⟨
      t,
      M,
      ht,
      hM,
      hBound
    ⟩

  exact
    ⟨
      t,
      M,
      ht,
      hM,
      hBound,
      h3PreterminalH3Bound_selectedHighOrderOnRestart
        hNS ht hM hBound
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
