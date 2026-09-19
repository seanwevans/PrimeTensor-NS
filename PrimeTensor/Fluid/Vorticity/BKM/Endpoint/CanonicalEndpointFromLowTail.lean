import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.CanonicalSelectedLogBound
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.LogarithmicGradientInterface
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Mixed.Derivative

/-!
# BKM endpoint: canonical logarithmic endpoint from a zeroth-order L² tail bound

The selected low/middle/high estimate has already been converted to the
canonical logarithmic form, conditional on one time-independent scalar `L`
controlling the zeroth-order physical velocity `L²` mass.

This file removes all remaining pointwise spectral bookkeeping from that
hypothesis.

We package the low-frequency datum directly in physical variables:

    ∫ |u_j(t,x)|² dx ≤ L²

for every velocity component and every strict tail time.

The generic H³ profile already supplies square integrability at each time.
Preterminal Navier--Stokes regularity supplies measurability and exact Fourier
compatibility.  The physical square-energy bound therefore converts to

    ‖velocityH3L2JetAt ... (h3JetSlot0 j)‖ ≤ L,

which feeds directly into the canonical selected logarithmic estimate.

Finally the intrinsic `Axis Depth.three` coordinates are converted to `Fin 3`
using the already-proved exact inverse coordinate bridge.  The result is an
`ActualVelocityGradientLogBoundFrom` theorem for the canonical normalized H³
energy.

The only remaining analytic input is now the standard kinetic-energy statement
that produces one such time-independent `L` from the tail anchor.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeBKMEndpointCanonicalEndpointFromLowTail
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Physical low-frequency tail datum -/

/--
Uniform zeroth-order physical `L²` control on a strict terminal tail.

The nonnegative scalar `L` is the actual `L²` radius, so the physical square
energy is bounded by `L²`.
-/
def BKMZerothVelocityL2TailBound
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T L : ℝ) : Prop :=
  0 ≤ L
    ∧
  ∀ t : ℝ,
    t ∈ Set.Ioo a T →
      ∀ j : Fin 3,
        spatialSquareEnergy
            (loggedVelocityComponent
              u t (h3AxisOfFin3 j))
          ≤
        L ^ 2

/--
A physical zeroth-order square-energy tail bound gives the exact `L²` norm
bound needed by the selected low-frequency estimate.
-/
theorem norm_velocityH3L2JetAt_slot0_le_of_BKMZerothVelocityL2TailBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T L t : ℝ}
    (hLow : BKMZerothVelocityL2TailBound u a T L)
    (ht : t ∈ Set.Ioo a T)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j : Fin 3) :
    ‖velocityH3L2JetAt
        u t hInt hMeas
        (h3JetSlot0 j)‖
      ≤
    L := by

  have hSquare :
      ‖velocityH3L2JetAt
          u t hInt hMeas
          (h3JetSlot0 j)‖ ^ 2
        ≤
      L ^ 2 := by

    rw [
      velocityH3L2JetAt_coordinate_norm_sq
        hInt hMeas (h3JetSlot0 j)
    ]

    simpa only [
      h3JetSlot0,
      velocityH3JetFieldAt
    ] using
      hLow.2 t ht j

  have hNorm :
      0 ≤
      ‖velocityH3L2JetAt
          u t hInt hMeas
          (h3JetSlot0 j)‖ :=
    norm_nonneg _

  nlinarith [hLow.1]

/-! ## Canonical logarithmic bound on the whole tail -/

/--
The canonical selected estimate can be invoked at every strict tail time using
only the H³ profile and the physical zeroth-order `L²` tail bound.
-/
theorem one_add_abs_loggedVelocityComponent_spatial_d_le_canonicalSelectedBKM_of_lowTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T L t : ℝ}
    {g : ℝ → ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ha : a ∈ Set.Ioo (0 : ℝ) T)
    (hg :
      ∀ s : ℝ,
        s ∈ Set.Ioo a T →
          VorticityEnvelope u g s)
    (hProfile :
      H3EnergyProfileFrom
        u a T
        (velocityH3EnergyAt u))
    (hLow : BKMZerothVelocityL2TailBound u a T L)
    (ht : t ∈ Set.Ioo a T)
    (j i : Fin 3)
    (x : Point3) :
    1
        +
      abs
        (spatial3.d
          (h3AxisOfFin3 i)
          (loggedVelocityComponent
            u t (h3AxisOfFin3 j))
          x)
      ≤
    h3BKMCanonicalSelectedLogGradientConstant L
      * (1 + |g t|)
      * (1 + Real.log (velocityH3EnergyAt u t)) := by

  have htNS :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans ha.1 ht.1,
      ht.2
    ⟩

  have hAt :
      1 ≤ velocityH3EnergyAt u t
        ∧
      VelocityH3BoundAt
        u t (velocityH3EnergyAt u t) :=
    hProfile
      t
      ⟨
        le_of_lt ht.1,
        ht.2
      ⟩

  let hInt :
      VelocityH3IntegrableAt u t :=
    velocityH3IntegrableAt_of_bound
      hAt.2

  let hMeas :
      VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS htNS

  let hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS htNS hInt

  have hLowNorm :
      ∀ k : Fin 3,
        ‖velocityH3L2JetAt
            u t hInt hMeas
            (h3JetSlot0 k)‖
          ≤
        L := by

    intro k

    exact
      norm_velocityH3L2JetAt_slot0_le_of_BKMZerothVelocityL2TailBound
        hLow ht hInt hMeas k

  exact
    one_add_abs_loggedVelocityComponent_spatial_d_le_canonicalSelectedBKM
      hNS
      htNS
      hFourier
      (hg t ht)
      L
      hLow.1
      hLowNorm
      j i x

/-! ## Intrinsic-axis public endpoint form -/

/--
A physical zeroth-order `L²` tail bound closes the corrected actual-gradient
logarithmic endpoint for the canonical normalized H³ energy.
-/
theorem actualVelocityGradientLogBoundFrom_canonicalSelectedBKM_of_lowTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T L : ℝ}
    {g : ℝ → ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ha : a ∈ Set.Ioo (0 : ℝ) T)
    (hg :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          VorticityEnvelope u g t)
    (hProfile :
      H3EnergyProfileFrom
        u a T
        (velocityH3EnergyAt u))
    (hLow : BKMZerothVelocityL2TailBound u a T L) :
    ActualVelocityGradientLogBoundFrom
      u a T g
      (velocityH3EnergyAt u)
      (h3BKMCanonicalSelectedLogGradientConstant L) := by

  intro t ht i j x

  let ii : Fin 3 :=
    h3ClassicalizationFinOfAxis i

  let jj : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have hFin :=
    one_add_abs_loggedVelocityComponent_spatial_d_le_canonicalSelectedBKM_of_lowTail
      hNS ha hg hProfile hLow ht jj ii x

  dsimp only [ii, jj] at hFin

  rw [
    h3AxisOfFin3_h3ClassicalizationFinOfAxis i,
    h3AxisOfFin3_h3ClassicalizationFinOfAxis j
  ] at hFin

  change
    1
        +
      abs
        (spatial3.d
          i
          (fun y : Point3 =>
            (logSpaceTimeVectorField u t y).component j)
          x)
      ≤
    h3BKMCanonicalSelectedLogGradientConstant L
      * (1 + |g t|)
      * (1 + Real.log (velocityH3EnergyAt u t))
    at hFin

  exact hFin

/--
The canonical selected logarithmic constant produced from a physical low-tail
bound is nonnegative.
-/
theorem h3BKMCanonicalSelectedLogGradientConstant_nonneg_of_lowTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T L : ℝ}
    (hLow : BKMZerothVelocityL2TailBound u a T L) :
    0 ≤ h3BKMCanonicalSelectedLogGradientConstant L :=
  h3BKMCanonicalSelectedLogGradientConstant_nonneg
    hLow.1

end

end Euclidean
end Bridge
end PrimeTensor
