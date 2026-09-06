import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Selected.FirstSpatial
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Variation.Of.Constants

/-!
# Physical L² temporal admissibility: endpoint first-jet joint continuity

The selected-restart route has now closed all of its own spacetime regularity,
but using selected/old overlap to transfer that regularity back to the old
branch leaves the temporal FTC theorem conditional on
`H3PreterminalTailPhysicalEvolutionOnRestartRadius`.

This file starts a non-circular route.

The endpoint canonical path

    W : ℝ → H3SpectralFinVectorState

is already globally continuous in the weighted H³ norm whenever the reduced
zeroth/third physical `L²` endpoint-continuity hypothesis is available.

The decoder lemmas proved in the preceding temporal work are path-generic:

* `(G,x) ↦ Rep(G)(x)` is jointly continuous;
* `(G,x) ↦ ∂ₐ Rep(G)(x)` is jointly continuous.

Therefore they apply directly to the endpoint canonical path itself.  No
selected mild solution, overlap equality, or physical-evolution hypothesis is
used.

This closes joint spacetime continuity of the old endpoint velocity and its
complete first spatial jet.  In particular, the nonlinear advection term can
now be handled on the old endpoint path without any overlap assumption.  The
next weak-FTC step can integrate the viscous term by parts and annihilate
pressure against divergence-free compact tests, avoiding the unavailable
second-spatial-jet/pressure joint continuity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFirstJet
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Match the norm topology used by the physical weak-test layer. -/
local instance point3NormTopologicalSpaceH3PhysicalL2TemporalEndpointFirstJet :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Joint continuity of one real reconstructed coordinate of the endpoint
canonical path, with no selected-overlap hypothesis. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_coordinate_jointContinuous
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (i : Fin 3) :
    Continuous
      (fun z : ℝ × Point3 =>
        h3SpectralScalarRealC1RepresentativeOnPoint3
          ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau hEnd hE hTail hEndpoint) z.1 i)
          z.2) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau hEnd hE hTail hEndpoint

  have hW :
      Continuous W := by
    dsimp only [W]
    exact
      continuous_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau hEnd hE hTail hEndpoint

  have hJoint :=
    h3SpectralScalarRealC1RepresentativeOnPoint3_jointContinuous_of_finSpectralPath
      W hW i

  simpa only [W] using hJoint

/-- Joint continuity of one first spatial derivative of one endpoint
reconstructed coordinate, again directly from H³ path continuity. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_coordinate_spatial_d_jointContinuous
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (i a : Fin 3) :
    Continuous
      (fun z : ℝ × Point3 =>
        spatial3.d
          (h3AxisOfFin3 a)
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
              hNS ht htau hEnd hE hTail hEndpoint) z.1 i))
          z.2) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau hEnd hE hTail hEndpoint

  have hW :
      Continuous W := by
    dsimp only [W]
    exact
      continuous_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau hEnd hE hTail hEndpoint

  have hJoint :=
    h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_jointContinuous_of_finSpectralPath
      W hW i a

  simpa only [W] using hJoint

/-- Exact endpoint-path velocity components are jointly continuous. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_velocity_component_jointContinuous
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (j : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun z : ℝ × Point3 =>
        (h3SpectralRealVelocityOfPath
          (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau hEnd hE hTail hEndpoint)
          z.1 z.2).component j) := by
  let i : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have hCoordinate :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_coordinate_jointContinuous
      hNS ht htau hEnd hE hTail hEndpoint i

  apply hCoordinate.congr

  intro z

  rw [
    h3SpectralRealVelocityOfPath_component
  ]

  unfold
    h3SpectralVelocityRealC1RepresentativeOnPoint3

  dsimp only [i]

/-- Exact endpoint-path first spatial velocity derivatives are jointly
continuous. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_velocity_spatial_d_jointContinuous
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (a j : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun z : ℝ × Point3 =>
        spatial3.d
          a
          (fun y : Point3 =>
            (h3SpectralRealVelocityOfPath
              (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                hNS ht htau hEnd hE hTail hEndpoint)
              z.1 y).component j)
          z.2) := by
  let i : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  let k : Fin 3 :=
    h3ClassicalizationFinOfAxis a

  have hCoordinate :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_coordinate_spatial_d_jointContinuous
      hNS ht htau hEnd hE hTail hEndpoint i k

  rw [
    h3AxisOfFin3_h3ClassicalizationFinOfAxis
      a
  ] at hCoordinate

  apply hCoordinate.congr

  intro z

  have hField :
      (fun y : Point3 =>
        (h3SpectralRealVelocityOfPath
          (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau hEnd hE hTail hEndpoint)
          z.1 y).component j)
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3
        ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau hEnd hE hTail hEndpoint)
          z.1 i) := by
    funext y

    rw [
      h3SpectralRealVelocityOfPath_component
    ]

    unfold
      h3SpectralVelocityRealC1RepresentativeOnPoint3

    dsimp only [i]

  exact
    congrArg
      (fun f : Point3 → ℝ =>
        spatial3.d a f z.2)
      hField

/-- Package the non-circular old-endpoint first-jet result on the genuine
elapsed slab. -/
def H3PreterminalTailCanonicalEndpointVelocityFirstJetsJointlyContinuousOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) : Prop :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint
  (∀ j : PrimeTensor.Axis Depth.three,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        (h3SpectralRealVelocityOfPath W z.1 z.2).component j)
      (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ))
    ∧
  (∀ a j : PrimeTensor.Axis Depth.three,
    ContinuousOn
      (fun z : ℝ × Point3 =>
        spatial3.d
          a
          (fun y : Point3 =>
            (h3SpectralRealVelocityOfPath W z.1 y).component j)
          z.2)
      (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ))

/-- Endpoint H³ path continuity automatically supplies the complete value/first
spatial jet joint-continuity package; no physical-evolution/overlap hypothesis
is involved. -/
theorem H3PreterminalTailCanonicalEndpointVelocityFirstJetsJointlyContinuousOnElapsed_proved
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalTailCanonicalEndpointVelocityFirstJetsJointlyContinuousOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint := by
  unfold
    H3PreterminalTailCanonicalEndpointVelocityFirstJetsJointlyContinuousOnElapsed

  dsimp only

  constructor

  · intro j

    exact
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_velocity_component_jointContinuous
        hNS ht htau.le hEnd hE hTail hEndpoint j).continuousOn

  · intro a j

    exact
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_velocity_spatial_d_jointContinuous
        hNS ht htau.le hEnd hE hTail hEndpoint a j).continuousOn

end

end Euclidean
end Bridge
end PrimeTensor
