import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.FirstJet
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Raw.Outer.Divergence.Advection

/-!
# Physical L² temporal admissibility: endpoint advection joint continuity

The endpoint canonical velocity and its complete first spatial jet are now
jointly continuous in `(elapsed time, physical point)` without selected/old
overlap.

This file closes the corresponding nonlinear physical field.

For each output coordinate,

    (u · ∇)uᵢ
      =
    uₓ ∂ₓuᵢ + uᵧ ∂ᵧuᵢ + u_z ∂_z uᵢ,

so joint continuity follows directly from the value/first-jet package.

The endpoint raw-outer-divergence bridge already identifies the inverse Fourier
reconstruction of the unprojected nonlinear term with this same physical
advection on every genuine elapsed slice.  Hence its real physical
reconstruction is jointly continuous on the slab as well.

No selected mild solution, overlap equality, physical-evolution hypothesis,
pressure regularity, or second spatial derivative is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointAdvection
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Match the norm topology used by the physical weak-test layer. -/
local instance point3NormTopologicalSpaceH3PhysicalL2TemporalEndpointAdvection :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The endpoint canonical physical advection is jointly continuous on the
strict elapsed slab, with no overlap/evolution hypothesis. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_advection_component_jointContinuousOn
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
        hNS ht hEnd hTail)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    ContinuousOn
      (fun z : ℝ × Point3 =>
        (PrimeTensor.Bridge.RealFluid.advection
          spatial3
          (h3SpectralRealVelocityOfPath W)
          z.1 z.2).component
            (h3AxisOfFin3 i))
      (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hJets :
      H3PreterminalTailCanonicalEndpointVelocityFirstJetsJointlyContinuousOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint :=
    H3PreterminalTailCanonicalEndpointVelocityFirstJetsJointlyContinuousOnElapsed_proved
      hNS ht htau hEnd hE hTail hEndpoint

  unfold
    H3PreterminalTailCanonicalEndpointVelocityFirstJetsJointlyContinuousOnElapsed
    at hJets

  dsimp only at hJets

  rcases hJets with
    ⟨hValue, hFirst⟩

  change
    ContinuousOn
      (fun z : ℝ × Point3 =>
        (h3SpectralRealVelocityOfPath W z.1 z.2).component xAxis
            *
          spatial3.d
            xAxis
            (fun y : Point3 =>
              (h3SpectralRealVelocityOfPath W z.1 y).component
                (h3AxisOfFin3 i))
            z.2
          +
        (
          (h3SpectralRealVelocityOfPath W z.1 z.2).component yAxis
              *
            spatial3.d
              yAxis
              (fun y : Point3 =>
                (h3SpectralRealVelocityOfPath W z.1 y).component
                  (h3AxisOfFin3 i))
              z.2
            +
          (h3SpectralRealVelocityOfPath W z.1 z.2).component zAxis
              *
            spatial3.d
              zAxis
              (fun y : Point3 =>
                (h3SpectralRealVelocityOfPath W z.1 y).component
                  (h3AxisOfFin3 i))
              z.2
        ))
      (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ)

  exact
    ((hValue xAxis).mul
        (hFirst
          xAxis
          (h3AxisOfFin3 i))).add
      (((hValue yAxis).mul
          (hFirst
            yAxis
            (h3AxisOfFin3 i))).add
        ((hValue zAxis).mul
          (hFirst
            zAxis
            (h3AxisOfFin3 i))))

/-- The real inverse-Fourier reconstruction of the endpoint unprojected raw
outer-product divergence is jointly continuous on the strict elapsed slab.

This is the exact raw nonlinear field, not the Leray-projected forcing. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawOuterDivergence_fourierInv_re_jointContinuousOn
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
        hNS ht hEnd hTail)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    ContinuousOn
      (fun z : ℝ × Point3 =>
        (FourierTransformInv.fourierInv
          (h3RawFinOuterProductDivergence
            (W z.1) (W z.1) i)
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) z.2)).re)
      (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hAdvection :
      ContinuousOn
        (fun z : ℝ × Point3 =>
          (PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (h3SpectralRealVelocityOfPath W)
            z.1 z.2).component
              (h3AxisOfFin3 i))
        (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ) := by
    simpa only [W] using
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_advection_component_jointContinuousOn
        hNS ht htau hEnd hE hTail hEndpoint i

  apply hAdvection.congr

  intro z hz

  have hsClosed :
      z.1 ∈ Set.Icc (0 : ℝ) tau :=
    ⟨hz.1.1.le, hz.1.2.le⟩

  simpa only [W] using
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawOuterDivergence_fourierInv_re_eq_advection
      hNS ht htau hEnd hE hTail hEndpoint
      z.1 hsClosed i z.2

end

end Euclidean
end Bridge
end PrimeTensor
