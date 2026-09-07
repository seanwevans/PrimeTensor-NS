import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.PointwiseTemporalFTC
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Velocity.Pairing.Continuity

/-!
# Physical L² temporal admissibility: pair the pointwise temporal primitive

`PointwiseTemporalFTC` changed the order of the weak temporal argument.

Instead of differentiating the compactly tested spatial integral and requiring a
uniform pointwise spatial majorant, we first applied ordinary scalar FTC at each
fixed physical point:

    W_i(q,x) - W_i(0,x)
      =
    ∫₀^q ∂ₜ W_i(r,x) dr.

This file now performs the harmless spatial operation around that identity.

For every compact weak test vector `φ`, the endpoint velocity slices at `q` and
zero are continuous in space.  Compact support therefore makes

    x ↦ φ_i(x) W_i(q,x),
    x ↦ φ_i(x) W_i(0,x)

integrable.  Hence their difference may be combined under one spatial
integral.  The pointwise FTC then identifies that integrand with the temporal
primitive.

After summing the three velocity coordinates we obtain

    <φ,W(q)> - <φ,W(0)>
      =
    Σ_i ∫_x φ_i(x) [∫₀^q ∂ₜW_i(r,x) dr] dx.

Crucially, there is still no interchange of time and space integrals here.
Thus no new spacetime domination statement has been smuggled into the proof.
The next checkpoint is exactly the Fubini step, to be justified from `L²`
control rather than from the superseded pointwise-majorant frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointPointwiseTemporalPrimitivePairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2TemporalEndpointPointwiseTemporalPrimitivePairing :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A compact smooth scalar test times one endpoint velocity coordinate is
integrable on every closed elapsed slice. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_test_mul_velocity_integrable_closed
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
    {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (φ : H3WeakTestFunction) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          ((h3SpectralRealVelocityOfPath W s x).component
            (h3AxisOfFin3 i)))
      (volume : Measure Point3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let f : Point3 → ℝ :=
    fun x =>
      (h3SpectralRealVelocityOfPath W s x).component
        (h3AxisOfFin3 i)

  have hAbs :
      t + s ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd ⟨s, hs⟩

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hOldContinuous :
      Continuous
        (loggedVelocityComponent
          u
          (t + s)
          (h3AxisOfFin3 i)) := by
    unfold loggedVelocityComponent
    exact
      (hPDE.regularity.velocity_spatial_three
        (t + s)
        hAbs
        (h3AxisOfFin3 i)).continuous

  have hEq :
      f
        =
      loggedVelocityComponent
        u
        (t + s)
        (h3AxisOfFin3 i) := by
    dsimp only [f, W]
    exact
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_eq_old
        hNS ht htau hEnd hE hTail hEndpoint
        s hs i

  have hfContinuous :
      Continuous f := by
    rw [hEq]
    exact hOldContinuous

  change
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          (f x))
      (volume : Measure Point3)

  exact
    φ.integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (hfContinuous.locallyIntegrable.locallyIntegrableOn Set.univ)

/-- The compactly tested endpoint velocity increment is the spatial integral of
the pointwise temporal primitive.

This theorem deliberately does not swap the time and space integrals. -/
theorem h3PreterminalTailCanonicalVelocityWeakPairingDifference_eq_spatialIntegral_temporalPrimitive_to
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (φ : H3WeakTestVector)
    (hq : q ∈ Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨q, hq⟩
      -
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨0, ⟨le_rfl, htau.le⟩⟩
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (∫ r in (0 : ℝ)..q,
            temporal.d
              (fun s : ℝ =>
                (h3SpectralRealVelocityOfPath
                  (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                    hNS ht htau.le hEnd hE hTail hEndpoint)
                  s x).component
                    (h3AxisOfFin3 i))
              r)
        ∂volume := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let qI : Set.Icc (0 : ℝ) tau :=
    ⟨q, hq⟩

  let zI : Set.Icc (0 : ℝ) tau :=
    ⟨0, ⟨le_rfl, htau.le⟩⟩

  have hQ :
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail φ qI
        =
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3SpectralRealVelocityOfPath W q x).component
              (h3AxisOfFin3 i))
          ∂volume := by
    simpa only [W, qI] using
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed_eq_integral_normalizedRealPath
        hNS ht htau hEnd hE hTail hEndpoint φ qI

  have hZero :
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail φ zI
        =
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3SpectralRealVelocityOfPath W 0 x).component
              (h3AxisOfFin3 i))
          ∂volume := by
    simpa only [W, zI] using
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed_eq_integral_normalizedRealPath
        hNS ht htau hEnd hE hTail hEndpoint φ zI

  change
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ qI
      -
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ zI
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (∫ r in (0 : ℝ)..q,
            temporal.d
              (fun s : ℝ =>
                (h3SpectralRealVelocityOfPath W s x).component
                  (h3AxisOfFin3 i))
              r)
        ∂volume

  rw [hQ, hZero, ← Finset.sum_sub_distrib]

  apply Finset.sum_congr rfl
  intro i hi

  have hIntQ :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3SpectralRealVelocityOfPath W q x).component
              (h3AxisOfFin3 i)))
        (volume : Measure Point3) := by
    simpa only [W] using
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_test_mul_velocity_integrable_closed
        hNS ht htau hEnd hE hTail hEndpoint
        hq i (φ i)

  have hIntZero :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((h3SpectralRealVelocityOfPath W 0 x).component
              (h3AxisOfFin3 i)))
        (volume : Measure Point3) := by
    simpa only [W] using
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_test_mul_velocity_integrable_closed
        hNS ht htau hEnd hE hTail hEndpoint
        ⟨le_rfl, htau.le⟩ i (φ i)

  rw [← integral_sub hIntQ hIntZero]

  apply integral_congr_ae

  filter_upwards with x

  have hFTC :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_intervalIntegral_temporalDerivative_to
      hNS ht htau hEnd hE hTail hEndpoint
      hq i x

  change
    (φ i x) *
          (h3SpectralRealVelocityOfPath W q x).component
            (h3AxisOfFin3 i)
        -
      (φ i x) *
          (h3SpectralRealVelocityOfPath W 0 x).component
            (h3AxisOfFin3 i)
      =
    (φ i x) *
      (∫ r in (0 : ℝ)..q,
        temporal.d
          (fun s : ℝ =>
            (h3SpectralRealVelocityOfPath W s x).component
              (h3AxisOfFin3 i))
          r)

  dsimp only [W] at hFTC

  rw [hFTC]

  ring

end

end Euclidean
end Bridge
end PrimeTensor
