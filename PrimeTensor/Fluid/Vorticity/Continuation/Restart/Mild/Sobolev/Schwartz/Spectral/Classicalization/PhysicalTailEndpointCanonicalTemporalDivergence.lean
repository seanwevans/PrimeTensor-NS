import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalOldMomentum

/-!
# Classicalization: endpoint temporal derivative is divergence-free

The endpoint path now satisfies the old preterminal momentum equation
pointwise, but the remaining quotient-safe evolution step must eliminate
pressure through the incompressible/Leray structure rather than by
Fourier-transforming the old pressure.

The first structural fact needed for that step is that the endpoint temporal
derivative itself is divergence-free.

For the old preterminal velocity this follows from two hypotheses already
present in `PreterminalVorticityRegularity3`:

* incompressibility holds at every nearby preterminal time;
* every first spatial velocity derivative has a genuine time derivative, with
  time and space derivatives commuting.

Differentiate the three-coordinate divergence identity in time.  The mixed
`HasDerivAt` witnesses give the derivative coefficient, while local
incompressibility identifies the differentiated scalar function with the
constant zero function.  Uniqueness of derivatives therefore gives

    div (∂ₜ u_old) = 0.

The endpoint temporal-derivative identification then transports this identity
coordinatewise to the canonical reconstructed endpoint path.

No `L²`-valued time derivative is asserted here.  This is a pointwise spatial
divergence statement designed for the later weak/Leray projection argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalTemporalDivergence
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The old preterminal temporal derivative is divergence-free at every
strictly preterminal spacetime point. -/
theorem h3PreterminalLoggedVelocity_temporalDivergence_eq_zero
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hr : r ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    ∑ k : Fin 3,
      spatial3.d
        (h3AxisOfFin3 k)
        (fun y : Point3 =>
          temporal.d
            (fun q : ℝ =>
              (logSpaceTimeVectorField u q y).component
                (h3AxisOfFin3 k))
            r)
        x
      =
    0 := by
  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hx :=
    hPDE.regularity.velocity_space_time_hasDerivAt
      r hr x xAxis xAxis

  have hy :=
    hPDE.regularity.velocity_space_time_hasDerivAt
      r hr x yAxis yAxis

  have hz :=
    hPDE.regularity.velocity_space_time_hasDerivAt
      r hr x zAxis zAxis

  have hSum :=
    hx.add (hy.add hz)

  let D : ℝ → ℝ :=
    fun q : ℝ =>
      spatial3.d
          xAxis
          (fun y : Point3 =>
            (logSpaceTimeVectorField u q y).component xAxis)
          x
        +
      (spatial3.d
          yAxis
          (fun y : Point3 =>
            (logSpaceTimeVectorField u q y).component yAxis)
          x
        +
       spatial3.d
          zAxis
          (fun y : Point3 =>
            (logSpaceTimeVectorField u q y).component zAxis)
          x)

  have hSumD :
      HasDerivAt
        D
        (spatial3.d
            xAxis
            (fun y : Point3 =>
              temporal.d
                (fun q : ℝ =>
                  (logSpaceTimeVectorField u q y).component xAxis)
                r)
            x
          +
         (spatial3.d
            yAxis
            (fun y : Point3 =>
              temporal.d
                (fun q : ℝ =>
                  (logSpaceTimeVectorField u q y).component yAxis)
                r)
            x
          +
          spatial3.d
            zAxis
            (fun y : Point3 =>
              temporal.d
                (fun q : ℝ =>
                  (logSpaceTimeVectorField u q y).component zAxis)
                r)
            x))
        r := by
    dsimp only [D]
    exact hSum

  have hNeighborhood :
      Set.Ioo (0 : ℝ) T ∈ 𝓝 r :=
    Ioo_mem_nhds hr.1 hr.2

  have hEventuallyZero :
      D =ᶠ[𝓝 r] (fun _ : ℝ => 0) := by
    filter_upwards [hNeighborhood] with q hq
    dsimp only [D]
    exact
      hPDE.incompressible_xyz hq x

  have hZero :
      HasDerivAt
        (fun _ : ℝ => (0 : ℝ))
        0
        r :=
    hasDerivAt_const r 0

  have hDZero :
      HasDerivAt D 0 r :=
    hZero.congr_of_eventuallyEq hEventuallyZero

  have hExplicit :
      spatial3.d
          xAxis
          (fun y : Point3 =>
            temporal.d
              (fun q : ℝ =>
                (logSpaceTimeVectorField u q y).component xAxis)
              r)
          x
        +
      (spatial3.d
          yAxis
          (fun y : Point3 =>
            temporal.d
              (fun q : ℝ =>
                (logSpaceTimeVectorField u q y).component yAxis)
              r)
          x
        +
       spatial3.d
          zAxis
          (fun y : Point3 =>
            temporal.d
              (fun q : ℝ =>
                (logSpaceTimeVectorField u q y).component zAxis)
              r)
          x)
        =
      0 :=
    hSumD.unique hDZero

  simpa only [
    Fin.sum_univ_three,
    h3AxisOfFin3_zero,
    h3AxisOfFin3_one,
    h3AxisOfFin3_two,
    add_assoc
  ] using hExplicit

/-- On every strict physical elapsed time, the temporal derivative of the
canonical endpoint reconstructed velocity is divergence-free pointwise. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_temporalDivergence_eq_zero
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
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    ∑ k : Fin 3,
      spatial3.d
        (h3AxisOfFin3 k)
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              (h3SpectralRealVelocityOfPath W r y).component
                (h3AxisOfFin3 k))
            s)
        x
      =
    0 := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hsClosed :
      s ∈ Set.Icc (0 : ℝ) tau :=
    ⟨hs.1.le, hs.2.le⟩

  have hAbs :
      t + s ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd ⟨s, hsClosed⟩

  have hOld :
      ∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 k)
          (fun y : Point3 =>
            temporal.d
              (fun q : ℝ =>
                (logSpaceTimeVectorField u q y).component
                  (h3AxisOfFin3 k))
              (t + s))
          x
        =
      0 :=
    h3PreterminalLoggedVelocity_temporalDivergence_eq_zero
      hNS hAbs x

  have hTimeField
      (k : Fin 3) :
      (fun y : Point3 =>
        temporal.d
          (fun r : ℝ =>
            (h3SpectralRealVelocityOfPath W r y).component
              (h3AxisOfFin3 k))
          s)
        =
      (fun y : Point3 =>
        temporal.d
          (fun q : ℝ =>
            (logSpaceTimeVectorField u q y).component
              (h3AxisOfFin3 k))
          (t + s)) := by
    funext y

    have h :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_temporal_d_eq_old
        hNS ht htau hEnd hE hTail hEndpoint hs k y

    unfold loggedVelocityComponent at h

    simpa only [W] using h

  calc
    (∑ k : Fin 3,
      spatial3.d
        (h3AxisOfFin3 k)
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              (h3SpectralRealVelocityOfPath W r y).component
                (h3AxisOfFin3 k))
            s)
        x)
        =
      ∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 k)
          (fun y : Point3 =>
            temporal.d
              (fun q : ℝ =>
                (logSpaceTimeVectorField u q y).component
                  (h3AxisOfFin3 k))
              (t + s))
          x := by
      apply Finset.sum_congr rfl
      intro k hk
      exact
        congrArg
          (fun f : ScalarField3 =>
            spatial3.d
              (h3AxisOfFin3 k)
              f
              x)
          (hTimeField k)
    _ = 0 :=
      hOld

end

end Euclidean
end Bridge
end PrimeTensor
