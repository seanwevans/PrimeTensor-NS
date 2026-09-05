import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalOldTemporalDerivative
import PrimeTensor.Fluid.Vorticity.Preterminal.Equation

/-!
# Classicalization: old preterminal momentum on the endpoint canonical path

The endpoint canonical normalized real path has now been identified with the old
preterminal solution in all three pieces entering the classical momentum
equation:

* its scalar relative-time derivative is the old absolute-time derivative;
* its physical advection is the old physical advection;
* its spatial Laplacian is the old physical Laplacian.

This file composes those three exact representation bridges with the genuine
preterminal Navier--Stokes momentum equation.

The old pressure supplied by
`LoggedPreterminalNavierStokesAdmissible` is deliberately retained.  The result
is therefore a pointwise classical PDE for the endpoint reconstructed velocity,

    ∂ₛ W + (W · ∇)W = -∇p_old(t+s) + ΔW,

throughout the strict physical elapsed interval `(0,τ)`.

No Fourier transform of the old pressure is introduced.  In particular this
does not yet claim the quotient-safe Fourier `L²` evolution equation; pressure
elimination there still belongs to the weak/Leray step.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalOldMomentum
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Stable conversion of the project's three-axis Laplacian fold to the
`Fin 3` sum used by the endpoint spectral classicalization layer. -/
theorem realFluid_laplacianVector_component_eq_fin_sum_three_endpoint
    (v : SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (s : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    (PrimeTensor.Bridge.RealFluid.laplacianVector
      spatial3 v s x).component j
      =
    ∑ k : Fin 3,
      spatial3.d
        (h3AxisOfFin3 k)
        (spatial3.d
          (h3AxisOfFin3 k)
          (fun y : Point3 =>
            (v s y).component j))
        x := by
  change
    PrimeTensor.Axis.fold
        (· + ·)
        Depth.three
        (fun a =>
          spatial3.d
            a
            (spatial3.d
              a
              (fun y : Point3 =>
                (v s y).component j))
            x)
      =
    ∑ k : Fin 3,
      spatial3.d
        (h3AxisOfFin3 k)
        (spatial3.d
          (h3AxisOfFin3 k)
          (fun y : Point3 =>
            (v s y).component j))
        x

  rw [PrimeTensor.Bridge.Euclidean.axis_fold_three]

  simp only [
    Fin.sum_univ_three,
    h3AxisOfFin3_zero,
    h3AxisOfFin3_one,
    h3AxisOfFin3_two
  ]

  rw [add_assoc]

/-- On every strict physical elapsed time, the endpoint reconstructed velocity
satisfies the genuine old preterminal momentum equation with the old pressure,
written entirely in the endpoint clock. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_oldPressure_momentum_fin
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
    (i : Fin 3)
    (x : Point3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
    let pOld :
        SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
      Classical.choose hNS
    temporal.d
        (fun r : ℝ =>
          (h3SpectralRealVelocityOfPath W r x).component
            (h3AxisOfFin3 i))
        s
      +
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3
      (h3SpectralRealVelocityOfPath W)
      s x).component
        (h3AxisOfFin3 i)
      =
    PrimeTensor.Bridge.RealFluid.pressureForceComponent
        spatial3
        pOld
        (t + s)
        x
        (h3AxisOfFin3 i)
      +
    ∑ k : Fin 3,
      spatial3.d
        (h3AxisOfFin3 k)
        (spatial3.d
          (h3AxisOfFin3 k)
          (fun y : Point3 =>
            (h3SpectralRealVelocityOfPath W s y).component
              (h3AxisOfFin3 i)))
        x := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hsClosed :
      s ∈ Set.Icc (0 : ℝ) tau :=
    ⟨hs.1.le, hs.2.le⟩

  have hAbs :
      t + s ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd ⟨s, hsClosed⟩

  have hTemporal :
      temporal.d
          (fun r : ℝ =>
            (h3SpectralRealVelocityOfPath W r x).component
              (h3AxisOfFin3 i))
          s
        =
      temporal.d
          (fun q : ℝ =>
            loggedVelocityComponent
              u q (h3AxisOfFin3 i) x)
          (t + s) := by
    simpa only [W] using
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_component_temporal_d_eq_old
        hNS ht htau hEnd hE hTail hEndpoint hs i x

  unfold loggedVelocityComponent at hTemporal

  have hAdvection :
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (h3SpectralRealVelocityOfPath W)
        s x).component
          (h3AxisOfFin3 i)
        =
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (logSpaceTimeVectorField u)
        (t + s) x).component
          (h3AxisOfFin3 i) := by
    simpa only [W] using
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_advection_eq_old
        hNS ht htau hEnd hE hTail hEndpoint
        s hsClosed i x

  have hLaplacian :
      (∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            (fun y : Point3 =>
              (h3SpectralRealVelocityOfPath W s y).component
                (h3AxisOfFin3 i)))
          x)
        =
      ∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            (loggedVelocityComponent
              u
              (t + s)
              (h3AxisOfFin3 i)))
          x := by
    simpa only [W] using
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_laplacian_eq_old
        hNS ht htau hEnd hE hTail hEndpoint
        s hsClosed i x

  unfold loggedVelocityComponent at hLaplacian

  have hOldMomentumRaw :=
    hPDE.momentum
      (t + s)
      hAbs
      x
      (h3AxisOfFin3 i)

  have hOldMomentum :
      temporal.d
          (fun q : ℝ =>
            (logSpaceTimeVectorField u q x).component
              (h3AxisOfFin3 i))
          (t + s)
        +
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (logSpaceTimeVectorField u)
        (t + s) x).component
          (h3AxisOfFin3 i)
        =
      PrimeTensor.Bridge.RealFluid.pressureForceComponent
          spatial3
          pOld
          (t + s)
          x
          (h3AxisOfFin3 i)
        +
      ∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            (fun y : Point3 =>
              (logSpaceTimeVectorField u (t + s) y).component
                (h3AxisOfFin3 i)))
          x := by
    rw [
      realFluid_laplacianVector_component_eq_fin_sum_three_endpoint
        (logSpaceTimeVectorField u)
        (t + s)
        x
        (h3AxisOfFin3 i)
    ] at hOldMomentumRaw

    unfold
      PrimeTensor.Bridge.RealFluid.temporalVectorDerivative
      at hOldMomentumRaw

    exact hOldMomentumRaw

  calc
    temporal.d
        (fun r : ℝ =>
          (h3SpectralRealVelocityOfPath W r x).component
            (h3AxisOfFin3 i))
        s
      +
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3
      (h3SpectralRealVelocityOfPath W)
      s x).component
        (h3AxisOfFin3 i)
        =
      temporal.d
          (fun q : ℝ =>
            (logSpaceTimeVectorField u q x).component
              (h3AxisOfFin3 i))
          (t + s)
        +
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (logSpaceTimeVectorField u)
        (t + s) x).component
          (h3AxisOfFin3 i) := by
      rw [hTemporal, hAdvection]
    _ =
      PrimeTensor.Bridge.RealFluid.pressureForceComponent
          spatial3
          pOld
          (t + s)
          x
          (h3AxisOfFin3 i)
        +
      ∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            (fun y : Point3 =>
              (logSpaceTimeVectorField u (t + s) y).component
                (h3AxisOfFin3 i)))
          x :=
      hOldMomentum
    _ =
      PrimeTensor.Bridge.RealFluid.pressureForceComponent
          spatial3
          pOld
          (t + s)
          x
          (h3AxisOfFin3 i)
        +
      ∑ k : Fin 3,
        spatial3.d
          (h3AxisOfFin3 k)
          (spatial3.d
            (h3AxisOfFin3 k)
            (fun y : Point3 =>
              (h3SpectralRealVelocityOfPath W s y).component
                (h3AxisOfFin3 i)))
          x := by
      rw [hLaplacian]

end

end Euclidean
end Bridge
end PrimeTensor
