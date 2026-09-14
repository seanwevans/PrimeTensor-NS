import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalMassReduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Advection
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.Force

/-!
# Zeroth-order endpoint continuity: isolate the old pressure-gradient defect

The endpoint-independent branch already has the exact bounded projected RHS

    Δu - P div(u ⊗ u)

as a real physical `L²` field.  The remaining temporal Fubini reduction,
however, concerns the actual classical pointwise temporal derivative.

At one closed elapsed slice `q`, let `U_q` be the old canonical H³ spectral
snapshot and let `p_can(q)` be the canonical pressure reconstructed from the
constant spectral path `W(s) = U_q`.

The generic spectral pressure identity gives

    -∂ᵢ p_can
      =
    advectionᵢ - (P div(u ⊗ u))ᵢ.

Combining this with the actual old preterminal momentum equation gives the
pointwise identity

    ∂ₜuᵢ
      =
    Δuᵢ
      - (P div(u ⊗ u))ᵢ
      - (∂ᵢ p_old - ∂ᵢ p_can).

Thus the only difference between the actual old temporal derivative and the
already-bounded projected RHS is an explicit old-vs-canonical pressure-gradient
defect.

No endpoint continuity, selected restart, or time integration is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldTemporalPressureDefect
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroOldTemporalPressureDefect :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Canonical static pressure attached to one old elapsed H³ snapshot. -/
noncomputable def h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    ScalarField3 :=
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q
  let W : ℝ → H3SpectralFinVectorState :=
    fun _ => U
  h3RawFinPressureRealC1OfPath W 0

/-- Coordinatewise old-vs-canonical pressure-gradient defect at one elapsed
slice. -/
noncomputable def h3PreterminalTailCanonicalZeroPressureGradientDefectOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (x : Point3) :
    ℝ :=
  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS
  spatial3.d
      (h3AxisOfFin3 i)
      (pOld (t + (q : ℝ)))
      x
    -
  spatial3.d
      (h3AxisOfFin3 i)
      (h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
        hNS ht hEnd hTail q)
      x

/-- The actual old temporal derivative is exactly the bounded projected
physical RHS plus the explicit negative pressure-gradient defect. -/
theorem h3PreterminalLoggedVelocity_temporalDerivative_eq_zeroProjectedLiteralRHS_sub_pressureGradientDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (x : Point3) :
    temporal.d
        (fun a : ℝ =>
          loggedVelocityComponent
            u a (h3AxisOfFin3 i) x)
        (t + (q : ℝ))
      =
    (PrimeTensor.Bridge.RealFluid.laplacianVector
      spatial3
      (logSpaceTimeVectorField u)
      (t + (q : ℝ))
      x).component
        (h3AxisOfFin3 i)
      -
    (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q)
      (h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q)
      i x).re
      -
    h3PreterminalTailCanonicalZeroPressureGradientDefectOnElapsed
      hNS ht hEnd hTail q i x := by
  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  let W : ℝ → H3SpectralFinVectorState :=
    fun _ => U

  let pCan :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3RawFinPressureRealC1OfPath W

  have hAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd q

  have hMomentum :=
    hPDE.momentum
      (t + (q : ℝ))
      hAbs
      x
      (h3AxisOfFin3 i)

  have hAdv :=
    h3PreterminalTailCanonicalRawOuterDivergence_fourierInv_re_eq_old_advection
      hNS ht hEnd hTail q i x

  have hPressure :=
    h3RawFinPressureRealC1OfPath_pressureForceComponent_eq_raw_sub_leray
      W 0 i x

  have hPressureOld :
      PrimeTensor.Bridge.RealFluid.pressureForceComponent
          spatial3
          pOld
          (t + (q : ℝ))
          x
          (h3AxisOfFin3 i)
        =
      -
      spatial3.d
        (h3AxisOfFin3 i)
        (pOld (t + (q : ℝ)))
        x := by
    rfl

  have hPressureCan :
      PrimeTensor.Bridge.RealFluid.pressureForceComponent
          spatial3
          pCan
          0
          x
          (h3AxisOfFin3 i)
        =
      -
      spatial3.d
        (h3AxisOfFin3 i)
        (pCan 0)
        x := by
    rfl

  have hAdv' :
      (FourierTransformInv.fourierInv
        (h3RawFinOuterProductDivergence
          U U i)
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
        =
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (logSpaceTimeVectorField u)
        (t + (q : ℝ))
        x).component
          (h3AxisOfFin3 i) := by
    simpa only [U] using hAdv

  have hPressureRelation :
      -
      spatial3.d
        (h3AxisOfFin3 i)
        (pCan 0)
        x
        =
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (logSpaceTimeVectorField u)
        (t + (q : ℝ))
        x).component
          (h3AxisOfFin3 i)
        -
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        U U i x).re := by
    rw [← hPressureCan]

    change
      PrimeTensor.Bridge.RealFluid.pressureForceComponent
          spatial3
          pCan
          0
          x
          (h3AxisOfFin3 i)
        =
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (logSpaceTimeVectorField u)
        (t + (q : ℝ))
        x).component
          (h3AxisOfFin3 i)
        -
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        U U i x).re

    dsimp only [pCan]

    simpa only [W, hAdv'] using hPressure

  change
    temporal.d
        (fun a : ℝ =>
          (logSpaceTimeVectorField u a x).component
            (h3AxisOfFin3 i))
        (t + (q : ℝ))
      =
    (PrimeTensor.Bridge.RealFluid.laplacianVector
      spatial3
      (logSpaceTimeVectorField u)
      (t + (q : ℝ))
      x).component
        (h3AxisOfFin3 i)
      -
    (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      U U i x).re
      -
    (spatial3.d
        (h3AxisOfFin3 i)
        (pOld (t + (q : ℝ)))
        x
      -
     spatial3.d
        (h3AxisOfFin3 i)
        (pCan 0)
        x)

  rw [hPressureOld] at hMomentum

  have hMomentum' :
      temporal.d
          (fun a : ℝ =>
            (logSpaceTimeVectorField u a x).component
              (h3AxisOfFin3 i))
          (t + (q : ℝ))
        +
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (logSpaceTimeVectorField u)
        (t + (q : ℝ))
        x).component
          (h3AxisOfFin3 i)
        =
      -
      spatial3.d
        (h3AxisOfFin3 i)
        (pOld (t + (q : ℝ)))
        x
        +
      (PrimeTensor.Bridge.RealFluid.laplacianVector
        spatial3
        (logSpaceTimeVectorField u)
        (t + (q : ℝ))
        x).component
          (h3AxisOfFin3 i) := by
    exact hMomentum

  linarith

end

end Euclidean
end Bridge
end PrimeTensor
