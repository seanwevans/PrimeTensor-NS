import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Cauchy

/-!
# Zeroth-order endpoint continuity: uniformly bound the projected-RHS mass

`TemporalPressureMass` reduced the old temporal spatial norm mass to

    M_temporal
      ≤
    M_projectedRHS + M_pressureDefect.

The first summand is already analytically closed.

`RHSPhysicalWeak` constructed an exact real physical `L²` package `R_i(q)` for
the endpoint-independent projected RHS and proved the uniform bound

    ‖R_i(q)‖₂ ≤ K(E),

where

    K(E) = 2 E + 2304 π C E².

Its almost-everywhere representative is exactly the literal old-snapshot field

    Δu_i - (P div(u ⊗ u))_i.

This file transports the Hilbert `L²` norm square through that representative
identity, obtaining

    ∫ |R_i(q,x)|² dx ≤ K(E)².

The existing compact-test Cauchy theorem then gives

    M_projectedRHS(q,i,ψ)
      ≤
    ‖ψ‖₂ · (K(E)²)^(1/2).

Thus the projected-RHS contribution to the temporal mass is now uniformly
bounded from the retained H³ ceiling alone.  The only remaining term in the
mass split is the old-vs-canonical pressure-gradient defect.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldProjectedRHSMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroOldProjectedRHSMass :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Exact norm-square formula for a real scalar `L²(Point3)` class, written in
the PrimeTensor spatial-energy convention. -/
theorem h3ScalarL2_norm_sq_eq_spatialSquareEnergy_coe
    (F : H3ScalarL2) :
    ‖F‖ ^ 2
      =
    spatialSquareEnergy
      (fun x : Point3 => F x) := by
  change
    ‖F‖ ^ 2
      =
    ∫ x : Point3, (F x) ^ 2

  rw [← real_inner_self_eq_norm_sq]
  rw [MeasureTheory.L2.inner_def]

  apply integral_congr_ae
  filter_upwards with x

  simp [
    Real.norm_eq_abs,
    sq_abs
  ]

/-- The literal old-snapshot projected RHS has a uniform spatial square bound
given by the square of the already-proved physical `L²` RHS ceiling. -/
theorem h3PreterminalTailCanonicalZeroProjectedLiteralRHS_spatialL2SquareBound
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    SpatialL2SquareBound
      (h3PreterminalTailCanonicalZeroProjectedLiteralRHSOnElapsed
        hNS ht hEnd hTail q i)
      ((h3UnitViscosityZeroRHSBound E) ^ 2) := by
  let R : H3ScalarL2 :=
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
      hNS ht hEnd hTail q i

  let f : ScalarField3 :=
    h3PreterminalTailCanonicalZeroProjectedLiteralRHSOnElapsed
      hNS ht hEnd hTail q i

  have hAE :
      (R : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      f := by
    dsimp only [R, f]

    change
      ((h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
          hNS ht hEnd hTail q i : H3ScalarL2) :
          Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
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
          i x).re)

    exact
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed_ae_eq_old
        hNS ht hEnd hTail q i

  have hSqAE :
      (fun x : Point3 => (R x) ^ 2)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 => (f x) ^ 2) := by
    filter_upwards [hAE] with x hx
    rw [hx]

  have hRSqInt :
      Integrable
        (fun x : Point3 => (R x) ^ 2)
        (volume : Measure Point3) := by
    have h :=
      (MeasureTheory.Lp.memLp R).norm.integrable_sq

    simpa only [
      Real.norm_eq_abs,
      sq_abs
    ] using h

  have hFSqInt :
      Integrable
        (fun x : Point3 => (f x) ^ 2)
        (volume : Measure Point3) :=
    hRSqInt.congr hSqAE

  have hRNorm :
      ‖R‖
        ≤
      h3UnitViscosityZeroRHSBound E := by
    dsimp only [R]

    simpa only [
      h3UnitViscosityZeroRHSBound
    ] using
      norm_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed_le
        hNS ht hEnd hE hTail q i

  have hE0 : 0 ≤ E := by
    linarith

  have hK0 :
      0 ≤ h3UnitViscosityZeroRHSBound E := by
    unfold h3UnitViscosityZeroRHSBound
    have hC := h3SobolevDeweightingConstant_nonneg
    positivity

  have hNorm0 : 0 ≤ ‖R‖ :=
    norm_nonneg R

  have hSqNorm :
      ‖R‖ ^ 2
        ≤
      (h3UnitViscosityZeroRHSBound E) ^ 2 := by
    nlinarith

  have hNormSq :
      ‖R‖ ^ 2
        =
      ∫ x : Point3, (R x) ^ 2 := by
    simpa only [spatialSquareEnergy] using
      h3ScalarL2_norm_sq_eq_spatialSquareEnergy_coe R

  have hIntegralEq :
      (∫ x : Point3, (R x) ^ 2)
        =
      ∫ x : Point3, (f x) ^ 2 :=
    integral_congr_ae hSqAE

  constructor
  · simpa only [f] using hFSqInt
  · calc
      (∫ x : Point3, (f x) ^ 2)
          =
        ∫ x : Point3, (R x) ^ 2 :=
        hIntegralEq.symm
      _ =
        ‖R‖ ^ 2 :=
        hNormSq.symm
      _ ≤
        (h3UnitViscosityZeroRHSBound E) ^ 2 :=
        hSqNorm

/-- Uniform compact-test spatial mass bound for the literal projected RHS. -/
theorem h3PreterminalTailCanonicalZeroProjectedRHSSpatialNormMassOnElapsed_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (ψ : H3WeakTestFunction) :
    h3PreterminalTailCanonicalZeroProjectedRHSSpatialNormMassOnElapsed
        hNS ht hEnd hTail q i ψ
      ≤
    h3WeakTestFunctionL2Mass ψ
      *
    ((h3UnitViscosityZeroRHSBound E) ^ 2) ^
      (1 / (2 : ℝ)) := by
  let f : ScalarField3 :=
    h3PreterminalTailCanonicalZeroProjectedLiteralRHSOnElapsed
      hNS ht hEnd hTail q i

  let R : H3ScalarL2 :=
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
      hNS ht hEnd hTail q i

  have hAE :
      (R : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      f := by
    dsimp only [R, f]

    change
      ((h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
          hNS ht hEnd hTail q i : H3ScalarL2) :
          Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
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
          i x).re)

    exact
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed_ae_eq_old
        hNS ht hEnd hTail q i

  have hfMeas :
      AEStronglyMeasurable
        f
        (volume : Measure Point3) :=
    (MeasureTheory.Lp.aestronglyMeasurable R).congr hAE

  have hBound :
      SpatialL2SquareBound
        f
        ((h3UnitViscosityZeroRHSBound E) ^ 2) := by
    dsimp only [f]

    exact
      h3PreterminalTailCanonicalZeroProjectedLiteralRHS_spatialL2SquareBound
        hNS ht hEnd hE hTail q i

  have hCauchy :
      (∫ x : Point3,
          ‖ψ x‖ * ‖f x‖
        ∂volume)
        ≤
      h3WeakTestFunctionL2Mass ψ
        *
      ((h3UnitViscosityZeroRHSBound E) ^ 2) ^
        (1 / (2 : ℝ)) :=
    integral_weakTest_norm_mul_norm_le_of_spatialL2SquareBound
      ψ hfMeas hBound

  unfold
    h3PreterminalTailCanonicalZeroProjectedRHSSpatialNormMassOnElapsed

  change
    (∫ x : Point3,
      ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (f x)‖
      ∂volume)
      ≤
    h3WeakTestFunctionL2Mass ψ
      *
    ((h3UnitViscosityZeroRHSBound E) ^ 2) ^
      (1 / (2 : ℝ))

  calc
    (∫ x : Point3,
      ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (f x)‖
      ∂volume)
        =
      ∫ x : Point3,
        ‖ψ x‖ * ‖f x‖
        ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [
        ContinuousLinearMap.lsmul_apply,
        smul_eq_mul,
        norm_mul
      ]
    _ ≤
      h3WeakTestFunctionL2Mass ψ
        *
      ((h3UnitViscosityZeroRHSBound E) ^ 2) ^
        (1 / (2 : ℝ)) :=
      hCauchy

end

end Euclidean
end Bridge
end PrimeTensor
