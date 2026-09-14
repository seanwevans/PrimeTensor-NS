import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalWeak
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.L2.RHS.Pairing

/-!
# Zeroth-order endpoint continuity: physical old projected RHS weak identity

The endpoint-independent branch now has all three ingredients separately:

* `RHSReality`: an exact real physical `L²` reconstruction of the bounded
  Fourier projected RHS;
* `TemporalWeak`: the old preterminal temporal derivative pairs with
  `weakDiffusion - weakLerayForcing`;
* the old physical Laplacian and the raw Leray forcing both have exact
  quotient-safe physical `L²` packages.

This file closes the representation seam.

For one old elapsed snapshot `U_q`, first package the nonlinear forcing as

    inverse Plancherel
      -> real part
      -> transport to Point3.

Raw Hermitian reality of `U_q` implies forward scalar Plancherel recovers the
canonical Leray forcing Fourier `L²` state exactly.  Hence

    direct physical RHS from RHSReality
      =
    old physical Laplacian - old-snapshot physical Leray forcing

by injectivity of scalar Plancherel.

The decomposed package has the literal almost-everywhere representative

    Δu_i - Re F⁻¹(P div(U_q ⊗ U_q))_i.

Therefore its compact-test Hilbert pairing is exactly the endpoint-independent
weak projected RHS pairing.  Combining with `TemporalWeak` yields

    Σ_i ∫ φ_i ∂ₜu_i
      =
    Σ_i <φ_i, R_i(q)>_L²

for every divergence-free compact smooth test vector and every closed elapsed
slice `q ∈ [0,τ]`.

Finally Plancherel transfers the existing Fourier RHS estimate directly to the
real physical `L²` RHS coordinate:

    ‖R_i(q)‖₂
      ≤ 2 E + 2304 π C E².

No endpoint continuity, selected restart, pressure transform, or Banach-valued
time derivative is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldPhysicalRHSWeak
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroOldPhysicalRHSWeak :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Endpoint-independent real physical `L²` package of one old-snapshot
Leray-forcing coordinate. -/
noncomputable def h3PreterminalTailCanonicalZeroLerayForcingPhysicalL2OnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    H3ScalarL2 :=
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q
  h3FromFourierRealL2
    (h3RealPartFourierL2
      (h3RawFinLerayOuterProductDivergencePhysicalL2
        U U i))

/-- The endpoint-independent real physical forcing package represents the real
part of the continuous old-snapshot Leray forcing reconstruction almost
everywhere. -/
theorem h3PreterminalTailCanonicalZeroLerayForcingPhysicalL2OnElapsed_ae
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    let U : H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q
    ((h3PreterminalTailCanonicalZeroLerayForcingPhysicalL2OnElapsed
        hNS ht hEnd hTail q i : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        U U i x).re) := by
  dsimp only

  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  let FComplex : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergencePhysicalL2
      U U i

  let FReal : H3FourierRealL2 :=
    h3RealPartFourierL2 FComplex

  have hFrom :
      ((h3FromFourierRealL2 FReal : H3ScalarL2) :
          Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        FReal
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    unfold h3FromFourierRealL2

    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        FReal
        (PiLp.volume_preserving_toLp
          (PrimeTensor.Axis Depth.three))

  have hRe :
      (FReal : H3FourierPoint3 → ℝ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun xi : H3FourierPoint3 =>
        (FComplex xi).re) := by
    dsimp only [FReal, h3RealPartFourierL2]

    exact
      Complex.reCLM.coeFn_compLp FComplex

  have hReComp :
      (fun x : Point3 =>
        FReal
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (FComplex
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re) := by
    exact
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hRe

  have hC0 :
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          U U i
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        FComplex
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    dsimp only [FComplex]

    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_ae_eq_physicalL2
        U U i

  change
    ((h3FromFourierRealL2 FReal : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        U U i x).re)

  filter_upwards [hFrom, hReComp, hC0] with
      x hxFrom hxRe hxC0

  calc
    (h3FromFourierRealL2 FReal : H3ScalarL2) x
        =
      FReal
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x) :=
      hxFrom
    _ =
      (FComplex
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re :=
      hxRe
    _ =
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        U U i x).re := by
      exact congrArg Complex.re hxC0.symm

/-- Forward scalar Plancherel of the endpoint-independent real physical
forcing package recovers the exact old-snapshot Leray forcing Fourier state. -/
theorem h3ScalarFourierL2_h3PreterminalTailCanonicalZeroLerayForcingPhysicalL2OnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3ScalarFourierL2
        (h3PreterminalTailCanonicalZeroLerayForcingPhysicalL2OnElapsed
          hNS ht hEnd hTail q i)
      =
    h3RawFinLerayOuterProductDivergenceFourierL2
      (h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q)
      (h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q)
      i := by
  unfold
    h3PreterminalTailCanonicalZeroLerayForcingPhysicalL2OnElapsed
    h3RawFinLerayOuterProductDivergencePhysicalL2

  exact
    h3ScalarFourierL2_realPhysicalReconstruction_eq_of_hermitian
      (h3RawFinLerayOuterProductDivergenceFourierL2
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q)
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q)
        i)
      (h3PreterminalTailCanonicalSnapshotLerayForcingFourierL2_hermitian
        hNS ht hEnd hTail q i)

/-- Decomposed endpoint-independent physical projected RHS:
old physical Laplacian minus old-snapshot real physical Leray forcing. -/
noncomputable def h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2DecomposedOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    H3ScalarL2 :=
  h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
      hNS ht hEnd hTail q i
    -
  h3PreterminalTailCanonicalZeroLerayForcingPhysicalL2OnElapsed
      hNS ht hEnd hTail q i

/-- The decomposed physical RHS has exactly the bounded endpoint-independent
Fourier projected RHS as scalar Plancherel transform. -/
theorem h3ScalarFourierL2_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2DecomposedOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3ScalarFourierL2
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2DecomposedOnElapsed
          hNS ht hEnd hTail q i)
      =
    h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed
      hNS ht hEnd hTail q i := by
  unfold
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2DecomposedOnElapsed

  rw [
    h3ScalarFourierL2_sub,
    h3ScalarFourierL2_h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed,
    h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_eq_snapshotLaplacian,
    h3ScalarFourierL2_h3PreterminalTailCanonicalZeroLerayForcingPhysicalL2OnElapsed
  ]

  unfold
    h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed

  rfl

/-- Scalar Plancherel is injective, extracted directly from its norm isometry. -/
theorem h3ScalarFourierL2_injective_zeroWeak :
    Function.Injective h3ScalarFourierL2 := by
  intro f g hfg

  have hFourierZero :
      h3ScalarFourierL2 (f - g) = 0 := by
    rw [h3ScalarFourierL2_sub, hfg, sub_self]

  have hNormZero :
      ‖f - g‖ = 0 := by
    rw [
      ← norm_h3ScalarFourierL2 (f - g),
      hFourierZero,
      norm_zero
    ]

  exact
    sub_eq_zero.mp
      (norm_eq_zero.mp hNormZero)

/-- The direct Hermitian reconstruction from `RHSReality` and the decomposed
physical Laplacian-minus-forcing package are exactly the same `L²` class. -/
theorem h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed_eq_decomposed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
        hNS ht hEnd hTail q i
      =
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2DecomposedOnElapsed
      hNS ht hEnd hTail q i := by
  apply h3ScalarFourierL2_injective_zeroWeak

  rw [
    h3ScalarFourierL2_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed,
    h3ScalarFourierL2_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2DecomposedOnElapsed
  ]

/-- The direct physical RHS represents the literal old physical Laplacian minus
the continuous old-snapshot Leray forcing almost everywhere. -/
theorem h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed_ae_eq_old
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
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
        i x).re) := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  let L : H3ScalarL2 :=
    h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed
      hNS ht hEnd hTail q i

  let F : H3ScalarL2 :=
    h3PreterminalTailCanonicalZeroLerayForcingPhysicalL2OnElapsed
      hNS ht hEnd hTail q i

  have hEq :=
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed_eq_decomposed
      hNS ht hEnd hTail q i

  have hSub :=
    MeasureTheory.Lp.coeFn_sub L F

  have hLap :
      (L : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ∑ k : Fin 3,
          spatial3.d
            (h3AxisOfFin3 k)
            (spatial3.d
              (h3AxisOfFin3 k)
              (loggedVelocityComponent
                u
                (t + (q : ℝ))
                (h3AxisOfFin3 i)))
            x) := by
    dsimp only [L]

    exact
      h3PreterminalTailCanonicalVelocityLaplacianPhysicalL2OnElapsed_ae_eq_old
        hNS ht hEnd hTail q i

  have hForce :
      (F : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          U U i x).re) := by
    dsimp only [F, U]

    exact
      h3PreterminalTailCanonicalZeroLerayForcingPhysicalL2OnElapsed_ae
        hNS ht hEnd hTail q i

  rw [hEq]

  change
    (((L - F : H3ScalarL2) : Point3 → ℝ))
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
        U U i x).re)

  filter_upwards [hSub, hLap, hForce] with
      x hxSub hxLap hxForce

  rw [hxSub]
  simp only [Pi.sub_apply]
  rw [hxLap, hxForce]

  have hLoggedField :
      (fun y : Point3 =>
        (logSpaceTimeVectorField
          u
          (t + (q : ℝ))
          y).component
            (h3AxisOfFin3 i))
        =
      loggedVelocityComponent
        u
        (t + (q : ℝ))
        (h3AxisOfFin3 i) := by
    rfl

  have hLapPoint :=
    realFluid_laplacianVector_component_eq_fin_sum_three_endpoint
      (logSpaceTimeVectorField u)
      (t + (q : ℝ))
      x
      (h3AxisOfFin3 i)

  rw [hLoggedField] at hLapPoint
  rw [← hLapPoint]

/-- Hilbert pairing of a compact scalar test with one direct physical RHS
coordinate equals the old physical Laplacian pairing minus the canonical
old-snapshot Leray forcing weak pairing. -/
theorem h3WeakTestFunctionPhysicalL2_inner_zeroProjectedRHSPhysicalL2OnElapsed_eq
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : H3WeakTestFunction)
    (i : Fin 3) :
    inner ℝ
        (h3WeakTestFunctionPhysicalL2 φ)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
          hNS ht hEnd hTail q i)
      =
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        ((PrimeTensor.Bridge.RealFluid.laplacianVector
          spatial3
          (logSpaceTimeVectorField u)
          (t + (q : ℝ))
          x).component
            (h3AxisOfFin3 i))
      ∂volume)
      -
    h3RawFinLerayOuterProductDivergenceWeakPairing
      φ i
      (h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q) := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  let R : H3ScalarL2 :=
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
      hNS ht hEnd hTail q i

  have hAE :
      (R : Point3 → ℝ)
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
          U U i x).re) := by
    dsimp only [R, U]

    exact
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed_ae_eq_old
        hNS ht hEnd hTail q i

  have hLapInt :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ x)
            ((PrimeTensor.Bridge.RealFluid.laplacianVector
              spatial3
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x).component
                (h3AxisOfFin3 i)))
        (volume : Measure Point3) :=
    h3PreterminalLoggedVelocity_test_mul_laplacianVector_integrable
      hNS ht hEnd hTail q i φ

  have hForceInt :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ x)
            ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              U U i x).re))
        (volume : Measure Point3) :=
    h3RawFinLerayOuterProductDivergenceWeakPairing_integrable
      φ i U

  calc
    inner ℝ
        (h3WeakTestFunctionPhysicalL2 φ)
        R
        =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          (R x)
        ∂volume :=
      h3WeakTestFunctionPhysicalL2_inner_eq_integral
        φ R
    _ =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          ((PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i)
            -
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            U U i x).re)
        ∂volume := by
          apply integral_congr_ae
          filter_upwards [hAE] with x hx
          rw [hx]
    _ =
      ∫ x : Point3,
        ((ContinuousLinearMap.lsmul ℝ ℝ)
            (φ x)
            ((PrimeTensor.Bridge.RealFluid.laplacianVector
              spatial3
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x).component
                (h3AxisOfFin3 i))
          -
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            U U i x).re))
        ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          rw [map_sub]
    _ =
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          ((PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i))
        ∂volume)
        -
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            U U i x).re)
        ∂volume := by
          exact integral_sub hLapInt hForceInt
    _ =
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          ((PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i))
        ∂volume)
        -
      h3RawFinLerayOuterProductDivergenceWeakPairing
        φ i U := by
          rfl

/-- Physical `L²` pairing of a compact test vector with the exact
endpoint-independent projected RHS. -/
noncomputable def h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
    ℝ :=
  ∑ i : Fin 3,
    inner ℝ
      (h3WeakTestFunctionPhysicalL2 (φ i))
      (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
        hNS ht hEnd hTail q i)

/-- The exact physical `L²` projected RHS pairing is the endpoint-independent
weak projected RHS pairing on every closed elapsed slice. -/
theorem h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed_eq_weak
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed
        hNS ht hEnd hTail φ q
      =
    h3PreterminalTailCanonicalZeroWeakProjectedRHSPairingOnElapsed
      hNS ht hEnd hTail φ q := by
  have hCoord
      (i : Fin 3) :
      inner ℝ
          (h3WeakTestFunctionPhysicalL2 (φ i))
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
            hNS ht hEnd hTail q i)
        =
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i))
        ∂volume)
        -
      h3RawFinLerayOuterProductDivergenceWeakPairing
        (φ i) i
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q) :=
    h3WeakTestFunctionPhysicalL2_inner_zeroProjectedRHSPhysicalL2OnElapsed_eq
      hNS ht hEnd hTail q (φ i) i

  have hDiff :=
    h3PreterminalTailCanonicalZeroWeakDiffusionPairingOnElapsed_eq_oldLaplacian
      hNS ht hEnd hTail q φ

  unfold
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed
    h3PreterminalTailCanonicalZeroWeakProjectedRHSPairingOnElapsed

  calc
    (∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
          hNS ht hEnd hTail q i))
        =
      ∑ i : Fin 3,
        ((∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((PrimeTensor.Bridge.RealFluid.laplacianVector
              spatial3
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x).component
                (h3AxisOfFin3 i))
          ∂volume)
          -
        h3RawFinLerayOuterProductDivergenceWeakPairing
          (φ i) i
          (h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hCoord i
    _ =
      (∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            ((PrimeTensor.Bridge.RealFluid.laplacianVector
              spatial3
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x).component
                (h3AxisOfFin3 i))
          ∂volume)
        -
      ∑ i : Fin 3,
        h3RawFinLerayOuterProductDivergenceWeakPairing
          (φ i) i
          (h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q) := by
      rw [Finset.sum_sub_distrib]
    _ =
      h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed
          hNS ht hEnd hTail φ q
        -
      ∑ i : Fin 3,
        h3RawFinLerayOuterProductDivergenceWeakPairing
          (φ i) i
          (h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q) := by
      rw [hDiff]
    _ =
      h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed
          hNS ht hEnd hTail φ q
        -
      ∑ i : Fin 3,
        h3RawFinLerayOuterProductDivergenceWeakPairing
          (φ i) i
          (h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q) := by
      rfl

/-- The actual old temporal derivative equals the exact bounded physical `L²`
projected RHS against every divergence-free compact smooth test vector. -/
theorem h3PreterminalLoggedVelocity_weakTemporalPairing_eq_zeroProjectedRHSPhysicalL2WeakPairingOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent
                u a (h3AxisOfFin3 i) x)
            (t + (q : ℝ)))
        ∂volume)
      =
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed
      hNS ht hEnd hTail φ q := by
  calc
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent
                u a (h3AxisOfFin3 i) x)
            (t + (q : ℝ)))
        ∂volume)
        =
      h3PreterminalTailCanonicalZeroWeakProjectedRHSPairingOnElapsed
        hNS ht hEnd hTail φ q :=
      h3PreterminalLoggedVelocity_weakTemporalPairing_eq_zeroWeakProjectedRHSPairingOnElapsed
        hNS ht hEnd hTail q φ hφ
    _ =
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed
        hNS ht hEnd hTail φ q := by
      exact
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed_eq_weak
          hNS ht hEnd hTail φ q).symm

/-- The endpoint-independent real physical projected RHS carries the same
uniform coordinatewise `L²` bound as its exact Fourier representation. -/
theorem norm_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed_le
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
    ‖h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
        hNS ht hEnd hTail q i‖
      ≤
    2 * E
      +
    2304 * Real.pi * h3SobolevDeweightingConstant * E ^ 2 := by
  calc
    ‖h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
        hNS ht hEnd hTail q i‖
        =
      ‖h3ScalarFourierL2
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
          hNS ht hEnd hTail q i)‖ := by
      exact
        (norm_h3ScalarFourierL2
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
            hNS ht hEnd hTail q i)).symm
    _ =
      ‖h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed
        hNS ht hEnd hTail q i‖ := by
      rw [
        h3ScalarFourierL2_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
      ]
    _ ≤
      2 * E
        +
      2304 * Real.pi * h3SobolevDeweightingConstant * E ^ 2 :=
      norm_h3PreterminalTailCanonicalZeroProjectedRHSFourierL2OnElapsed_le
        hNS ht hEnd hE hTail q i

end

end Euclidean
end Bridge
end PrimeTensor
