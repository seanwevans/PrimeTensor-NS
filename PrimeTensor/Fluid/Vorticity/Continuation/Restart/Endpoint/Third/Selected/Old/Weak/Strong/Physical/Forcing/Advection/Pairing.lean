import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Generic.Weak.Forcing.Advection
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureFamilySpan

/-!
# Weak--strong forcing/advection identity in physical `L²`

The preceding generic weak theorem identifies Leray forcing with ordinary
advection against compact smooth divergence-free tests.  This file upgrades
that identity into the native physical `L²` Hilbert product.

For one spectral slice `U` we construct two quotient-safe physical vectors:

* `P div(U ⊗ U)`, reconstructed from the existing Leray-forcing `L²` package;
* `div(U ⊗ U)`, reconstructed from the unprojected raw divergence `L¹ ∩ L²`
  amplitude.

When `U` is realizable and raw-divergence-free, the second vector has the
ordinary physical advection `(u · ∇)u` as an almost-everywhere representative.

The generic weak pressure-cancellation theorem therefore says that the two
Hilbert pairings agree on every compact smooth divergence-free test vector.
Both pairings are continuous in the test vector, so the identity extends to the
closed divergence-free weak-test span.  The already-closed parameter-free
Leray-density theorem then allows every physical Leray-fixed `L²` state as a
test vector.

This is the precise bridge needed to insert the concrete selected-minus-old
difference into the nonlinear forcing pairing.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

attribute [local instance]
  point3MeasureSpaceH3SelectedOldWeakStrongGenericWeakForcingAdvection

noncomputable local instance axisFintypeH3SelectedOldWeakStrongPhysicalForcingAdvectionPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Real physical `L²(Point3)` reconstruction of one Leray-projected nonlinear
forcing coordinate. -/
noncomputable def h3WeakStrongLerayForcingPhysicalL2
    (U : H3SpectralFinVectorState)
    (i : Fin 3) :
    H3ScalarL2 :=
  h3FromFourierRealL2
    (h3RealPartFourierL2
      (h3RawFinLerayOuterProductDivergencePhysicalL2
        U U i))

/-- The projected physical `L²` forcing has the existing continuous forcing
reconstruction as an almost-everywhere representative. -/
theorem h3WeakStrongLerayForcingPhysicalL2_ae
    (U : H3SpectralFinVectorState)
    (i : Fin 3) :
    ((h3WeakStrongLerayForcingPhysicalL2 U i : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        U U i x).re) := by
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
      (fun ξ : H3FourierPoint3 =>
        (FComplex ξ).re) := by
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

/-- Canonical Fourier `L²` package of one unprojected raw outer-product
divergence coordinate. -/
noncomputable def h3WeakStrongRawOuterProductDivergenceFourierL2
    (U : H3SpectralFinVectorState)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  (h3RawFinOuterProductDivergence_memLp2 U U i).toLp
    (h3RawFinOuterProductDivergence U U i)

/-- Canonical unitary inverse-Fourier reconstruction of the unprojected raw
outer-product divergence. -/
noncomputable def h3WeakStrongRawOuterProductDivergencePhysicalComplexL2
    (U : H3SpectralFinVectorState)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  (MeasureTheory.Lp.fourierTransformₗᵢ
    H3FourierPoint3 ℂ).symm
    (h3WeakStrongRawOuterProductDivergenceFourierL2
      U i)

/-- Real physical `L²(Point3)` reconstruction of the unprojected nonlinear
term.  For realizable incompressible slices this is physical advection almost
everywhere. -/
noncomputable def h3WeakStrongAdvectionPhysicalL2
    (U : H3SpectralFinVectorState)
    (i : Fin 3) :
    H3ScalarL2 :=
  h3FromFourierRealL2
    (h3RealPartFourierL2
      (h3WeakStrongRawOuterProductDivergencePhysicalComplexL2
        U i))

/-- For a realizable raw-divergence-free slice, the quotient-safe unprojected
physical `L²` reconstruction is represented almost everywhere by ordinary
physical advection. -/
theorem h3WeakStrongAdvectionPhysicalL2_ae
    (U : H3SpectralFinVectorState)
    (hReal : H3SpectralVelocityRealizable U)
    (hDiv : H3SpectralFinRawDivergenceFree U)
    (i : Fin 3) :
    ((h3WeakStrongAdvectionPhysicalL2 U i : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (h3SpectralRealVelocityOfPath
          (fun _ : ℝ => U))
        0 x).component
          (h3AxisOfFin3 i)) := by
  let f : H3FourierPoint3 → ℂ :=
    h3RawFinOuterProductDivergence U U i

  let FComplex : H3FourierComplexL2 :=
    h3WeakStrongRawOuterProductDivergencePhysicalComplexL2
      U i

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
      (fun ξ : H3FourierPoint3 =>
        (FComplex ξ).re) := by
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

  have hInv :
      FourierTransformInv.fourierInv f
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (FComplex : H3FourierPoint3 → ℂ) := by
    dsimp only [
      f,
      FComplex,
      h3WeakStrongRawOuterProductDivergencePhysicalComplexL2,
      h3WeakStrongRawOuterProductDivergenceFourierL2
    ]

    exact
      h3FourierInv_integrable_memLp2_ae_eq_L2
        (h3RawFinOuterProductDivergence_integrable U U i)
        (h3RawFinOuterProductDivergence_memLp2 U U i)

  have hInvComp :
      (fun x : Point3 =>
        FourierTransformInv.fourierInv f
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        FComplex
          ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)) := by
    exact
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hInv

  change
    ((h3FromFourierRealL2 FReal : H3ScalarL2) :
        Point3 → ℝ)
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (h3SpectralRealVelocityOfPath
          (fun _ : ℝ => U))
        0 x).component
          (h3AxisOfFin3 i))

  filter_upwards [hFrom, hReComp, hInvComp] with
      x hxFrom hxRe hxInv

  have hAdv :=
    h3RawFinOuterProductDivergence_fourierInv_re_eq_advection_of_realizable_of_rawDivergenceFree
      (fun _ : ℝ => U)
      0
      hReal
      hDiv
      i x

  have hInvRe :
      (FComplex
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
        =
      (FourierTransformInv.fourierInv f
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re := by
    exact congrArg Complex.re hxInv.symm

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
      (FourierTransformInv.fourierInv f
        ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re :=
      hInvRe
    _ =
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (h3SpectralRealVelocityOfPath
          (fun _ : ℝ => U))
        0 x).component
          (h3AxisOfFin3 i) := by
      simpa only [f] using hAdv

/-- Three-component physical Leray forcing in the native `PiLp 2` Hilbert
product. -/
noncomputable def h3WeakStrongLerayForcingPhysicalL2Hilbert
    (U : H3SpectralFinVectorState) :
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2
    (fun i : Fin 3 =>
      h3WeakStrongLerayForcingPhysicalL2 U i)

/-- Three-component physical unprojected advection in the native `PiLp 2`
Hilbert product. -/
noncomputable def h3WeakStrongAdvectionPhysicalL2Hilbert
    (U : H3SpectralFinVectorState) :
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2
    (fun i : Fin 3 =>
      h3WeakStrongAdvectionPhysicalL2 U i)

/-- Compact-test Hilbert pairing with the generic physical Leray forcing is
exactly the existing weak forcing pairing. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_weakStrongLerayForcing
    (U : H3SpectralFinVectorState)
    (φ : H3WeakTestVector) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3WeakStrongLerayForcingPhysicalL2Hilbert U)
      =
    ∑ i : Fin 3,
      h3RawFinLerayOuterProductDivergenceWeakPairing
        (φ i) i U := by
  unfold
    h3WeakTestVectorPhysicalL2Hilbert
    h3WeakStrongLerayForcingPhysicalL2Hilbert

  rw [PiLp.inner_apply]

  apply Finset.sum_congr rfl
  intro i hi

  rw [h3WeakTestFunctionPhysicalL2_inner_eq_integral]

  unfold h3RawFinLerayOuterProductDivergenceWeakPairing

  apply integral_congr_ae

  filter_upwards [
    h3WeakStrongLerayForcingPhysicalL2_ae U i
  ] with x hx

  rw [hx]

/-- For a realizable incompressible slice, compact-test Hilbert pairing with
the quotient-safe unprojected physical vector is the literal advection
pairing. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_weakStrongAdvection
    (U : H3SpectralFinVectorState)
    (hReal : H3SpectralVelocityRealizable U)
    (hDiv : H3SpectralFinRawDivergenceFree U)
    (φ : H3WeakTestVector) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3WeakStrongAdvectionPhysicalL2Hilbert U)
      =
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (h3SpectralRealVelocityOfPath
              (fun _ : ℝ => U))
            0 x).component
              (h3AxisOfFin3 i))
        ∂volume := by
  unfold
    h3WeakTestVectorPhysicalL2Hilbert
    h3WeakStrongAdvectionPhysicalL2Hilbert

  rw [PiLp.inner_apply]

  apply Finset.sum_congr rfl
  intro i hi

  rw [h3WeakTestFunctionPhysicalL2_inner_eq_integral]

  apply integral_congr_ae

  filter_upwards [
    h3WeakStrongAdvectionPhysicalL2_ae U hReal hDiv i
  ] with x hx

  rw [hx]

/-- The two physical nonlinear vectors have the same Hilbert pairing with every
compact smooth divergence-free weak test. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_weakStrongLerayForcing_eq_advection
    (U : H3SpectralFinVectorState)
    (hReal : H3SpectralVelocityRealizable U)
    (hDiv : H3SpectralFinRawDivergenceFree U)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3WeakStrongLerayForcingPhysicalL2Hilbert U)
      =
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3WeakStrongAdvectionPhysicalL2Hilbert U) := by
  rw [
    inner_h3WeakTestVectorPhysicalL2Hilbert_weakStrongLerayForcing,
    inner_h3WeakTestVectorPhysicalL2Hilbert_weakStrongAdvection
      U hReal hDiv φ
  ]

  exact
    h3RawFinLerayOuterProductDivergenceWeakPairing_sum_eq_advection_of_realizable_of_rawDivergenceFree
      U hReal hDiv φ hφ

/-- By continuity, the forcing/advection pairing identity extends from compact
smooth divergence-free tests to their closed physical `L²` span. -/
theorem inner_weakStrongLerayForcing_eq_advection_of_mem_divergenceFreeWeakTestClosedSpan
    (U : H3SpectralFinVectorState)
    (hReal : H3SpectralVelocityRealizable U)
    (hDiv : H3SpectralFinRawDivergenceFree U)
    (Φ : H3PhysicalRealFinVectorL2Hilbert)
    (hΦ :
      Φ ∈ h3DivergenceFreeWeakTestPhysicalL2ClosedSpan) :
    inner ℝ
        Φ
        (h3WeakStrongLerayForcingPhysicalL2Hilbert U)
      =
    inner ℝ
        Φ
        (h3WeakStrongAdvectionPhysicalL2Hilbert U) := by
  let S : Set H3PhysicalRealFinVectorL2Hilbert :=
    { Ψ |
      inner ℝ
          Ψ
          (h3WeakStrongLerayForcingPhysicalL2Hilbert U)
        =
      inner ℝ
          Ψ
          (h3WeakStrongAdvectionPhysicalL2Hilbert U) }

  have hClosed : IsClosed S := by
    dsimp only [S]

    exact
      isClosed_eq
        (continuous_id.inner continuous_const)
        (continuous_id.inner continuous_const)

  have hSpanSubset :
      (h3DivergenceFreeWeakTestPhysicalL2Span :
          Set H3PhysicalRealFinVectorL2Hilbert)
        ⊆
      S := by
    intro Ψ hΨ

    rw [
      h3DivergenceFreeWeakTestPhysicalL2Span_eq_submodule_zeroSpan
    ] at hΨ

    change
      Ψ ∈ h3DivergenceFreeWeakTestPhysicalL2Set
    at hΨ

    rcases hΨ with ⟨φ, hφ, rfl⟩

    dsimp only [S]

    exact
      inner_h3WeakTestVectorPhysicalL2Hilbert_weakStrongLerayForcing_eq_advection
        U hReal hDiv φ hφ

  have hClosureSubset :
      closure
          (h3DivergenceFreeWeakTestPhysicalL2Span :
            Set H3PhysicalRealFinVectorL2Hilbert)
        ⊆
      S :=
    closure_minimal hSpanSubset hClosed

  have hΦClosure :
      Φ ∈
      closure
        (h3DivergenceFreeWeakTestPhysicalL2Span :
          Set H3PhysicalRealFinVectorL2Hilbert) := by
    unfold h3DivergenceFreeWeakTestPhysicalL2ClosedSpan at hΦ

    change
      Φ ∈
      closure
        (h3DivergenceFreeWeakTestPhysicalL2Span :
          Set H3PhysicalRealFinVectorL2Hilbert)
    at hΦ

    exact hΦ

  have hResult := hClosureSubset hΦClosure

  dsimp only [S] at hResult
  exact hResult

/-- Every physical Leray-fixed `L²` state may be used directly as the test
vector in the pressure-free nonlinear forcing/advection identity. -/
theorem inner_weakStrongLerayForcing_eq_advection_of_lerayFixed
    (U : H3SpectralFinVectorState)
    (hReal : H3SpectralVelocityRealizable U)
    (hDiv : H3SpectralFinRawDivergenceFree U)
    (Φ : H3PhysicalRealFinVectorL2Hilbert)
    (hΦ :
      H3PhysicalRealFinVectorL2HilbertLerayFixed Φ) :
    inner ℝ
        Φ
        (h3WeakStrongLerayForcingPhysicalL2Hilbert U)
      =
    inner ℝ
        Φ
        (h3WeakStrongAdvectionPhysicalL2Hilbert U) := by
  have hΦFixed :
      Φ ∈
      h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
    rw [
      mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff
    ]

    exact hΦ

  have hΦClosed :
      Φ ∈
      h3DivergenceFreeWeakTestPhysicalL2ClosedSpan :=
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_proved
      hΦFixed

  exact
    inner_weakStrongLerayForcing_eq_advection_of_mem_divergenceFreeWeakTestClosedSpan
      U hReal hDiv Φ hΦClosed

end

end Euclidean
end Bridge
end PrimeTensor
