import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Reduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Diffusion.Pairing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fourier.Derivative.AE
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.Encoded.Incompressibility

/-!
# Classicalization: divergence-free weak tests are physically Leray-fixed

The parameter-free density reduction introduced the closed Hilbert span of all
compactly supported smooth divergence-free weak test vectors.  Before proving
that this span is *all* of the physical Leray-fixed `L²` subspace, one direction
must be closed exactly:

    divergence-free compact smooth tests
      ⊆
    physical Leray-fixed `L²`.

This file proves that direction.

The proof stays entirely quotient-safe.

For one scalar compact smooth test function `φ`, its bundled
`TestFunction.lineDerivCLM` coordinate derivative is first identified with the
project's concrete Euclidean `spatial3.d`.  The existing
`h3ScalarFourierL2_spatialDerivative_fin_ae` theorem then gives

    Fourier(∂ᵢ φ)
      =
    dᵢ(ξ) Fourier(φ)

almost everywhere.

For a divergence-free test vector, the three bundled coordinate derivatives
sum to zero already in `TestFunction`.  We transport that equality through
physical `L²` and the scalar Plancherel map.  Combining the resulting zero
Fourier sum with the three derivative-multiplier identities yields the exact
raw Fourier divergence-free predicate expected by the finite Leray projector.
Hence the projector fixes the physical `L²` test state.

Finally we pass from generators to algebraic span and then to topological
closure.  Thus

    divergence-free weak-test closed span
      ≤
    physical Leray-fixed closed submodule.

Consequently the parameter-free density frontier from the previous checkpoint
is now equivalent to equality of these two closed submodules.

No density theorem is assumed or proved here; this closes the easy inclusion
needed before the genuine density direction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityTestFixed
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2AdmissibleClosureLerayDensityTestFixed :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Bundled test derivatives agree with `spatial3.d` -/

/-- The bundled compact-test coordinate derivative is exactly the project's
ordinary Euclidean coordinate derivative. -/
theorem h3WeakTestFunctionSpatialDerivative_eq_spatial3_d
    (φ : H3WeakTestFunction)
    (i : Fin 3) :
    (h3WeakTestFunctionSpatialDerivative
        (h3AxisOfFin3 i) φ :
        Point3 → ℝ)
      =
    spatial3.d
      (h3AxisOfFin3 i)
      (φ : Point3 → ℝ) := by
  funext x

  have hφC1 :
      SpatialC1
        (φ : Point3 → ℝ) := by
    unfold SpatialC1
    exact
      φ.contDiff.of_le
        (by norm_num)

  unfold h3WeakTestFunctionSpatialDerivative

  rw [
    TestFunction.lineDerivCLM_apply_of_le
      (by simp)
  ]

  change
    lineDeriv ℝ
        (φ : Point3 → ℝ)
        x
        (axisDirection (h3AxisOfFin3 i))
      =
    partialDeriv
      (h3AxisOfFin3 i)
      (φ : Point3 → ℝ)
      x

  calc
    lineDeriv ℝ
        (φ : Point3 → ℝ)
        x
        (axisDirection (h3AxisOfFin3 i))
        =
      (fderiv ℝ
        (φ : Point3 → ℝ)
        x)
        (axisDirection (h3AxisOfFin3 i)) := by
          exact
            (hφC1.differentiable_one).differentiableAt.lineDeriv_eq_fderiv
    _ =
      partialDeriv
        (h3AxisOfFin3 i)
        (φ : Point3 → ℝ)
        x := by
          symm
          exact
            hφC1.partialDeriv_eq_fderiv_axisDirection
              x
              (h3AxisOfFin3 i)

/-! ## Fourier multiplier identity for one weak-test derivative -/

/-- The scalar Plancherel transform of one bundled compact-test derivative is
the expected coordinate Fourier multiplier almost everywhere. -/
theorem h3WeakTestFunctionPhysicalL2_spatialDerivative_fourier_ae
    (φ : H3WeakTestFunction)
    (i : Fin 3) :
    (h3ScalarFourierL2
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 i) φ)) :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol i ξ
        *
      h3ScalarFourierL2
        (h3WeakTestFunctionPhysicalL2 φ)
        ξ) := by
  let f : ScalarField3 :=
    (φ : Point3 → ℝ)

  let dφ : H3WeakTestFunction :=
    h3WeakTestFunctionSpatialDerivative
      (h3AxisOfFin3 i) φ

  have hfC1 :
      SpatialC1 f := by
    dsimp only [f]
    unfold SpatialC1
    exact
      φ.contDiff.of_le
        (by norm_num)

  have hf :
      MemLp f 2 volume := by
    dsimp only [f]
    exact
      φ.continuous.memLp_of_hasCompactSupport
        φ.hasCompactSupport

  have hdEq :
      (dφ : Point3 → ℝ)
        =
      spatial3.d
        (h3AxisOfFin3 i)
        f := by
    dsimp only [dφ, f]
    exact
      h3WeakTestFunctionSpatialDerivative_eq_spatial3_d
        φ i

  have hd :
      MemLp
        (spatial3.d
          (h3AxisOfFin3 i)
          f)
        2
        volume := by
    rw [← hdEq]
    exact
      dφ.continuous.memLp_of_hasCompactSupport
        dφ.hasCompactSupport

  have hBaseLp :
      hf.toLp f
        =
      h3WeakTestFunctionPhysicalL2 φ := by
    apply MeasureTheory.Lp.ext

    filter_upwards [
      MeasureTheory.MemLp.coeFn_toLp hf,
      h3WeakTestFunctionPhysicalL2_ae φ
    ] with x hx hφx

    rw [hx, hφx]

  have hDerivLp :
      hd.toLp
          (spatial3.d
            (h3AxisOfFin3 i)
            f)
        =
      h3WeakTestFunctionPhysicalL2 dφ := by
    apply MeasureTheory.Lp.ext

    filter_upwards [
      MeasureTheory.MemLp.coeFn_toLp hd,
      h3WeakTestFunctionPhysicalL2_ae dφ
    ] with x hx hdx

    rw [hx, hdx]

    exact
      congrFun hdEq x |>.symm

  have hAE :=
    h3ScalarFourierL2_spatialDerivative_fin_ae
      hfC1 i hf hd

  rw [hBaseLp, hDerivLp] at hAE

  simpa only [dφ] using hAE

/-! ## Divergence-free test vectors are raw-Fourier divergence-free -/

/-- A compact smooth weak test vector satisfying the project's bundled
divergence-free condition has raw Fourier divergence zero almost everywhere
after physical `L²` packaging. -/
theorem h3WeakTestVectorPhysicalL2Hilbert_rawFourier_divergenceFree
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    H3SpectralFinDivergenceFree
      (h3PhysicalRealFinVectorL2HilbertRawFourier
        (h3WeakTestVectorPhysicalL2Hilbert φ)) := by
  let D : Fin 3 → H3WeakTestFunction :=
    fun i =>
      h3WeakTestFunctionSpatialDerivative
        (h3AxisOfFin3 i)
        (φ i)

  have hDsum :
      (∑ i : Fin 3, D i)
        =
      (0 : H3WeakTestFunction) := by
    unfold H3WeakTestVectorDivergenceFree at hφ
    simpa only [
      D,
      h3WeakTestFunctionSpatialDerivative
    ] using hφ

  have hL2sum :
      (∑ i : Fin 3,
        h3WeakTestFunctionPhysicalL2 (D i))
        =
      (0 : H3ScalarL2) := by
    simp only [Fin.sum_univ_three]
    rw [add_assoc]

    apply MeasureTheory.Lp.ext

    filter_upwards [
      MeasureTheory.Lp.coeFn_add
        (h3WeakTestFunctionPhysicalL2 (D 0))
        (h3WeakTestFunctionPhysicalL2 (D 1)
          + h3WeakTestFunctionPhysicalL2 (D 2)),
      MeasureTheory.Lp.coeFn_add
        (h3WeakTestFunctionPhysicalL2 (D 1))
        (h3WeakTestFunctionPhysicalL2 (D 2)),
      h3WeakTestFunctionPhysicalL2_ae (D 0),
      h3WeakTestFunctionPhysicalL2_ae (D 1),
      h3WeakTestFunctionPhysicalL2_ae (D 2),
      MeasureTheory.Lp.coeFn_zero
        ℝ (2 : ENNReal) (volume : Measure Point3)
    ] with x hOuter hInner h0 h1 h2 hZero

    rw [hOuter]
    simp only [Pi.add_apply]
    rw [hInner]
    simp only [Pi.add_apply]
    rw [h0, h1, h2, hZero]

    have hx :=
      congrArg
        (fun ψ : H3WeakTestFunction => ψ x)
        hDsum

    rw [Fin.sum_univ_three] at hx

    change
      ((D 0) x + (D 1) x) + (D 2) x
        =
      0
      at hx

    rw [add_assoc] at hx

    exact hx

  let F : Fin 3 → H3FourierComplexL2 :=
    fun i =>
      h3ScalarFourierL2
        (h3WeakTestFunctionPhysicalL2 (D i))

  have hFourierSum :
      (∑ i : Fin 3, F i)
        =
      (0 : H3FourierComplexL2) := by
    have h :=
      congrArg h3ScalarFourierL2 hL2sum

    simp only [Fin.sum_univ_three] at h ⊢

    rw [
      h3ScalarFourierL2_add,
      h3ScalarFourierL2_add,
      h3ScalarFourierL2_zero
    ] at h

    simpa only [F] using h

  have hF0 :=
    h3WeakTestFunctionPhysicalL2_spatialDerivative_fourier_ae
      (φ 0) 0

  have hF1 :=
    h3WeakTestFunctionPhysicalL2_spatialDerivative_fourier_ae
      (φ 1) 1

  have hF2 :=
    h3WeakTestFunctionPhysicalL2_spatialDerivative_fourier_ae
      (φ 2) 2

  have hFourierZero :
      ((F 0 + (F 1 + F 2) :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[volume]
      (fun _ : H3FourierPoint3 => 0) := by
    have hEq :
        F 0 + (F 1 + F 2)
          =
        (0 : H3FourierComplexL2) := by
      simpa only [Fin.sum_univ_three, add_assoc] using hFourierSum

    rw [hEq]

    exact
      MeasureTheory.Lp.coeFn_zero
        ℂ (2 : ENNReal)
        (volume : Measure H3FourierPoint3)

  unfold H3SpectralFinDivergenceFree

  filter_upwards [
    hF0,
    hF1,
    hF2,
    MeasureTheory.Lp.coeFn_add
      (F 0)
      (F 1 + F 2),
    MeasureTheory.Lp.coeFn_add
      (F 1)
      (F 2),
    hFourierZero
  ] with ξ h0ξ h1ξ h2ξ hOuter hInner hZero

  have hPointZero :
      F 0 ξ + (F 1 ξ + F 2 ξ)
        =
      0 := by
    have hZero' := hZero
    rw [hOuter] at hZero'
    simp only [Pi.add_apply] at hZero'
    rw [hInner] at hZero'
    simp only [Pi.add_apply] at hZero'
    exact hZero'

  have hRaw
      (i : Fin 3) :
      h3PhysicalRealFinVectorL2HilbertRawFourier
          (h3WeakTestVectorPhysicalL2Hilbert φ)
          i
        =
      h3ScalarFourierL2
        (h3WeakTestFunctionPhysicalL2 (φ i)) := by
    unfold
      h3PhysicalRealFinVectorL2HilbertRawFourier
      h3WeakTestVectorPhysicalL2Hilbert

    rfl

  simp only [Fin.sum_univ_three]

  rw [hRaw 0, hRaw 1, hRaw 2]

  rw [← h0ξ, ← h1ξ, ← h2ξ]

  simpa only [F, D, add_assoc] using hPointZero

/-! ## Leray invariance and closed-span inclusion -/

/-- Every compact smooth divergence-free weak test state is physically
Leray-fixed after embedding in the genuine finite `PiLp 2` Hilbert product. -/
theorem h3WeakTestVectorPhysicalL2Hilbert_lerayFixed
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3WeakTestVectorPhysicalL2Hilbert φ) := by
  unfold H3PhysicalRealFinVectorL2HilbertLerayFixed

  exact
    h3SpectralFinLerayApply_eq_of_divergenceFree
      (h3WeakTestVectorPhysicalL2Hilbert_rawFourier_divergenceFree
        φ hφ)

/-- The unrestricted divergence-free weak-test generator set is contained in
the physical Leray-fixed closed submodule. -/
theorem h3DivergenceFreeWeakTestPhysicalL2Set_subset_lerayFixedSubmodule :
    h3DivergenceFreeWeakTestPhysicalL2Set
      ⊆
    (h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule :
      Set H3PhysicalRealFinVectorL2Hilbert) := by
  intro Φ hΦ

  rcases hΦ with
    ⟨φ, hDiv, rfl⟩

  exact
    (mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff
      (h3WeakTestVectorPhysicalL2Hilbert φ)).2
      (h3WeakTestVectorPhysicalL2Hilbert_lerayFixed
        φ hDiv)

/-- The algebraic span generated by compact smooth divergence-free weak tests
is contained in the physical Leray-fixed submodule. -/
theorem h3DivergenceFreeWeakTestPhysicalL2Span_le_lerayFixedSubmodule :
    h3DivergenceFreeWeakTestPhysicalL2Span
      ≤
    h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
  unfold h3DivergenceFreeWeakTestPhysicalL2Span

  exact
    Submodule.span_le.mpr
      h3DivergenceFreeWeakTestPhysicalL2Set_subset_lerayFixedSubmodule

/-- The entire closed span of compact smooth divergence-free weak tests is
contained in the exact physical Leray-fixed closed submodule. -/
theorem h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_le_lerayFixedSubmodule :
    h3DivergenceFreeWeakTestPhysicalL2ClosedSpan
      ≤
    h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
  unfold h3DivergenceFreeWeakTestPhysicalL2ClosedSpan

  exact
    Submodule.topologicalClosure_minimal
      h3DivergenceFreeWeakTestPhysicalL2Span
      h3DivergenceFreeWeakTestPhysicalL2Span_le_lerayFixedSubmodule
      isClosed_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule

/-- Since the easy inclusion is now proved, the parameter-free Leray-density
frontier is exactly equality between the closed weak-test span and the physical
Leray-fixed submodule. -/
theorem H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_iff_eq :
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan
      ↔
    h3DivergenceFreeWeakTestPhysicalL2ClosedSpan
      =
    h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
  unfold
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan

  constructor

  · intro hDensity

    exact
      le_antisymm
        h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_le_lerayFixedSubmodule
        hDensity

  · intro hEq

    exact hEq.ge

end

end Euclidean
end Bridge
end PrimeTensor
