import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Transport

/-!
# Classicalization: transported weak-test derivatives

`Schwartz.Transport` proved that the tempered `L²` pairing on the Euclidean
carrier agrees exactly with the physical real `L²` pairing on every transported
compact weak test.

This file closes the derivative part of that transport.

For a physical weak test `ψ` and physical coordinate axis `a`, transport to the
Euclidean carrier commutes with the corresponding directional derivative:

    ∂_{e_a} transport(ψ) = transport(∂_a ψ).

The statement is first proved for the real transported Schwartz function.  The
pointwise proof uses the Fréchet chain rule for the canonical continuous linear
equivalence between the Euclidean and physical carriers.  It is then lifted
through pointwise complexification.

Consequently the original weak curl identities imply equality of the three
tempered distributional curl derivatives when evaluated on every transported
compact weak test.

After this checkpoint the sole remaining analytic fact is a generic determining
statement:

    transported compact weak tests determine complex tempered distributions.

That is now completely independent of Navier--Stokes, Leray projection, and
Fourier algebra.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzDerivative :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## The carrier equivalence sends Euclidean coordinate directions to the
physical coordinate directions -/

@[simp]
theorem h3FourierPoint3EquivPoint3_fourierAxisDirection
    (a : PrimeTensor.Axis Depth.three) :
    h3FourierPoint3EquivPoint3
        (h3FourierAxisDirection a)
      =
    axisDirection a := by
  ext b
  rfl

/-! ## Real transported weak tests commute with coordinate derivatives -/

/-- Pullback through the canonical Euclidean-to-physical carrier equivalence
commutes with the matching coordinate directional derivative. -/
theorem h3WeakTestToFourierRealSchwartz_lineDeriv
    (a : PrimeTensor.Axis Depth.three)
    (ψ : H3WeakTestFunction) :
    ∂_{h3FourierAxisDirection a}
        (h3WeakTestToFourierRealSchwartz ψ)
      =
    h3WeakTestToFourierRealSchwartz
      (h3WeakTestFunctionSpatialDerivative a ψ) := by
  ext x

  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]

  change
    (fderiv ℝ
        ((ψ : Point3 → ℝ) ∘
          (h3FourierPoint3EquivPoint3 :
            H3FourierPoint3 → Point3))
        x)
      (h3FourierAxisDirection a)
      =
    (h3WeakTestFunctionSpatialDerivative a ψ)
      (h3FourierPoint3EquivPoint3 x)

  rw [ContinuousLinearEquiv.comp_right_fderiv]
  rw [ContinuousLinearMap.comp_apply]

  have hDirection :
      (h3FourierPoint3EquivPoint3 :
        H3FourierPoint3 →L[ℝ] Point3)
        (h3FourierAxisDirection a)
      =
      axisDirection a := by
    simpa using
      h3FourierPoint3EquivPoint3_fourierAxisDirection a

  rw [hDirection]

  have hDiff :
      DifferentiableAt ℝ
        (ψ : Point3 → ℝ)
        (h3FourierPoint3EquivPoint3 x) :=
    (ψ.contDiff.differentiable (by simp)).differentiableAt

  calc
    (fderiv ℝ
        (ψ : Point3 → ℝ)
        (h3FourierPoint3EquivPoint3 x))
        (axisDirection a)
        =
      lineDeriv ℝ
        (ψ : Point3 → ℝ)
        (h3FourierPoint3EquivPoint3 x)
        (axisDirection a) := by
          exact hDiff.lineDeriv_eq_fderiv.symm
    _ =
      (h3WeakTestFunctionSpatialDerivative a ψ)
        (h3FourierPoint3EquivPoint3 x) := by
          simpa only [
            h3WeakTestFunctionSpatialDerivative
          ] using
            (TestFunction.lineDerivCLM_apply_of_le
              (𝕜 := ℝ)
              (f := ψ)
              (v := axisDirection a)
              (x := h3FourierPoint3EquivPoint3 x)
              (by simp)).symm

/-! ## Complexification commutes with Schwartz directional derivatives -/

/-- Pointwise real-to-complex embedding commutes with directional derivative
on Schwartz space. -/
theorem h3SchwartzComplexify_lineDeriv
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (v : H3FourierPoint3) :
    ∂_{v}
        ((SchwartzMap.postcompCLM
          (𝕜 := ℝ)
          Complex.ofRealCLM) φ)
      =
    (SchwartzMap.postcompCLM
      (𝕜 := ℝ)
      Complex.ofRealCLM)
      (∂_{v} φ) := by
  ext x

  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]

  change
    (fderiv ℝ
        (fun y : H3FourierPoint3 =>
          Complex.ofRealCLM (φ y))
        x)
      v
      =
    Complex.ofRealCLM
      ((∂_{v} φ) x)

  have hComp :
      HasFDerivAt
        (fun y : H3FourierPoint3 =>
          Complex.ofRealCLM (φ y))
        (Complex.ofRealCLM.comp
          (fderiv ℝ
            (φ : H3FourierPoint3 → ℝ)
            x))
        x := by
    exact
      Complex.ofRealCLM.hasFDerivAt.comp
        x
        (φ.hasFDerivAt x)

  rw [hComp.fderiv]
  rw [ContinuousLinearMap.comp_apply]
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- The fully complex transported weak test commutes with the matching
coordinate directional derivative. -/
theorem h3WeakTestToFourierComplexSchwartz_lineDeriv
    (a : PrimeTensor.Axis Depth.three)
    (ψ : H3WeakTestFunction) :
    ∂_{h3FourierAxisDirection a}
        (h3WeakTestToFourierComplexSchwartz ψ)
      =
    h3WeakTestToFourierComplexSchwartz
      (h3WeakTestFunctionSpatialDerivative a ψ) := by
  unfold h3WeakTestToFourierComplexSchwartz

  rw [h3SchwartzComplexify_lineDeriv]
  rw [h3WeakTestToFourierRealSchwartz_lineDeriv]

/-! ## Tempered curl equality on the transported compact test class -/

/-- The three tempered curl derivatives agree when tested against every
transported compact weak test. -/
def H3PhysicalRealFinVectorL2HilbertTemperedCurlFreeOnWeakTestTransport
    (V : H3PhysicalRealFinVectorL2Hilbert) : Prop :=
  ∀ ψ : H3WeakTestFunction,
    (∂_{h3FourierAxisDirection (h3AxisOfFin3 1)}
        ((h3PhysicalScalarL2EuclideanComplex (V 0) :
            H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ)))
        (h3WeakTestToFourierComplexSchwartz ψ)
      =
    (∂_{h3FourierAxisDirection (h3AxisOfFin3 0)}
        ((h3PhysicalScalarL2EuclideanComplex (V 1) :
            H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ)))
        (h3WeakTestToFourierComplexSchwartz ψ)
    ∧
    (∂_{h3FourierAxisDirection (h3AxisOfFin3 2)}
        ((h3PhysicalScalarL2EuclideanComplex (V 0) :
            H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ)))
        (h3WeakTestToFourierComplexSchwartz ψ)
      =
    (∂_{h3FourierAxisDirection (h3AxisOfFin3 0)}
        ((h3PhysicalScalarL2EuclideanComplex (V 2) :
            H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ)))
        (h3WeakTestToFourierComplexSchwartz ψ)
    ∧
    (∂_{h3FourierAxisDirection (h3AxisOfFin3 2)}
        ((h3PhysicalScalarL2EuclideanComplex (V 1) :
            H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ)))
        (h3WeakTestToFourierComplexSchwartz ψ)
      =
    (∂_{h3FourierAxisDirection (h3AxisOfFin3 1)}
        ((h3PhysicalScalarL2EuclideanComplex (V 2) :
            H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ)))
        (h3WeakTestToFourierComplexSchwartz ψ)

/-- Weak physical curl-freeness already gives the three tempered derivative
identities on every transported compact weak test. -/
theorem h3PhysicalRealFinVectorL2Hilbert_temperedCurlFreeOnWeakTestTransport_of_weakCurlFree
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hWeak :
      H3PhysicalRealFinVectorL2HilbertWeakCurlFree V) :
    H3PhysicalRealFinVectorL2HilbertTemperedCurlFreeOnWeakTestTransport V := by
  intro ψ

  have h01 :
      (∂_{h3FourierAxisDirection (h3AxisOfFin3 1)}
          ((h3PhysicalScalarL2EuclideanComplex (V 0) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)))
          (h3WeakTestToFourierComplexSchwartz ψ)
        =
      (∂_{h3FourierAxisDirection (h3AxisOfFin3 0)}
          ((h3PhysicalScalarL2EuclideanComplex (V 1) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)))
          (h3WeakTestToFourierComplexSchwartz ψ) := by
    rw [
      TemperedDistribution.lineDerivOp_apply_apply,
      TemperedDistribution.lineDerivOp_apply_apply,
      h3WeakTestToFourierComplexSchwartz_lineDeriv,
      h3WeakTestToFourierComplexSchwartz_lineDeriv,
      map_neg,
      map_neg,
      h3PhysicalScalarL2EuclideanComplex_apply_weakTestTransport,
      h3PhysicalScalarL2EuclideanComplex_apply_weakTestTransport
    ]

    exact
      congrArg Neg.neg
        (congrArg Complex.ofReal
          (sub_eq_zero.mp ((hWeak ψ).1)))

  have h02 :
      (∂_{h3FourierAxisDirection (h3AxisOfFin3 2)}
          ((h3PhysicalScalarL2EuclideanComplex (V 0) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)))
          (h3WeakTestToFourierComplexSchwartz ψ)
        =
      (∂_{h3FourierAxisDirection (h3AxisOfFin3 0)}
          ((h3PhysicalScalarL2EuclideanComplex (V 2) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)))
          (h3WeakTestToFourierComplexSchwartz ψ) := by
    rw [
      TemperedDistribution.lineDerivOp_apply_apply,
      TemperedDistribution.lineDerivOp_apply_apply,
      h3WeakTestToFourierComplexSchwartz_lineDeriv,
      h3WeakTestToFourierComplexSchwartz_lineDeriv,
      map_neg,
      map_neg,
      h3PhysicalScalarL2EuclideanComplex_apply_weakTestTransport,
      h3PhysicalScalarL2EuclideanComplex_apply_weakTestTransport
    ]

    exact
      congrArg Neg.neg
        (congrArg Complex.ofReal
          (sub_eq_zero.mp ((hWeak ψ).2.1)))

  have h12 :
      (∂_{h3FourierAxisDirection (h3AxisOfFin3 2)}
          ((h3PhysicalScalarL2EuclideanComplex (V 1) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)))
          (h3WeakTestToFourierComplexSchwartz ψ)
        =
      (∂_{h3FourierAxisDirection (h3AxisOfFin3 1)}
          ((h3PhysicalScalarL2EuclideanComplex (V 2) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)))
          (h3WeakTestToFourierComplexSchwartz ψ) := by
    rw [
      TemperedDistribution.lineDerivOp_apply_apply,
      TemperedDistribution.lineDerivOp_apply_apply,
      h3WeakTestToFourierComplexSchwartz_lineDeriv,
      h3WeakTestToFourierComplexSchwartz_lineDeriv,
      map_neg,
      map_neg,
      h3PhysicalScalarL2EuclideanComplex_apply_weakTestTransport,
      h3PhysicalScalarL2EuclideanComplex_apply_weakTestTransport
    ]

    exact
      congrArg Neg.neg
        (congrArg Complex.ofReal
          (sub_eq_zero.mp ((hWeak ψ).2.2)))

  exact ⟨h01, h02, h12⟩

/-! ## Exact remaining generic determining frontier -/

/-- Transported compact real weak tests, after complexification, determine all
complex tempered distributions.

This is now the sole generic density/continuity theorem needed by the physical
L² Leray-density argument. -/
def H3TransportedWeakTestsDetermineTemperedDistributions : Prop :=
  ∀ S T : 𝓢'(H3FourierPoint3, ℂ),
    (∀ ψ : H3WeakTestFunction,
      S (h3WeakTestToFourierComplexSchwartz ψ)
        =
      T (h3WeakTestToFourierComplexSchwartz ψ)) →
    S = T

/-- The generic determining theorem upgrades compact-test curl equality to full
tempered-distribution curl equality. -/
theorem H3PhysicalL2WeakCurlFreeImpliesTemperedCurlFree_of_transportedWeakTestsDetermine
    (hDetermine :
      H3TransportedWeakTestsDetermineTemperedDistributions) :
    H3PhysicalL2WeakCurlFreeImpliesTemperedCurlFree := by
  intro V hWeak

  have hCompact :
      H3PhysicalRealFinVectorL2HilbertTemperedCurlFreeOnWeakTestTransport V :=
    h3PhysicalRealFinVectorL2Hilbert_temperedCurlFreeOnWeakTestTransport_of_weakCurlFree
      hWeak

  unfold H3PhysicalRealFinVectorL2HilbertTemperedCurlFree

  exact
    ⟨
      hDetermine
        (∂_{h3FourierAxisDirection (h3AxisOfFin3 1)}
          ((h3PhysicalScalarL2EuclideanComplex (V 0) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)))
        (∂_{h3FourierAxisDirection (h3AxisOfFin3 0)}
          ((h3PhysicalScalarL2EuclideanComplex (V 1) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)))
        (fun ψ => (hCompact ψ).1),
      hDetermine
        (∂_{h3FourierAxisDirection (h3AxisOfFin3 2)}
          ((h3PhysicalScalarL2EuclideanComplex (V 0) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)))
        (∂_{h3FourierAxisDirection (h3AxisOfFin3 0)}
          ((h3PhysicalScalarL2EuclideanComplex (V 2) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)))
        (fun ψ => (hCompact ψ).2.1),
      hDetermine
        (∂_{h3FourierAxisDirection (h3AxisOfFin3 2)}
          ((h3PhysicalScalarL2EuclideanComplex (V 1) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)))
        (∂_{h3FourierAxisDirection (h3AxisOfFin3 1)}
          ((h3PhysicalScalarL2EuclideanComplex (V 2) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)))
        (fun ψ => (hCompact ψ).2.2)
    ⟩

/-- Therefore the same generic determining theorem is sufficient for the full
parameter-free physical Leray-density theorem. -/
theorem H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_of_transportedWeakTestsDetermine
    (hDetermine :
      H3TransportedWeakTestsDetermineTemperedDistributions) :
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan := by
  exact
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_of_temperedBridge
      (H3PhysicalL2WeakCurlFreeImpliesTemperedCurlFree_of_transportedWeakTestsDetermine
        hDetermine)

end

end Euclidean
end Bridge
end PrimeTensor
