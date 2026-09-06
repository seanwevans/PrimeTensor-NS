import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Distribution
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Transport

/-!
# Classicalization: transport compact weak-test pairings to the tempered L² carrier

`Schwartz.Distribution` has closed the compact-test side of the curl argument:
weak curl-freeness is now literal ordinary distributional curl-freeness on
physical `Point3`.

The tempered/Fourier argument lives on the Euclidean carrier

    H3FourierPoint3 = EuclideanSpace ℝ (Axis three).

Before extending from compact tests to arbitrary Schwartz tests, this file
closes the carrier and complexification seam exactly.

A physical weak test `ψ` is pulled through the canonical continuous linear
equivalence

    H3FourierPoint3 ≃L[ℝ] Point3,

which is pointwise the same coordinate map as `WithLp.ofLp`.  Compact support
and smoothness therefore make the pullback a real Schwartz function.  We then
complexify that Schwartz function pointwise.

For every physical scalar `L²` class `f`, evaluation of the transported
tempered `L²` distribution on this complexified test is exactly the complex
embedding of the original physical real `L²` Hilbert pairing:

    [transport f](transport ψ) = ofReal ⟪f, ψ⟫.

Thus no information is lost in the `Point3` -> Euclidean carrier ->
complex-tempered passage on compact weak tests.

After this checkpoint, the remaining analytic issue is only extension from
these transported compact tests to arbitrary Schwartz tests.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzTransport
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzTransport :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## The exact carrier equivalence -/

/-- The canonical continuous linear equivalence from the Euclidean Fourier
carrier to the physical product carrier.

Its underlying map is `WithLp.ofLp`, exactly the map already used by
`h3ToFourierRealL2`. -/
noncomputable def h3FourierPoint3EquivPoint3 :
    H3FourierPoint3 ≃L[ℝ] Point3 :=
  PiLp.continuousLinearEquiv
    2
    ℝ
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)

@[simp]
theorem h3FourierPoint3EquivPoint3_apply
    (x : H3FourierPoint3)
    (a : PrimeTensor.Axis Depth.three) :
    h3FourierPoint3EquivPoint3 x a = x a := by
  rfl

theorem h3FourierPoint3EquivPoint3_eq_ofLp :
    (h3FourierPoint3EquivPoint3 :
      H3FourierPoint3 → Point3)
      =
    (WithLp.ofLp :
      H3FourierPoint3 → Point3) := by
  funext x
  ext a
  rfl

/-! ## Weak tests transported to Euclidean Schwartz space -/

/-- Pull a physical compact smooth weak test to the Euclidean Fourier carrier.
It remains compactly supported and smooth, hence is Schwartz. -/
noncomputable def h3WeakTestToFourierRealSchwartz
    (ψ : H3WeakTestFunction) :
    𝓢(H3FourierPoint3, ℝ) :=
  (ψ.hasCompactSupport.comp_homeomorph
      h3FourierPoint3EquivPoint3.toHomeomorph).toSchwartzMap
    (ψ.contDiff.comp
      h3FourierPoint3EquivPoint3.contDiff)

@[simp]
theorem h3WeakTestToFourierRealSchwartz_apply
    (ψ : H3WeakTestFunction)
    (x : H3FourierPoint3) :
    h3WeakTestToFourierRealSchwartz ψ x
      =
    ψ ((WithLp.ofLp : H3FourierPoint3 → Point3) x) := by
  rfl

/-- Complexify the transported real weak test as a Schwartz function. -/
noncomputable def h3WeakTestToFourierComplexSchwartz
    (ψ : H3WeakTestFunction) :
    𝓢(H3FourierPoint3, ℂ) :=
  (SchwartzMap.postcompCLM
    (𝕜 := ℝ)
    Complex.ofRealCLM)
    (h3WeakTestToFourierRealSchwartz ψ)

@[simp]
theorem h3WeakTestToFourierComplexSchwartz_apply
    (ψ : H3WeakTestFunction)
    (x : H3FourierPoint3) :
    h3WeakTestToFourierComplexSchwartz ψ x
      =
    (ψ ((WithLp.ofLp : H3FourierPoint3 → Point3) x) : ℂ) := by
  simp [
    h3WeakTestToFourierComplexSchwartz,
    h3WeakTestToFourierRealSchwartz_apply
  ]

/-! ## Raw representative of the transported physical L² class -/

/-- The complex Euclidean `L²` class used before Fourier transformation has
the expected transported physical representative almost everywhere. -/
theorem h3PhysicalScalarL2EuclideanComplex_coeFn_ae
    (f : H3ScalarL2) :
    (h3PhysicalScalarL2EuclideanComplex f :
      H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    fun x : H3FourierPoint3 =>
      ((f ((WithLp.ofLp :
        H3FourierPoint3 → Point3) x) : ℝ) : ℂ) := by
  have hReal :
      (h3ToFourierRealL2 f :
        H3FourierPoint3 → ℝ)
        =ᵐ[volume]
      fun x : H3FourierPoint3 =>
        f ((WithLp.ofLp :
          H3FourierPoint3 → Point3) x) := by
    unfold h3ToFourierRealL2
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        f
        (PiLp.volume_preserving_ofLp
          (PrimeTensor.Axis Depth.three))

  have hComplex :=
    Complex.ofRealCLM.coeFn_compLp
      (h3ToFourierRealL2 f)

  unfold
    h3PhysicalScalarL2EuclideanComplex
    h3ComplexifyFourierL2

  filter_upwards [hComplex, hReal] with x hComplexx hRealx

  rw [hComplexx, hRealx]

  rfl

/-! ## Exact pairing transport -/

/-- Evaluation of the transported complex `L²` tempered distribution on a
transported compact weak test is exactly the complexification of the original
physical real `L²` Hilbert pairing. -/
theorem h3PhysicalScalarL2EuclideanComplex_apply_weakTestTransport
    (f : H3ScalarL2)
    (ψ : H3WeakTestFunction) :
    ((h3PhysicalScalarL2EuclideanComplex f :
        H3FourierComplexL2) :
      𝓢'(H3FourierPoint3, ℂ))
      (h3WeakTestToFourierComplexSchwartz ψ)
      =
    Complex.ofReal
      (inner ℝ
        f
        (h3WeakTestFunctionPhysicalL2 ψ)) := by
  let Φ : H3ScalarL2 :=
    h3WeakTestFunctionPhysicalL2 ψ

  have hF :=
    h3PhysicalScalarL2EuclideanComplex_coeFn_ae f

  have hPhysicalTest :=
    h3WeakTestFunctionPhysicalL2_ae ψ

  have hChangeOfVariables :
      (∫ x : H3FourierPoint3,
        (ψ ((WithLp.ofLp :
            H3FourierPoint3 → Point3) x) : ℂ)
          *
        ((f ((WithLp.ofLp :
            H3FourierPoint3 → Point3) x) : ℝ) : ℂ)
        ∂volume)
        =
      ∫ y : Point3,
        (ψ y : ℂ) * ((f y : ℝ) : ℂ)
        ∂volume := by
    let e :
        H3FourierPoint3 ≃L[ℝ] Point3 :=
      h3FourierPoint3EquivPoint3

    have hPreserving :
        MeasurePreserving
          (e : H3FourierPoint3 → Point3)
          (volume : Measure H3FourierPoint3)
          (volume : Measure Point3) := by
      simpa only [
        e,
        h3FourierPoint3EquivPoint3_eq_ofLp
      ] using
        (PiLp.volume_preserving_ofLp
          (PrimeTensor.Axis Depth.three))

    have hIntegral :=
      hPreserving.integral_comp
        e.toHomeomorph.measurableEmbedding
        (fun y : Point3 =>
          (ψ y : ℂ) * ((f y : ℝ) : ℂ))

    simpa only [
      e,
      h3FourierPoint3EquivPoint3_eq_ofLp
    ] using hIntegral

  have hInnerIntegrable :
      Integrable
        (fun y : Point3 =>
          inner ℝ
            ((f : Point3 → ℝ) y)
            ((Φ : Point3 → ℝ) y))
        (volume : Measure Point3) :=
    MeasureTheory.L2.integrable_inner f Φ

  have hOfRealIntegral :=
    Complex.ofRealCLM.integral_comp_comm
      hInnerIntegrable

  rw [MeasureTheory.Lp.toTemperedDistribution_apply]

  calc
    (∫ x : H3FourierPoint3,
      h3WeakTestToFourierComplexSchwartz ψ x •
        h3PhysicalScalarL2EuclideanComplex f x
      ∂volume)
        =
      ∫ x : H3FourierPoint3,
        (ψ ((WithLp.ofLp :
            H3FourierPoint3 → Point3) x) : ℂ)
          *
        ((f ((WithLp.ofLp :
            H3FourierPoint3 → Point3) x) : ℝ) : ℂ)
        ∂volume := by
          apply integral_congr_ae
          filter_upwards [hF] with x hFx
          rw [hFx]
          simp [
            h3WeakTestToFourierComplexSchwartz_apply,
            smul_eq_mul
          ]
    _ =
      ∫ y : Point3,
        (ψ y : ℂ) * ((f y : ℝ) : ℂ)
        ∂volume :=
      hChangeOfVariables
    _ =
      ∫ y : Point3,
        Complex.ofReal
          (inner ℝ
            ((f : Point3 → ℝ) y)
            ((Φ : Point3 → ℝ) y))
        ∂volume := by
          apply integral_congr_ae
          filter_upwards [hPhysicalTest] with y hψy
          rw [hψy]
          simp [mul_comm]
    _ =
      Complex.ofReal
        (∫ y : Point3,
          inner ℝ
            ((f : Point3 → ℝ) y)
            ((Φ : Point3 → ℝ) y)
          ∂volume) := by
          exact hOfRealIntegral
    _ =
      Complex.ofReal
        (inner ℝ f Φ) := by
          rw [MeasureTheory.L2.inner_def]
    _ =
      Complex.ofReal
        (inner ℝ
          f
          (h3WeakTestFunctionPhysicalL2 ψ)) := by
          rfl

end

end Euclidean
end Bridge
end PrimeTensor
