import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Real

/-!
# Classicalization: real Schwartz curl identities imply tempered curl-freeness

`Schwartz.Real` extended the weak curl identities from transported compact
tests to every real Schwartz test in the exact `W¹,²` graph topology.

The tempered distributions themselves are complex-linear, so one final
algebraic step remains.  Every complex Schwartz test decomposes exactly as

    Φ = ofReal (re Φ) + i • ofReal (im Φ).

Consequently two complex tempered distributions agree everywhere once they
agree on all complexifications of real Schwartz tests.

For the particular first derivatives of transported physical `L²` classes,
evaluation on a complexified real Schwartz test is exactly minus the
complexification of the corresponding real first-derivative `L²` pairing.
Thus the three real-Schwartz curl identities immediately become equalities of
complex tempered distributions.

This closes

    H3PhysicalL2WeakCurlFreeImpliesTemperedCurlFree.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzComplex
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Real and imaginary parts of a complex Schwartz function -/

/-- Pointwise real part of a complex Schwartz function, still Schwartz. -/
noncomputable def h3ComplexSchwartzRealPart
    (Φ : 𝓢(H3FourierPoint3, ℂ)) :
    𝓢(H3FourierPoint3, ℝ) :=
  (SchwartzMap.postcompCLM
    (𝕜 := ℝ)
    Complex.reCLM) Φ

/-- Pointwise imaginary part of a complex Schwartz function, still Schwartz. -/
noncomputable def h3ComplexSchwartzImagPart
    (Φ : 𝓢(H3FourierPoint3, ℂ)) :
    𝓢(H3FourierPoint3, ℝ) :=
  (SchwartzMap.postcompCLM
    (𝕜 := ℝ)
    Complex.imCLM) Φ

@[simp]
theorem h3ComplexSchwartzRealPart_apply
    (Φ : 𝓢(H3FourierPoint3, ℂ))
    (x : H3FourierPoint3) :
    h3ComplexSchwartzRealPart Φ x = (Φ x).re := by
  rfl

@[simp]
theorem h3ComplexSchwartzImagPart_apply
    (Φ : 𝓢(H3FourierPoint3, ℂ))
    (x : H3FourierPoint3) :
    h3ComplexSchwartzImagPart Φ x = (Φ x).im := by
  rfl

/-- Every complex Schwartz test is the complexification of its real part plus
`i` times the complexification of its imaginary part. -/
theorem h3ComplexSchwartz_eq_real_add_I_imag
    (Φ : 𝓢(H3FourierPoint3, ℂ)) :
    Φ
      =
    h3RealSchwartzComplexification
        (h3ComplexSchwartzRealPart Φ)
      +
    Complex.I •
      h3RealSchwartzComplexification
        (h3ComplexSchwartzImagPart Φ) := by
  ext x

  apply Complex.ext

  · simp [
      h3RealSchwartzComplexification_apply,
      h3ComplexSchwartzRealPart_apply,
      h3ComplexSchwartzImagPart_apply
    ]

  · simp [
      h3RealSchwartzComplexification_apply,
      h3ComplexSchwartzRealPart_apply,
      h3ComplexSchwartzImagPart_apply
    ]

/-! ## Complex-linear determination by real Schwartz complexifications -/

/-- A complex tempered distribution is determined by its values on
complexifications of real Schwartz tests. -/
theorem h3RealSchwartzComplexifications_determine_temperedDistributions
    (S T : 𝓢'(H3FourierPoint3, ℂ))
    (hReal :
      ∀ φ : 𝓢(H3FourierPoint3, ℝ),
        S (h3RealSchwartzComplexification φ)
          =
        T (h3RealSchwartzComplexification φ)) :
    S = T := by
  ext Φ

  rw [h3ComplexSchwartz_eq_real_add_I_imag Φ]

  simp only [
    map_add,
    map_smul
  ]

  rw [
    hReal (h3ComplexSchwartzRealPart Φ),
    hReal (h3ComplexSchwartzImagPart Φ)
  ]

/-! ## Evaluation of one transported L² derivative on real Schwartz tests -/

/-- A coordinate derivative of a transported physical `L²` distribution,
tested against the complexification of a real Schwartz function, is minus the
complexification of the corresponding real first-derivative `L²` pairing. -/
theorem h3PhysicalScalarL2EuclideanComplex_lineDeriv_apply_realSchwartz
    (f : H3ScalarL2)
    (i : Fin 3)
    (φ : 𝓢(H3FourierPoint3, ℝ)) :
    (∂_{h3FourierAxisDirection (h3AxisOfFin3 i)}
        ((h3PhysicalScalarL2EuclideanComplex f :
            H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ)))
        (h3RealSchwartzComplexification φ)
      =
    - Complex.ofReal
        (inner ℝ
          (h3ToFourierRealL2 f)
          ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
            𝓢(H3FourierPoint3, ℝ)).toLp
              2
              (volume : Measure H3FourierPoint3))) := by
  have hDeriv :
      ∂_{h3FourierAxisDirection (h3AxisOfFin3 i)}
          (h3RealSchwartzComplexification φ)
        =
      h3RealSchwartzComplexification
        (∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ) := by
    unfold h3RealSchwartzComplexification
    exact
      h3SchwartzComplexify_lineDeriv
        φ
        (h3FourierAxisDirection (h3AxisOfFin3 i))

  rw [
    TemperedDistribution.lineDerivOp_apply_apply,
    hDeriv,
    map_neg,
    h3PhysicalScalarL2EuclideanComplex_apply_realSchwartz
  ]

/-! ## Generic real-pairing-to-tempered-derivative bridge -/

/-- Equality of two real first-derivative `L²` pairings on every real Schwartz
test implies equality of the corresponding complex tempered derivatives. -/
theorem h3PhysicalScalarL2EuclideanComplex_lineDeriv_eq_of_realSchwartz_pairing_eq
    (f g : H3ScalarL2)
    (i j : Fin 3)
    (hPair :
      ∀ φ : 𝓢(H3FourierPoint3, ℝ),
        inner ℝ
            (h3ToFourierRealL2 f)
            ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
              𝓢(H3FourierPoint3, ℝ)).toLp
                2
                (volume : Measure H3FourierPoint3))
          =
        inner ℝ
            (h3ToFourierRealL2 g)
            ((∂_{h3FourierAxisDirection (h3AxisOfFin3 j)} φ :
              𝓢(H3FourierPoint3, ℝ)).toLp
                2
                (volume : Measure H3FourierPoint3))) :
    ∂_{h3FourierAxisDirection (h3AxisOfFin3 i)}
        ((h3PhysicalScalarL2EuclideanComplex f :
            H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ))
      =
    ∂_{h3FourierAxisDirection (h3AxisOfFin3 j)}
        ((h3PhysicalScalarL2EuclideanComplex g :
            H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ)) := by
  apply
    h3RealSchwartzComplexifications_determine_temperedDistributions

  intro φ

  rw [
    h3PhysicalScalarL2EuclideanComplex_lineDeriv_apply_realSchwartz,
    h3PhysicalScalarL2EuclideanComplex_lineDeriv_apply_realSchwartz
  ]

  exact
    congrArg Neg.neg
      (congrArg Complex.ofReal
        (hPair φ))

/-! ## Close tempered curl-freeness -/

/-- Real-Schwartz curl-freeness is already enough to give the full complex
tempered curl identities. -/
theorem h3PhysicalRealFinVectorL2Hilbert_temperedCurlFree_of_realSchwartzCurlFree
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hReal :
      H3PhysicalRealFinVectorL2HilbertRealSchwartzCurlFree V) :
    H3PhysicalRealFinVectorL2HilbertTemperedCurlFree V := by
  unfold H3PhysicalRealFinVectorL2HilbertTemperedCurlFree

  have h01 :
      ∂_{h3FourierAxisDirection (h3AxisOfFin3 1)}
          ((h3PhysicalScalarL2EuclideanComplex (V 0) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ))
        =
      ∂_{h3FourierAxisDirection (h3AxisOfFin3 0)}
          ((h3PhysicalScalarL2EuclideanComplex (V 1) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)) := by
    apply
      h3PhysicalScalarL2EuclideanComplex_lineDeriv_eq_of_realSchwartz_pairing_eq
        (V 0)
        (V 1)
        1
        0

    intro φ
    exact (hReal φ).1

  have h02 :
      ∂_{h3FourierAxisDirection (h3AxisOfFin3 2)}
          ((h3PhysicalScalarL2EuclideanComplex (V 0) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ))
        =
      ∂_{h3FourierAxisDirection (h3AxisOfFin3 0)}
          ((h3PhysicalScalarL2EuclideanComplex (V 2) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)) := by
    apply
      h3PhysicalScalarL2EuclideanComplex_lineDeriv_eq_of_realSchwartz_pairing_eq
        (V 0)
        (V 2)
        2
        0

    intro φ
    exact (hReal φ).2.1

  have h12 :
      ∂_{h3FourierAxisDirection (h3AxisOfFin3 2)}
          ((h3PhysicalScalarL2EuclideanComplex (V 1) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ))
        =
      ∂_{h3FourierAxisDirection (h3AxisOfFin3 1)}
          ((h3PhysicalScalarL2EuclideanComplex (V 2) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)) := by
    apply
      h3PhysicalScalarL2EuclideanComplex_lineDeriv_eq_of_realSchwartz_pairing_eq
        (V 1)
        (V 2)
        2
        1

    intro φ
    exact (hReal φ).2.2

  exact ⟨h01, h02, h12⟩

/-- The exact weak-curl-to-tempered-curl frontier is now proved. -/
theorem H3PhysicalL2WeakCurlFreeImpliesTemperedCurlFree_proved :
    H3PhysicalL2WeakCurlFreeImpliesTemperedCurlFree := by
  intro V hWeak

  exact
    h3PhysicalRealFinVectorL2Hilbert_temperedCurlFree_of_realSchwartzCurlFree
      (h3PhysicalRealFinVectorL2Hilbert_realSchwartzCurlFree_of_weakCurlFree
        hWeak)

end

end Euclidean
end Bridge
end PrimeTensor
