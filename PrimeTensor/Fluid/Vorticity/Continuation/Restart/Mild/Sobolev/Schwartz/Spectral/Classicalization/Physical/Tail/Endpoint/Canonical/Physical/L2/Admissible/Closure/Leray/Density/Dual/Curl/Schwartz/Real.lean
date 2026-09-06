import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Cutoff.Graph

/-!
# Classicalization: extend weak curl identities to all real Schwartz tests

The cutoff analysis is now complete:

    H3TransportedWeakTestsDenseInRealW12Schwartz.

This file uses that exact density theorem to extend the three physical weak
curl identities from transported compact tests to arbitrary real Schwartz
tests.

The first bridge identifies evaluation of the transported complex `L²`
tempered distribution on the complexification of an arbitrary real Schwartz
function with the real `L²` Hilbert pairing on the Euclidean carrier.

As a compact-test corollary, transport preserves the physical scalar `L²`
pairing exactly.  The generic closed-hyperplane theorem from `Schwartz.Sobolev`
can then be applied to each of the three curl coordinates.

No complex Schwartz decomposition is used yet.  The output of this file is the
real-Schwartz curl identity; the next checkpoint only has to complexify it.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzReal
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Real Schwartz complexification -/

/-- Pointwise real-to-complex embedding of an arbitrary real Schwartz test. -/
noncomputable def h3RealSchwartzComplexification
    (φ : 𝓢(H3FourierPoint3, ℝ)) :
    𝓢(H3FourierPoint3, ℂ) :=
  (SchwartzMap.postcompCLM
    (𝕜 := ℝ)
    Complex.ofRealCLM) φ

@[simp]
theorem h3RealSchwartzComplexification_apply
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (x : H3FourierPoint3) :
    h3RealSchwartzComplexification φ x
      =
    Complex.ofReal (φ x) := by
  simp [h3RealSchwartzComplexification]

/-! ## Arbitrary real-Schwartz pairing with transported physical L² -/

/-- Evaluation of the transported complex `L²` tempered distribution on the
complexification of any real Schwartz test is exactly the complexification of
the real Euclidean `L²` Hilbert pairing. -/
theorem h3PhysicalScalarL2EuclideanComplex_apply_realSchwartz
    (f : H3ScalarL2)
    (φ : 𝓢(H3FourierPoint3, ℝ)) :
    ((h3PhysicalScalarL2EuclideanComplex f :
        H3FourierComplexL2) :
      𝓢'(H3FourierPoint3, ℂ))
      (h3RealSchwartzComplexification φ)
      =
    Complex.ofReal
      (inner ℝ
        (h3ToFourierRealL2 f)
        (φ.toLp 2 volume)) := by
  let F : H3FourierRealL2 :=
    h3ToFourierRealL2 f

  let Φ : H3FourierRealL2 :=
    φ.toLp 2 volume

  have hComplex :=
    Complex.ofRealCLM.coeFn_compLp F

  have hTest :=
    φ.coeFn_toLp
      2
      (volume : Measure H3FourierPoint3)

  have hInnerIntegrable :
      Integrable
        (fun x : H3FourierPoint3 =>
          inner ℝ
            ((F : H3FourierPoint3 → ℝ) x)
            ((Φ : H3FourierPoint3 → ℝ) x))
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.L2.integrable_inner F Φ

  have hOfRealIntegral :=
    Complex.ofRealCLM.integral_comp_comm
      hInnerIntegrable

  rw [MeasureTheory.Lp.toTemperedDistribution_apply]

  unfold
    h3PhysicalScalarL2EuclideanComplex
    h3ComplexifyFourierL2

  calc
    (∫ x : H3FourierPoint3,
      h3RealSchwartzComplexification φ x •
        (Complex.ofRealCLM.compLp F) x
      ∂volume)
        =
      ∫ x : H3FourierPoint3,
        Complex.ofReal
          (inner ℝ
            ((F : H3FourierPoint3 → ℝ) x)
            ((Φ : H3FourierPoint3 → ℝ) x))
        ∂volume := by
          apply integral_congr_ae
          filter_upwards [hComplex, hTest] with x hComplexx hTestx
          rw [hComplexx, hTestx]
          simp [
            h3RealSchwartzComplexification_apply,
            smul_eq_mul,
            mul_comm
          ]
    _ =
      Complex.ofReal
        (∫ x : H3FourierPoint3,
          inner ℝ
            ((F : H3FourierPoint3 → ℝ) x)
            ((Φ : H3FourierPoint3 → ℝ) x)
          ∂volume) := by
            exact hOfRealIntegral
    _ =
      Complex.ofReal
        (inner ℝ F Φ) := by
          rw [MeasureTheory.L2.inner_def]
    _ =
      Complex.ofReal
        (inner ℝ
          (h3ToFourierRealL2 f)
          (φ.toLp 2 volume)) := by
            rfl

/-- Transport to the Euclidean carrier preserves the scalar pairing with every
transported compact weak test. -/
theorem inner_h3ToFourierRealL2_weakTestTransport
    (f : H3ScalarL2)
    (ψ : H3WeakTestFunction) :
    inner ℝ
        (h3ToFourierRealL2 f)
        ((h3WeakTestToFourierRealSchwartz ψ).toLp
          2 volume)
      =
    inner ℝ
        f
        (h3WeakTestFunctionPhysicalL2 ψ) := by
  apply Complex.ofReal_injective

  have hReal :=
    h3PhysicalScalarL2EuclideanComplex_apply_realSchwartz
      f
      (h3WeakTestToFourierRealSchwartz ψ)

  have hWeak :=
    h3PhysicalScalarL2EuclideanComplex_apply_weakTestTransport
      f ψ

  change
    ((h3PhysicalScalarL2EuclideanComplex f :
        H3FourierComplexL2) :
      𝓢'(H3FourierPoint3, ℂ))
      (h3WeakTestToFourierComplexSchwartz ψ)
      =
    Complex.ofReal
      (inner ℝ
        (h3ToFourierRealL2 f)
        ((h3WeakTestToFourierRealSchwartz ψ).toLp
          2 volume))
    at hReal

  exact hReal.symm.trans hWeak

/-! ## Real-Schwartz curl predicate -/

/-- The three curl identities after extension to every real Schwartz test,
written directly as first-derivative `L²` pairings. -/
def H3PhysicalRealFinVectorL2HilbertRealSchwartzCurlFree
    (V : H3PhysicalRealFinVectorL2Hilbert) : Prop :=
  ∀ φ : 𝓢(H3FourierPoint3, ℝ),
    inner ℝ
        (h3ToFourierRealL2 (V 0))
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 1)} φ :
          𝓢(H3FourierPoint3, ℝ)).toLp 2 volume)
      =
    inner ℝ
        (h3ToFourierRealL2 (V 1))
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 0)} φ :
          𝓢(H3FourierPoint3, ℝ)).toLp 2 volume)
    ∧
    inner ℝ
        (h3ToFourierRealL2 (V 0))
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 2)} φ :
          𝓢(H3FourierPoint3, ℝ)).toLp 2 volume)
      =
    inner ℝ
        (h3ToFourierRealL2 (V 2))
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 0)} φ :
          𝓢(H3FourierPoint3, ℝ)).toLp 2 volume)
    ∧
    inner ℝ
        (h3ToFourierRealL2 (V 1))
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 2)} φ :
          𝓢(H3FourierPoint3, ℝ)).toLp 2 volume)
      =
    inner ℝ
        (h3ToFourierRealL2 (V 2))
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 1)} φ :
          𝓢(H3FourierPoint3, ℝ)).toLp 2 volume)

/-! ## Weak curl identities in transported graph coordinates -/

theorem h3PhysicalRealFinVectorL2Hilbert_weakCurl01_fourierPairing
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hWeak : H3PhysicalRealFinVectorL2HilbertWeakCurlFree V)
    (ψ : H3WeakTestFunction) :
    inner ℝ
        (h3ToFourierRealL2 (V 0))
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 1)}
            (h3WeakTestToFourierRealSchwartz ψ) :
          𝓢(H3FourierPoint3, ℝ)).toLp 2 volume)
      =
    inner ℝ
        (h3ToFourierRealL2 (V 1))
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 0)}
            (h3WeakTestToFourierRealSchwartz ψ) :
          𝓢(H3FourierPoint3, ℝ)).toLp 2 volume) := by
  rw [
    h3WeakTestToFourierRealSchwartz_lineDeriv,
    h3WeakTestToFourierRealSchwartz_lineDeriv,
    inner_h3ToFourierRealL2_weakTestTransport,
    inner_h3ToFourierRealL2_weakTestTransport
  ]

  exact sub_eq_zero.mp ((hWeak ψ).1)

theorem h3PhysicalRealFinVectorL2Hilbert_weakCurl02_fourierPairing
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hWeak : H3PhysicalRealFinVectorL2HilbertWeakCurlFree V)
    (ψ : H3WeakTestFunction) :
    inner ℝ
        (h3ToFourierRealL2 (V 0))
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 2)}
            (h3WeakTestToFourierRealSchwartz ψ) :
          𝓢(H3FourierPoint3, ℝ)).toLp 2 volume)
      =
    inner ℝ
        (h3ToFourierRealL2 (V 2))
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 0)}
            (h3WeakTestToFourierRealSchwartz ψ) :
          𝓢(H3FourierPoint3, ℝ)).toLp 2 volume) := by
  rw [
    h3WeakTestToFourierRealSchwartz_lineDeriv,
    h3WeakTestToFourierRealSchwartz_lineDeriv,
    inner_h3ToFourierRealL2_weakTestTransport,
    inner_h3ToFourierRealL2_weakTestTransport
  ]

  exact sub_eq_zero.mp ((hWeak ψ).2.1)

theorem h3PhysicalRealFinVectorL2Hilbert_weakCurl12_fourierPairing
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hWeak : H3PhysicalRealFinVectorL2HilbertWeakCurlFree V)
    (ψ : H3WeakTestFunction) :
    inner ℝ
        (h3ToFourierRealL2 (V 1))
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 2)}
            (h3WeakTestToFourierRealSchwartz ψ) :
          𝓢(H3FourierPoint3, ℝ)).toLp 2 volume)
      =
    inner ℝ
        (h3ToFourierRealL2 (V 2))
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 1)}
            (h3WeakTestToFourierRealSchwartz ψ) :
          𝓢(H3FourierPoint3, ℝ)).toLp 2 volume) := by
  rw [
    h3WeakTestToFourierRealSchwartz_lineDeriv,
    h3WeakTestToFourierRealSchwartz_lineDeriv,
    inner_h3ToFourierRealL2_weakTestTransport,
    inner_h3ToFourierRealL2_weakTestTransport
  ]

  exact sub_eq_zero.mp ((hWeak ψ).2.2)

/-! ## Close the real-Schwartz extension -/

/-- Weak physical curl-freeness extends to every real Schwartz test by the
proved `W¹,²` graph density theorem. -/
theorem h3PhysicalRealFinVectorL2Hilbert_realSchwartzCurlFree_of_weakCurlFree
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hWeak : H3PhysicalRealFinVectorL2HilbertWeakCurlFree V) :
    H3PhysicalRealFinVectorL2HilbertRealSchwartzCurlFree V := by
  intro φ

  have h01 :=
    h3FourierReal_lineDeriv_pairing_eq_of_transportW12Dense
      H3TransportedWeakTestsDenseInRealW12Schwartz_proved
      (h3ToFourierRealL2 (V 0))
      (h3ToFourierRealL2 (V 1))
      1 0
      (h3PhysicalRealFinVectorL2Hilbert_weakCurl01_fourierPairing
        hWeak)
      φ

  have h02 :=
    h3FourierReal_lineDeriv_pairing_eq_of_transportW12Dense
      H3TransportedWeakTestsDenseInRealW12Schwartz_proved
      (h3ToFourierRealL2 (V 0))
      (h3ToFourierRealL2 (V 2))
      2 0
      (h3PhysicalRealFinVectorL2Hilbert_weakCurl02_fourierPairing
        hWeak)
      φ

  have h12 :=
    h3FourierReal_lineDeriv_pairing_eq_of_transportW12Dense
      H3TransportedWeakTestsDenseInRealW12Schwartz_proved
      (h3ToFourierRealL2 (V 1))
      (h3ToFourierRealL2 (V 2))
      2 1
      (h3PhysicalRealFinVectorL2Hilbert_weakCurl12_fourierPairing
        hWeak)
      φ

  exact ⟨h01, h02, h12⟩

end

end Euclidean
end Bridge
end PrimeTensor
