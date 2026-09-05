import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Reduction

/-!
# Classicalization: reduce weak-curl uniqueness to a Fourier bridge and spectral algebra

The preceding checkpoint reduced parameter-free physical Leray density to

    Leray-fixed + weakly curl-free  ==>  zero

for a three-component physical `L²` state.

This file separates that remaining statement into its two genuinely distinct
parts.

1. **Weak-to-Fourier bridge.**
   The three distributional curl identities against compact smooth scalar test
   functions imply the corresponding almost-everywhere Fourier multiplier
   identities.

2. **Pointwise spectral algebra.**
   A three-component spectral `L²` state that is both Fourier divergence-free
   and Fourier curl-free must vanish.

The return from Fourier space to physical `L²` is not an additional frontier:
it is already forced by the exact scalar Plancherel norm identity.  We prove
that injectivity here.

Thus after this file the remaining mathematics is isolated precisely as:

    weak curl  -->  Fourier curl
    divergence + Fourier curl  -->  zero.

No endpoint or temporal parameters occur in either obligation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlFourierReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2AdmissibleClosureLerayDensityDualCurlFourierReduction :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Fourier curl-free predicate -/

/-- Almost-everywhere Fourier curl-free relation for a three-component
spectral state.

The three equations are the multiplier forms of

    ∂₁ V₀ - ∂₀ V₁ = 0,
    ∂₂ V₀ - ∂₀ V₂ = 0,
    ∂₂ V₁ - ∂₁ V₂ = 0.

Using the project's derivative symbol keeps the convention exactly aligned with
the already-established Fourier divergence predicate. -/
def H3SpectralFinCurlFree
    (G : H3SpectralFinVectorState) : Prop :=
  ∀ᵐ ξ ∂volume,
    h3FourierDerivativeSymbol 1 ξ *
        (G 0 : H3FourierPoint3 → ℂ) ξ
      -
      h3FourierDerivativeSymbol 0 ξ *
        (G 1 : H3FourierPoint3 → ℂ) ξ
      =
    0
    ∧
    h3FourierDerivativeSymbol 2 ξ *
        (G 0 : H3FourierPoint3 → ℂ) ξ
      -
      h3FourierDerivativeSymbol 0 ξ *
        (G 2 : H3FourierPoint3 → ℂ) ξ
      =
    0
    ∧
    h3FourierDerivativeSymbol 2 ξ *
        (G 1 : H3FourierPoint3 → ℂ) ξ
      -
      h3FourierDerivativeSymbol 1 ξ *
        (G 2 : H3FourierPoint3 → ℂ) ξ
      =
    0

/-- Fourier curl-free predicate specialized to the canonical raw Fourier vector
of a physical `L²` Hilbert state. -/
def H3PhysicalRealFinVectorL2HilbertFourierCurlFree
    (V : H3PhysicalRealFinVectorL2Hilbert) : Prop :=
  H3SpectralFinCurlFree
    (h3PhysicalRealFinVectorL2HilbertRawFourier V)

/-! ## Exact remaining bridge and algebra frontiers -/

/-- Distributional weak curl-freeness implies the almost-everywhere Fourier
curl multiplier identities. -/
def H3PhysicalL2WeakCurlFreeImpliesFourierCurlFree : Prop :=
  ∀ V : H3PhysicalRealFinVectorL2Hilbert,
    H3PhysicalRealFinVectorL2HilbertWeakCurlFree V →
    H3PhysicalRealFinVectorL2HilbertFourierCurlFree V

/-- Pure Fourier algebra frontier: a spectral state that is simultaneously
divergence-free and curl-free vanishes. -/
def H3SpectralFinDivergenceFreeCurlFreeTrivial : Prop :=
  ∀ G : H3SpectralFinVectorState,
    H3SpectralFinDivergenceFree G →
    H3SpectralFinCurlFree G →
    G = 0

/-! ## Plancherel already makes the raw Fourier transform injective -/

/-- A physical scalar `L²` class with zero canonical Fourier transform is
itself zero.  This is immediate from the exact Plancherel norm identity. -/
theorem h3ScalarL2_eq_zero_of_fourier_eq_zero
    (f : H3ScalarL2)
    (hf :
      h3ScalarFourierL2 f = 0) :
    f = 0 := by
  have hNorm :
      ‖f‖ = 0 := by
    rw [
      ← norm_h3ScalarFourierL2 f,
      hf,
      norm_zero
    ]

  exact
    norm_eq_zero.mp hNorm

/-- The canonical raw Fourier vector is injective on the finite physical
`L²` Hilbert product. -/
theorem h3PhysicalRealFinVectorL2Hilbert_eq_zero_of_rawFourier_eq_zero
    (V : H3PhysicalRealFinVectorL2Hilbert)
    (hV :
      h3PhysicalRealFinVectorL2HilbertRawFourier V
        =
      0) :
    V = 0 := by
  apply PiLp.ext

  intro i

  change V i = 0

  apply h3ScalarL2_eq_zero_of_fourier_eq_zero

  have hi :=
    congrFun hV i

  simpa only [
    h3PhysicalRealFinVectorL2HilbertRawFourier,
    Pi.zero_apply
  ] using hi

/-! ## The two Fourier obligations imply weak-curl uniqueness -/

/-- Once the weak-to-Fourier bridge and the pure spectral
divergence-plus-curl uniqueness theorem are available, the physical
Leray-fixed weak-curl uniqueness frontier is closed.

Leray-fixedness supplies Fourier divergence-freeness through the existing
finite Leray theorem; the bridge supplies Fourier curl-freeness; spectral
uniqueness gives zero raw Fourier state; Plancherel injectivity returns to
physical `L²`. -/
theorem H3PhysicalL2LerayFixedWeakCurlFreeTrivial_of_fourierBridge_of_spectralTrivial
    (hBridge :
      H3PhysicalL2WeakCurlFreeImpliesFourierCurlFree)
    (hSpectral :
      H3SpectralFinDivergenceFreeCurlFreeTrivial) :
    H3PhysicalL2LerayFixedWeakCurlFreeTrivial := by
  intro V hLeray hWeakCurl

  have hFixed :
      H3PhysicalRealFinVectorL2HilbertLerayFixed V :=
    (mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff V).1
      hLeray

  have hDiv :
      H3SpectralFinDivergenceFree
        (h3PhysicalRealFinVectorL2HilbertRawFourier V) := by
    exact
      h3SpectralFinDivergenceFree_of_lerayFixed
        hFixed

  have hCurl :
      H3SpectralFinCurlFree
        (h3PhysicalRealFinVectorL2HilbertRawFourier V) := by
    exact
      hBridge V hWeakCurl

  have hFourierZero :
      h3PhysicalRealFinVectorL2HilbertRawFourier V
        =
      0 :=
    hSpectral
      (h3PhysicalRealFinVectorL2HilbertRawFourier V)
      hDiv
      hCurl

  exact
    h3PhysicalRealFinVectorL2Hilbert_eq_zero_of_rawFourier_eq_zero
      V
      hFourierZero

/-- Therefore the two isolated Fourier obligations are sufficient for the
original parameter-free physical Leray density theorem. -/
theorem H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_of_fourierBridge_of_spectralTrivial
    (hBridge :
      H3PhysicalL2WeakCurlFreeImpliesFourierCurlFree)
    (hSpectral :
      H3SpectralFinDivergenceFreeCurlFreeTrivial) :
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan := by
  exact
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_of_weakCurlFreeTrivial
      (H3PhysicalL2LerayFixedWeakCurlFreeTrivial_of_fourierBridge_of_spectralTrivial
        hBridge
        hSpectral)

end

end Euclidean
end Bridge
end PrimeTensor
