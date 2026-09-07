import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Orthogonality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Weak.Fubini

/-!
# Physical L² temporal endpoint family: product-integrable orthogonality

`Weak.Fubini` replaces the earlier pointwise spatial-majorant route by the
minimal coordinatewise product-space integrability needed to interchange the
time and space integrals.

The Hilbert-space algebra in `Family.Orthogonality` is independent of how the
weak evolution identity was proved.  This file therefore packages the parallel
orthogonality statements obtained from product integrability:

* a divergence-free weak test satisfying product integrability at `q` pairs
  equally with the velocity increment and the projected-RHS Bochner integral;
* consequently the same test annihilates the physical evolution defect.

No density or closed-span conclusion is made here.  That next step will quantify
the product-integrability hypothesis over the divergence-free test family and
close the defect directly in the Leray-fixed subspace.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointProductOrthogonality
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Under coordinatewise spacetime product integrability at `q`, a compact
smooth divergence-free weak test sees the same Hilbert pairing against the
velocity increment and the projected-RHS Bochner integral. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo_eq_bochnerProjectedRHSTo_of_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) tau)
    (hProd :
      H3PreterminalTailCanonicalWeakTemporalProductIntegrableTo
        hNS ht htau hEnd hE hTail hEndpoint
        (q := (q : ℝ)) φ) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q)
      =
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo
          hNS ht htau hEnd hE hTail hEndpoint q) := by
  have hWeak :=
    h3PreterminalTailCanonicalWeakVelocityPairingDifference_eq_intervalIntegral_to_of_productIntegrable
      hNS ht htau hEnd hE hTail hEndpoint
      φ hφ q.property hProd

  have hRhsEq :
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal
          hNS ht htau hEnd hE hTail hEndpoint φ
        =
      h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ :=
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal_eq_weakProjectedRHSPairingReal
      hNS ht htau hEnd hE hTail hEndpoint φ

  rw [← hRhsEq] at hWeak

  calc
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q)
        =
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail φ q
        -
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail φ
          ⟨0, ⟨le_rfl, htau.le⟩⟩ :=
      inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo
        hNS ht htau hEnd hTail φ q
    _ =
      ∫ s in (0 : ℝ)..(q : ℝ),
        h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal
          hNS ht htau hEnd hE hTail hEndpoint φ s :=
      hWeak
    _ =
      ∑ i : Fin 3,
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 (φ i))
          (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralTo
            hNS ht htau hEnd hE hTail hEndpoint q i) :=
      intervalIntegral_h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal_to_eq_sum_inner_bochnerTo
        hNS ht htau hEnd hE hTail hEndpoint φ q
    _ =
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo
          hNS ht htau hEnd hE hTail hEndpoint q) :=
      (inner_h3WeakTestVectorPhysicalL2Hilbert_bochnerProjectedRHSTo
        hNS ht htau hEnd hE hTail hEndpoint φ q).symm

/-- A divergence-free weak test satisfying product integrability at `q`
annihilates the intermediate physical evolution defect. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_evolutionDefectTo_eq_zero_of_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) tau)
    (hProd :
      H3PreterminalTailCanonicalWeakTemporalProductIntegrableTo
        hNS ht htau hEnd hE hTail hEndpoint
        (q := (q : ℝ)) φ) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
          hNS ht htau hEnd hE hTail hEndpoint q)
      =
    0 := by
  unfold h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
  rw [inner_sub_right]

  exact
    sub_eq_zero.mpr
      (inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo_eq_bochnerProjectedRHSTo_of_productIntegrable
        hNS ht htau hEnd hE hTail hEndpoint
        φ hφ q hProd)

end

end Euclidean
end Bridge
end PrimeTensor
