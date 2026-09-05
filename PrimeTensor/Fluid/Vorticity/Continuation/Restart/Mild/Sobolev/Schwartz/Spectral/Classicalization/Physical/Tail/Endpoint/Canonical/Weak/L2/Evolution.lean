import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.L2.RHS.Pairing

/-!
# Classicalization: weak physical `L²` integral evolution

The previous two checkpoints have isolated the time-calculus issue and removed
all representative-level ambiguity from the projected RHS.

* `PhysicalTailEndpointCanonicalWeakVelocityPairingFTCReduction` proves scalar
  FTC under the explicit local temporal-domination frontier.
* `PhysicalTailEndpointCanonicalWeakL2RHSPairing` identifies the continuous
  weak projected RHS pairing, on every closed elapsed slice, with the Hilbert
  pairing against the quotient-safe physical `L²` RHS.

This file combines them.

We extend the closed-interval physical `L²` RHS pairing by zero outside
`[0,τ]`.  Pointwise, this extension is exactly the ambient-real weak projected
RHS wrapper used by the FTC theorem.  Therefore the scalar FTC identity becomes

    ∫₀^τ Σᵢ ⟪φᵢ, Rᵢ(s)⟫ ds
      =
    Σᵢ ⟪φᵢ, Uᵢ(τ)⟫
      -
    Σᵢ ⟪φᵢ, Uᵢ(0)⟫

for every divergence-free compact test vector `φ`, assuming only the already
isolated local temporal-domination frontier.

The statement is now entirely quotient-safe and Hilbert-space valued at each
time slice.  No pointwise temporal derivative, pressure transform, or
fixed-frequency evaluation occurs in the conclusion.

This is the correct input for the next functional-analytic step: density of
compactly supported smooth solenoidal tests in the relevant solenoidal `L²`
subspace, followed by recovery of an actual `L²` integral identity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalWeakL2Evolution
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalWeakL2Evolution :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Ambient-real extension of the quotient-safe physical `L²` RHS weak pairing.

On the genuine elapsed interval it is the Hilbert pairing from
`PhysicalTailEndpointCanonicalWeakL2RHSPairing`; off the interval it is zero.
This mirrors exactly the ambient-real weak-RHS extension used by the FTC
reduction. -/
noncomputable def h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal
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
    (s : ℝ) :
    ℝ :=
  if hs : s ∈ Set.Icc (0 : ℝ) tau then
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint φ ⟨s, hs⟩
  else
    0

/-- On the physical interval, the ambient-real physical `L²` RHS pairing is the
closed-interval Hilbert pairing. -/
theorem h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal_apply_of_mem
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
    {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ s
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint φ ⟨s, hs⟩ := by
  simp only [
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal,
    dif_pos hs
  ]

/-- The ambient-real quotient-safe physical `L²` RHS pairing is pointwise
identical to the ambient-real continuous weak projected RHS pairing.

The equality is valid both on and off `[0,τ]`; on the interval it is the closed
representation theorem from the preceding file, while off the interval both
wrappers are zero. -/
theorem h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal_eq_weakProjectedRHSPairingReal
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
    (φ : H3WeakTestVector) :
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ
      =
    h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
      hNS ht htau hEnd hE hTail hEndpoint φ := by
  funext s

  by_cases hs : s ∈ Set.Icc (0 : ℝ) tau

  · rw [
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal_apply_of_mem
        hNS ht htau hEnd hE hTail hEndpoint φ hs
    ]

    rw [
      h3PreterminalTailCanonicalWeakProjectedRHSPairingReal_apply_of_mem
        hNS ht htau hEnd hE hTail hEndpoint φ hs
    ]

    exact
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingOnElapsed_eq_weakProjectedRHSPairingOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ ⟨s, hs⟩

  · simp only [
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal,
      h3PreterminalTailCanonicalWeakProjectedRHSPairingReal,
      dif_neg hs
    ]

/-- Under the explicit local temporal-domination frontier, the endpoint path
satisfies the complete weak physical `L²` integral evolution identity against
every divergence-free compact test vector.

Every quantity in the conclusion is a Hilbert-space pairing of genuine
`L²(Point3)` classes. -/
theorem h3PreterminalTailCanonicalWeakPhysicalL2Evolution_intervalIntegral_of_localDomination
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
    (hDom :
      H3PreterminalTailCanonicalWeakTemporalLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint φ) :
    (∫ s in (0 : ℝ)..tau,
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ s)
      =
    (∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 i)
          ⟨tau, ⟨htau.le, le_rfl⟩⟩))
      -
    (∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 i)
          ⟨0, ⟨le_rfl, htau.le⟩⟩)) := by
  have hFTC :=
    h3PreterminalTailCanonicalWeakVelocityPairing_intervalIntegral_of_localDomination
      hNS ht htau hEnd hE hTail hEndpoint
      φ hφ hDom

  have hRhsEq :
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal
          hNS ht htau hEnd hE hTail hEndpoint φ
        =
      h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ :=
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal_eq_weakProjectedRHSPairingReal
      hNS ht htau hEnd hE hTail hEndpoint φ

  rw [← hRhsEq] at hFTC

  unfold h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed at hFTC

  exact hFTC

/-- Equivalent difference form: the terminal-minus-initial physical velocity
`L²` pairing equals the time integral of the physical projected RHS pairing.

This orientation is convenient for the forthcoming density argument. -/
theorem h3PreterminalTailCanonicalWeakPhysicalL2VelocityDifference_eq_intervalIntegral_projectedRHS_of_localDomination
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
    (hDom :
      H3PreterminalTailCanonicalWeakTemporalLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint φ) :
    (∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 i)
          ⟨tau, ⟨htau.le, le_rfl⟩⟩))
      -
    (∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 i)
          ⟨0, ⟨le_rfl, htau.le⟩⟩))
      =
    ∫ s in (0 : ℝ)..tau,
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ s := by
  exact
    (h3PreterminalTailCanonicalWeakPhysicalL2Evolution_intervalIntegral_of_localDomination
      hNS ht htau hEnd hE hTail hEndpoint
      φ hφ hDom).symm

end

end Euclidean
end Bridge
end PrimeTensor
