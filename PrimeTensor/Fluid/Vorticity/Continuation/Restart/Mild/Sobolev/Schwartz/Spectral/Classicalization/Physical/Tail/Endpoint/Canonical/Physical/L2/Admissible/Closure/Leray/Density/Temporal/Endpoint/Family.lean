import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Weak.Pairing.Family
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Defect.Orthogonality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Velocity.Increment.Leray.Fixed

/-!
# Physical L² temporal admissibility: intermediate physical Hilbert states

`WeakPairingFamily` upgraded the scalar weak FTC from the single terminal time
`tau` to every target `q ∈ [0,tau]`, while keeping the same endpoint path.

This file now packages the two genuine physical Hilbert-space states that occur
at such an intermediate target.

* `velocityIncrementPhysicalL2HilbertTo q` is the physical velocity state at
  `q` minus the physical velocity state at zero.
* `projectedRHSPhysicalL2BochnerIntegralHilbertTo q` is the coordinatewise
  Bochner interval integral of the already-constructed strongly continuous
  physical projected RHS over `[0,q]`.

No truncated endpoint problem is introduced.  Both objects use the original
`tau` endpoint data and merely shorten the integration/evaluation interval.

We also record the pairing identities needed by the next closure step:

* pairing an embedded weak test with the velocity increment is exactly the
  difference of the existing weak velocity pairings at `q` and zero;
* pairing one scalar weak test with one intermediate RHS coordinate integral is
  exactly the interval integral of its pointwise physical `L²` pairing.

The next increment can therefore focus only on assembling the finite coordinate
sum and reusing the already-proved solenoidal closed-span nondegeneracy.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointPhysicalL2Family
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2TemporalEndpointPhysicalL2Family :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Physical velocity increment from elapsed zero to one arbitrary target
`q ∈ [0,tau]`, bundled in the finite physical `L²` Hilbert product. -/
noncomputable def h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3PhysicalRealFinVectorL2Hilbert :=
  h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail q
    -
  h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail
      ⟨0, ⟨le_rfl, htau.le⟩⟩

/-- Coordinate form of the intermediate physical velocity increment. -/
@[simp]
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_apply
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail q i
      =
    h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail (h3JetSlot0 i) q
      -
    h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail (h3JetSlot0 i)
        ⟨0, ⟨le_rfl, htau.le⟩⟩ := by
  rfl

/-- One intermediate coordinatewise Bochner integral of the physical projected
RHS, over `[0,q]` inside the original endpoint interval `[0,tau]`. -/
noncomputable def h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralTo
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
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    H3ScalarL2 :=
  ∫ s in (0 : ℝ)..(q : ℝ),
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
      hNS ht htau hEnd hE hTail hEndpoint i s

/-- The three intermediate projected-RHS coordinate integrals, bundled in the
finite physical `L²` Hilbert product. -/
noncomputable def h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo
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
    (q : Set.Icc (0 : ℝ) tau) :
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2
    (fun i : Fin 3 =>
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralTo
        hNS ht htau hEnd hE hTail hEndpoint q i)

/-- Coordinate projection of the intermediate projected-RHS Hilbert state. -/
@[simp]
theorem h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo_apply
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
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo
        hNS ht htau hEnd hE hTail hEndpoint q i
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralTo
      hNS ht htau hEnd hE hTail hEndpoint q i := by
  rfl

/-- The physical projected RHS remains Bochner interval-integrable on every
shortened interval `[0,q]`. -/
theorem h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real_intervalIntegrable_to
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
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    IntervalIntegrable
      (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
        hNS ht htau hEnd hE hTail hEndpoint i)
      volume
      (0 : ℝ)
      (q : ℝ) := by
  have hContinuousTau :=
    continuousOn_h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
      hNS ht htau hEnd hE hTail hEndpoint i

  have hSub :
      Set.Icc (0 : ℝ) (q : ℝ)
        ⊆
      Set.Icc (0 : ℝ) tau := by
    intro s hs
    exact ⟨hs.1, hs.2.trans q.property.2⟩

  have hContinuousQ :=
    hContinuousTau.mono hSub

  exact
    hContinuousQ.intervalIntegrable_of_Icc
      q.property.1

/-- Pairing an embedded weak test with one physical velocity slice is exactly
the existing weak velocity pairing at that elapsed time. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_velocityOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)
      =
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
      hNS ht hEnd hTail φ q := by
  unfold
    h3WeakTestVectorPhysicalL2Hilbert
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed

  rw [PiLp.inner_apply]

/-- Consequently, pairing with the intermediate physical velocity increment is
the difference of the weak velocity pairings at `q` and zero. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
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
        ⟨0, ⟨le_rfl, htau.le⟩⟩ := by
  unfold h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo

  rw [inner_sub_right]

  rw [
    inner_h3WeakTestVectorPhysicalL2Hilbert_velocityOnElapsed
      hNS ht hEnd hTail φ q,
    inner_h3WeakTestVectorPhysicalL2Hilbert_velocityOnElapsed
      hNS ht hEnd hTail φ
      ⟨0, ⟨le_rfl, htau.le⟩⟩
  ]

/-- Pairing one scalar weak test with one intermediate physical RHS coordinate
integral commutes with the shortened Bochner interval integral. -/
theorem inner_h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralTo_eq_intervalIntegral
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
    (φ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    inner ℝ
        (h3WeakTestFunctionPhysicalL2 φ)
        (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralTo
          hNS ht htau hEnd hE hTail hEndpoint q i)
      =
    ∫ s in (0 : ℝ)..(q : ℝ),
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 φ)
        (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
          hNS ht htau hEnd hE hTail hEndpoint i s) := by
  have hR :=
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real_intervalIntegrable_to
      hNS ht htau hEnd hE hTail hEndpoint q i

  let L : H3ScalarL2 →L[ℝ] ℝ :=
    innerSL ℝ (h3WeakTestFunctionPhysicalL2 φ)

  have hComm :
      (∫ s in (0 : ℝ)..(q : ℝ),
        L
          (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
            hNS ht htau hEnd hE hTail hEndpoint i s))
        =
      L
        (∫ s in (0 : ℝ)..(q : ℝ),
          h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
            hNS ht htau hEnd hE hTail hEndpoint i s) :=
    L.intervalIntegral_comp_comm hR

  simpa only [
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralTo,
    L,
    innerSL_apply_apply
  ] using hComm.symm

end

end Euclidean
end Bridge
end PrimeTensor
