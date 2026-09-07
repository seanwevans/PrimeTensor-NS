import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.PhysicalL2Family
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.L2.Evolution

/-!
# Physical L² temporal admissibility: intermediate evolution defect orthogonality

`PhysicalL2Family` packages the genuine physical Hilbert states attached to an
arbitrary target `q ∈ [0,tau]` on the original endpoint problem:

    V_q = U(q) - U(0),
    B_q = ∫₀^q R(s) ds.

This file assembles the scalar weak FTC family into Hilbert-space orthogonality
for the intermediate defect

    D_q = V_q - B_q.

The argument is exactly the terminal-time argument already used by the
repository, but with the shortened interval `[0,q]`.

1. The physical weak projected RHS wrapper is pointwise the finite sum of
   coordinate Hilbert pairings.
2. `intervalIntegral.integral_finsetSum` commutes that finite sum through
   `[0,q]`.
3. Each scalar pairing commutes with its coordinate Bochner integral by the
   theorem from `PhysicalL2Family`.
4. The intermediate weak FTC identifies the velocity-pairing difference with
   that same RHS integral.
5. Therefore every currently admissible compact smooth solenoidal test
   annihilates `D_q`.

No spatial density or Leray-closure argument is repeated here.  The next file
will use the existing closed-span machinery to turn this orthogonality into the
actual vector identity once `D_q` is known to lie in the physical Leray-fixed
subspace.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointPhysicalL2FamilyOrthogonality
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2TemporalEndpointPhysicalL2FamilyOrthogonality :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The shortened physical weak-RHS integral is the finite sum of Hilbert
pairings against the shortened coordinatewise Bochner integrals. -/
theorem intervalIntegral_h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal_to_eq_sum_inner_bochnerTo
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
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ s in (0 : ℝ)..(q : ℝ),
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ s)
      =
    ∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralTo
          hNS ht htau hEnd hE hTail hEndpoint q i) := by
  have hPointwise :
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal
          hNS ht htau hEnd hE hTail hEndpoint φ
        =
      (fun s : ℝ =>
        ∑ i : Fin 3,
          inner ℝ
            (h3WeakTestFunctionPhysicalL2 (φ i))
            (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
              hNS ht htau hEnd hE hTail hEndpoint i s)) := by
    funext s
    exact
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal_eq_sum_inner_physicalL2Real
        hNS ht htau hEnd hE hTail hEndpoint φ s

  rw [hPointwise]

  have hEach
      (i : Fin 3) :
      IntervalIntegrable
        (fun s : ℝ =>
          inner ℝ
            (h3WeakTestFunctionPhysicalL2 (φ i))
            (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
              hNS ht htau hEnd hE hTail hEndpoint i s))
        volume
        (0 : ℝ)
        (q : ℝ) := by
    have hR :=
      h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real_intervalIntegrable_to
        hNS ht htau hEnd hE hTail hEndpoint q i

    let L : H3ScalarL2 →L[ℝ] ℝ :=
      innerSL ℝ (h3WeakTestFunctionPhysicalL2 (φ i))

    have hMapped :
        IntervalIntegrable
          (fun s : ℝ =>
            L
              (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
                hNS ht htau hEnd hE hTail hEndpoint i s))
          volume
          (0 : ℝ)
          (q : ℝ) := by
      constructor
      · exact L.integrable_comp hR.1
      · exact L.integrable_comp hR.2

    simpa only [L, innerSL_apply_apply] using hMapped

  calc
    (∫ s in (0 : ℝ)..(q : ℝ),
      ∑ i : Fin 3,
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 (φ i))
          (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
            hNS ht htau hEnd hE hTail hEndpoint i s))
        =
      ∑ i : Fin 3,
        ∫ s in (0 : ℝ)..(q : ℝ),
          inner ℝ
            (h3WeakTestFunctionPhysicalL2 (φ i))
            (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
              hNS ht htau hEnd hE hTail hEndpoint i s) := by
          exact
            intervalIntegral.integral_finsetSum
              (fun i _hi => hEach i)
    _ =
      ∑ i : Fin 3,
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 (φ i))
          (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralTo
            hNS ht htau hEnd hE hTail hEndpoint q i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact
            (inner_h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralTo_eq_intervalIntegral
              hNS ht htau hEnd hE hTail hEndpoint
              (φ i) q i).symm

/-- Pairing the embedded vector weak test with the shortened RHS Hilbert state
is exactly the finite sum of the coordinate pairings. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_bochnerProjectedRHSTo
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
    (q : Set.Icc (0 : ℝ) tau) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo
          hNS ht htau hEnd hE hTail hEndpoint q)
      =
    ∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralTo
          hNS ht htau hEnd hE hTail hEndpoint q i) := by
  unfold
    h3WeakTestVectorPhysicalL2Hilbert
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo

  rw [PiLp.inner_apply]

/-- Under the existing local temporal-domination hypothesis, every compact
smooth divergence-free weak test sees the same Hilbert pairing against the two
intermediate evolution states. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo_eq_bochnerProjectedRHSTo_of_localDomination
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
        hNS ht htau hEnd hE hTail hEndpoint φ)
    (q : Set.Icc (0 : ℝ) tau) :
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
    h3PreterminalTailCanonicalWeakVelocityPairingDifference_eq_intervalIntegral_to_of_localDomination
      hNS ht htau hEnd hE hTail hEndpoint
      φ hφ hDom q.property

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

/-- Intermediate physical evolution defect at target `q`. -/
noncomputable def h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
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
  h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
      hNS ht htau hEnd hTail q
    -
  h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo
      hNS ht htau hEnd hE hTail hEndpoint q

/-- Every admissible compact smooth divergence-free test annihilates the
intermediate physical evolution defect. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_evolutionDefectTo_eq_zero_of_localDomination
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
        hNS ht htau hEnd hE hTail hEndpoint φ)
    (q : Set.Icc (0 : ℝ) tau) :
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
      (inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo_eq_bochnerProjectedRHSTo_of_localDomination
        hNS ht htau hEnd hE hTail hEndpoint
        φ hφ hDom q)

/-- The entire existing admissible weak-test set is contained in the
zero-pairing set of the intermediate evolution defect. -/
theorem h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Set_subset_evolutionDefectTo_zeroPairing
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
    h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Set
        hNS ht htau hEnd hE hTail hEndpoint
      ⊆
    { Φ : H3PhysicalRealFinVectorL2Hilbert |
      inner ℝ Φ
        (h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
          hNS ht htau hEnd hE hTail hEndpoint q) = 0 } := by
  intro Φ hΦ

  change
    ∃ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ ∧
      H3PreterminalTailCanonicalWeakTemporalLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint φ ∧
      Φ = h3WeakTestVectorPhysicalL2Hilbert φ
    at hΦ

  rcases hΦ with ⟨φ, hφ, hDom, rfl⟩

  exact
    inner_h3WeakTestVectorPhysicalL2Hilbert_evolutionDefectTo_eq_zero_of_localDomination
      hNS ht htau hEnd hE hTail hEndpoint
      φ hφ hDom q

end

end Euclidean
end Bridge
end PrimeTensor
