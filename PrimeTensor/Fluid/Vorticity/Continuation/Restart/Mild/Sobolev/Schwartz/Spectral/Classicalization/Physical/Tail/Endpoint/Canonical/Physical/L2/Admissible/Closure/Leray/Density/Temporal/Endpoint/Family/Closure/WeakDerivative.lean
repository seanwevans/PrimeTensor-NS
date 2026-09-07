import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Velocity.Pairing.FTC.Reduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Orthogonality

/-!
# Physical L² endpoint closure from scalar weak-pairing derivatives

The product-integrability route is sufficient but stronger than the actual weak
evolution argument needs.  It asks for coordinatewise absolute spacetime
integrability before applying Fubini.

For divergence-free testing, the Hilbert/density closure only needs the scalar
velocity pairing

    Pφ(s) = <φ, W(s)>

to have derivative equal to the already-continuous scalar projected RHS pairing

    Gφ(s).

This file isolates exactly that weaker frontier.

For every compact smooth divergence-free weak test, assume only

    Pφ'(s) = Gφ(s),    0 < s < tau.

The existing continuity theorems for `Pφ` and `Gφ` then give scalar FTC on every
shortened interval `[0,q]`.  The established Hilbert pairing identities convert
that scalar equality into orthogonality of the physical evolution defect, and
the existing Leray density theorem forces the defect to vanish.

No coordinatewise spacetime Fubini hypothesis is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointWeakDerivativeClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact scalar weak-time frontier on one endpoint problem: every divergence-
free compact smooth test sees the continuous velocity pairing differentiated by
the continuous projected RHS pairing throughout the strict elapsed interior. -/
def H3PreterminalTailCanonicalAllDivergenceFreeWeakVelocityPairingsHaveProjectedRHSDerivativeOnElapsed
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
        hNS ht hEnd hTail) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    ∀ s : ℝ,
      s ∈ Set.Ioo (0 : ℝ) tau →
      HasDerivAt
        (h3PreterminalTailCanonicalWeakVelocityPairingReal
          hNS ht htau hEnd hE hTail hEndpoint φ)
        (h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
          hNS ht htau hEnd hE hTail hEndpoint φ s)
        s

/-- Scalar FTC on every shortened interval follows directly from the weak
pairing derivative frontier. -/
theorem h3PreterminalTailCanonicalWeakVelocityPairingDifference_eq_intervalIntegral_to_of_all_weakPairingDerivatives
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
    (hAll :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakVelocityPairingsHaveProjectedRHSDerivativeOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ q
      -
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨0, ⟨le_rfl, htau.le⟩⟩
      =
    ∫ s in (0 : ℝ)..(q : ℝ),
      h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ s := by
  let P : ℝ → ℝ :=
    h3PreterminalTailCanonicalWeakVelocityPairingReal
      hNS ht htau hEnd hE hTail hEndpoint φ

  let G : ℝ → ℝ :=
    h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
      hNS ht htau hEnd hE hTail hEndpoint φ

  have hSub :
      Set.Icc (0 : ℝ) (q : ℝ) ⊆ Set.Icc (0 : ℝ) tau := by
    intro s hs
    exact ⟨hs.1, hs.2.trans q.property.2⟩

  have hPContinuous :
      ContinuousOn P (Set.Icc (0 : ℝ) (q : ℝ)) := by
    dsimp only [P]
    exact
      (continuousOn_h3PreterminalTailCanonicalWeakVelocityPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ).mono hSub

  have hGContinuous :
      ContinuousOn G (Set.Icc (0 : ℝ) (q : ℝ)) := by
    dsimp only [G]
    exact
      (continuousOn_h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ).mono hSub

  have hGIntegrable :
      IntervalIntegrable
        G
        volume
        (0 : ℝ)
        (q : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le q.property.1] using hGContinuous

  have hPDeriv :
      ∀ s : ℝ,
        s ∈ Set.Ioo (0 : ℝ) (q : ℝ) →
        HasDerivAt P (G s) s := by
    intro s hs

    have hsTau :
        s ∈ Set.Ioo (0 : ℝ) tau :=
      ⟨hs.1, hs.2.trans_le q.property.2⟩

    dsimp only [P, G]
    exact hAll φ hφ s hsTau

  have hFTC :
      (∫ s in (0 : ℝ)..(q : ℝ), G s)
        =
      P (q : ℝ) - P 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      q.property.1
      hPContinuous
      hPDeriv
      hGIntegrable

  have hPq :
      P (q : ℝ)
        =
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ q := by
    dsimp only [P]
    exact
      h3PreterminalTailCanonicalWeakVelocityPairingReal_eq_onElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ q

  have hPzero :
      P 0
        =
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨0, ⟨le_rfl, htau.le⟩⟩ := by
    dsimp only [P]
    exact
      h3PreterminalTailCanonicalWeakVelocityPairingReal_eq_onElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ
        ⟨0, ⟨le_rfl, htau.le⟩⟩

  dsimp only [G] at hFTC
  rw [hPq, hPzero] at hFTC

  exact hFTC.symm

/-- Under the scalar weak-pairing derivative frontier, a divergence-free weak
test pairs equally with the physical velocity increment and the projected-RHS
Bochner integral at every shortened target. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo_eq_bochnerProjectedRHSTo_of_all_weakPairingDerivatives
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
    (hAll :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakVelocityPairingsHaveProjectedRHSDerivativeOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
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
    h3PreterminalTailCanonicalWeakVelocityPairingDifference_eq_intervalIntegral_to_of_all_weakPairingDerivatives
      hNS ht htau hEnd hE hTail hEndpoint
      hAll φ hφ q

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

/-- Every divergence-free weak test annihilates the intermediate physical
evolution defect under the scalar weak-pairing derivative frontier. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_evolutionDefectTo_eq_zero_of_all_weakPairingDerivatives
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
    (hAll :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakVelocityPairingsHaveProjectedRHSDerivativeOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
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
      (inner_h3WeakTestVectorPhysicalL2Hilbert_velocityIncrementTo_eq_bochnerProjectedRHSTo_of_all_weakPairingDerivatives
        hNS ht htau hEnd hE hTail hEndpoint
        hAll φ hφ q)

/-- The physical evolution defect is orthogonal to the full algebraic span of
divergence-free weak tests under the scalar weak-pairing derivative frontier. -/
theorem h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_mem_divergenceFreeWeakTestSpan_orthogonal_of_all_weakPairingDerivatives
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
    (hAll :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakVelocityPairingsHaveProjectedRHSDerivativeOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
        hNS ht htau hEnd hE hTail hEndpoint q
      ∈
    h3DivergenceFreeWeakTestPhysicalL2Spanᗮ := by
  let D : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
      hNS ht htau hEnd hE hTail hEndpoint q

  let S : Set H3PhysicalRealFinVectorL2Hilbert :=
    h3DivergenceFreeWeakTestPhysicalL2Set

  let K : Submodule ℝ H3PhysicalRealFinVectorL2Hilbert :=
    Submodule.span ℝ S

  let L : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] ℝ :=
    innerSL ℝ D

  have hGeneratorKer : S ⊆ L.ker := by
    intro Φ hΦ
    rcases hΦ with ⟨φ, hDiv, rfl⟩

    have hPair :
        inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert φ)
            D
          =
        0 := by
      dsimp only [D]
      exact
        inner_h3WeakTestVectorPhysicalL2Hilbert_evolutionDefectTo_eq_zero_of_all_weakPairingDerivatives
          hNS ht htau hEnd hE hTail hEndpoint
          hAll φ hDiv q

    change L (h3WeakTestVectorPhysicalL2Hilbert φ) = 0
    dsimp only [L]

    simpa only [innerSL_apply_apply, real_inner_comm] using hPair

  have hSpanKer : K ≤ L.ker := by
    dsimp only [K]
    exact Submodule.span_le.mpr hGeneratorKer

  change D ∈ Kᗮ
  rw [Submodule.mem_orthogonal']

  intro Φ hΦ

  have hKer : Φ ∈ L.ker :=
    hSpanKer hΦ

  change L Φ = 0 at hKer
  dsimp only [L] at hKer

  simpa only [innerSL_apply_apply] using hKer

/-- Leray density closes the intermediate defect under the scalar weak-pairing
derivative frontier. -/
theorem h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_eq_zero_of_all_weakPairingDerivatives
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
    (hAll :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakVelocityPairingsHaveProjectedRHSDerivativeOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
        hNS ht htau hEnd hE hTail hEndpoint q
      =
    0 := by
  let D : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
      hNS ht htau hEnd hE hTail hEndpoint q

  let K : Submodule ℝ H3PhysicalRealFinVectorL2Hilbert :=
    h3DivergenceFreeWeakTestPhysicalL2Span

  have hOrth : D ∈ Kᗮ := by
    dsimp only [D, K]
    exact
      h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_mem_divergenceFreeWeakTestSpan_orthogonal_of_all_weakPairingDerivatives
        hNS ht htau hEnd hE hTail hEndpoint hAll q

  have hFixed :
      D ∈ h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
    dsimp only [D]
    exact
      h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_mem_lerayFixedSubmodule
        hNS ht htau hEnd hE hTail hEndpoint q

  have hMemClosed :
      D ∈ h3DivergenceFreeWeakTestPhysicalL2ClosedSpan := by
    rw [h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule]
    exact hFixed

  have hClosedEq :
      h3DivergenceFreeWeakTestPhysicalL2ClosedSpan
        =
      Kᗮᗮ := by
    dsimp only [K]
    unfold h3DivergenceFreeWeakTestPhysicalL2ClosedSpan
    symm
    exact
      Submodule.orthogonal_orthogonal_eq_closure
        h3DivergenceFreeWeakTestPhysicalL2Span

  have hDouble : D ∈ Kᗮᗮ := by
    rw [← hClosedEq]
    exact hMemClosed

  have hBoth : D ∈ Kᗮ ⊓ Kᗮᗮ :=
    ⟨hOrth, hDouble⟩

  have hBot :
      D ∈ (⊥ : Submodule ℝ H3PhysicalRealFinVectorL2Hilbert) := by
    rw [← Submodule.inf_orthogonal_eq_bot Kᗮ]
    exact hBoth

  simpa using hBot

/-- Genuine physical `L²` vector evolution on every target follows from the
scalar weak-pairing derivative frontier. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_eq_BochnerProjectedRHSTo_of_all_weakPairingDerivatives
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
    (hAll :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakVelocityPairingsHaveProjectedRHSDerivativeOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail q
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo
      hNS ht htau hEnd hE hTail hEndpoint q := by
  have hZero :=
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_eq_zero_of_all_weakPairingDerivatives
      hNS ht htau hEnd hE hTail hEndpoint hAll q

  unfold h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo at hZero

  exact sub_eq_zero.mp hZero

end

end Euclidean
end Bridge
end PrimeTensor
