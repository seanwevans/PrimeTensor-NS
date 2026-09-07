import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Velocity.Pairing.FTC.Reduction

/-!
# Physical L² temporal admissibility: intermediate-time weak pairing family

The existing weak FTC theorem is stated only at the terminal elapsed time `tau`.
The quotient-safe endpoint variation-of-constants route, however, needs an
evolution identity for every intermediate target `q ∈ [0,tau]`.

There is no need to rebuild a truncated endpoint problem.

All ingredients in `Weak.Velocity.Pairing.FTC.Reduction` already live on the
single normalized real endpoint path associated with `tau`:

* the velocity pairing is continuous on `[0,tau]`;
* the projected RHS pairing is continuous on `[0,tau]`;
* under `H3PreterminalTailCanonicalWeakTemporalLocallyDominated`, the velocity
  pairing has the projected RHS as derivative at every strict time in
  `(0,tau)`.

For any `q ∈ [0,tau]`, restrict those facts to `[0,q]` and apply the same scalar
FTC.  This produces the required weak evolution family while keeping the
endpoint object, all proof witnesses, and the ambient-real path fixed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointWeakPairingFamily
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Intermediate-time weak projected evolution on the same endpoint path.

For every `q ∈ [0,tau]`, the compact divergence-free weak velocity pairing at
`q` minus its value at zero is the interval integral of the quotient-safe weak
projected RHS pairing over `[0,q]`. -/
theorem h3PreterminalTailCanonicalWeakVelocityPairing_intervalIntegral_to_of_localDomination
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
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
    (hq : q ∈ Set.Icc (0 : ℝ) tau) :
    (∫ s in (0 : ℝ)..q,
      h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ s)
      =
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨q, hq⟩
      -
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨0, ⟨le_rfl, htau.le⟩⟩ := by
  let P : ℝ → ℝ :=
    h3PreterminalTailCanonicalWeakVelocityPairingReal
      hNS ht htau hEnd hE hTail hEndpoint φ

  let G : ℝ → ℝ :=
    h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
      hNS ht htau hEnd hE hTail hEndpoint φ

  have hPContinuousTau :
      ContinuousOn P (Set.Icc (0 : ℝ) tau) := by
    dsimp only [P]
    exact
      continuousOn_h3PreterminalTailCanonicalWeakVelocityPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ

  have hGContinuousTau :
      ContinuousOn G (Set.Icc (0 : ℝ) tau) := by
    dsimp only [G]
    exact
      continuousOn_h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ

  have hIccSub :
      Set.Icc (0 : ℝ) q ⊆ Set.Icc (0 : ℝ) tau := by
    intro r hr
    exact ⟨hr.1, hr.2.trans hq.2⟩

  have hPContinuous :
      ContinuousOn P (Set.Icc (0 : ℝ) q) :=
    hPContinuousTau.mono hIccSub

  have hGContinuous :
      ContinuousOn G (Set.Icc (0 : ℝ) q) :=
    hGContinuousTau.mono hIccSub

  have hGIntegrable :
      IntervalIntegrable
        G
        volume
        (0 : ℝ)
        q := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hq.1] using hGContinuous

  have hPDeriv :
      ∀ s : ℝ,
        s ∈ Set.Ioo (0 : ℝ) q →
        HasDerivAt P (G s) s := by
    intro s hs

    have hsTau :
        s ∈ Set.Ioo (0 : ℝ) tau :=
      ⟨hs.1, hs.2.trans_le hq.2⟩

    have h :=
      h3PreterminalTailCanonicalWeakVelocityPairingReal_hasDerivAt_weakProjectedRHS_of_localDomination
        hNS ht htau hEnd hE hTail hEndpoint
        hsTau φ hφ (hDom s hsTau)

    have hsClosed :
        s ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hsTau.1.le, hsTau.2.le⟩

    have hG :
        G s
          =
        h3PreterminalTailCanonicalWeakProjectedRHSPairingOnElapsed
          hNS ht htau hEnd hE hTail hEndpoint φ
          ⟨s, hsClosed⟩ := by
      dsimp only [G]
      exact
        h3PreterminalTailCanonicalWeakProjectedRHSPairingReal_apply_of_mem
          hNS ht htau hEnd hE hTail hEndpoint φ hsClosed

    dsimp only [P]
    rw [hG]
    exact h

  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hq.1
      hPContinuous
      hPDeriv
      hGIntegrable

  have hPq :
      P q
        =
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨q, hq⟩ := by
    dsimp only [P]
    exact
      h3PreterminalTailCanonicalWeakVelocityPairingReal_eq_onElapsed
        hNS ht htau hEnd hE hTail hEndpoint φ
        ⟨q, hq⟩

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

  exact hFTC

/-- Difference-oriented form of the same intermediate-time weak evolution
identity. -/
theorem h3PreterminalTailCanonicalWeakVelocityPairingDifference_eq_intervalIntegral_to_of_localDomination
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
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
    (hq : q ∈ Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨q, hq⟩
      -
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨0, ⟨le_rfl, htau.le⟩⟩
      =
    ∫ s in (0 : ℝ)..q,
      h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ s := by
  exact
    (h3PreterminalTailCanonicalWeakVelocityPairing_intervalIntegral_to_of_localDomination
      hNS ht htau hEnd hE hTail hEndpoint
      φ hφ hDom hq).symm

end

end Euclidean
end Bridge
end PrimeTensor
