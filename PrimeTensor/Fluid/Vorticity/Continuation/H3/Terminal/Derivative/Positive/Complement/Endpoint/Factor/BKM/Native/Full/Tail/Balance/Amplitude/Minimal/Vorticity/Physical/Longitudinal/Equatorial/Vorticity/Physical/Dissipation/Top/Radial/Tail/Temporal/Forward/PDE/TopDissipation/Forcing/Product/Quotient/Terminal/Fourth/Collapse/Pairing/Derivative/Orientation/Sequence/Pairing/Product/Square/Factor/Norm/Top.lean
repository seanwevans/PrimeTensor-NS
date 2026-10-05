import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Tail.Cascade

/-!
# Eliminate the top-dissipation Hilbert derivative branch

The normalized Hilbert derivative branch is genuinely new for three of the
resolved channels, but not for top dissipation.

Indeed, the top-dissipation derivative-square envelope is exactly

    ∑ k : Fin 3, ‖d/dt (q² û_k)‖²,

and each summand is the canonical fourth-temporal channel amplitude for that
coordinate.  Therefore divergence of the aggregated top derivative square
forces one fixed fourth-temporal coordinate to diverge on a cofinal
subsequence.

This file packages that finite-coordinate reduction.  It introduces no new PDE
estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000

/--
The top-dissipation Hilbert derivative-square envelope is exactly the sum of
the three fourth-temporal channel amplitudes.
-/
theorem h3TerminalTopDissipationHilbertDerivativeSquareEnvelope_eq_sum_fourthTemporalAmplitude
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3) :
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.topDissipation
        t
      =
    ∑ k : Fin 3,
      h3TerminalResolvedPhysicalPDEChannelAmplitude
        hH3 hClass k
        H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
        t := by

  rfl

/--
A real sequence is either eventually bounded above or admits a cofinal
extraction tending to `+∞`.

This is the one-factor specialization of the existing relative-tail
alternative.
-/
private theorem eventuallyBounded_or_cofinalTendstoAtTop
    (f : ℕ → ℝ) :
    (
      ∃ C : ℝ,
        ∀ᶠ n : ℕ in atTop,
          f n ≤ C
    )
      ∨
    (
      ∃ k : ℕ → ℕ,
        (∀ n : ℕ, n ≤ k n)
          ∧
        Tendsto k atTop atTop
          ∧
        Tendsto
          (fun n : ℕ => f (k n))
          atTop
          atTop
    ) := by

  have hIdentity :
      ∀ᶠ n : ℕ in atTop,
        (1 + f n : ℝ) = 1 + f n :=
    Eventually.of_forall
      (fun _ => rfl)

  have hTail :=
    relativeTailAlternative_of_eventually_ratio_identity
      f
      (fun n => 1 + f n)
      hIdentity

  unfold H3TerminalRelativeTailAlternative at hTail

  rcases hTail with
    ⟨C, hBound⟩
    |
    ⟨k, hk, hkTop, hfTop, hRatioTop⟩

  · exact
      Or.inl
        ⟨
          C,
          hBound.mono
            (fun n hn => hn.1)
        ⟩

  · exact
      Or.inr
        ⟨
          k,
          (fun n => (hk n).1),
          hkTop,
          hfTop
        ⟩

/--
If the top-dissipation Hilbert derivative-square envelope diverges along a
terminal sequence, then one fixed fourth-temporal coordinate amplitude
diverges on a cofinal subsequence.

The original terminal-time limit is preserved.
-/
theorem exists_fixed_fourthTemporalAmplitude_subsequence_of_topDissipationHilbertDerivativeSquare_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (hTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.topDissipation
              (τ n)
        )
        atTop
        atTop) :
    ∃ kStar : Fin 3,
      ∃ m : ℕ → ℕ,
        (∀ n : ℕ, n ≤ m n)
          ∧
        Tendsto m atTop atTop
          ∧
        Tendsto
          (fun n : ℕ => τ (m n))
          atTop
          (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalResolvedPhysicalPDEChannelAmplitude
                hH3 hClass kStar
                H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
                (τ (m n))
          )
          atTop
          atTop := by

  let f0 : ℕ → ℝ :=
    fun n =>
      h3TerminalResolvedPhysicalPDEChannelAmplitude
        hH3 hClass (0 : Fin 3)
        H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
        (τ n)

  let f1 : ℕ → ℝ :=
    fun n =>
      h3TerminalResolvedPhysicalPDEChannelAmplitude
        hH3 hClass (1 : Fin 3)
        H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
        (τ n)

  let f2 : ℕ → ℝ :=
    fun n =>
      h3TerminalResolvedPhysicalPDEChannelAmplitude
        hH3 hClass (2 : Fin 3)
        H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
        (τ n)

  rcases
    eventuallyBounded_or_cofinalTendstoAtTop f0
  with
    ⟨C0, h0Bound⟩
    |
    ⟨m0, hm0, hm0Top, hf0Top⟩

  · rcases
      eventuallyBounded_or_cofinalTendstoAtTop f1
    with
      ⟨C1, h1Bound⟩
      |
      ⟨m1, hm1, hm1Top, hf1Top⟩

    · have hf2Top :
          Tendsto f2 atTop atTop := by

        refine
          tendsto_atTop.2
            ?_

        intro M

        have hLarge :
            ∀ᶠ n : ℕ in atTop,
              M + C0 + C1
                ≤
              h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeSquareEnvelope
                hH3 hClass j
                H3TerminalResolvedPhysicalPDEChannel.topDissipation
                (τ n) :=
          (tendsto_atTop.1 hTop)
            (M + C0 + C1)

        filter_upwards
          [h0Bound, h1Bound, hLarge]
          with n h0n h1n hLargeN

        have hIdentity :=
          h3TerminalTopDissipationHilbertDerivativeSquareEnvelope_eq_sum_fourthTemporalAmplitude
            (t := τ n)
            hH3 hClass j

        rw [hIdentity, Fin.sum_univ_three] at hLargeN

        dsimp only [f0, f1, f2] at h0n h1n ⊢

        linarith

      refine
        ⟨
          (2 : Fin 3),
          (fun n : ℕ => n),
          ?_,
          tendsto_id,
          ?_,
          ?_
        ⟩

      · intro n
        exact le_rfl

      · simpa only [Function.comp_apply] using hTauTendsto

      · simpa only [f2] using hf2Top

    · refine
        ⟨
          (1 : Fin 3),
          m1,
          hm1,
          hm1Top,
          hTauTendsto.comp hm1Top,
          ?_
        ⟩

      simpa only [f1] using hf1Top

  · refine
      ⟨
        (0 : Fin 3),
        m0,
        hm0,
        hm0Top,
        hTauTendsto.comp hm0Top,
        ?_
      ⟩

    simpa only [f0] using hf0Top

end

end Euclidean
end Bridge
end PrimeTensor
