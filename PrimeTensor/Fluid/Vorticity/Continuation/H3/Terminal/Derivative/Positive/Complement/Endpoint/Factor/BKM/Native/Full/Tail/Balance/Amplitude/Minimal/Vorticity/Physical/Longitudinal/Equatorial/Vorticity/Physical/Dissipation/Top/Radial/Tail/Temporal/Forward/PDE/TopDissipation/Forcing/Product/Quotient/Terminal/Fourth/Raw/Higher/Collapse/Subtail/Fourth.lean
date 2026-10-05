import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Higher.Collapse.Subtail

/-!
# Resolve the sixth-diffusion branch inside fourth-temporal escape

The fourth-temporal Hilbert derivative frontier previously had two branches:

* sixth-diffusion Hilbert derivative escape on a cofinal subsequence;
* escape of the terminal `q² F_j` forcing derivative on the original
  sequence.

The sixth-diffusion branch is now completely classified.  Substituting that
classification leaves exactly three structural outcomes:

* physical H³-energy escape;
* escape of one fixed nonzero extended higher-radial moment;
* escape of `‖(q² F_j)'‖`.

Thus the only forcing-specific branch still exposed at this level is the
fourth-weight forcing time derivative.
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
Fourth-temporal Hilbert derivative escape resolves, after cofinal refinement,
into H³-energy escape or one fixed nonzero extended higher-radial escape,
unless the terminal `q² F_j` forcing derivative itself diverges on the
original sequence.
-/
theorem fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_forcingDerivative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (hFourth :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
              (τ n)
        )
        atTop
        atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n)
          ∧
        Tendsto s atTop atTop
          ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop
          (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              velocityH3EnergyAt u (τ (s n))
          )
          atTop
          atTop
    )
      ∨
    (
      ∃ m : ℕ,
        m ≠ 0
          ∧
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n)
            ∧
          Tendsto s atTop atTop
            ∧
          Tendsto
            (fun n : ℕ => τ (s n))
            atTop
            (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalPhysicalExtendedHigherRadialMomentAt
                  hH3 hClass m
                  (τ (s n))
                  (hτ (s n))
            )
            atTop
            (𝓝 ∞)
    )
      ∨
    Tendsto
      (
        fun n : ℕ =>
          ‖deriv
            (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
              hH3 hClass j)
            (τ n)‖
      )
      atTop
      atTop := by

  rcases
    fourthTemporal_hilbertDerivativeNorm_escape_sixth_or_forcingDerivative
      hH3 hClass j τ hτ hTauTendsto hFourth
  with
    hSixth
    |
    hForcing

  · rcases hSixth with
      ⟨k, hk, hkTop, hTauK, hSixthTop⟩

    rcases
      sixthDiffusion_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial
        hH3
        hClass
        j
        (fun n : ℕ => τ (k n))
        (fun n : ℕ => hτ (k n))
        hTauK
        hSixthTop
    with
      hEnergy
      |
      hHigher

    · rcases hEnergy with
        ⟨s, hs, hsTop, hTauSub, hEnergyTop⟩

      refine
        Or.inl
          ⟨
            (fun n : ℕ => k (s n)),
            ?_,
            hkTop.comp hsTop,
            hTauSub,
            hEnergyTop
          ⟩

      intro n

      exact
        le_trans
          (hs n)
          (hk (s n))

    · rcases hHigher with
        ⟨m, hm, s, hs, hsTop, hTauSub, hHigherTop⟩

      refine
        Or.inr
          (
            Or.inl
              ⟨
                m,
                hm,
                (fun n : ℕ => k (s n)),
                ?_,
                hkTop.comp hsTop,
                hTauSub,
                hHigherTop
              ⟩
          )

      intro n

      exact
        le_trans
          (hs n)
          (hk (s n))

  · exact
      Or.inr
        (Or.inr hForcing)

end

end Euclidean
end Bridge
end PrimeTensor
