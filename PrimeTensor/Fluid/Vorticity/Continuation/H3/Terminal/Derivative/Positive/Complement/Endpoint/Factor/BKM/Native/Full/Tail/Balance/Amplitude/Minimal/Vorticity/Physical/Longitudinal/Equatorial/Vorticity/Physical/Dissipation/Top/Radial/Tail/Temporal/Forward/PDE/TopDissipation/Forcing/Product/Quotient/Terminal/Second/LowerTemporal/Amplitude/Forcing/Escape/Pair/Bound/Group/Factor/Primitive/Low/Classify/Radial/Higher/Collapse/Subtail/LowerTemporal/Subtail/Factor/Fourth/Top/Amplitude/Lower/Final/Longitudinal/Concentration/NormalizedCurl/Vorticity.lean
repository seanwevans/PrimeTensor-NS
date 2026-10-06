import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Normalized.Vorticity.Channel

/-!
# Freeze a complementary normalized-vorticity component on the final witness

The synchronized final witness now carries eventual positive normalized
longitudinal curl-pair mass on the exact cofinal pair `τ (q n), τ (p n)`.

The pair consists of two normalized curl channels.  On the eventual tail,
at least one channel carries half of the pair mass.  A finite-pigeonhole
extraction freezes one channel on a strictly increasing subsequence.

That channel is exactly one fixed normalized-vorticity component, and its
vorticity index is complementary to the surviving longitudinal coordinate.

The original `τ`, `p`, and `q` are retained.  Only one strictly increasing
index selector is added.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/--
The final resolved-PDE witness admits a strictly increasing subsequence on
which one fixed complementary normalized-vorticity component carries more
than `ε²/32` square mass in the shrinking equatorial cone.

The states remain the original synchronized pair `τ (q n), τ (p n)`.
-/
theorem exists_fixed_terminalSequence_with_fixed_complementary_normalizedVorticityEquatorialConcentration_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ j₀ : Fin 3,
      ∃ τ : ℕ → ℝ,
        ∃ hτ :
          ∀ n : ℕ,
            τ n ∈ Set.Ioo a T
              ∧
            τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T,
          ∃ p q : ℕ → ℕ,
            (∀ n : ℕ, n ≤ p n)
              ∧
            (∀ n : ℕ, p n ≤ q n)
              ∧
            Tendsto τ atTop (𝓝 T)
              ∧
            Tendsto
              (fun n : ℕ =>
                velocityH3EnergyAt u (τ n))
              atTop atTop
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  norm
                    (
                      h3TerminalVelocityComponentSpectralStateAt
                        hH3
                        i
                        (τ n)
                        ⟨
                          lt_trans hClass.terminal_start.1 (hτ n).1.1,
                          (hτ n).1.2
                        ⟩
                    )
              )
              atTop
              atTop
              ∧
            ∃ m : ℕ → ℕ,
              StrictMono m
                ∧
              Tendsto
                (fun n : ℕ => τ (p (m n)))
                atTop
                (𝓝 T)
                ∧
              Tendsto
                (fun n : ℕ => τ (q (m n)))
                atTop
                (𝓝 T)
                ∧
              Tendsto
                (
                  fun n : ℕ =>
                    (1 : ℝ) / (((m n : ℕ) : ℝ) + 1)
                )
                atTop
                (𝓝 0)
                ∧
              ∃ r : Fin 3,
                r ≠ i
                  ∧
                (
                  ∀ n : ℕ,
                    ε ^ 2 / 32
                      <
                    h3TerminalNormalizedVorticityComponentBadConeSquareDefect
                      i r
                      ((1 : ℝ) / (((m n : ℕ) : ℝ) + 1))
                      (h3TerminalVelocitySpectralStateAt
                        hH3
                        (τ (q (m n)))
                        ⟨
                          lt_trans hClass.terminal_start.1
                            (hτ (q (m n))).1.1,
                          (hτ (q (m n))).1.2
                        ⟩)
                      (h3TerminalVelocitySpectralStateAt
                        hH3
                        (τ (p (m n)))
                        ⟨
                          lt_trans hClass.terminal_start.1
                            (hτ (p (m n))).1.1,
                          (hτ (p (m n))).1.2
                        ⟩)
                ) := by

  classical

  obtain
    ⟨
      j₀,
      τ,
      hτ,
      p,
      q,
      hnp,
      hpq,
      hTau,
      hEnergyTop,
      hLongTop,
      hTauP,
      hTauQ,
      N,
      _hN1,
      hPair
    ⟩ :=
    exists_fixed_terminalSequence_with_eventual_normalizedCurlEquatorialConcentration_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension
      hε

  let hStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T :=
    fun n =>
      ⟨
        lt_trans hClass.terminal_start.1 (hτ n).1.1,
        (hτ n).1.2
      ⟩

  have hChannelChoice :
      ∀ d : ℕ,
        ∃ k : Fin 2,
          ε ^ 2 / 32
            <
          h3TerminalNormalizedLongitudinalCurlChannelBadConeSquareDefect
            i k
            ((1 : ℝ) / (((N + d : ℕ) : ℝ) + 1))
            (h3TerminalVelocitySpectralStateAt
              hH3
              (τ (q (N + d)))
              (hStrict (q (N + d))))
            (h3TerminalVelocitySpectralStateAt
              hH3
              (τ (p (N + d)))
              (hStrict (p (N + d)))) := by

    intro d

    have hNd :
        N ≤ N + d :=
      Nat.le_add_right N d

    have hPairNd :
        ε ^ 2 / 16
          <
        h3TerminalNormalizedLongitudinalCurlPairBadConeSquareDefect
          i
          ((1 : ℝ) / (((N + d : ℕ) : ℝ) + 1))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ (q (N + d)))
            (hStrict (q (N + d))))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ (p (N + d)))
            (hStrict (p (N + d)))) := by

      have h :=
        hPair
          (N + d)
          hNd

      simpa only [hStrict] using
        h

    obtain
      ⟨k, hk⟩ :=
      exists_normalizedLongitudinalCurlChannelBadConeSquareDefect_gt_half_of_pair
        i
        ((1 : ℝ) / (((N + d : ℕ) : ℝ) + 1))
        (ε ^ 2 / 16)
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (q (N + d)))
          (hStrict (q (N + d))))
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (p (N + d)))
          (hStrict (p (N + d))))
        hPairNd

    refine
      ⟨
        k,
        ?_
      ⟩

    convert hk using 1 <;> ring

  choose channel hChannelMass using hChannelChoice

  obtain
    ⟨
      kStar,
      hInfinite
    ⟩ :=
    Finite.exists_infinite_fiber
      channel

  rw [Set.infinite_coe_iff] at hInfinite

  let P : ℕ → Prop :=
    fun d =>
      ε ^ 2 / 32
        <
      h3TerminalNormalizedLongitudinalCurlChannelBadConeSquareDefect
        i kStar
        ((1 : ℝ) / (((N + d : ℕ) : ℝ) + 1))
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (q (N + d)))
          (hStrict (q (N + d))))
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (p (N + d)))
          (hStrict (p (N + d))))

  have hStrictlyCofinal :
      ∀ D : ℕ,
        ∃ d > D,
          P d := by

    intro D

    obtain
      ⟨
        d,
        hdFiber,
        hDd
      ⟩ :=
      Set.Infinite.exists_gt
        hInfinite
        D

    have hChannelEq :
        channel d = kStar := by
      change channel d = kStar at hdFiber
      exact
        hdFiber

    have hMass :=
      hChannelMass d

    rw [
      hChannelEq
    ] at hMass

    exact
      ⟨
        d,
        hDd,
        by
          simpa only [P] using hMass
      ⟩

  obtain
    ⟨
      s,
      hSMono,
      hMassSub
    ⟩ :=
    Nat.exists_strictMono_subsequence
      hStrictlyCofinal

  let m : ℕ → ℕ :=
    fun n =>
      N + s n

  have hMMono :
      StrictMono m := by

    intro n₁ n₂ hn

    dsimp only [m]

    exact
      Nat.add_lt_add_left
        (hSMono hn)
        N

  have hMTop :
      Tendsto m atTop atTop :=
    hMMono.tendsto_atTop

  have hTauPSub :
      Tendsto
        (fun n : ℕ => τ (p (m n)))
        atTop
        (𝓝 T) := by

    exact
      hTauP.comp
        hMTop

  have hTauQSub :
      Tendsto
        (fun n : ℕ => τ (q (m n)))
        atTop
        (𝓝 T) := by

    exact
      hTauQ.comp
        hMTop

  have hApertureBase :
      Tendsto
        (
          fun n : ℕ =>
            (1 : ℝ) / ((n : ℝ) + 1)
        )
        atTop
        (𝓝 0) := by

    simpa only [
      Nat.cast_add,
      Nat.cast_one
    ] using
      tendsto_one_div_add_atTop_nhds_zero_nat

  have hApertureSub :
      Tendsto
        (
          fun n : ℕ =>
            (1 : ℝ) / (((m n : ℕ) : ℝ) + 1)
        )
        atTop
        (𝓝 0) := by

    exact
      hApertureBase.comp
        hMTop

  let r : Fin 3 :=
    h3TerminalNormalizedLongitudinalCurlChannelVorticityIndex
      i kStar

  have hrNe :
      r ≠ i := by

    dsimp only [r]

    exact
      normalizedLongitudinalCurlChannelVorticityIndex_ne_longitudinal
        i kStar

  have hVorticityMass :
      ∀ n : ℕ,
        ε ^ 2 / 32
          <
        h3TerminalNormalizedVorticityComponentBadConeSquareDefect
          i r
          ((1 : ℝ) / (((m n : ℕ) : ℝ) + 1))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ (q (m n)))
            (hStrict (q (m n))))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ (p (m n)))
            (hStrict (p (m n)))) := by

    intro n

    have hMass :=
      hMassSub n

    change
      ε ^ 2 / 32
        <
      h3TerminalNormalizedLongitudinalCurlChannelBadConeSquareDefect
        i kStar
        ((1 : ℝ) / (((m n : ℕ) : ℝ) + 1))
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (q (m n)))
          (hStrict (q (m n))))
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (p (m n)))
          (hStrict (p (m n)))) at hMass

    rw [
      normalizedLongitudinalCurlChannelBadConeSquareDefect_eq_normalizedVorticityComponentBadConeSquareDefect
    ] at hMass

    simpa only [r] using
      hMass

  refine
    ⟨
      j₀,
      τ,
      hτ,
      p,
      q,
      hnp,
      hpq,
      hTau,
      hEnergyTop,
      hLongTop,
      m,
      hMMono,
      hTauPSub,
      hTauQSub,
      hApertureSub,
      r,
      hrNe,
      ?_
    ⟩

  intro n

  have h :=
    hVorticityMass n

  simpa only [hStrict] using
    h

end

end Euclidean
end Bridge
end PrimeTensor
