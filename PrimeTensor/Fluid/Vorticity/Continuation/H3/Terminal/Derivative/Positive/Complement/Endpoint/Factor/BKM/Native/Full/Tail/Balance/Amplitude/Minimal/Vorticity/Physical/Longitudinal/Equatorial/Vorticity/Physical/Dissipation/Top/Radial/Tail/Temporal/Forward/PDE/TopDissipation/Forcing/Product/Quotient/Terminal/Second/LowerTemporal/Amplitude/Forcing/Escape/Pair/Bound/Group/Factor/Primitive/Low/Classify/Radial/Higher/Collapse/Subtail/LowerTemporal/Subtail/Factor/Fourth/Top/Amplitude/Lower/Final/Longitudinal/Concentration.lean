import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Concentration

/-!
# Synchronize the final longitudinal witness with shrinking equatorial concentration

The completed resolved-PDE closure now provides one explicit terminal sequence
whose total H³ energy and same-index longitudinal spectral H³ norm both escape.

This file keeps that sequence fixed.

For every positive separation scale `ε`, we extract two cofinal index maps
`p n ≤ q n` from the same sequence.  The longitudinal states at those two
indices remain separated by at least `ε`, and the existing good-cone Cauchy
estimate forces a scale-invariant amount of their difference into the shrinking
equatorial bad cone

    κ_n = 1 / (n + 1).

Thus the final PDE witness and the equatorial concentration mechanism are
carried by one common terminal sequence rather than unrelated choices of times.
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
Longitudinal spectral-norm escape along one fixed terminal sequence yields two
cofinal index selections from that same sequence whose longitudinal difference
keeps a fixed positive square mass inside the shrinking equatorial cone.
-/
theorem exists_cofinal_pair_shrinkingEquatorialCone_longitudinalBadConeSquareDefect_of_longitudinalSpectralNorm_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (τ : ℕ → ℝ)
    (hStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (hLongitudinalTop :
      Tendsto
        (
          fun n : ℕ =>
            norm
              (
                h3TerminalVelocityComponentSpectralStateAt
                  hH3 i (τ n) (hStrict n)
              )
        )
        atTop
        atTop)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ p q : ℕ → ℕ,
      (∀ n : ℕ, n ≤ p n)
        ∧
      (∀ n : ℕ, p n ≤ q n)
        ∧
      Tendsto p atTop atTop
        ∧
      Tendsto q atTop atTop
        ∧
      Tendsto
        (fun n : ℕ => τ (p n))
        atTop
        (𝓝 T)
        ∧
      Tendsto
        (fun n : ℕ => τ (q n))
        atTop
        (𝓝 T)
        ∧
      (
        ∀ n : ℕ,
          ε
            ≤
          norm
            (
              h3TerminalVelocityComponentSpectralStateAt
                  hH3 i (τ (q n)) (hStrict (q n))
                -
              h3TerminalVelocityComponentSpectralStateAt
                  hH3 i (τ (p n)) (hStrict (p n))
            )
            ∧
          ε ^ 2 / 2
            <
          h3TerminalLongitudinalBadConeSquareDefect
            i
            ((1 : ℝ) / ((n : ℝ) + 1))
            (h3TerminalVelocitySpectralStateAt
              hH3
              (τ (q n))
              (hStrict (q n)))
            (h3TerminalVelocitySpectralStateAt
              hH3
              (τ (p n))
              (hStrict (p n)))
      ) := by

  classical

  have hTauMetric := hTauTendsto
  rw [Metric.tendsto_atTop] at hTauMetric

  have hChoice :
      ∀ n : ℕ,
        ∃ p q : ℕ,
          n ≤ p
            ∧
          p ≤ q
            ∧
          ε
            ≤
          norm
            (
              h3TerminalVelocityComponentSpectralStateAt
                  hH3 i (τ q) (hStrict q)
                -
              h3TerminalVelocityComponentSpectralStateAt
                  hH3 i (τ p) (hStrict p)
            )
            ∧
          ε ^ 2 / 2
            <
          h3TerminalLongitudinalBadConeSquareDefect
            i
            ((1 : ℝ) / ((n : ℝ) + 1))
            (h3TerminalVelocitySpectralStateAt
              hH3
              (τ q)
              (hStrict q))
            (h3TerminalVelocitySpectralStateAt
              hH3
              (τ p)
              (hStrict p)) := by

    intro n

    let κ : ℝ :=
      (1 : ℝ) / ((n : ℝ) + 1)

    have hκ :
        0 < κ := by
      dsimp only [κ]
      positivity

    obtain
      ⟨η, hη, hBadNear⟩ :=
      longitudinalBadConeScaledSquareDefect_gt_half_of_actualVorticityStrongH3EndpointPath
        hH3
        hPhysical
        hκ
        hε

    obtain
      ⟨N, hNear⟩ :=
      hTauMetric
        η
        hη

    let p : ℕ :=
      max n N

    have hnp :
        n ≤ p := by
      dsimp only [p]
      exact le_max_left n N

    have hNp :
        N ≤ p := by
      dsimp only [p]
      exact le_max_right n N

    have hpNear :
        dist (τ p) T < η :=
      hNear
        p
        hNp

    let Up : H3SpectralScalarState :=
      h3TerminalVelocityComponentSpectralStateAt
        hH3 i (τ p) (hStrict p)

    have hLarge :
        ∀ᶠ q : ℕ in atTop,
          norm Up + ε
            <
          norm
            (
              h3TerminalVelocityComponentSpectralStateAt
                hH3 i (τ q) (hStrict q)
            ) :=
      hLongitudinalTop.eventually
        (eventually_gt_atTop (norm Up + ε))

    obtain
      ⟨q, hpq, hqLarge⟩ :=
      (
        (eventually_ge_atTop p).and
          hLarge
      ).exists

    have hNq :
        N ≤ q :=
      hNp.trans hpq

    have hqNear :
        dist (τ q) T < η :=
      hNear
        q
        hNq

    let Uq : H3SpectralScalarState :=
      h3TerminalVelocityComponentSpectralStateAt
        hH3 i (τ q) (hStrict q)

    have hTriangle :
        norm Uq
          ≤
        norm (Uq - Up)
          +
        norm Up := by

      calc
        norm Uq
            =
          norm ((Uq - Up) + Up) := by
            rw [sub_add_cancel]
        _ ≤
          norm (Uq - Up) + norm Up :=
            norm_add_le _ _

    have hSeparation :
        ε ≤ norm (Uq - Up) := by

      have hLarge' :
          norm Up + ε < norm Uq := by
        dsimp only [Uq]
        exact hqLarge

      linarith

    have hScaled :=
      hBadNear
        (τ q)
        (hStrict q)
        (τ p)
        (hStrict p)
        hqNear
        hpNear
        (by
          dsimp only [Uq, Up] at hSeparation
          exact hSeparation)

    rw [
      h3TerminalLongitudinalBadConeScaledSquareDefect_eq_sq_mul
    ] at hScaled

    have hκ2 :
        0 < κ ^ 2 :=
      pow_pos hκ 2

    have hMul :
        κ ^ 2 * (ε ^ 2 / 2)
          <
        κ ^ 2
          *
        h3TerminalLongitudinalBadConeSquareDefect
          i κ
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ q)
            (hStrict q))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ p)
            (hStrict p)) := by

      convert hScaled using 1 <;> ring

    have hUnscaled :
        ε ^ 2 / 2
          <
        h3TerminalLongitudinalBadConeSquareDefect
          i κ
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ q)
            (hStrict q))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ p)
            (hStrict p)) :=
      lt_of_mul_lt_mul_left
        hMul
        (le_of_lt hκ2)

    refine
      ⟨
        p,
        q,
        hnp,
        hpq,
        ?_,
        ?_
      ⟩

    · dsimp only [Uq, Up] at hSeparation
      exact hSeparation

    · simpa only [κ] using hUnscaled

  choose p q hnp hpq hSep hBad using hChoice

  have hpTop :
      Tendsto p atTop atTop := by

    refine tendsto_atTop.2 ?_

    intro N

    filter_upwards [eventually_ge_atTop N] with n hn

    exact
      hn.trans
        (hnp n)

  have hqTop :
      Tendsto q atTop atTop := by

    refine tendsto_atTop.2 ?_

    intro N

    filter_upwards [eventually_ge_atTop N] with n hn

    exact
      (hn.trans (hnp n)).trans
        (hpq n)

  have hTauP :
      Tendsto
        (fun n : ℕ => τ (p n))
        atTop
        (𝓝 T) :=
    hTauTendsto.comp hpTop

  have hTauQ :
      Tendsto
        (fun n : ℕ => τ (q n))
        atTop
        (𝓝 T) :=
    hTauTendsto.comp hqTop

  exact
    ⟨
      p,
      q,
      hnp,
      hpq,
      hpTop,
      hqTop,
      hTauP,
      hTauQ,
      fun n =>
        ⟨
          hSep n,
          hBad n
        ⟩
    ⟩

/--
Apply the synchronized concentration extraction to the explicit final
resolved-PDE witness.  The two shrinking-cone states are selected from the
same `τ` that already carries total H³-energy and longitudinal spectral escape.
-/
theorem exists_fixed_terminalSequence_with_cofinal_shrinkingEquatorialConcentration_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
            Tendsto
              (fun n : ℕ => τ (p n))
              atTop
              (𝓝 T)
              ∧
            Tendsto
              (fun n : ℕ => τ (q n))
              atTop
              (𝓝 T)
              ∧
            (
              ∀ n : ℕ,
                ε ^ 2 / 2
                  <
                h3TerminalLongitudinalBadConeSquareDefect
                  i
                  ((1 : ℝ) / ((n : ℝ) + 1))
                  (h3TerminalVelocitySpectralStateAt
                    hH3
                    (τ (q n))
                    ⟨
                      lt_trans hClass.terminal_start.1
                        (hτ (q n)).1.1,
                      (hτ (q n)).1.2
                    ⟩)
                  (h3TerminalVelocitySpectralStateAt
                    hH3
                    (τ (p n))
                    ⟨
                      lt_trans hClass.terminal_start.1
                        (hτ (p n)).1.1,
                      (hτ (p n)).1.2
                    ⟩)
            ) := by

  obtain
    ⟨j₀, τ, hτ, hTau, hEnergyTop, hLongTop⟩ :=
    exists_fixed_terminalSequence_h3Energy_and_longitudinalSpectralNorm_escape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension

  let hStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T :=
    fun n =>
      ⟨
        lt_trans hClass.terminal_start.1 (hτ n).1.1,
        (hτ n).1.2
      ⟩

  have hLongTop' :
      Tendsto
        (
          fun n : ℕ =>
            norm
              (
                h3TerminalVelocityComponentSpectralStateAt
                  hH3 i (τ n) (hStrict n)
              )
        )
        atTop
        atTop := by
    simpa only [hStrict] using hLongTop

  obtain
    ⟨
      p,
      q,
      hnp,
      hpq,
      _hpTop,
      _hqTop,
      hTauP,
      hTauQ,
      hData
    ⟩ :=
    exists_cofinal_pair_shrinkingEquatorialCone_longitudinalBadConeSquareDefect_of_longitudinalSpectralNorm_tendstoAtTop
      hH3
      hPhysical
      τ
      hStrict
      hTau
      hLongTop'
      hε

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
      hTauP,
      hTauQ,
      ?_
    ⟩

  intro n

  have hBad :=
    (hData n).2

  simpa only [hStrict] using hBad

end

end Euclidean
end Bridge
end PrimeTensor
