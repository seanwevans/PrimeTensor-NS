import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High.Dissipation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Single.Time.Concentration
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Angular.Vanishing.Criterion

/-!
# Synchronize the final witness with single-time physical dissipation concentration

The canonical resolved-PDE witness now carries a uniformly positive
spectral dissipation-difference control mass on a shrinking equatorial cone.

That control mass is bounded by the physical two-snapshot majorant

    8 * (M_s + M_t),

where `M_s` and `M_t` are the localized one-time physical H³ dissipation
masses at the two synchronized times.

At every index choose whichever snapshot carries the larger physical mass.
Because both synchronized time sequences converge to `T`, this pointwise
choice also converges to `T`.  The chosen single-time mass retains the same
positive lower bound up to the sharp factor two.

Thus the final obstruction is realized by actual one-time physical H³
dissipation concentration on the same canonical witness.
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
Under hypothetical nonextension, the synchronized final witness admits a
single-time selection from its exact two synchronized snapshots such that:

* the selected times tend to `T`;
* the same shrinking equatorial aperture tends to zero;
* localized physical H³ dissipation stays uniformly positive above unit
  radial frequency;
* physical single-time angular vanishing at cutoff `1` fails.

No new subsequence is introduced.
-/
theorem exists_fixed_terminalSequence_with_singleTimePhysicalDissipationConcentration_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
            ∃ r : Fin 3,
              r ≠ i
                ∧
              ∃ k : ℕ → ℕ,
                StrictMono k
                  ∧
                Tendsto
                  (fun n : ℕ => τ (p (k n)))
                  atTop
                  (𝓝 T)
                  ∧
                Tendsto
                  (fun n : ℕ => τ (q (k n)))
                  atTop
                  (𝓝 T)
                  ∧
                Tendsto
                  (
                    fun n : ℕ =>
                      (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)
                  )
                  atTop
                  (𝓝 0)
                  ∧
                ∃ σ : ℕ → ℝ,
                  ∃ hσ :
                    ∀ n : ℕ,
                      σ n ∈ Set.Ioo a T,
                    Tendsto σ atTop (𝓝 T)
                      ∧
                    (
                      ∀ n : ℕ,
                        ENNReal.ofReal (ε ^ 2 / 64)
                          <
                        16 *
                          h3TerminalPhysicalDissipationBadConeHighRadialMass
                            hH3
                            i
                            ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
                            1
                            (σ n)
                            ⟨
                              lt_trans hClass.terminal_start.1
                                (hσ n).1,
                              (hσ n).2
                            ⟩
                    )
                      ∧
                    ¬
                      H3TerminalPhysicalDissipationSingleTimeAngularVanishingAtEndpoint
                        hH3 hClass i 1 := by

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
      r,
      hrNe,
      k,
      hKMono,
      hTauPK,
      hTauQK,
      hAperture,
      hControl,
      hNotSpectralVanishing
    ⟩ :=
    exists_fixed_terminalSequence_with_spectralDissipationAngularConcentration_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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

  let κ : ℕ → ℝ :=
    fun n =>
      (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)

  have hκPos :
      ∀ n : ℕ,
        0 < κ n := by

    intro n

    dsimp only [κ]

    positivity

  let s : ℕ → ℝ :=
    fun n =>
      τ (q (k n))

  let t : ℕ → ℝ :=
    fun n =>
      τ (p (k n))

  have hs :
      ∀ n : ℕ,
        s n ∈ Set.Ioo a T := by

    intro n

    dsimp only [s]

    exact
      (hτ (q (k n))).1

  have ht :
      ∀ n : ℕ,
        t n ∈ Set.Ioo a T := by

    intro n

    dsimp only [t]

    exact
      (hτ (p (k n))).1

  have hsTendsto :
      Tendsto s atTop (𝓝 T) := by

    simpa only [s] using
      hTauQK

  have htTendsto :
      Tendsto t atTop (𝓝 T) := by

    simpa only [t] using
      hTauPK

  let hsAbs :
      ∀ n : ℕ,
        s n ∈ Set.Ioo (0 : ℝ) T :=
    fun n =>
      ⟨
        lt_trans hClass.terminal_start.1 (hs n).1,
        (hs n).2
      ⟩

  let htAbs :
      ∀ n : ℕ,
        t n ∈ Set.Ioo (0 : ℝ) T :=
    fun n =>
      ⟨
        lt_trans hClass.terminal_start.1 (ht n).1,
        (ht n).2
      ⟩

  have hPair :
      ∀ n : ℕ,
        ENNReal.ofReal (ε ^ 2 / 64)
          <
        h3TerminalPhysicalDissipationPairBadConeHighRadialMajorantMass
          hH3
          i
          (κ n)
          1
          (s n)
          (t n)
          (hsAbs n)
          (htAbs n) := by

    intro n

    have hControlN :
        ENNReal.ofReal (ε ^ 2 / 64)
          <
        h3TerminalSpectralDissipationDifferenceBadConeHighRadialControlMass
          i
          (κ n)
          1
          (h3TerminalVelocitySpectralStateAt
            hH3
            (s n)
            (hsAbs n))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (t n)
            (htAbs n)) := by

      dsimp only [κ, s, t, hsAbs, htAbs]

      simpa only [hStrict] using
        hControl n

    have hPairLe :=
      spectralDissipationDifferenceControlMass_le_physicalDissipationPairMajorantMass
        hH3
        i
        (κ n)
        1
        (s n)
        (t n)
        (hsAbs n)
        (htAbs n)

    exact
      hControlN.trans_le
        hPairLe

  let Ms : ℕ → ℝ :=
    fun n =>
      h3TerminalPhysicalDissipationBadConeHighRadialRealMass
        hH3
        i
        (κ n)
        1
        (s n)
        (hsAbs n)

  let Mt : ℕ → ℝ :=
    fun n =>
      h3TerminalPhysicalDissipationBadConeHighRadialRealMass
        hH3
        i
        (κ n)
        1
        (t n)
        (htAbs n)

  let σ : ℕ → ℝ :=
    fun n =>
      if Ms n ≤ Mt n
        then t n
        else s n

  have hσ :
      ∀ n : ℕ,
        σ n ∈ Set.Ioo a T := by

    intro n

    dsimp only [σ]

    by_cases hComp :
        Ms n ≤ Mt n

    · simp only [if_pos hComp]
      exact
        ht n

    · simp only [if_neg hComp]
      exact
        hs n

  have hσTendsto :
      Tendsto σ atTop (𝓝 T) := by

    rw [Metric.tendsto_atTop]
    rw [Metric.tendsto_atTop] at hsTendsto
    rw [Metric.tendsto_atTop] at htTendsto

    intro δ hδ

    obtain
      ⟨Ns, hNs⟩ :=
      hsTendsto
        δ
        hδ

    obtain
      ⟨Nt, hNt⟩ :=
      htTendsto
        δ
        hδ

    refine
      ⟨
        max Ns Nt,
        ?_
      ⟩

    intro n hn

    dsimp only [σ]

    by_cases hComp :
        Ms n ≤ Mt n

    · simp only [if_pos hComp]

      exact
        hNt
          n
          ((le_max_right Ns Nt).trans hn)

    · simp only [if_neg hComp]

      exact
        hNs
          n
          ((le_max_left Ns Nt).trans hn)

  have hSingle :
      ∀ n : ℕ,
        ENNReal.ofReal (ε ^ 2 / 64)
          <
        16 *
          h3TerminalPhysicalDissipationBadConeHighRadialMass
            hH3
            i
            (κ n)
            1
            (σ n)
            ⟨
              lt_trans hClass.terminal_start.1
                (hσ n).1,
              (hσ n).2
            ⟩ := by

    intro n

    have hPairEq :=
      physicalDissipationPairBadConeHighRadialMajorantMass_eq_ofReal_eight_mul_realMass_add
        hH3
        hClass
        (hs n)
        (ht n)
        i
        (κ n)
        1

    have hPairEq' :
        h3TerminalPhysicalDissipationPairBadConeHighRadialMajorantMass
            hH3
            i
            (κ n)
            1
            (s n)
            (t n)
            (hsAbs n)
            (htAbs n)
          =
        ENNReal.ofReal
          (
            8 *
              (
                Ms n
                  +
                Mt n
              )
          ) := by

      dsimp only [Ms, Mt, hsAbs, htAbs] at hPairEq ⊢

      simpa only using
        hPairEq

    have hPairReal :
        ENNReal.ofReal (ε ^ 2 / 64)
          <
        ENNReal.ofReal
          (
            8 *
              (
                Ms n
                  +
                Mt n
              )
          ) := by

      exact
        (hPair n).trans_eq
          hPairEq'

    by_cases hComp :
        Ms n ≤ Mt n

    · have hMtNonneg :
          0 ≤ Mt n := by

        dsimp only [Mt]

        exact
          h3TerminalPhysicalDissipationBadConeHighRadialRealMass_nonneg
            hH3
            i
            (κ n)
            1
            (t n)
            (htAbs n)

      have hRealLe :
          8 * (Ms n + Mt n)
            ≤
          16 * Mt n := by

        nlinarith

      have hOfRealLe :
          ENNReal.ofReal
              (8 * (Ms n + Mt n))
            ≤
          ENNReal.ofReal
              (16 * Mt n) :=
        ENNReal.ofReal_le_ofReal
          hRealLe

      have hBridge :=
        ofReal_physicalDissipationBadConeHighRadialRealMass_eq_mass
          hH3
          hClass
          (ht n)
          i
          (κ n)
          1

      have hFinal :
          ENNReal.ofReal (ε ^ 2 / 64)
            <
          16 *
            h3TerminalPhysicalDissipationBadConeHighRadialMass
              hH3
              i
              (κ n)
              1
              (t n)
              (htAbs n) := by

        calc
          ENNReal.ofReal (ε ^ 2 / 64)
              <
            ENNReal.ofReal
              (8 * (Ms n + Mt n)) :=
            hPairReal

          _ ≤
            ENNReal.ofReal
              (16 * Mt n) :=
            hOfRealLe

          _ =
            16 *
              h3TerminalPhysicalDissipationBadConeHighRadialMass
                hH3
                i
                (κ n)
                1
                (t n)
                (htAbs n) := by

            rw [
              ENNReal.ofReal_mul
                (by norm_num : (0 : ℝ) ≤ 16)
            ]

            norm_num

            dsimp only [Mt] at hBridge

            rw [
              hBridge
            ]

      simpa only [σ, if_pos hComp] using
        hFinal

    · have hMsNonneg :
          0 ≤ Ms n := by

        dsimp only [Ms]

        exact
          h3TerminalPhysicalDissipationBadConeHighRadialRealMass_nonneg
            hH3
            i
            (κ n)
            1
            (s n)
            (hsAbs n)

      have hReverse :
          Mt n ≤ Ms n :=
        le_of_not_ge
          hComp

      have hRealLe :
          8 * (Ms n + Mt n)
            ≤
          16 * Ms n := by

        nlinarith

      have hOfRealLe :
          ENNReal.ofReal
              (8 * (Ms n + Mt n))
            ≤
          ENNReal.ofReal
              (16 * Ms n) :=
        ENNReal.ofReal_le_ofReal
          hRealLe

      have hBridge :=
        ofReal_physicalDissipationBadConeHighRadialRealMass_eq_mass
          hH3
          hClass
          (hs n)
          i
          (κ n)
          1

      have hFinal :
          ENNReal.ofReal (ε ^ 2 / 64)
            <
          16 *
            h3TerminalPhysicalDissipationBadConeHighRadialMass
              hH3
              i
              (κ n)
              1
              (s n)
              (hsAbs n) := by

        calc
          ENNReal.ofReal (ε ^ 2 / 64)
              <
            ENNReal.ofReal
              (8 * (Ms n + Mt n)) :=
            hPairReal

          _ ≤
            ENNReal.ofReal
              (16 * Ms n) :=
            hOfRealLe

          _ =
            16 *
              h3TerminalPhysicalDissipationBadConeHighRadialMass
                hH3
                i
                (κ n)
                1
                (s n)
                (hsAbs n) := by

            rw [
              ENNReal.ofReal_mul
                (by norm_num : (0 : ℝ) ≤ 16)
            ]

            norm_num

            dsimp only [Ms] at hBridge

            rw [
              hBridge
            ]

      simpa only [σ, if_neg hComp] using
        hFinal

  have hNotPhysicalVanishing :
      ¬
        H3TerminalPhysicalDissipationSingleTimeAngularVanishingAtEndpoint
          hH3 hClass i 1 := by

    intro hPhysicalVanishing

    exact
      hNotSpectralVanishing
        (
          spectralDissipationDifferenceAngularVanishingAtEndpoint_of_physicalDissipationSingleTimeAngularVanishingAtEndpoint
            hH3
            hClass
            i
            1
            hPhysicalVanishing
        )

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
      r,
      hrNe,
      k,
      hKMono,
      hTauPK,
      hTauQK,
      hAperture,
      σ,
      hσ,
      hσTendsto,
      ?_,
      hNotPhysicalVanishing
    ⟩

  intro n

  have h :=
    hSingle n

  dsimp only [κ] at h

  simpa only using
    h

end

end Euclidean
end Bridge
end PrimeTensor
