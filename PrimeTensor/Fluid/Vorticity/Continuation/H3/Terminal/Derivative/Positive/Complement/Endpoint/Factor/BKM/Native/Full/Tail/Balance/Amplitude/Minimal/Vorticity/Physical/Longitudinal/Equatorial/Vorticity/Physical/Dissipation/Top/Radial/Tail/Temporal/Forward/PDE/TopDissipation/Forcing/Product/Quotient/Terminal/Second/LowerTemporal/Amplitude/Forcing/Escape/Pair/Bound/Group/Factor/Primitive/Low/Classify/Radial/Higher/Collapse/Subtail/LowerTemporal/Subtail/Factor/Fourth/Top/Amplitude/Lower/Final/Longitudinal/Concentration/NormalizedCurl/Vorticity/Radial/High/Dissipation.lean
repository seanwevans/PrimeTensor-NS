import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower.Final.Longitudinal.Concentration.NormalizedCurl.Vorticity.Radial.High
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Dissipation.Angular.Concentration

/-!
# Synchronize the final witness with angular dissipation concentration

The synchronized terminal witness now carries a fixed complementary raw
vorticity component with uniformly positive high-radial square mass inside
shrinking equatorial cones.

The raw-vorticity square mass is pointwise controlled by the complete H³
spectral dissipation-difference mass.  Therefore the same witness carries a
uniform positive lower bound in the dissipation-difference channel.

Because the aperture tends to zero and both selected times tend to `T`, this
same sequence directly contradicts angular dissipation vanishing at radial
cutoff `ρ = 1`.

Thus the remaining conditional nonextension mechanism is localized on the
canonical PDE-selected witness itself.
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
Under hypothetical nonextension, the synchronized final witness carries a
uniformly positive full-H³ spectral dissipation-difference mass in shrinking
equatorial cones above unit radial frequency.

Consequently angular dissipation vanishing at cutoff `1` fails.
-/
theorem exists_fixed_terminalSequence_with_spectralDissipationAngularConcentration_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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
                (
                  ∀ n : ℕ,
                    ENNReal.ofReal (ε ^ 2 / 64)
                      <
                    h3TerminalSpectralDissipationDifferenceBadConeHighRadialControlMass
                      i
                      ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
                      1
                      (h3TerminalVelocitySpectralStateAt
                        hH3
                        (τ (q (k n)))
                        ⟨
                          lt_trans hClass.terminal_start.1
                            (hτ (q (k n))).1.1,
                          (hτ (q (k n))).1.2
                        ⟩)
                      (h3TerminalVelocitySpectralStateAt
                        hH3
                        (τ (p (k n)))
                        ⟨
                          lt_trans hClass.terminal_start.1
                            (hτ (p (k n))).1.1,
                          (hτ (p (k n))).1.2
                        ⟩)
                )
                  ∧
                ¬
                  H3TerminalSpectralDissipationDifferenceAngularVanishingAtEndpoint
                    hH3 i 1 := by

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
      hRawHigh
    ⟩ :=
    exists_fixed_terminalSequence_with_fixed_complementary_highRadialRawVorticity_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
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

  have hControl :
      ∀ n : ℕ,
        ENNReal.ofReal (ε ^ 2 / 64)
          <
        h3TerminalSpectralDissipationDifferenceBadConeHighRadialControlMass
          i
          ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
          1
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ (q (k n)))
            (hStrict (q (k n))))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ (p (k n)))
            (hStrict (p (k n)))) := by

    intro n

    have hRaw :=
      hRawHigh n

    have hLe :=
      rawVorticityComponentBadConeHighRadialSquareMass_le_spectralDissipationDifferenceControlMass
        i
        r
        ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
        1
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (q (k n)))
          (hStrict (q (k n))))
        (h3TerminalVelocitySpectralStateAt
          hH3
          (τ (p (k n)))
          (hStrict (p (k n))))

    have hRaw' :
        ENNReal.ofReal (ε ^ 2 / 64)
          <
        h3TerminalRawVorticityComponentBadConeHighRadialSquareMass
          i r
          ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
          1
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ (q (k n)))
            (hStrict (q (k n))))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ (p (k n)))
            (hStrict (p (k n)))) := by

      simpa only [hStrict] using
        hRaw

    exact
      hRaw'.trans_le
        hLe

  have hNotVanishing :
      ¬
        H3TerminalSpectralDissipationDifferenceAngularVanishingAtEndpoint
          hH3 i 1 := by

    intro hVanishing

    have hDelta :
        0 < ε ^ 2 / 64 := by
      positivity

    obtain
      ⟨
        κ₀,
        hκ₀,
        η,
        hη,
        hSmall
      ⟩ :=
      hVanishing
        (ε ^ 2 / 64)
        hDelta

    have hQNear :
        ∀ᶠ n : ℕ in atTop,
          dist (τ (q (k n))) T < η := by

      have hBall :
          Metric.ball T η ∈ 𝓝 T :=
        Metric.ball_mem_nhds
          T
          hη

      have hEventually :=
        hTauQK.eventually
          hBall

      filter_upwards [hEventually] with n hn

      simpa only [
        Metric.mem_ball,
        dist_comm
      ] using
        hn

    have hPNear :
        ∀ᶠ n : ℕ in atTop,
          dist (τ (p (k n))) T < η := by

      have hBall :
          Metric.ball T η ∈ 𝓝 T :=
        Metric.ball_mem_nhds
          T
          hη

      have hEventually :=
        hTauPK.eventually
          hBall

      filter_upwards [hEventually] with n hn

      simpa only [
        Metric.mem_ball,
        dist_comm
      ] using
        hn

    have hKappaSmall :
        ∀ᶠ n : ℕ in atTop,
          (1 : ℝ) / (((k n : ℕ) : ℝ) + 1)
            <
          κ₀ := by

      exact
        (tendsto_order.1 hAperture).2
          κ₀
          hκ₀

    obtain
      ⟨
        n,
        hqNear,
        hpNear,
        hκSmall
      ⟩ :=
      (
        hQNear.and
          (
            hPNear.and
              hKappaSmall
          )
      ).exists

    have hκ :
        0
          <
        (1 : ℝ) / (((k n : ℕ) : ℝ) + 1) := by
      positivity

    have hSmallN :
        h3TerminalSpectralDissipationDifferenceBadConeHighRadialControlMass
            i
            ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
            1
            (h3TerminalVelocitySpectralStateAt
              hH3
              (τ (q (k n)))
              (hStrict (q (k n))))
            (h3TerminalVelocitySpectralStateAt
              hH3
              (τ (p (k n)))
              (hStrict (p (k n))))
          <
        ENNReal.ofReal (ε ^ 2 / 64) := by

      exact
        hSmall
          (τ (q (k n)))
          (τ (p (k n)))
          (hStrict (q (k n)))
          (hStrict (p (k n)))
          hqNear
          hpNear
          ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
          hκ
          hκSmall

    exact
      (lt_irrefl
        (ENNReal.ofReal (ε ^ 2 / 64)))
        (
          (hControl n).trans
            hSmallN
        )

  have hControlOut :
      ∀ n : ℕ,
        ENNReal.ofReal (ε ^ 2 / 64)
          <
        h3TerminalSpectralDissipationDifferenceBadConeHighRadialControlMass
          i
          ((1 : ℝ) / (((k n : ℕ) : ℝ) + 1))
          1
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ (q (k n)))
            ⟨
              lt_trans hClass.terminal_start.1
                (hτ (q (k n))).1.1,
              (hτ (q (k n))).1.2
            ⟩)
          (h3TerminalVelocitySpectralStateAt
            hH3
            (τ (p (k n)))
            ⟨
              lt_trans hClass.terminal_start.1
                (hτ (p (k n))).1.1,
              (hτ (p (k n))).1.2
            ⟩) := by

    intro n

    have h :=
      hControl n

    simpa only [hStrict] using
      h

  exact
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
      hControlOut,
      hNotVanishing
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
