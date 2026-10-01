import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Infrared.Vanishing.From.Raw.L2.Cauchy

/-!
# High-radial angular vanishing frontier for terminal raw vorticity

The infrared branch has now been reduced to zeroth-order terminal raw Fourier
velocity `L²` Cauchy control. Under that hypothesis, hypothetical nonextension
leaves only a positive-cutoff high-radial raw-vorticity obstruction.

That surviving branch still carries an angular scale tending to zero. Its
raw-vorticity mass therefore represents concentration of the one-additional-
derivative spectral quantity into shrinking equatorial cones.

This file isolates the exact compactness statement that excludes that
mechanism.

For a fixed positive radial cutoff `ρ`, high-radial angular vanishing says
that sufficiently terminal differences have arbitrarily small extended
raw-vorticity square mass in sufficiently thin equatorial bad cones.

A high-radial raw-vorticity branch is incompatible with this property: its
angular apertures tend to zero while its extended mass remains above the fixed
positive threshold

    ρ² ε² / 64.

Consequently, once terminal raw Fourier velocity `L²` Cauchy has removed the
infrared alternative, hypothetical nonextension forces failure of high-radial
angular vanishing for one complementary physical vorticity component.

No claim is made here that this angular compactness is automatic at H³.
Indeed, the raw-vorticity mass spends one additional radial derivative and is
precisely an H⁴-type terminal concentration frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Fixed-cutoff high-radial angular vanishing -/

/--
At one fixed radial cutoff `ρ`, terminal high-radial raw-vorticity mass for
component `q` vanishes uniformly in sufficiently thin equatorial bad cones.

The estimate is uniform over all sufficiently late pairs of strict
preterminal times.
-/
def H3TerminalRawVorticityHighRadialAngularVanishingAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (i q : Fin 3)
    (ρ : ℝ) : Prop :=
  ∀ δ : ℝ,
    0 < δ
      →
    ∃ κ₀ : ℝ,
      0 < κ₀
        ∧
      ∃ η : ℝ,
        0 < η
          ∧
        ∀ s t : ℝ,
          ∀ hs :
            s ∈ Set.Ioo (0 : ℝ) T,
            ∀ ht :
              t ∈ Set.Ioo (0 : ℝ) T,
              dist s T < η
                →
              dist t T < η
                →
              ∀ κ : ℝ,
                0 < κ
                  →
                κ < κ₀
                  →
                h3TerminalRawVorticityComponentBadConeHighRadialSquareMass
                    i q κ ρ
                    (h3TerminalVelocitySpectralStateAt
                      hH3 s hs)
                    (h3TerminalVelocitySpectralStateAt
                      hH3 t ht)
                  <
                ENNReal.ofReal δ

/-! ## Incompatibility with the surviving high-radial branch -/

/--
A positive-cutoff high-radial raw-vorticity branch with fixed positive mass
cannot coexist with high-radial angular vanishing at the same cutoff and
component.
-/
theorem false_of_highRadialRawBranch_of_rawVorticityHighRadialAngularVanishingAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (i q : Fin 3)
    {ε ρ : ℝ}
    (hε : 0 < ε)
    (hρ : 0 < ρ)
    (hVanishing :
      H3TerminalRawVorticityHighRadialAngularVanishingAtEndpoint
        hH3 i q ρ)
    (hBranch :
      H3TerminalHighRadialRawVorticityBranchAtCutoff
        hH3 i q ε ρ) :
    False := by

  unfold
    H3TerminalHighRadialRawVorticityBranchAtCutoff
  at hBranch

  obtain
    ⟨
      s,
      t,
      hs,
      ht,
      p,
      hPMono,
      hSTendsto,
      hTTendsto,
      hKappaTendsto,
      hMass
    ⟩ :=
    hBranch

  have hThresholdPos :
      0
        <
      ρ ^ 2 * (ε ^ 2 / 64) := by
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
      (ρ ^ 2 * (ε ^ 2 / 64))
      hThresholdPos

  have hKappaSmall :
      ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) / (((p n : ℕ) : ℝ) + 2)
          <
        κ₀ := by

    exact
      (tendsto_order.1 hKappaTendsto).2
        κ₀
        hκ₀

  have hSNear :
      ∀ᶠ n : ℕ in atTop,
        dist (s (p n)) T < η := by

    have hBall :
        Metric.ball T η ∈ 𝓝 T :=
      Metric.ball_mem_nhds
        T
        hη

    have hEventually :=
      hSTendsto.eventually
        hBall

    filter_upwards [hEventually] with n hn

    simpa only [
      Metric.mem_ball,
      dist_comm
    ] using
      hn

  have hTNear :
      ∀ᶠ n : ℕ in atTop,
        dist (t (p n)) T < η := by

    have hBall :
        Metric.ball T η ∈ 𝓝 T :=
      Metric.ball_mem_nhds
        T
        hη

    have hEventually :=
      hTTendsto.eventually
        hBall

    filter_upwards [hEventually] with n hn

    simpa only [
      Metric.mem_ball,
      dist_comm
    ] using
      hn

  obtain
    ⟨
      n,
      hnKappa,
      hnS,
      hnT
    ⟩ :=
    (
      hKappaSmall.and
        (
          hSNear.and
            hTNear
        )
    ).exists

  have hKappaPos :
      0
        <
      (1 : ℝ) / (((p n : ℕ) : ℝ) + 2) := by
    positivity

  have hUpper :
      h3TerminalRawVorticityComponentBadConeHighRadialSquareMass
          i q
          ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
          ρ
          (h3TerminalVelocitySpectralStateAt
            hH3
            (s (p n))
            (hs (p n)))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (t (p n))
            (ht (p n)))
        <
      ENNReal.ofReal
        (ρ ^ 2 * (ε ^ 2 / 64)) := by

    exact
      hSmall
        (s (p n))
        (t (p n))
        (hs (p n))
        (ht (p n))
        hnS
        hnT
        ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
        hKappaPos
        hnKappa

  have hLower :
      ENNReal.ofReal
          (ρ ^ 2 * (ε ^ 2 / 64))
        <
      h3TerminalRawVorticityComponentBadConeHighRadialSquareMass
          i q
          ((1 : ℝ) / (((p n : ℕ) : ℝ) + 2))
          ρ
          (h3TerminalVelocitySpectralStateAt
            hH3
            (s (p n))
            (hs (p n)))
          (h3TerminalVelocitySpectralStateAt
            hH3
            (t (p n))
            (ht (p n))) :=
    hMass n

  have hContradiction :
      ENNReal.ofReal
          (ρ ^ 2 * (ε ^ 2 / 64))
        <
      ENNReal.ofReal
          (ρ ^ 2 * (ε ^ 2 / 64)) :=
    hLower.trans
      hUpper

  exact
    (lt_irrefl _)
      hContradiction

/-! ## Necessary angular concentration under hypothetical nonextension -/

/--
Once terminal raw Fourier velocity `L²` Cauchy has excluded the infrared
branch, hypothetical nonextension forces one failing complementary physical
vorticity component to exhibit both:

* a positive-cutoff high-radial raw-vorticity branch; and
* failure of high-radial angular vanishing at that same cutoff.

Thus the remaining obstruction is explicitly an H⁴-type angular concentration
phenomenon.
-/
theorem exists_failing_complementary_vorticityComponent_highRadialRaw_and_not_angularVanishing_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬
        ∃
          v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension
            u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint
        hH3)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ρ : ℝ,
      0 < ρ
        ∧
      ∃ q : Fin 3,
        q ≠ i
          ∧
        ¬
          H3TerminalActualVorticityStrongH3EndpointPath
            hH3 q
          ∧
        H3TerminalHighRadialRawVorticityBranchAtCutoff
          hH3 i q ε ρ
          ∧
        ¬
          H3TerminalRawVorticityHighRadialAngularVanishingAtEndpoint
            hH3 i q ρ := by

  obtain
    ⟨
      ρ,
      hρ,
      q,
      hqNe,
      hqFail,
      hBranch
    ⟩ :=
    exists_failing_complementary_vorticityComponent_highRadialRaw_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy
      hε

  refine
    ⟨
      ρ,
      hρ,
      q,
      hqNe,
      hqFail,
      hBranch,
      ?_
    ⟩

  intro hVanishing

  exact
    false_of_highRadialRawBranch_of_rawVorticityHighRadialAngularVanishingAtEndpoint
      hH3
      i
      q
      hε
      hρ
      hVanishing
      hBranch

/-! ## Conditional continuation criterion -/

/--
If one physical vorticity component has its strong H³ endpoint, terminal raw
Fourier velocity is `L²` Cauchy, and every complementary component has
high-radial angular vanishing at every positive cutoff, then the path extends
smoothly through `T`.

This is only a reduction theorem: it does not assert that the two compactness
properties are automatic.
-/
theorem smoothContinuationExtension_of_velocityRawFourierL2Cauchy_of_rawVorticityHighRadialAngularVanishing_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint
        hH3)
    (hAngular :
      ∀ q : Fin 3,
        q ≠ i
          →
        ∀ ρ : ℝ,
          0 < ρ
            →
          H3TerminalRawVorticityHighRadialAngularVanishingAtEndpoint
            hH3 i q ρ) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension
        u v T := by

  by_contra hNoExtension

  obtain
    ⟨
      ρ,
      hρ,
      q,
      hqNe,
      hqFail,
      hBranch,
      hNotAngular
    ⟩ :=
    exists_failing_complementary_vorticityComponent_highRadialRaw_and_not_angularVanishing_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical
      hCauchy
      (ε := (1 : ℝ))
      zero_lt_one

  exact
    hNotAngular
      (
        hAngular
          q
          hqNe
          ρ
          hρ
      )

end

end Euclidean
end Bridge
end PrimeTensor
