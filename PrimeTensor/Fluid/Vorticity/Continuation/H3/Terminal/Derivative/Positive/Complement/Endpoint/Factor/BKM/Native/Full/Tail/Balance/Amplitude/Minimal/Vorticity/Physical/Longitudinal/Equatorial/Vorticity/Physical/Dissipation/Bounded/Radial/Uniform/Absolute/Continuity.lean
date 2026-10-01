import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Bounded.Radial.Weighted.Cauchy
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Bounded-radial uniform absolute continuity of physical H³ dissipation

The preceding checkpoint proves that terminal raw Fourier `L²` Cauchy control
upgrades, on every fixed bounded radial region, to terminal weighted spectral
`L²` Cauchy control.

This file turns that local Cauchy statement into the corresponding compactness
property for the one-time physical H³ dissipation density.

The mechanism is standard and invariant:

1. choose one fixed strict terminal anchor time;
2. the anchor weighted spectral square density is an integrable `L¹` function,
   hence its integral is absolutely continuous with respect to Fourier volume;
3. every sufficiently late weighted spectral state is close to the anchor in
   `L²` on the fixed radial region;
4. the elementary inequality
      |G|² ≤ 2 |G-H|² + 2 |H|²
   transfers the anchor's small-set control uniformly to the late states;
5. on `|D| < R`, the physical H³ dissipation density is bounded by
      R² |G|².

No pointwise Fourier evaluation continuity is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalDissipationBoundedRadialUniformAbsoluteContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalPhysicalDissipationBoundedRadialUniformAbsoluteContinuity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Integrability and elementary square comparison -/

theorem h3TerminalSpectralStateSquareAmplitude_integrable
    (G : H3SpectralFinVectorState) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3TerminalSpectralStateSquareAmplitude G ξ)
      volume := by

  have h0 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          norm (G 0 ξ) ^ 2)
        volume :=
    (MeasureTheory.Lp.memLp (G 0)).norm.integrable_sq

  have h1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          norm (G 1 ξ) ^ 2)
        volume :=
    (MeasureTheory.Lp.memLp (G 1)).norm.integrable_sq

  have h2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          norm (G 2 ξ) ^ 2)
        volume :=
    (MeasureTheory.Lp.memLp (G 2)).norm.integrable_sq

  unfold h3TerminalSpectralStateSquareAmplitude

  exact
    (h0.add h1).add h2

/--
The square amplitude of one state is controlled by twice its square difference
from another state plus twice the latter state's square amplitude.
-/
theorem h3TerminalSpectralStateSquareAmplitude_le_two_mul_difference_add_two_mul
    (G H : H3SpectralFinVectorState)
    (ξ : H3FourierPoint3) :
    h3TerminalSpectralStateSquareAmplitude G ξ
      ≤
    2
        *
      h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity
        G H ξ
      +
    2
        *
      h3TerminalSpectralStateSquareAmplitude H ξ := by

  have component_bound :
      ∀ j : Fin 3,
        norm (G j ξ) ^ 2
          ≤
        2 * norm (h3TerminalSpectralDifferenceAt G H j ξ) ^ 2
          +
        2 * norm (H j ξ) ^ 2 := by

    intro j

    have hRewrite :
        G j ξ
          =
        h3TerminalSpectralDifferenceAt G H j ξ
          +
        H j ξ := by
      unfold h3TerminalSpectralDifferenceAt
      ring

    have hTri :
        norm (G j ξ)
          ≤
        norm (h3TerminalSpectralDifferenceAt G H j ξ)
          +
        norm (H j ξ) := by
      rw [hRewrite]
      exact norm_add_le _ _

    have hRightNonneg :
        0 ≤
          norm (h3TerminalSpectralDifferenceAt G H j ξ)
            +
          norm (H j ξ) := by
      positivity

    have hSquare :
        norm (G j ξ) ^ 2
          ≤
        (
          norm (h3TerminalSpectralDifferenceAt G H j ξ)
            +
          norm (H j ξ)
        ) ^ 2 :=
      (sq_le_sq₀
        (norm_nonneg _)
        hRightNonneg).2
        hTri

    nlinarith [
      sq_nonneg
        (
          norm (h3TerminalSpectralDifferenceAt G H j ξ)
            -
          norm (H j ξ)
        )
    ]

  have h0 := component_bound (0 : Fin 3)
  have h1 := component_bound (1 : Fin 3)
  have h2 := component_bound (2 : Fin 3)

  unfold
    h3TerminalSpectralStateSquareAmplitude
    h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity

  linarith

/-!
## Absolute continuity for one fixed weighted spectral state
-/

/--
The square amplitude of one fixed weighted H³ spectral state has absolutely
continuous set integrals with respect to Fourier volume.
-/
theorem exists_small_volume_for_spectralStateSquareAmplitude
    (G : H3SpectralFinVectorState)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ α : ℝ≥0∞,
      0 < α
        ∧
      ∀ S : Set H3FourierPoint3,
        MeasurableSet S
          →
        volume S < α
          →
        (∫ ξ in S,
            h3TerminalSpectralStateSquareAmplitude G ξ
            ∂volume)
          <
        ε := by

  let A : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3TerminalSpectralStateSquareAmplitude G ξ

  have hAInt :
      Integrable A volume := by
    dsimp only [A]
    exact
      h3TerminalSpectralStateSquareAmplitude_integrable G

  have hAMem :
      MemLp A 1 volume :=
    memLp_one_iff_integrable.mpr
      hAInt

  have hHalf :
      0 < ε / 2 := by
    linarith

  let e : ℝ≥0∞ :=
    ENNReal.ofReal (ε / 2)

  obtain
    ⟨αReal, hαReal, hSmall⟩ :=
    hAMem.eLpNorm_indicator_le
      (p := (1 : ℝ≥0∞))
      (μ := volume)
      (by simp)
      (by simp)
      hHalf

  let α : ℝ≥0∞ :=
    ENNReal.ofReal αReal

  have hα :
      0 < α := by
    dsimp only [α]
    exact
      ENNReal.ofReal_pos.2
        hαReal

  refine
    ⟨
      α,
      hα,
      ?_
    ⟩

  intro S hS hVolume

  have hVolumeLe :
      volume S
        ≤
      ENNReal.ofReal αReal := by
    dsimp only [α] at hVolume
    exact
      le_of_lt
        hVolume

  have hIndicatorNorm :
      eLpNorm
          (S.indicator A)
          1
          volume
        ≤
      ENNReal.ofReal (ε / 2) :=
    hSmall
      S
      hS
      hVolumeLe

  have hNorm :
      eLpNorm
          A
          1
          (volume.restrict S)
        ≤
      e := by
    simpa only [
      e,
      eLpNorm_indicator_eq_eLpNorm_restrict hS
    ] using
      hIndicatorNorm

  have hAMemS :
      MemLp
        A
        1
        (volume.restrict S) :=
    hAMem.mono_measure
      Measure.restrict_le_self

  have hFormula :=
    hAMemS.eLpNorm_eq_integral_rpow_norm
      (by simp)
      (by simp)

  have hNormIntegral :
      eLpNorm
          A
          1
          (volume.restrict S)
        =
      ENNReal.ofReal
        (
          ∫ ξ : H3FourierPoint3,
            A ξ
            ∂(volume.restrict S)
        ) := by

    rw [
      hFormula
    ]

    congr 1

    simp only [
      ENNReal.toReal_one,
      inv_one,
      Real.rpow_one
    ]

    apply integral_congr_ae

    filter_upwards with ξ

    rw [
      Real.norm_eq_abs,
      abs_of_nonneg
        (h3TerminalSpectralStateSquareAmplitude_nonneg G ξ)
    ]

  rw [hNormIntegral] at hNorm

  have hRealLe :
      (∫ ξ : H3FourierPoint3,
          A ξ
          ∂(volume.restrict S))
        ≤
      ε / 2 := by

    apply
      (ENNReal.ofReal_le_ofReal_iff hHalf.le).1

    simpa only [e] using
      hNorm

  have hRealLt :
      (∫ ξ : H3FourierPoint3,
          A ξ
          ∂(volume.restrict S))
        <
      ε := by
    linarith

  simpa only [A] using
    hRealLt

/-! ## Dissipation versus weighted state on one bounded radial region -/

/--
Below radial cutoff `R`, the physical H³ dissipation density is bounded by
`R²` times the weighted spectral-state square amplitude.
-/
theorem h3TerminalSpectralDissipationSingleDensity_le_radial_sq_mul_stateSquareAmplitude
    (G : H3SpectralFinVectorState)
    {R : ℝ}
    (hR : 0 ≤ R)
    {ξ : H3FourierPoint3}
    (hξ :
      ξ ∈ h3TerminalRadialFrequencyBelow R) :
    h3TerminalSpectralDissipationSingleDensity G ξ
      ≤
    R ^ 2
      *
    h3TerminalSpectralStateSquareAmplitude G ξ := by

  have hGrad :
      h3FourierGradientMagnitude ξ < R := by
    simpa only [
      h3TerminalRadialFrequencyBelow,
      Set.mem_ofPred_eq
    ] using hξ

  have hGradNonneg :
      0 ≤ h3FourierGradientMagnitude ξ :=
    h3FourierGradientMagnitude_nonneg ξ

  have hSquare :
      (h3FourierGradientMagnitude ξ) ^ 2
        ≤
      R ^ 2 :=
    pow_le_pow_left₀
      hGradNonneg
      (le_of_lt hGrad)
      2

  rw [
    h3TerminalSpectralDissipationSingleDensity_eq_gradientMagnitude_sq_mul_stateSquareAmplitude
  ]

  exact
    mul_le_mul_of_nonneg_right
      hSquare
      (h3TerminalSpectralStateSquareAmplitude_nonneg G ξ)

/-! ## Bounded-radial uniform absolute continuity package -/

/--
Uniform absolute continuity of the physical H³ dissipation mass after
intersecting with one fixed radial cutoff.
-/
def H3TerminalPhysicalDissipationSingleTimeUniformAbsoluteContinuityBelowRadialCutoffAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R : ℝ) : Prop :=
  ∀ δ : ℝ,
    0 < δ
      →
    ∃ α : ℝ≥0∞,
      0 < α
        ∧
      ∃ η : ℝ,
        0 < η
          ∧
        ∀ t : ℝ,
          ∀ ht : t ∈ Set.Ioo a T,
            dist t T < η
              →
            ∀ S : Set H3FourierPoint3,
              MeasurableSet S
                →
              volume S < α
                →
              (∫ ξ in
                  S ∩ h3TerminalRadialFrequencyBelow R,
                  h3TerminalSpectralDissipationSingleDensity
                    (h3TerminalVelocitySpectralStateAt
                      hH3
                      t
                      ⟨
                        lt_trans hClass.terminal_start.1 ht.1,
                        ht.2
                      ⟩)
                    ξ
                  ∂volume)
                <
              δ

/--
Raw Fourier terminal `L²` Cauchy control implies uniform absolute continuity
of the physical H³ dissipation mass on every fixed positive radial cutoff.
-/
theorem physicalDissipationUniformAbsoluteContinuityBelowRadialCutoffAtEndpoint_of_velocityRawFourierL2Cauchy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    {R : ℝ}
    (hR : 0 < R) :
    H3TerminalPhysicalDissipationSingleTimeUniformAbsoluteContinuityBelowRadialCutoffAtEndpoint
      hH3 hClass R := by

  intro δ hδ

  let eps : ℝ :=
    δ / (16 * R ^ 2)

  have hR2 :
      0 < R ^ 2 := by
    positivity

  have hDen :
      0 < 16 * R ^ 2 := by
    positivity

  have hEps :
      0 < eps := by
    dsimp only [eps]
    exact div_pos hδ hDen

  have hWeighted :=
    weightedSpectralL2CauchyBelowRadialCutoffAtEndpoint_of_velocityRawFourierL2Cauchy
      hH3
      hCauchy
      hR.le

  obtain
    ⟨etaC, hetaC, hDifferenceSmall⟩ :=
    hWeighted
      eps
      hEps

  have hLower :
      max a (T - etaC) < T := by
    exact
      max_lt
        hClass.terminal_start.2
        (by linarith)

  obtain
    ⟨b, hbLower, hbT⟩ :=
    exists_between
      hLower

  have hba :
      a < b :=
    lt_of_le_of_lt
      (le_max_left a (T - etaC))
      hbLower

  have hbNear :
      dist b T < etaC := by
    have hLowerB :
        T - etaC < b :=
      lt_of_le_of_lt
        (le_max_right a (T - etaC))
        hbLower

    rw [
      Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hbT.le)
    ]

    linarith

  let hbAbs : b ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 hba,
      hbT
    ⟩

  let G0 : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3
      b
      hbAbs

  obtain
    ⟨alpha, halpha, hAnchorSmall⟩ :=
    exists_small_volume_for_spectralStateSquareAmplitude
      G0
      hEps

  refine
    ⟨
      alpha,
      halpha,
      etaC,
      hetaC,
      ?_
    ⟩

  intro t ht htNear S hS hVolume

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  let G : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3
      t
      htAbs

  let B : Set H3FourierPoint3 :=
    h3TerminalRadialFrequencyBelow R

  let P : Set H3FourierPoint3 :=
    S ∩ B

  have hBMeas :
      MeasurableSet B := by
    dsimp only [B]
    exact
      measurableSet_h3TerminalRadialFrequencyBelow R

  have hPMeas :
      MeasurableSet P := by
    dsimp only [P]
    exact
      hS.inter hBMeas

  have hPVolume :
      volume P < alpha := by
    exact
      lt_of_le_of_lt
        (measure_mono
          (by
            intro ξ hξ
            exact hξ.1))
        hVolume

  have hAnchor :
      (∫ ξ in P,
          h3TerminalSpectralStateSquareAmplitude
            G0 ξ
          ∂volume)
        <
      eps :=
    hAnchorSmall
      P
      hPMeas
      hPVolume

  have hDifference :
      h3TerminalWeightedSpectralVelocityRadialSquareDefect
          R
          G
          G0
        <
      eps := by

    dsimp only [G, G0, htAbs, hbAbs]

    exact
      hDifferenceSmall
        t
        b
        ⟨
          lt_trans hClass.terminal_start.1 ht.1,
          ht.2
        ⟩
        ⟨
          lt_trans hClass.terminal_start.1 hba,
          hbT
        ⟩
        htNear
        hbNear

  let D : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity
        G G0 ξ

  have hDInt :
      Integrable D volume := by
    dsimp only [D]
    exact
      h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity_integrable
        G G0

  have hDNonneg :
      0 ≤ᵐ[volume] D := by
    exact
      Eventually.of_forall
        (fun ξ =>
          h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity_nonneg
            G G0 ξ)

  have hPSubsetB :
      P ⊆ B := by
    intro ξ hξ
    exact hξ.2

  have hDifferenceRestricted :
      (∫ ξ in P, D ξ ∂volume)
        ≤
      h3TerminalWeightedSpectralVelocityRadialSquareDefect
        R G G0 := by

    unfold
      h3TerminalWeightedSpectralVelocityRadialSquareDefect

    apply
      setIntegral_mono_set
        hDInt.integrableOn

    · exact
        hDNonneg.filter_mono
          ae_restrict_le

    · exact
        Eventually.of_forall
          (fun ξ hξ =>
            hPSubsetB hξ)

  have hDifferenceRestrictedSmall :
      (∫ ξ in P, D ξ ∂volume)
        <
      eps :=
    lt_of_le_of_lt
      hDifferenceRestricted
      hDifference

  let A : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3TerminalSpectralStateSquareAmplitude G ξ

  let A0 : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3TerminalSpectralStateSquareAmplitude G0 ξ

  have hAInt :
      Integrable A volume := by
    dsimp only [A]
    exact
      h3TerminalSpectralStateSquareAmplitude_integrable G

  have hA0Int :
      Integrable A0 volume := by
    dsimp only [A0]
    exact
      h3TerminalSpectralStateSquareAmplitude_integrable G0

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          2 * D ξ + 2 * A0 ξ)
        volume :=
    (hDInt.const_mul 2).add
      (hA0Int.const_mul 2)

  have hAmplitudePointwise :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume.restrict P),
        A ξ
          ≤
        2 * D ξ + 2 * A0 ξ := by
    filter_upwards with ξ

    dsimp only [A, D, A0]

    exact
      h3TerminalSpectralStateSquareAmplitude_le_two_mul_difference_add_two_mul
        G G0 ξ

  have hAmplitudeIntegralLe :
      (∫ ξ in P, A ξ ∂volume)
        ≤
      ∫ ξ in P,
        (2 * D ξ + 2 * A0 ξ)
        ∂volume := by

    exact
      integral_mono_ae
        (hAInt.mono_measure Measure.restrict_le_self)
        (hMajorInt.mono_measure Measure.restrict_le_self)
        hAmplitudePointwise

  have hMajorSplit :
      (∫ ξ in P,
          (2 * D ξ + 2 * A0 ξ)
          ∂volume)
        =
      2 * (∫ ξ in P, D ξ ∂volume)
        +
      2 * (∫ ξ in P, A0 ξ ∂volume) := by

    rw [
      integral_add
        ((hDInt.const_mul 2).mono_measure Measure.restrict_le_self)
        ((hA0Int.const_mul 2).mono_measure Measure.restrict_le_self),
      integral_const_mul,
      integral_const_mul
    ]

  have hAmplitudeSmall :
      (∫ ξ in P, A ξ ∂volume)
        <
      4 * eps := by

    rw [hMajorSplit] at hAmplitudeIntegralLe

    have hAnchor' :
        (∫ ξ in P, A0 ξ ∂volume)
          <
        eps := by
      simpa only [A0] using
        hAnchor

    linarith

  let F : H3FourierPoint3 → ℝ :=
    fun ξ =>
      h3TerminalSpectralDissipationSingleDensity
        G ξ

  let M : H3FourierPoint3 → ℝ :=
    fun ξ =>
      R ^ 2 * A ξ

  have hFInt :
      Integrable F volume := by
    dsimp only [F, G, htAbs]
    simpa only using
      (h3TerminalSpectralDissipationSingleDensity_integrable
        hH3
        hClass
        ht)

  have hMInt :
      Integrable M volume := by
    dsimp only [M]
    exact
      hAInt.const_mul
        (R ^ 2)

  have hDissipationPointwise :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume.restrict P),
        F ξ ≤ M ξ := by

    rw [
      ae_restrict_iff'
        hPMeas
    ]

    filter_upwards with ξ

    intro hξP

    have hξB :
        ξ ∈ B :=
      hξP.2

    dsimp only [F, M, A, B]

    exact
      h3TerminalSpectralDissipationSingleDensity_le_radial_sq_mul_stateSquareAmplitude
        G
        hR.le
        hξB

  have hDissipationLe :
      (∫ ξ in P, F ξ ∂volume)
        ≤
      ∫ ξ in P, M ξ ∂volume := by

    exact
      integral_mono_ae
        (hFInt.mono_measure Measure.restrict_le_self)
        (hMInt.mono_measure Measure.restrict_le_self)
        hDissipationPointwise

  have hMIntegral :
      (∫ ξ in P, M ξ ∂volume)
        =
      R ^ 2 * (∫ ξ in P, A ξ ∂volume) := by

    dsimp only [M]

    rw [
      integral_const_mul
    ]

  have hDissipationSmall :
      (∫ ξ in P, F ξ ∂volume)
        <
      δ := by

    rw [hMIntegral] at hDissipationLe

    have hScaled :
        R ^ 2 * (∫ ξ in P, A ξ ∂volume)
          <
        R ^ 2 * (4 * eps) :=
      mul_lt_mul_of_pos_left
        hAmplitudeSmall
        hR2

    have hNumerical :
        R ^ 2 * (4 * eps)
          =
        δ / 4 := by
      dsimp only [eps]
      field_simp [ne_of_gt hR2]
      ring

    have hQuarter :
        δ / 4 < δ := by
      linarith

    exact
      lt_of_le_of_lt
        hDissipationLe
        (lt_trans
          (by
            simpa only [hNumerical] using
              hScaled)
          hQuarter)

  simpa only [P, B, F, G, htAbs] using
    hDissipationSmall

end

end Euclidean
end Bridge
end PrimeTensor
