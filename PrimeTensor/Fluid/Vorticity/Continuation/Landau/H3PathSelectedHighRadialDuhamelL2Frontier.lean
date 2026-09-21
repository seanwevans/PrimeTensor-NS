import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedHighRadialFourierL2Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Mild.Raw.Second
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.Moment.Free.Heat

/-!
# Remove the free-heat contribution from the selected radial high-L² frontier

`H3PathSelectedHighRadialFourierL2Frontier` reduced the high-diffusion branch
to

    |ξ|⁴ raw(W(q)) ∈ L²,
    |ξ|⁵ raw(W(q)) ∈ L².

A frequencywise `L∞` bound is not the correct way to prove this from arbitrary
H³ restart data: the initial Fourier representative is only an `L²` class.

The exact selected mild equation provides the correct split instead:

    raw(W(q)) = raw(H_q U₀) - raw(D(q)).

The free-heat term is automatic.  Positive heat time absorbs every finite
radial polynomial multiplier, and the initial raw Fourier amplitude is already
in `L²` by H³ deweighting.  This file proves that statement directly with the
all-orders heat multiplier theorem.

Consequently only the nonlinear Duhamel contribution remains:

    |ξ|⁴ raw(D(q)) ∈ L²,
    |ξ|⁵ raw(D(q)) ∈ L².

This is the genuine parabolic nonlinear frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedHighRadialDuhamelL2Frontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Arbitrary-order free-heat radial L² smoothing -/

private theorem h3SelectedInitialHeatRawFourier_radialWeight_memLp2
    {ν t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (ht : 0 < t)
    (j : Fin 3)
    (n : ℕ) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ n : ℝ) : ℂ) *
          (((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht j : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ))
      2
      (volume : Measure H3FourierPoint3) := by

  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier (U₀ j)

  let g : H3FourierPoint3 → ℂ :=
    fun ξ =>
      ((‖ξ‖ ^ n : ℝ) : ℂ) *
        h3SpectralScalarHeatRawRepresentative
          ν t (U₀ j) ξ

  let C : ℝ :=
    h3HeatNatMomentCoefficient n ν t

  have hBase :
      MemLp
        f
        2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SpectralScalarRawFourier_memLp2
        (U₀ j)

  have hWeightContinuous :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ n : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_norm.pow n)

  have hgMeas :
      AEStronglyMeasurable
        g
        (volume : Measure H3FourierPoint3) := by
    dsimp only [g]
    exact
      hWeightContinuous.aestronglyMeasurable.mul
        (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
          ν t (U₀ j))

  have hg :
      MemLp
        g
        2
        (volume : Measure H3FourierPoint3) := by

    refine
      hBase.of_le_mul
        (c := C)
        hgMeas
        ?_

    filter_upwards with ξ

    have hMoment :=
      h3HeatFourierMomentMultiplier_le_nat
        hν ht n ξ

    have hWeight0 :
        0 ≤ ‖ξ‖ ^ n :=
      pow_nonneg (norm_nonneg ξ) n

    dsimp only [g, f, C]

    unfold h3SpectralScalarHeatRawRepresentative

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hWeight0,
      norm_mul
    ]

    calc
      ‖ξ‖ ^ n *
          (‖h3HeatFourierSymbol ν t ξ‖ *
            ‖h3SpectralScalarRawFourier (U₀ j) ξ‖)
          =
        (‖ξ‖ ^ n *
          ‖h3HeatFourierSymbol ν t ξ‖) *
        ‖h3SpectralScalarRawFourier (U₀ j) ξ‖ := by
          ring
      _ ≤
        h3HeatNatMomentCoefficient n ν t *
          ‖h3SpectralScalarRawFourier (U₀ j) ξ‖ :=
        mul_le_mul_of_nonneg_right
          (by
            simpa only [
              h3FourierMomentWeight_natCast
            ] using hMoment)
          (norm_nonneg _)

  have hRep :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_ae_eq_heatRepresentative
      hν U₀ ht j

  have hWeightedRep :
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ n : ℝ) : ℂ) *
          (((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht j : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ))
        =ᵐ[(volume : Measure H3FourierPoint3)]
      g := by
    filter_upwards [hRep] with ξ hξ
    dsimp only [g]
    rw [hξ]

  exact
    (memLp_congr_ae hWeightedRep).2 hg

/-! ## Nonlinear Duhamel radial L² frontier -/

/--
At every strict positive selected restart time, the quotient-safe selected
Duhamel raw Fourier coordinate has fourth and fifth radial weights in `L²`.

The free heat is intentionally absent: it is automatic by the theorem above.
-/
def H3CanonicalSelectedDuhamelFourthFifthRadialRawFourierMemLp2OnRestartRadius :
    Prop :=
  ∀
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t₀ : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E),
      ∀ q : ℝ,
        q ∈
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        let U₀ : H3SpectralVelocityState :=
          h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail
        let hA : 0 < E :=
          lt_of_lt_of_le zero_lt_one hE
        let hU₀ : ‖U₀‖ ≤ E :=
          norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail
        (
          ∀ j : Fin 3,
            MemLp
              (fun ξ : H3FourierPoint3 =>
                ((‖ξ‖ ^ 4 : ℝ) : ℂ) *
                  (((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                      (t := q)
                      (one_pos : (0 : ℝ) < 1)
                      U₀ hA hU₀ j :
                    H3FourierComplexL2) :
                    H3FourierPoint3 → ℂ) ξ))
              2
              (volume : Measure H3FourierPoint3)
        )
          ∧
        (
          ∀ j : Fin 3,
            MemLp
              (fun ξ : H3FourierPoint3 =>
                ((‖ξ‖ ^ 5 : ℝ) : ℂ) *
                  (((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                      (t := q)
                      (one_pos : (0 : ℝ) < 1)
                      U₀ hA hU₀ j :
                    H3FourierComplexL2) :
                    H3FourierPoint3 → ℂ) ξ))
              2
              (volume : Measure H3FourierPoint3)
        )

/-! ## Mild assembly in weighted L² -/

private theorem h3SelectedMildRawFourier_radialWeight_memLp2_of_duhamel
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (j : Fin 3)
    (n : ℕ)
    (hDuhamel :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ n : ℝ) : ℂ) *
            (((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := t) hν U₀ hA hU₀ j :
              H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ))
        2
        (volume : Measure H3FourierPoint3)) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ n : ℝ) : ℂ) *
          (((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t j :
            H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ))
      2
      (volume : Measure H3FourierPoint3) := by

  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
      hν U₀ ht j

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t) hν U₀ hA hU₀ j

  let W : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
      hν U₀ hA hU₀ t j

  have hHeat :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ n : ℝ) : ℂ) * H ξ)
        2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SelectedInitialHeatRawFourier_radialWeight_memLp2
        hν U₀ ht j n

  have hD :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ n : ℝ) : ℂ) * D ξ)
        2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact hDuhamel

  have hDiff :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ n : ℝ) : ℂ) * H ξ
            -
          ((‖ξ‖ ^ n : ℝ) : ℂ) * D ξ)
        2
        (volume : Measure H3FourierPoint3) :=
    hHeat.sub hD

  have hRep :
      ((W : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        H ξ - D ξ) := by
    dsimp only [W, H, D]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_heat_add_duhamel
        hν U₀ hA hU₀ ht htR j

  have hWeightedRep :
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ n : ℝ) : ℂ) * W ξ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ n : ℝ) : ℂ) * H ξ
          -
        ((‖ξ‖ ^ n : ℝ) : ℂ) * D ξ) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]
    ring

  exact
    (memLp_congr_ae hWeightedRep).2 hDiff

/-! ## Duhamel high-L² closes the radial selected-state frontier -/

theorem h3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius_of_duhamel
    (hDuhamel :
      H3CanonicalSelectedDuhamelFourthFifthRadialRawFourierMemLp2OnRestartRadius) :
    H3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius := by

  intro E u T t₀ hNS ht₀ hE hTail q hq

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  have hD :=
    hDuhamel E u T t₀ hNS ht₀ hE hTail q hq

  dsimp only at hD ⊢

  constructor

  · intro j

    have hNamed :
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ 4 : ℝ) : ℂ) *
              (((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
                  (one_pos : (0 : ℝ) < 1)
                  U₀ hA hU₀ q j :
                H3FourierComplexL2) :
                H3FourierPoint3 → ℂ) ξ))
          2
          (volume : Measure H3FourierPoint3) :=
      h3SelectedMildRawFourier_radialWeight_memLp2_of_duhamel
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        hq.1 hq.2.le
        j 4
        (by
          dsimp only [U₀, hA, hU₀]
          exact hD.1 j)

    have hRep :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_rawFourier
        (t := q)
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ j

    have hAE :
        h3SelectedRawFourierFourthRadialWeight
            (W q j)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 4 : ℝ) : ℂ) *
            (((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
                (one_pos : (0 : ℝ) < 1)
                U₀ hA hU₀ q j :
              H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ)) := by
      filter_upwards [hRep] with ξ hξ
      unfold h3SelectedRawFourierFourthRadialWeight
      dsimp only [W]
      rw [← hξ]

    exact
      (memLp_congr_ae hAE).2 hNamed

  · intro j

    have hNamed :
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ 5 : ℝ) : ℂ) *
              (((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
                  (one_pos : (0 : ℝ) < 1)
                  U₀ hA hU₀ q j :
                H3FourierComplexL2) :
                H3FourierPoint3 → ℂ) ξ))
          2
          (volume : Measure H3FourierPoint3) :=
      h3SelectedMildRawFourier_radialWeight_memLp2_of_duhamel
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        hq.1 hq.2.le
        j 5
        (by
          dsimp only [U₀, hA, hU₀]
          exact hD.2 j)

    have hRep :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_rawFourier
        (t := q)
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ j

    have hAE :
        h3SelectedRawFourierFifthRadialWeight
            (W q j)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 5 : ℝ) : ℂ) *
            (((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
                (one_pos : (0 : ℝ) < 1)
                U₀ hA hU₀ q j :
              H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ)) := by
      filter_upwards [hRep] with ξ hξ
      unfold h3SelectedRawFourierFifthRadialWeight
      dsimp only [W]
      rw [← hξ]

    exact
      (memLp_congr_ae hAE).2 hNamed

/-! ## BKM closure with only nonlinear Duhamel high-L² data -/

theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_selectedDuhamelFourthFifthRadialL2_of_transportPressure_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hDuhamel :
      H3CanonicalSelectedDuhamelFourthFifthRadialRawFourierMemLp2OnRestartRadius)
    (hTP :
      H3PathEnergyClassProducesTransportPressureMemLp2)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_selectedRadialFourthFifthRawFourier_of_transportPressure_of_fullScalarEnergy
      hLow
      hDerivative
      (h3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius_of_duhamel
        hDuhamel)
      hTP
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
