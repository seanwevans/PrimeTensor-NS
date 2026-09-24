import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.High.Radial.Duhamel.L2.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FifteenQuarter.Duhamel.Head.Mass

/-!
# Reduce selected high radial Duhamel L² to the terminal half-tail

The preceding frontier removed the free initial heat contribution and left

    |ξ|⁴ raw(D(q)) ∈ L²,
    |ξ|⁵ raw(D(q)) ∈ L²

for the complete selected Duhamel term.

The midpoint decomposition is

    D(q) = Head(q) + Tail(q),

and the existing restart theorem identifies the head almost everywhere as

    Head(q,ξ) = H_{q/2}(ξ) D(q/2,ξ).

Because `q/2 > 0`, positive heat time absorbs every finite radial polynomial
weight.  The half-time Duhamel state is already an unweighted Fourier `L²`
class, so the head automatically has fourth and fifth radial `L²` mass.

Thus the only genuinely singular piece is the terminal half-tail, where the
heat lag tends to zero.

After this file the nonlinear high-frequency frontier is exactly

    |ξ|⁴ Tail(q,ξ) ∈ L²,
    |ξ|⁵ Tail(q,ξ) ∈ L².
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedHighRadialDuhamelTailL2Frontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Arbitrary radial L² smoothing of a positive-lag heat multiplier -/

/--
Positive heat time sends an arbitrary Fourier `L²` amplitude into every finite
radially weighted `L²` class.
-/
private theorem h3HeatFourierSymbol_radialWeight_memLp2
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (F : H3FourierComplexL2)
    (n : ℕ) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ n : ℝ) : ℂ) *
          (h3HeatFourierSymbol ν τ ξ * F ξ))
      2
      (volume : Measure H3FourierPoint3) := by

  let C : ℝ :=
    h3HeatNatMomentCoefficient n ν τ

  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ n : ℝ) : ℂ) *
            (h3HeatFourierSymbol ν τ ξ * F ξ))
        (volume : Measure H3FourierPoint3) := by
    exact
      (Complex.continuous_ofReal.comp
        (continuous_norm.pow n)).aestronglyMeasurable.mul
        ((continuous_h3HeatFourierSymbol ν τ).aestronglyMeasurable.mul
          (MeasureTheory.Lp.aestronglyMeasurable F))

  refine
    (MeasureTheory.Lp.memLp F).of_le_mul
      (c := C)
      hMeas
      ?_

  filter_upwards with ξ

  have hMoment :=
    h3HeatFourierMomentMultiplier_le_nat
      hν hτ n ξ

  have hWeight0 :
      0 ≤ ‖ξ‖ ^ n :=
    pow_nonneg (norm_nonneg ξ) n

  dsimp only [C]

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hWeight0,
    norm_mul
  ]

  calc
    ‖ξ‖ ^ n *
        (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
        =
      (‖ξ‖ ^ n *
        ‖h3HeatFourierSymbol ν τ ξ‖) *
      ‖F ξ‖ := by
        ring
    _ ≤
      h3HeatNatMomentCoefficient n ν τ *
        ‖F ξ‖ :=
      mul_le_mul_of_nonneg_right
        (by
          simpa only [
            h3FourierMomentWeight_natCast
          ] using hMoment)
        (norm_nonneg _)

/-! ## The midpoint Duhamel head is automatically high-L² -/

/--
Every finite radial weight of the selected midpoint Duhamel head belongs to
Fourier `L²`.  Only the strict positive midpoint heat lag is used.
-/
private theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_radialWeight_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (n : ℕ) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ n : ℝ) : ℂ) *
          (((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i :
            H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ))
      2
      (volume : Measure H3FourierPoint3) := by

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t / 2)
      hν U₀ hA hU₀ i

  have hhalf :
      0 < t / 2 := by
    positivity

  have hHeat :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ n : ℝ) : ℂ) *
            (h3HeatFourierSymbol ν (t / 2) ξ * D ξ))
        2
        (volume : Measure H3FourierPoint3) :=
    h3HeatFourierSymbol_radialWeight_memLp2
      hν hhalf D n

  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heat_mul_halfDuhamelRawFourierL2
      hν U₀ hA hU₀ ht i

  have hWeighted :
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ n : ℝ) : ℂ) *
          (((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i :
            H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ))
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ n : ℝ) : ℂ) *
          (h3HeatFourierSymbol ν (t / 2) ξ * D ξ)) := by

    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  exact
    (memLp_congr_ae hWeighted).2 hHeat

/-! ## Terminal half-tail high-L² frontier -/

/--
The only remaining fourth/fifth radial `L²` datum for the nonlinear Duhamel
term is the named terminal half-tail.
-/
def H3CanonicalSelectedDuhamelTailFourthFifthRadialRawFourierMemLp2OnRestartRadius :
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
                  (((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
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
                  (((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
                      (t := q)
                      (one_pos : (0 : ℝ) < 1)
                      U₀ hA hU₀ j :
                    H3FourierComplexL2) :
                    H3FourierPoint3 → ℂ) ξ))
              2
              (volume : Measure H3FourierPoint3)
        )

/-! ## Tail high-L² closes the complete Duhamel high-L² frontier -/

theorem h3CanonicalSelectedDuhamelFourthFifthRadialRawFourierMemLp2OnRestartRadius_of_tail
    (hTailL2 :
      H3CanonicalSelectedDuhamelTailFourthFifthRadialRawFourierMemLp2OnRestartRadius) :
    H3CanonicalSelectedDuhamelFourthFifthRadialRawFourierMemLp2OnRestartRadius := by

  intro E u T t₀ hNS ht₀ hE hTail q hq

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  have hT :=
    hTailL2 E u T t₀ hNS ht₀ hE hTail q hq

  dsimp only at hT ⊢

  constructor

  · intro j

    let H : H3FourierComplexL2 :=
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ hq.1 j

    let R : H3FourierComplexL2 :=
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
        (t := q)
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ j

    let D : H3FourierComplexL2 :=
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
        (t := q)
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ j

    have hHead :
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ 4 : ℝ) : ℂ) * H ξ)
          2
          (volume : Measure H3FourierPoint3) := by
      dsimp only [H]
      exact
        h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_radialWeight_memLp2
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀ hq.1 j 4

    have hTerminal :
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ 4 : ℝ) : ℂ) * R ξ)
          2
          (volume : Measure H3FourierPoint3) := by
      dsimp only [R]
      exact hT.1 j

    have hSum :
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ 4 : ℝ) : ℂ) * H ξ
              +
            ((‖ξ‖ ^ 4 : ℝ) : ℂ) * R ξ)
          2
          (volume : Measure H3FourierPoint3) :=
      hHead.add hTerminal

    have hRep :
        ((D : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          H ξ + R ξ) := by
      dsimp only [D, H, R]
      exact
        h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_head_add_tail
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀ hq.1 j

    have hWeighted :
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 4 : ℝ) : ℂ) * D ξ)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 4 : ℝ) : ℂ) * H ξ
            +
          ((‖ξ‖ ^ 4 : ℝ) : ℂ) * R ξ) := by
      filter_upwards [hRep] with ξ hξ
      rw [hξ]
      ring

    exact
      (memLp_congr_ae hWeighted).2 hSum

  · intro j

    let H : H3FourierComplexL2 :=
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ hq.1 j

    let R : H3FourierComplexL2 :=
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
        (t := q)
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ j

    let D : H3FourierComplexL2 :=
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
        (t := q)
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ j

    have hHead :
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ 5 : ℝ) : ℂ) * H ξ)
          2
          (volume : Measure H3FourierPoint3) := by
      dsimp only [H]
      exact
        h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_radialWeight_memLp2
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀ hq.1 j 5

    have hTerminal :
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ 5 : ℝ) : ℂ) * R ξ)
          2
          (volume : Measure H3FourierPoint3) := by
      dsimp only [R]
      exact hT.2 j

    have hSum :
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ 5 : ℝ) : ℂ) * H ξ
              +
            ((‖ξ‖ ^ 5 : ℝ) : ℂ) * R ξ)
          2
          (volume : Measure H3FourierPoint3) :=
      hHead.add hTerminal

    have hRep :
        ((D : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          H ξ + R ξ) := by
      dsimp only [D, H, R]
      exact
        h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_head_add_tail
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀ hq.1 j

    have hWeighted :
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 5 : ℝ) : ℂ) * D ξ)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 5 : ℝ) : ℂ) * H ξ
            +
          ((‖ξ‖ ^ 5 : ℝ) : ℂ) * R ξ) := by
      filter_upwards [hRep] with ξ hξ
      rw [hξ]
      ring

    exact
      (memLp_congr_ae hWeighted).2 hSum

/-! ## BKM closure with only terminal-tail high-L² data -/

theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_selectedDuhamelTailFourthFifthRadialL2_of_transportPressure_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hTailL2 :
      H3CanonicalSelectedDuhamelTailFourthFifthRadialRawFourierMemLp2OnRestartRadius)
    (hTP :
      H3PathEnergyClassProducesTransportPressureMemLp2)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_selectedDuhamelFourthFifthRadialL2_of_transportPressure_of_fullScalarEnergy
      hLow
      hDerivative
      (h3CanonicalSelectedDuhamelFourthFifthRadialRawFourierMemLp2OnRestartRadius_of_tail
        hTailL2)
      hTP
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
