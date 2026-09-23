import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderTwoSelectedVelocityDuhamelRawL2Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FifteenQuarter.Duhamel.Head.Mass

/-!
# Uniform fifth-radial L² bound for the selected Duhamel midpoint head

The exact midpoint identity in the existing Duhamel layer is

    Head(q) = H_{q/2} D(q/2).

For `q ∈ [a,b]` with `a > 0`, the heat lag satisfies

    a / 2 ≤ q / 2.

The fixed-lag heat estimate from the previous checkpoint therefore gives

    ‖ |ξ|⁵ Head_i(q) ‖₂
      ≤ C₅(ν,a/2) ‖D_i(q/2)‖₂.

The complete unweighted selected Duhamel coordinate is uniformly bounded by
`3A`, so the midpoint head has one slab-wide fifth-radial Fourier `L²` bound.

This file packages that weighted head quotient-safely and identifies it almost
everywhere with the literal fifth radial weight applied to the named head.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedVelocityHeadFifthRadialL2Bound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A.e. representative of the generic fixed-lag weighted heat package. -/
theorem h3HeatRadialFourierL2OfLowerLag_ae
    {ν τ₀ τ : ℝ}
    (hν : 0 < ν)
    (hτ₀ : 0 < τ₀)
    (hτ : τ₀ ≤ τ)
    (n : ℕ)
    (F : H3FourierComplexL2) :
    ((h3HeatRadialFourierL2OfLowerLag
        hν hτ₀ hτ n F : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ n : ℝ) : ℂ) *
        (h3HeatFourierSymbol ν τ ξ * F ξ)) := by
  unfold h3HeatRadialFourierL2OfLowerLag
  exact
    MeasureTheory.MemLp.coeFn_toLp
      (h3HeatRadialFourier_memLp2_of_lowerLag
        hν hτ₀ hτ n F)

/-- Fifth-radial quotient-safe selected midpoint head on a positive compact
target-time slab. -/
noncomputable def h3SelectedDuhamelHeadFifthRadialFourierL2OnCompact
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  let hlag0 : 0 < a / 2 := by
    positivity
  let hlag : a / 2 ≤ (q : ℝ) / 2 := by
    linarith [q.property.1]
  let Dhalf : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := (q : ℝ) / 2) hν U₀ hA hU₀ i
  h3HeatRadialFourierL2OfLowerLag
    hν hlag0 hlag 5 Dhalf

/-- The compact-slab fifth-radial head package is the literal radial weight
applied to the named selected midpoint head almost everywhere. -/
theorem h3SelectedDuhamelHeadFifthRadialFourierL2OnCompact_ae
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ((h3SelectedDuhamelHeadFifthRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha q i : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 5 : ℝ) : ℂ) *
        ((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
            hν U₀ hA hU₀
            (lt_of_lt_of_le ha q.property.1)
            i : H3FourierComplexL2) ξ)) := by

  let Dhalf : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := (q : ℝ) / 2) hν U₀ hA hU₀ i

  have hq0 : 0 < (q : ℝ) :=
    lt_of_lt_of_le ha q.property.1

  have hlag0 : 0 < a / 2 := by
    positivity

  have hlag : a / 2 ≤ (q : ℝ) / 2 := by
    linarith [q.property.1]

  have hWeighted :=
    h3HeatRadialFourierL2OfLowerLag_ae
      hν hlag0 hlag 5 Dhalf

  have hHead :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heat_mul_halfDuhamelRawFourierL2
      hν U₀ hA hU₀ hq0 i

  unfold h3SelectedDuhamelHeadFifthRadialFourierL2OnCompact

  filter_upwards [hWeighted, hHead] with ξ hWeightedξ hHeadξ
  rw [hWeightedξ, hHeadξ]

/-- The fifth-radial midpoint head has a single quantitative bound throughout
any positive compact restart slab. -/
theorem norm_h3SelectedDuhamelHeadFifthRadialFourierL2OnCompact_le
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ‖h3SelectedDuhamelHeadFifthRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha q i‖
      ≤
    h3HeatNatMomentCoefficient 5 ν (a / 2) * (3 * A) := by

  let Dhalf : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := (q : ℝ) / 2) hν U₀ hA hU₀ i

  have hq0 : 0 < (q : ℝ) :=
    lt_of_lt_of_le ha q.property.1

  have hqR :
      (q : ℝ) ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans q.property.2 hbR.le

  have hhalf0 : 0 < (q : ℝ) / 2 := by
    positivity

  have hhalfR :
      (q : ℝ) / 2 ≤ h3FinHeatLerayRestartRadius ν A := by
    calc
      (q : ℝ) / 2 ≤ (q : ℝ) := by
        linarith
      _ ≤ h3FinHeatLerayRestartRadius ν A :=
        hqR

  have hlag0 : 0 < a / 2 := by
    positivity

  have hlag : a / 2 ≤ (q : ℝ) / 2 := by
    linarith [q.property.1]

  have hHeat :
      ‖h3HeatRadialFourierL2OfLowerLag
          hν hlag0 hlag 5 Dhalf‖
        ≤
      h3HeatNatMomentCoefficient 5 ν (a / 2) *
        ‖Dhalf‖ :=
    norm_h3HeatRadialFourierL2OfLowerLag_le
      hν hlag0 hlag 5 Dhalf

  have hD :
      ‖Dhalf‖ ≤ 3 * A := by
    dsimp only [Dhalf]
    exact
      norm_h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_le_threeA
        hν U₀ hA hU₀ hhalf0 hhalfR i

  have hCoeff0 :
      0 ≤ h3HeatNatMomentCoefficient 5 ν (a / 2) := by
    exact
      h3HeatNatMomentCoefficient_nonneg
        5 ν (a / 2)

  unfold h3SelectedDuhamelHeadFifthRadialFourierL2OnCompact

  exact
    hHeat.trans
      (mul_le_mul_of_nonneg_left hD hCoeff0)

end

end Euclidean
end Bridge
end PrimeTensor
