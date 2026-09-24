import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Three.Selected.Velocity.Tail.Sixth.Radial.L2.Bound

/-!
# Uniform sixth-radial Fourier L² bound for the selected velocity

The order-three fifth-velocity continuity argument needs one locally uniform
sixth-radial Fourier `L²` ceiling.

The terminal-tail sixth-radial bound is now closed.  The other two pieces are
automatic from fixed positive heat lag:

* the selected initial heat on `q ∈ [a,b]` has lag at least `a`;
* the selected midpoint Duhamel head has lag `q/2 ≥ a/2`;
* the unweighted complete Duhamel coordinate at half time is bounded by `3A`.

We therefore package

    |ξ|⁶ H_q U₀,
    |ξ|⁶ Head(q),
    |ξ|⁶ Tail(q)

as quotient-safe Fourier `L²` states and define the compact sixth-radial mild
state directly by

    F₆(q) = H₆(q) - Head₆(q) - Tail₆(q).

Its a.e. representative is exactly `|ξ|⁶` times the selected mild raw Fourier
coordinate.  The elementary Hilbert estimate

    ‖x - y - z‖² ≤ 3 (‖x‖² + ‖y‖² + ‖z‖²)

then gives one sixth-radial norm-square ceiling on every positive compact
restart slab.

No global sixth-radial selected-velocity object is required.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderThreeSelectedVelocitySixthRadialL2CompactBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2000000

/-! ## Free heat -/

/-- Sixth-radial quotient-safe selected initial heat on a positive compact
target-time slab. -/
noncomputable def h3SelectedInitialHeatSixthRadialFourierL2OnCompact
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  h3HeatRadialFourierL2OfLowerLag
    hν ha q.property.1 6
    (h3SpectralScalarRawFourierL2 (U₀ i))

/-- The compact free-heat package is the literal sixth radial weight of the
named selected initial heat almost everywhere. -/
theorem h3SelectedInitialHeatSixthRadialFourierL2OnCompact_ae
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ((h3SelectedInitialHeatSixthRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha q i :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 6 : ℝ) : ℂ) *
        (((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
            hν U₀
            (lt_of_lt_of_le ha q.property.1)
            i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)) := by

  have hWeighted :=
    h3HeatRadialFourierL2OfLowerLag_ae
      hν ha q.property.1 6
      (h3SpectralScalarRawFourierL2 (U₀ i))

  have hRaw :=
    h3SpectralScalarRawFourierL2_ae
      (U₀ i)

  have hq0 :
      0 < (q : ℝ) :=
    lt_of_lt_of_le ha q.property.1

  have hHeat :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_ae_eq_heatRepresentative
      hν U₀ hq0 i

  unfold h3SelectedInitialHeatSixthRadialFourierL2OnCompact

  filter_upwards [hWeighted, hRaw, hHeat] with ξ hWeightedξ hRawξ hHeatξ

  rw [hWeightedξ, hHeatξ]
  unfold h3SpectralScalarHeatRawRepresentative
  rw [hRawξ]

/-- Fixed-lag sixth-radial free heat is bounded uniformly over a positive
compact target slab. -/
theorem norm_h3SelectedInitialHeatSixthRadialFourierL2OnCompact_le
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ‖h3SelectedInitialHeatSixthRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha q i‖
      ≤
    h3HeatNatMomentCoefficient 6 ν a * A := by

  have hHeat :=
    norm_h3HeatRadialFourierL2OfLowerLag_le
      hν ha q.property.1 6
      (h3SpectralScalarRawFourierL2 (U₀ i))

  have hRaw :
      ‖h3SpectralScalarRawFourierL2 (U₀ i)‖ ≤ A := by
    calc
      ‖h3SpectralScalarRawFourierL2 (U₀ i)‖
          ≤ ‖U₀ i‖ :=
        norm_h3SpectralScalarRawFourierL2_le
          (U₀ i)
      _ ≤ ‖U₀‖ :=
        h3SpectralVelocity_coordinate_norm_le U₀ i
      _ ≤ A :=
        hU₀

  have hCoeff0 :
      0 ≤ h3HeatNatMomentCoefficient 6 ν a :=
    h3HeatNatMomentCoefficient_nonneg 6 ν a

  unfold h3SelectedInitialHeatSixthRadialFourierL2OnCompact

  exact
    hHeat.trans
      (mul_le_mul_of_nonneg_left hRaw hCoeff0)

/-! ## Midpoint Duhamel head -/

/-- Sixth-radial quotient-safe selected midpoint head on a positive compact
target-time slab. -/
noncomputable def h3SelectedDuhamelHeadSixthRadialFourierL2OnCompact
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
    hν hlag0 hlag 6 Dhalf

/-- The compact sixth-radial head package is the literal sixth radial weight
of the named selected midpoint head almost everywhere. -/
theorem h3SelectedDuhamelHeadSixthRadialFourierL2OnCompact_ae
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ((h3SelectedDuhamelHeadSixthRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha q i :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 6 : ℝ) : ℂ) *
        ((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
            hν U₀ hA hU₀
            (lt_of_lt_of_le ha q.property.1)
            i : H3FourierComplexL2) ξ)) := by

  let Dhalf : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := (q : ℝ) / 2) hν U₀ hA hU₀ i

  have hq0 :
      0 < (q : ℝ) :=
    lt_of_lt_of_le ha q.property.1

  have hlag0 :
      0 < a / 2 := by
    positivity

  have hlag :
      a / 2 ≤ (q : ℝ) / 2 := by
    linarith [q.property.1]

  have hWeighted :=
    h3HeatRadialFourierL2OfLowerLag_ae
      hν hlag0 hlag 6 Dhalf

  have hHead :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heat_mul_halfDuhamelRawFourierL2
      hν U₀ hA hU₀ hq0 i

  unfold h3SelectedDuhamelHeadSixthRadialFourierL2OnCompact

  filter_upwards [hWeighted, hHead] with ξ hWeightedξ hHeadξ
  rw [hWeightedξ, hHeadξ]

/-- The sixth-radial midpoint head has one quantitative norm bound throughout
any positive compact restart slab. -/
theorem norm_h3SelectedDuhamelHeadSixthRadialFourierL2OnCompact_le
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ‖h3SelectedDuhamelHeadSixthRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha q i‖
      ≤
    h3HeatNatMomentCoefficient 6 ν (a / 2) * (3 * A) := by

  let Dhalf : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := (q : ℝ) / 2) hν U₀ hA hU₀ i

  have hq0 :
      0 < (q : ℝ) :=
    lt_of_lt_of_le ha q.property.1

  have hqR :
      (q : ℝ) ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans q.property.2 hbR.le

  have hhalf0 :
      0 < (q : ℝ) / 2 := by
    positivity

  have hhalfR :
      (q : ℝ) / 2 ≤ h3FinHeatLerayRestartRadius ν A := by
    calc
      (q : ℝ) / 2 ≤ (q : ℝ) := by
        linarith
      _ ≤ h3FinHeatLerayRestartRadius ν A :=
        hqR

  have hlag0 :
      0 < a / 2 := by
    positivity

  have hlag :
      a / 2 ≤ (q : ℝ) / 2 := by
    linarith [q.property.1]

  have hHeat :
      ‖h3HeatRadialFourierL2OfLowerLag
          hν hlag0 hlag 6 Dhalf‖
        ≤
      h3HeatNatMomentCoefficient 6 ν (a / 2) *
        ‖Dhalf‖ :=
    norm_h3HeatRadialFourierL2OfLowerLag_le
      hν hlag0 hlag 6 Dhalf

  have hD :
      ‖Dhalf‖ ≤ 3 * A := by
    dsimp only [Dhalf]
    exact
      norm_h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_le_threeA
        hν U₀ hA hU₀ hhalf0 hhalfR i

  have hCoeff0 :
      0 ≤ h3HeatNatMomentCoefficient 6 ν (a / 2) :=
    h3HeatNatMomentCoefficient_nonneg
      6 ν (a / 2)

  unfold h3SelectedDuhamelHeadSixthRadialFourierL2OnCompact

  exact
    hHeat.trans
      (mul_le_mul_of_nonneg_left hD hCoeff0)

/-! ## Compact sixth-radial mild package -/

/-- Local quotient-safe sixth-radial selected mild coordinate. -/
noncomputable def h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (q : Set.Icc a b)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  h3SelectedInitialHeatSixthRadialFourierL2OnCompact
      hν U₀ hA hU₀ ha q i
    -
  h3SelectedDuhamelHeadSixthRadialFourierL2OnCompact
      hν U₀ hA hU₀ ha q i
    -
  h3SelectedDuhamelTailSixthRadialFourierL2
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      i

/-- The local sixth-radial mild package is a.e. exactly `|ξ|⁶` times the named
selected mild raw Fourier coordinate. -/
theorem h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact_ae
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ((h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha hbR q i :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 6 : ℝ) : ℂ) *
        (((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
            hν U₀ hA hU₀ (q : ℝ) i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)) := by

  let H6 : H3FourierComplexL2 :=
    h3SelectedInitialHeatSixthRadialFourierL2OnCompact
      hν U₀ hA hU₀ ha q i

  let D6head : H3FourierComplexL2 :=
    h3SelectedDuhamelHeadSixthRadialFourierL2OnCompact
      hν U₀ hA hU₀ ha q i

  let D6tail : H3FourierComplexL2 :=
    h3SelectedDuhamelTailSixthRadialFourierL2
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      i

  let W0 : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
      hν U₀ hA hU₀ (q : ℝ) i

  let H0 : H3FourierComplexL2 :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
      hν U₀
      (lt_of_lt_of_le ha q.property.1)
      i

  let D0 : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := (q : ℝ))
      hν U₀ hA hU₀ i

  let Dh0 : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      i

  let Dt0 : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
      (t := (q : ℝ))
      hν U₀ hA hU₀ i

  have hMild :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_heat_add_duhamel
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      i

  have hDsplit :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_head_add_tail
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      i

  have hH6 :=
    h3SelectedInitialHeatSixthRadialFourierL2OnCompact_ae
      hν U₀ hA hU₀ ha q i

  have hDh6 :=
    h3SelectedDuhamelHeadSixthRadialFourierL2OnCompact_ae
      hν U₀ hA hU₀ ha q i

  have hDt6 :=
    h3SelectedDuhamelTailSixthRadialFourierL2_ae
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      i

  have hSub1 :=
    MeasureTheory.Lp.coeFn_sub H6 D6head

  have hSub2 :=
    MeasureTheory.Lp.coeFn_sub (H6 - D6head) D6tail

  unfold h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact

  filter_upwards [
    hMild,
    hDsplit,
    hH6,
    hDh6,
    hDt6,
    hSub1,
    hSub2
  ] with ξ hMildξ hDsplitξ hH6ξ hDh6ξ hDt6ξ hSub1ξ hSub2ξ

  rw [hSub2ξ]
  simp only [Pi.sub_apply] at hSub1ξ ⊢
  rw [hSub1ξ]

  rw [hH6ξ, hDh6ξ, hDt6ξ]

  change
    ((‖ξ‖ ^ 6 : ℝ) : ℂ) * H0 ξ -
        ((‖ξ‖ ^ 6 : ℝ) : ℂ) * Dh0 ξ -
        ((‖ξ‖ ^ 6 : ℝ) : ℂ) * Dt0 ξ
      =
    ((‖ξ‖ ^ 6 : ℝ) : ℂ) * W0 ξ

  rw [hMildξ, hDsplitξ]
  ring

/-! ## Uniform compact sixth-radial selected velocity bound -/

/-- One sixth-radial norm-square constant works for every selected coordinate
and every target time in a positive compact restart slab. -/
theorem exists_norm_sq_bound_h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hab : a ≤ b)
    (hbR : b < h3FinHeatLerayRestartRadius ν A) :
    ∃ B6 : ℝ,
      0 ≤ B6 ∧
      ∀ q : Set.Icc a b,
        ∀ i : Fin 3,
          ‖h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
              hν U₀ hA hU₀ ha hbR q i‖ ^ 2
            ≤
          B6 := by

  obtain ⟨BTail, hBTail0, hBTail⟩ :=
    exists_norm_sq_bound_h3SelectedDuhamelTailSixthRadialFourierL2OnCompact
      hν U₀ hA hU₀
      ha hab hbR

  let Cfree : ℝ :=
    h3HeatNatMomentCoefficient 6 ν a * A

  let Chead : ℝ :=
    h3HeatNatMomentCoefficient 6 ν (a / 2) * (3 * A)

  let B6 : ℝ :=
    3 * (Cfree ^ 2 + Chead ^ 2 + BTail)

  have hCfree0 :
      0 ≤ Cfree := by
    dsimp only [Cfree]
    exact
      mul_nonneg
        (h3HeatNatMomentCoefficient_nonneg 6 ν a)
        hA.le

  have hChead0 :
      0 ≤ Chead := by
    dsimp only [Chead]
    exact
      mul_nonneg
        (h3HeatNatMomentCoefficient_nonneg 6 ν (a / 2))
        (mul_nonneg (by norm_num) hA.le)

  have hB60 :
      0 ≤ B6 := by
    dsimp only [B6]
    positivity

  refine ⟨B6, hB60, ?_⟩

  intro q i

  let H6 : H3FourierComplexL2 :=
    h3SelectedInitialHeatSixthRadialFourierL2OnCompact
      hν U₀ hA hU₀ ha q i

  let D6head : H3FourierComplexL2 :=
    h3SelectedDuhamelHeadSixthRadialFourierL2OnCompact
      hν U₀ hA hU₀ ha q i

  let D6tail : H3FourierComplexL2 :=
    h3SelectedDuhamelTailSixthRadialFourierL2
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      i

  have hFree :
      ‖H6‖ ≤ Cfree := by
    dsimp only [H6, Cfree]
    exact
      norm_h3SelectedInitialHeatSixthRadialFourierL2OnCompact_le
        hν U₀ hA hU₀ ha q i

  have hHead :
      ‖D6head‖ ≤ Chead := by
    dsimp only [D6head, Chead]
    exact
      norm_h3SelectedDuhamelHeadSixthRadialFourierL2OnCompact_le
        hν U₀ hA hU₀ ha hbR q i

  have hTailSq :
      ‖D6tail‖ ^ 2 ≤ BTail := by
    dsimp only [D6tail]
    exact hBTail q i

  have hFreeSq :
      ‖H6‖ ^ 2 ≤ Cfree ^ 2 :=
    pow_le_pow_left₀
      (norm_nonneg H6)
      hFree
      2

  have hHeadSq :
      ‖D6head‖ ^ 2 ≤ Chead ^ 2 :=
    pow_le_pow_left₀
      (norm_nonneg D6head)
      hHead
      2

  have hNorm :
      ‖H6 - D6head - D6tail‖
        ≤
      ‖H6‖ + ‖D6head‖ + ‖D6tail‖ := by
    calc
      ‖H6 - D6head - D6tail‖
          ≤
        ‖H6 - D6head‖ + ‖D6tail‖ :=
        norm_sub_le _ _
      _ ≤
        (‖H6‖ + ‖D6head‖) + ‖D6tail‖ :=
        add_le_add
          (norm_sub_le H6 D6head)
          (le_refl ‖D6tail‖)
      _ =
        ‖H6‖ + ‖D6head‖ + ‖D6tail‖ := by
        ring

  have hNormSq :
      ‖H6 - D6head - D6tail‖ ^ 2
        ≤
      (‖H6‖ + ‖D6head‖ + ‖D6tail‖) ^ 2 :=
    pow_le_pow_left₀
      (norm_nonneg (H6 - D6head - D6tail))
      hNorm
      2

  have hThree :
      (‖H6‖ + ‖D6head‖ + ‖D6tail‖) ^ 2
        ≤
      3 *
        (‖H6‖ ^ 2 +
          ‖D6head‖ ^ 2 +
          ‖D6tail‖ ^ 2) := by
    nlinarith [
      sq_nonneg (‖H6‖ - ‖D6head‖),
      sq_nonneg (‖H6‖ - ‖D6tail‖),
      sq_nonneg (‖D6head‖ - ‖D6tail‖)
    ]

  have hPieces :
      3 *
        (‖H6‖ ^ 2 +
          ‖D6head‖ ^ 2 +
          ‖D6tail‖ ^ 2)
        ≤
      B6 := by
    dsimp only [B6]
    exact
      mul_le_mul_of_nonneg_left
        (add_le_add
          (add_le_add hFreeSq hHeadSq)
          hTailSq)
        (by norm_num)

  change
    ‖h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha hbR q i‖ ^ 2
      ≤
    B6

  unfold h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact

  exact
    hNormSq.trans
      (hThree.trans hPieces)

end

end Euclidean
end Bridge
end PrimeTensor
