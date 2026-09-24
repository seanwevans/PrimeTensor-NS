import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.Velocity.Tail.Fifth.Radial.L2.Bound

/-!
# Uniform sixth-radial Fourier L² bound for the selected Duhamel terminal tail

The order-three temporal coefficient requires continuity of fifth spatial
velocity jets.  The frequency-splitting route to that continuity needs one
locally uniform sixth-radial Fourier `L²` ceiling.

The terminal-tail part is already structurally solved at arbitrary natural
radial order: the named selected tail has

* a frequency-independent Fourier `L∞` envelope;
* every natural weighted `L¹` moment;
* arbitrary natural radial Fourier `L²` membership.

Only the compact quantitative specialization was previously recorded at order
five.  This file lifts that argument one order:

    radial L² order 6  ←  doubled L¹ moment order 12.

On an order-twelve selected moment slab the complete Duhamel state at `q` and
`q/2` both have moment mass at most `BDuhamel`.  Heat contraction preserves
the midpoint-head moment, and `Tail = Duhamel - Head` therefore has twelfth
moment mass at most `2 * BDuhamel`.  Combining that with the compact tail
`L∞` envelope gives one sixth-radial norm-square bound valid for every
coordinate and every target time in the compact slab.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderThreeSelectedVelocityTailSixthRadialL2Bound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2000000

/-! ## Quotient-safe sixth-radial tail package -/

/-- Sixth-radial quotient-safe selected terminal-tail coordinate. -/
noncomputable def h3SelectedDuhamelTailSixthRadialFourierL2
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  (h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_radialWeight_memLp2
      6 (by norm_num)
      hν U₀ hA hU₀ hq hqR i).toLp
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 6 : ℝ) : ℂ) *
        (((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := q) hν U₀ hA hU₀ i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ))

/-- The sixth-radial tail package has the literal weighted named-tail
representative almost everywhere. -/
theorem h3SelectedDuhamelTailSixthRadialFourierL2_ae
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ((h3SelectedDuhamelTailSixthRadialFourierL2
        hν U₀ hA hU₀ hq hqR i :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 6 : ℝ) : ℂ) *
        (((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := q) hν U₀ hA hU₀ i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)) := by
  unfold h3SelectedDuhamelTailSixthRadialFourierL2
  exact
    MemLp.coeFn_toLp
      (h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_radialWeight_memLp2
        6 (by norm_num)
        hν U₀ hA hU₀ hq hqR i)

/-- Exact norm-square identity for the quotient-safe sixth-radial tail
package. -/
theorem norm_sq_h3SelectedDuhamelTailSixthRadialFourierL2
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ‖h3SelectedDuhamelTailSixthRadialFourierL2
        hν U₀ hA hU₀ hq hqR i‖ ^ 2
      =
    ∫ ξ : H3FourierPoint3,
      ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) *
        (((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := q) hν U₀ hA hU₀ i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)‖ ^ 2 := by
  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [
    h3SelectedDuhamelTailSixthRadialFourierL2_ae
      hν U₀ hA hU₀ hq hqR i
  ] with ξ hξ
  rw [hξ]

/-! ## Compact tail envelope -/

/-- The explicit tail `L∞` envelope on a target `q ∈ [a,b]` is bounded by
one fixed interval `(0,b)`. -/
private theorem h3SelectedDuhamelTailFourierLinfEnvelope_le_compact_order3
    {A a b q : ℝ}
    (hA : 0 < A)
    (ha : 0 < a)
    (hq : q ∈ Set.Icc a b) :
    h3SelectedDuhamelTailFourierLinfEnvelope A q
      ≤
    h3SelectedForcingFourierLinfEnvelope A *
      (volume : Measure ℝ).real (Set.Ioo (0 : ℝ) b) := by

  have hq0 : 0 < q :=
    lt_of_lt_of_le ha hq.1

  have hSubset :
      Set.Ioo (q / 2) q ⊆ Set.Ioo (0 : ℝ) b := by
    intro s hs
    constructor
    · linarith [hs.1, hq0]
    · exact lt_of_lt_of_le hs.2 hq.2

  have hBigFinite :
      (volume : Measure ℝ) (Set.Ioo (0 : ℝ) b) < ∞ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top

  have hMeasure :
      (volume : Measure ℝ).real (Set.Ioo (q / 2) q)
        ≤
      (volume : Measure ℝ).real (Set.Ioo (0 : ℝ) b) := by
    rw [Measure.real_def, Measure.real_def]
    exact
      ENNReal.toReal_mono
        hBigFinite.ne
        (measure_mono hSubset)

  unfold h3SelectedDuhamelTailFourierLinfEnvelope

  exact
    mul_le_mul_of_nonneg_left
      hMeasure
      (h3SelectedForcingFourierLinfEnvelope_nonneg hA.le)

/-! ## Twelfth moment mass of the named tail -/

/-- On an order-twelve selected moment slab, the named terminal tail at a
target `q` has order-twelve weighted `L¹` mass at most `2 * BDuhamel`. -/
private theorem h3SelectedDuhamelTail_twelfthMoment_integral_le_twoBDuhamel
    {ν A a b q BState BDuhamel B0 : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hq : q ∈ Set.Icc a b)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (hSlab :
      H3SelectedMomentSlab
        (12 : ℝ) ν A (a / 2) b
        BState BDuhamel B0
        hν U₀ hA hU₀)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 12 *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
              (t := q) hν U₀ hA hU₀ i :
            H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    2 * BDuhamel := by

  have hq0 : 0 < q :=
    lt_of_lt_of_le ha hq.1

  have hhalf0 : 0 < q / 2 := by
    positivity

  have hhalfLe : q / 2 ≤ q := by
    linarith

  have haHalfLeQ :
      a / 2 ≤ q := by
    linarith [hq.1, ha]

  have haHalfLeHalf :
      a / 2 ≤ q / 2 := by
    linarith [hq.1]

  have hHalfLeB :
      q / 2 ≤ b := by
    exact le_trans hhalfLe hq.2

  have hSlabData := hSlab
  unfold H3SelectedMomentSlab at hSlabData
  rcases hSlabData with
    ⟨_hBS0, _hBD0, _hB00, hData⟩

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := q) hν U₀ hA hU₀ i

  let Dhalf : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := q / 2) hν U₀ hA hU₀ i

  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
      hν U₀ hA hU₀ hq0 i

  let R : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
      (t := q) hν U₀ hA hU₀ i

  have hAtQ :=
    hData q
      ⟨haHalfLeQ, hq.2⟩ i

  have hAtHalf :=
    hData (q / 2)
      ⟨haHalfLeHalf, hHalfLeB⟩ i

  dsimp only at hAtQ hAtHalf

  have hFullInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (12 : ℝ) ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact hAtQ.2.2.1

  have hFullMass :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (12 : ℝ) ξ * ‖D ξ‖)
        ≤ BDuhamel := by
    dsimp only [D]
    exact hAtQ.2.2.2.1

  have hHalfInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (12 : ℝ) ξ * ‖Dhalf ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Dhalf]
    exact hAtHalf.2.2.1

  have hHalfMass :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (12 : ℝ) ξ * ‖Dhalf ξ‖)
        ≤ BDuhamel := by
    dsimp only [Dhalf]
    exact hAtHalf.2.2.2.1

  have hHeadMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (12 : ℝ) ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_h3FourierMomentWeight
      (by norm_num : (0 : ℝ) ≤ 12)).aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable H).norm

  have hHeadRep :
      ((H : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3HeatFourierSymbol ν (q / 2) ξ * Dhalf ξ) := by
    dsimp only [H, Dhalf]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heat_mul_halfDuhamelRawFourierL2
        hν U₀ hA hU₀ hq0 i

  have hHeadInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (12 : ℝ) ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by

    refine
      Integrable.mono
        (f := fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (12 : ℝ) ξ * ‖H ξ‖)
        (g := fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (12 : ℝ) ξ * ‖Dhalf ξ‖)
        hHalfInt
        hHeadMeas
        ?_

    filter_upwards [hHeadRep] with ξ hξ

    have hWeight0 :
        0 ≤ h3FourierMomentWeight (12 : ℝ) ξ :=
      h3FourierMomentWeight_nonneg (12 : ℝ) ξ

    have hHeat :
        ‖h3HeatFourierSymbol ν (q / 2) ξ‖ ≤ 1 :=
      norm_h3HeatFourierSymbol_le_one
        hν.le hhalf0.le ξ

    have hPoint :
        h3FourierMomentWeight (12 : ℝ) ξ * ‖H ξ‖
          ≤
        h3FourierMomentWeight (12 : ℝ) ξ * ‖Dhalf ξ‖ := by
      rw [hξ, norm_mul]
      calc
        h3FourierMomentWeight (12 : ℝ) ξ *
            (‖h3HeatFourierSymbol ν (q / 2) ξ‖ * ‖Dhalf ξ‖)
            ≤
          h3FourierMomentWeight (12 : ℝ) ξ *
            (1 * ‖Dhalf ξ‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              hHeat (norm_nonneg _))
            hWeight0
        _ =
          h3FourierMomentWeight (12 : ℝ) ξ * ‖Dhalf ξ‖ := by
          ring

    have hLeft0 :
        0 ≤ h3FourierMomentWeight (12 : ℝ) ξ * ‖H ξ‖ :=
      mul_nonneg hWeight0 (norm_nonneg _)

    have hRight0 :
        0 ≤ h3FourierMomentWeight (12 : ℝ) ξ * ‖Dhalf ξ‖ :=
      mul_nonneg hWeight0 (norm_nonneg _)

    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hLeft0,
      abs_of_nonneg hRight0
    ] using hPoint

  have hHeadMass :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (12 : ℝ) ξ * ‖H ξ‖)
        ≤ BDuhamel := by
    calc
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (12 : ℝ) ξ * ‖H ξ‖)
          ≤
        ∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (12 : ℝ) ξ * ‖Dhalf ξ‖ := by
            refine integral_mono_ae hHeadInt hHalfInt ?_
            filter_upwards [hHeadRep] with ξ hξ

            have hWeight0 :
                0 ≤ h3FourierMomentWeight (12 : ℝ) ξ :=
              h3FourierMomentWeight_nonneg (12 : ℝ) ξ

            have hHeat :
                ‖h3HeatFourierSymbol ν (q / 2) ξ‖ ≤ 1 :=
              norm_h3HeatFourierSymbol_le_one
                hν.le hhalf0.le ξ

            rw [hξ, norm_mul]

            exact
              mul_le_mul_of_nonneg_left
                (by
                  calc
                    ‖h3HeatFourierSymbol ν (q / 2) ξ‖ * ‖Dhalf ξ‖
                        ≤ 1 * ‖Dhalf ξ‖ :=
                      mul_le_mul_of_nonneg_right
                        hHeat (norm_nonneg _)
                    _ = ‖Dhalf ξ‖ := by ring)
                hWeight0
      _ ≤ BDuhamel :=
        hHalfMass

  have hWeight12 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (12 : ℝ) ξ = ‖ξ‖ ^ 12 := by
    intro ξ
    have h := h3FourierMomentWeight_natCast 12 ξ
    norm_num at h ⊢
    exact h

  have hTailInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (12 : ℝ) ξ * ‖R ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [R]
    simpa only [hWeight12] using
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_natMoment_integrable
        12 (by norm_num)
        hν U₀ hA hU₀ hq0 hqR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (12 : ℝ) ξ * ‖D ξ‖ +
            h3FourierMomentWeight (12 : ℝ) ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFullInt.add hHeadInt

  have hDecomp :
      ((D : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ + R ξ) := by
    dsimp only [D, H, R]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_head_add_tail
        hν U₀ hA hU₀ hq0 i

  have hTailToMajor :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (12 : ℝ) ξ * ‖R ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierMomentWeight (12 : ℝ) ξ * ‖D ξ‖ +
          h3FourierMomentWeight (12 : ℝ) ξ * ‖H ξ‖) := by
    refine integral_mono_ae hTailInt hMajor ?_
    filter_upwards [hDecomp] with ξ hξ

    have hWeight0 :
        0 ≤ h3FourierMomentWeight (12 : ℝ) ξ :=
      h3FourierMomentWeight_nonneg (12 : ℝ) ξ

    have hR :
        R ξ = D ξ - H ξ := by
      rw [hξ]
      ring

    have hNorm :
        ‖R ξ‖ ≤ ‖D ξ‖ + ‖H ξ‖ := by
      rw [hR]
      exact norm_sub_le _ _

    calc
      h3FourierMomentWeight (12 : ℝ) ξ * ‖R ξ‖
          ≤
        h3FourierMomentWeight (12 : ℝ) ξ *
          (‖D ξ‖ + ‖H ξ‖) :=
        mul_le_mul_of_nonneg_left hNorm hWeight0
      _ =
        h3FourierMomentWeight (12 : ℝ) ξ * ‖D ξ‖ +
          h3FourierMomentWeight (12 : ℝ) ξ * ‖H ξ‖ := by
        ring

  have hGeneric :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (12 : ℝ) ξ * ‖R ξ‖)
        ≤
      2 * BDuhamel := by
    calc
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (12 : ℝ) ξ * ‖R ξ‖)
          ≤
        ∫ ξ : H3FourierPoint3,
          (h3FourierMomentWeight (12 : ℝ) ξ * ‖D ξ‖ +
            h3FourierMomentWeight (12 : ℝ) ξ * ‖H ξ‖) :=
        hTailToMajor
      _ =
        (∫ ξ : H3FourierPoint3,
            h3FourierMomentWeight (12 : ℝ) ξ * ‖D ξ‖)
          +
        (∫ ξ : H3FourierPoint3,
            h3FourierMomentWeight (12 : ℝ) ξ * ‖H ξ‖) := by
        rw [integral_add hFullInt hHeadInt]
      _ ≤ BDuhamel + BDuhamel :=
        add_le_add hFullMass hHeadMass
      _ = 2 * BDuhamel := by
        ring

  dsimp only [R] at hGeneric

  simpa only [hWeight12] using hGeneric

/-! ## Uniform compact sixth-radial selected tail bound -/

/-- One sixth-radial terminal-tail norm-square bound works simultaneously for
all coordinates and all target times in a positive compact restart slab. -/
theorem exists_norm_sq_bound_h3SelectedDuhamelTailSixthRadialFourierL2OnCompact
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
          ‖h3SelectedDuhamelTailSixthRadialFourierL2
              hν U₀ hA hU₀
              (lt_of_lt_of_le ha q.property.1)
              (le_trans q.property.2 hbR.le)
              i‖ ^ 2
            ≤
          B6 := by

  have haHalf : 0 < a / 2 := by
    positivity

  have haHalfB : a / 2 ≤ b := by
    linarith

  obtain ⟨BState, BDuhamel, B0, hSlab⟩ :=
    h3SelectedMomentSlab_nat_ge_three
      (a := a / 2)
      (t := b)
      12 (by norm_num)
      hν U₀ hA hU₀
      haHalf haHalfB hbR.le

  have hSlabData := hSlab
  unfold H3SelectedMomentSlab at hSlabData
  rcases hSlabData with
    ⟨_hBS0, hBD0, _hB00, _hData⟩

  let Lcompact : ℝ :=
    h3SelectedForcingFourierLinfEnvelope A *
      (volume : Measure ℝ).real (Set.Ioo (0 : ℝ) b)

  have hLcompact0 : 0 ≤ Lcompact := by
    dsimp only [Lcompact]
    exact
      mul_nonneg
        (h3SelectedForcingFourierLinfEnvelope_nonneg hA.le)
        (by
          rw [Measure.real_def]
          exact ENNReal.toReal_nonneg)

  let B6 : ℝ :=
    Lcompact * (2 * BDuhamel)

  have hB60 : 0 ≤ B6 := by
    dsimp only [B6]
    exact
      mul_nonneg
        hLcompact0
        (mul_nonneg (by norm_num) hBD0)

  refine ⟨B6, hB60, ?_⟩

  intro q i

  have hq0 : 0 < (q : ℝ) :=
    lt_of_lt_of_le ha q.property.1

  have hqR :
      (q : ℝ) ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans q.property.2 hbR.le

  let F : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
      (t := (q : ℝ)) hν U₀ hA hU₀ i

  have hTailMomentInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 12 * ‖F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_natMoment_integrable
        12 (by norm_num)
        hν U₀ hA hU₀ hq0 hqR i

  have hTailMomentMass :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 12 * ‖F ξ‖)
        ≤
      2 * BDuhamel := by
    dsimp only [F]
    exact
      h3SelectedDuhamelTail_twelfthMoment_integral_le_twoBDuhamel
        hν U₀ hA hU₀
        ha q.property hqR hSlab i

  have hEnvelope :
      h3SelectedDuhamelTailFourierLinfEnvelope A (q : ℝ)
        ≤ Lcompact := by
    dsimp only [Lcompact]
    exact
      h3SelectedDuhamelTailFourierLinfEnvelope_le_compact_order3
        hA ha q.property

  have hLinf :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖F ξ‖ ≤ Lcompact := by
    have hBase :=
      ae_norm_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_le_linfEnvelope
        hν U₀ hA hU₀ hq0 i
    filter_upwards [hBase] with ξ hξ
    exact hξ.trans hEnvelope

  have hWeightedMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 6 : ℝ) : ℂ) * F ξ)
        (volume : Measure H3FourierPoint3) :=
    (Complex.continuous_ofReal.comp
      (continuous_norm.pow 6)).aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable F)

  have hWeightedInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * F ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by
    have hMem :=
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_radialWeight_memLp2
        6 (by norm_num)
        hν U₀ hA hU₀ hq0 hqR i
    rw [memLp_two_iff_integrable_sq_norm hWeightedMeas] at hMem
    exact hMem

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          Lcompact * (‖ξ‖ ^ 12 * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hTailMomentInt.const_mul Lcompact

  have hIntegralBound :
      (∫ ξ : H3FourierPoint3,
          ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * F ξ‖ ^ 2)
        ≤
      ∫ ξ : H3FourierPoint3,
        Lcompact * (‖ξ‖ ^ 12 * ‖F ξ‖) := by

    refine integral_mono_ae hWeightedInt hMajorInt ?_

    filter_upwards [hLinf] with ξ hBound

    have hr0 : 0 ≤ ‖ξ‖ :=
      norm_nonneg ξ

    have hr6 : 0 ≤ ‖ξ‖ ^ 6 :=
      pow_nonneg hr0 6

    have hF0 : 0 ≤ ‖F ξ‖ :=
      norm_nonneg _

    have hPow :
        (‖ξ‖ ^ 6) ^ 2 = ‖ξ‖ ^ 12 := by
      rw [pow_two, ← pow_add]

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hr6,
      mul_pow,
      hPow
    ]

    calc
      ‖ξ‖ ^ 12 * ‖F ξ‖ ^ 2
          =
        ‖ξ‖ ^ 12 * (‖F ξ‖ * ‖F ξ‖) := by
        rw [pow_two]
      _ ≤
        ‖ξ‖ ^ 12 * (Lcompact * ‖F ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hBound hF0)
          (pow_nonneg hr0 12)
      _ =
        Lcompact * (‖ξ‖ ^ 12 * ‖F ξ‖) := by
        ring

  rw [
    norm_sq_h3SelectedDuhamelTailSixthRadialFourierL2
      hν U₀ hA hU₀ hq0 hqR i
  ]

  calc
    (∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) * F ξ‖ ^ 2)
        ≤
      ∫ ξ : H3FourierPoint3,
        Lcompact * (‖ξ‖ ^ 12 * ‖F ξ‖) :=
      hIntegralBound
    _ =
      Lcompact *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 12 * ‖F ξ‖) := by
      rw [integral_const_mul]
    _ ≤
      Lcompact * (2 * BDuhamel) :=
      mul_le_mul_of_nonneg_left
        hTailMomentMass hLcompact0
    _ =
      B6 := by
      rfl

end

end Euclidean
end Bridge
end PrimeTensor
