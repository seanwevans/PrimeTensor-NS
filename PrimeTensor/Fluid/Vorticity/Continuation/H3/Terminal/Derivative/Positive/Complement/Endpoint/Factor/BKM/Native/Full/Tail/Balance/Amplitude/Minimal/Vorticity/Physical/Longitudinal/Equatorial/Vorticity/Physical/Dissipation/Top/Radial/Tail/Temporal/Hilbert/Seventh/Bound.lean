import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Restriction
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Three.Selected.Velocity.Sixth.Radial.L2.Compact.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Duhamel.Tail.Radial.L2.Closure

/-!
# Compact seventh-radial selected velocity bound

The cutoff-independent Hilbert route requires continuity of the global
`q² û` derivative.  Its diffusion term is `q³ û`, corresponding to the
sixth Euclidean radial raw-Fourier weight.  The existing fifth-radial
continuity proof shows how to obtain continuity at one weighted order from a
uniform bound one order higher.

This file supplies exactly that next envelope: a locally uniform
seventh-radial selected velocity `L²` bound on every positive compact restart
slab.

No new smoothing mechanism is introduced.  The proof is the already-closed
sixth-radial compact argument shifted by one order:

* free heat: fixed positive lag absorbs radial order `7`;
* midpoint Duhamel head: fixed lag `q/2 ≥ a/2` absorbs order `7`;
* terminal half-tail: the arbitrary-order tail theorem gives radial `L²`
  order `7`, and the doubled weighted `L¹` moment is order `14`;
* the order-`14` selected moment slab gives a uniform tail norm-square bound;
* the three pieces assemble into the selected mild state.

The next checkpoint can therefore repeat the existing fifth→sixth
frequency-splitting continuity argument at sixth→seventh.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailSeventhBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 3000000

/-! ## Seventh-radial terminal-tail package -/

/-- Seventh-radial quotient-safe selected terminal-tail coordinate. -/
noncomputable def h3SelectedDuhamelTailSeventhRadialFourierL2
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
      7 (by norm_num)
      hν U₀ hA hU₀ hq hqR i).toLp
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 7 : ℝ) : ℂ) *
        (((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := q) hν U₀ hA hU₀ i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ))

/-- The seventh-radial tail package has the literal weighted representative. -/
theorem h3SelectedDuhamelTailSeventhRadialFourierL2_ae
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ((h3SelectedDuhamelTailSeventhRadialFourierL2
        hν U₀ hA hU₀ hq hqR i :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 7 : ℝ) : ℂ) *
        (((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := q) hν U₀ hA hU₀ i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)) := by

  unfold h3SelectedDuhamelTailSeventhRadialFourierL2

  exact
    MemLp.coeFn_toLp
      (h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_radialWeight_memLp2
        7 (by norm_num)
        hν U₀ hA hU₀ hq hqR i)

/-- Exact norm-square identity for the seventh-radial tail package. -/
theorem norm_sq_h3SelectedDuhamelTailSeventhRadialFourierL2
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ‖h3SelectedDuhamelTailSeventhRadialFourierL2
        hν U₀ hA hU₀ hq hqR i‖ ^ 2
      =
    ∫ ξ : H3FourierPoint3,
      ‖((‖ξ‖ ^ 7 : ℝ) : ℂ) *
        (((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := q) hν U₀ hA hU₀ i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)‖ ^ 2 := by

  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]

  apply integral_congr_ae

  filter_upwards [
    h3SelectedDuhamelTailSeventhRadialFourierL2_ae
      hν U₀ hA hU₀ hq hqR i
  ] with ξ hξ

  rw [hξ]

/-! ## Compact terminal-tail bound -/

/-- The explicit terminal-tail Fourier `L∞` envelope is uniformly bounded on
a compact target slab. -/
private theorem h3SelectedDuhamelTailFourierLinfEnvelope_le_compact_order4
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

/-- On an order-fourteen selected moment slab, the named terminal tail has
order-fourteen weighted `L¹` mass at most `2 * BDuhamel`. -/
private theorem h3SelectedDuhamelTail_fourteenthMoment_integral_le_twoBDuhamel
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
        (14 : ℝ) ν A (a / 2) b
        BState BDuhamel B0
        hν U₀ hA hU₀)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 14 *
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
          h3FourierMomentWeight (14 : ℝ) ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact hAtQ.2.2.1

  have hFullMass :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (14 : ℝ) ξ * ‖D ξ‖)
        ≤
      BDuhamel := by
    dsimp only [D]
    exact hAtQ.2.2.2.1

  have hHalfInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (14 : ℝ) ξ * ‖Dhalf ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Dhalf]
    exact hAtHalf.2.2.1

  have hHalfMass :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (14 : ℝ) ξ * ‖Dhalf ξ‖)
        ≤
      BDuhamel := by
    dsimp only [Dhalf]
    exact hAtHalf.2.2.2.1

  have hHeadMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (14 : ℝ) ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_h3FourierMomentWeight
      (by norm_num : (0 : ℝ) ≤ 14)).aestronglyMeasurable.mul
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
          h3FourierMomentWeight (14 : ℝ) ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by

    refine
      Integrable.mono
        (f := fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (14 : ℝ) ξ * ‖H ξ‖)
        (g := fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (14 : ℝ) ξ * ‖Dhalf ξ‖)
        hHalfInt
        hHeadMeas
        ?_

    filter_upwards [hHeadRep] with ξ hξ

    have hWeight0 :
        0 ≤ h3FourierMomentWeight (14 : ℝ) ξ :=
      h3FourierMomentWeight_nonneg (14 : ℝ) ξ

    have hHeat :
        ‖h3HeatFourierSymbol ν (q / 2) ξ‖ ≤ 1 :=
      norm_h3HeatFourierSymbol_le_one
        hν.le hhalf0.le ξ

    have hPoint :
        h3FourierMomentWeight (14 : ℝ) ξ * ‖H ξ‖
          ≤
        h3FourierMomentWeight (14 : ℝ) ξ * ‖Dhalf ξ‖ := by
      rw [hξ, norm_mul]
      exact
        mul_le_mul_of_nonneg_left
          (by
            calc
              ‖h3HeatFourierSymbol ν (q / 2) ξ‖ * ‖Dhalf ξ‖
                  ≤
                1 * ‖Dhalf ξ‖ :=
              mul_le_mul_of_nonneg_right
                hHeat (norm_nonneg _)
              _ = ‖Dhalf ξ‖ := by ring)
          hWeight0

    have hLeft0 :
        0 ≤ h3FourierMomentWeight (14 : ℝ) ξ * ‖H ξ‖ :=
      mul_nonneg hWeight0 (norm_nonneg _)

    have hRight0 :
        0 ≤ h3FourierMomentWeight (14 : ℝ) ξ * ‖Dhalf ξ‖ :=
      mul_nonneg hWeight0 (norm_nonneg _)

    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hLeft0,
      abs_of_nonneg hRight0
    ] using hPoint

  have hHeadMass :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (14 : ℝ) ξ * ‖H ξ‖)
        ≤
      BDuhamel := by
    calc
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (14 : ℝ) ξ * ‖H ξ‖)
          ≤
        ∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (14 : ℝ) ξ * ‖Dhalf ξ‖ := by
            refine integral_mono_ae hHeadInt hHalfInt ?_
            filter_upwards [hHeadRep] with ξ hξ

            have hWeight0 :
                0 ≤ h3FourierMomentWeight (14 : ℝ) ξ :=
              h3FourierMomentWeight_nonneg (14 : ℝ) ξ

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

  have hWeight14 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (14 : ℝ) ξ = ‖ξ‖ ^ 14 := by
    intro ξ
    have h := h3FourierMomentWeight_natCast 14 ξ
    norm_num at h ⊢
    exact h

  have hTailInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (14 : ℝ) ξ * ‖R ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [R]
    simpa only [hWeight14] using
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_natMoment_integrable
        14 (by norm_num)
        hν U₀ hA hU₀ hq0 hqR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (14 : ℝ) ξ * ‖D ξ‖ +
            h3FourierMomentWeight (14 : ℝ) ξ * ‖H ξ‖)
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
          h3FourierMomentWeight (14 : ℝ) ξ * ‖R ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierMomentWeight (14 : ℝ) ξ * ‖D ξ‖ +
          h3FourierMomentWeight (14 : ℝ) ξ * ‖H ξ‖) := by

    refine integral_mono_ae hTailInt hMajor ?_

    filter_upwards [hDecomp] with ξ hξ

    have hWeight0 :
        0 ≤ h3FourierMomentWeight (14 : ℝ) ξ :=
      h3FourierMomentWeight_nonneg (14 : ℝ) ξ

    have hR :
        R ξ = D ξ - H ξ := by
      rw [hξ]
      ring

    have hNorm :
        ‖R ξ‖ ≤ ‖D ξ‖ + ‖H ξ‖ := by
      rw [hR]
      exact norm_sub_le _ _

    calc
      h3FourierMomentWeight (14 : ℝ) ξ * ‖R ξ‖
          ≤
        h3FourierMomentWeight (14 : ℝ) ξ *
          (‖D ξ‖ + ‖H ξ‖) :=
        mul_le_mul_of_nonneg_left hNorm hWeight0
      _ =
        h3FourierMomentWeight (14 : ℝ) ξ * ‖D ξ‖ +
          h3FourierMomentWeight (14 : ℝ) ξ * ‖H ξ‖ := by
        ring

  have hGeneric :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (14 : ℝ) ξ * ‖R ξ‖)
        ≤
      2 * BDuhamel := by
    calc
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (14 : ℝ) ξ * ‖R ξ‖)
          ≤
        ∫ ξ : H3FourierPoint3,
          (h3FourierMomentWeight (14 : ℝ) ξ * ‖D ξ‖ +
            h3FourierMomentWeight (14 : ℝ) ξ * ‖H ξ‖) :=
        hTailToMajor
      _ =
        (∫ ξ : H3FourierPoint3,
            h3FourierMomentWeight (14 : ℝ) ξ * ‖D ξ‖)
          +
        (∫ ξ : H3FourierPoint3,
            h3FourierMomentWeight (14 : ℝ) ξ * ‖H ξ‖) := by
        rw [integral_add hFullInt hHeadInt]
      _ ≤ BDuhamel + BDuhamel :=
        add_le_add hFullMass hHeadMass
      _ = 2 * BDuhamel := by
        ring

  dsimp only [R] at hGeneric

  simpa only [hWeight14] using hGeneric

/-- One seventh-radial terminal-tail norm-square bound works simultaneously on
every positive compact restart slab. -/
theorem exists_norm_sq_bound_h3SelectedDuhamelTailSeventhRadialFourierL2OnCompact
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hab : a ≤ b)
    (hbR : b < h3FinHeatLerayRestartRadius ν A) :
    ∃ B7 : ℝ,
      0 ≤ B7 ∧
      ∀ q : Set.Icc a b,
        ∀ i : Fin 3,
          ‖h3SelectedDuhamelTailSeventhRadialFourierL2
              hν U₀ hA hU₀
              (lt_of_lt_of_le ha q.property.1)
              (le_trans q.property.2 hbR.le)
              i‖ ^ 2
            ≤
          B7 := by

  have haHalf : 0 < a / 2 := by
    positivity

  have haHalfB : a / 2 ≤ b := by
    linarith

  obtain ⟨BState, BDuhamel, B0, hSlab⟩ :=
    h3SelectedMomentSlab_nat_ge_three
      (a := a / 2)
      (t := b)
      14 (by norm_num)
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

  let B7 : ℝ :=
    Lcompact * (2 * BDuhamel)

  have hB70 : 0 ≤ B7 := by
    dsimp only [B7]
    exact
      mul_nonneg
        hLcompact0
        (mul_nonneg (by norm_num) hBD0)

  refine ⟨B7, hB70, ?_⟩

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
          ‖ξ‖ ^ 14 * ‖F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_natMoment_integrable
        14 (by norm_num)
        hν U₀ hA hU₀ hq0 hqR i

  have hTailMomentMass :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 14 * ‖F ξ‖)
        ≤
      2 * BDuhamel := by
    dsimp only [F]
    exact
      h3SelectedDuhamelTail_fourteenthMoment_integral_le_twoBDuhamel
        hν U₀ hA hU₀
        ha q.property hqR hSlab i

  have hEnvelope :
      h3SelectedDuhamelTailFourierLinfEnvelope A (q : ℝ)
        ≤ Lcompact := by
    dsimp only [Lcompact]
    exact
      h3SelectedDuhamelTailFourierLinfEnvelope_le_compact_order4
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
          ((‖ξ‖ ^ 7 : ℝ) : ℂ) * F ξ)
        (volume : Measure H3FourierPoint3) :=
    (Complex.continuous_ofReal.comp
      (continuous_norm.pow 7)).aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable F)

  have hWeightedInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ 7 : ℝ) : ℂ) * F ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by
    have hMem :=
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_radialWeight_memLp2
        7 (by norm_num)
        hν U₀ hA hU₀ hq0 hqR i
    rw [memLp_two_iff_integrable_sq_norm hWeightedMeas] at hMem
    exact hMem

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          Lcompact * (‖ξ‖ ^ 14 * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hTailMomentInt.const_mul Lcompact

  have hIntegralBound :
      (∫ ξ : H3FourierPoint3,
          ‖((‖ξ‖ ^ 7 : ℝ) : ℂ) * F ξ‖ ^ 2)
        ≤
      ∫ ξ : H3FourierPoint3,
        Lcompact * (‖ξ‖ ^ 14 * ‖F ξ‖) := by

    refine integral_mono_ae hWeightedInt hMajorInt ?_

    filter_upwards [hLinf] with ξ hBound

    have hr0 : 0 ≤ ‖ξ‖ :=
      norm_nonneg ξ

    have hr7 : 0 ≤ ‖ξ‖ ^ 7 :=
      pow_nonneg hr0 7

    have hF0 : 0 ≤ ‖F ξ‖ :=
      norm_nonneg _

    have hPow :
        (‖ξ‖ ^ 7) ^ 2 = ‖ξ‖ ^ 14 := by
      rw [pow_two, ← pow_add]

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hr7,
      mul_pow,
      hPow
    ]

    calc
      ‖ξ‖ ^ 14 * ‖F ξ‖ ^ 2
          =
        ‖ξ‖ ^ 14 * (‖F ξ‖ * ‖F ξ‖) := by
        rw [pow_two]
      _ ≤
        ‖ξ‖ ^ 14 * (Lcompact * ‖F ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hBound hF0)
          (pow_nonneg hr0 14)
      _ =
        Lcompact * (‖ξ‖ ^ 14 * ‖F ξ‖) := by
        ring

  rw [
    norm_sq_h3SelectedDuhamelTailSeventhRadialFourierL2
      hν U₀ hA hU₀ hq0 hqR i
  ]

  calc
    (∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ 7 : ℝ) : ℂ) * F ξ‖ ^ 2)
        ≤
      ∫ ξ : H3FourierPoint3,
        Lcompact * (‖ξ‖ ^ 14 * ‖F ξ‖) :=
      hIntegralBound
    _ =
      Lcompact *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 14 * ‖F ξ‖) := by
      rw [integral_const_mul]
    _ ≤
      Lcompact * (2 * BDuhamel) :=
      mul_le_mul_of_nonneg_left
        hTailMomentMass hLcompact0
    _ =
      B7 := by
      rfl

/-! ## Free heat and midpoint head -/

/-- Seventh-radial selected initial heat on a positive compact slab. -/
noncomputable def h3SelectedInitialHeatSeventhRadialFourierL2OnCompact
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
    hν ha q.property.1 7
    (h3SpectralScalarRawFourierL2 (U₀ i))

theorem h3SelectedInitialHeatSeventhRadialFourierL2OnCompact_ae
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ((h3SelectedInitialHeatSeventhRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha q i :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 7 : ℝ) : ℂ) *
        (((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
            hν U₀
            (lt_of_lt_of_le ha q.property.1)
            i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)) := by

  have hWeighted :=
    h3HeatRadialFourierL2OfLowerLag_ae
      hν ha q.property.1 7
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

  unfold h3SelectedInitialHeatSeventhRadialFourierL2OnCompact

  filter_upwards [hWeighted, hRaw, hHeat] with ξ hWeightedξ hRawξ hHeatξ

  rw [hWeightedξ, hHeatξ]
  unfold h3SpectralScalarHeatRawRepresentative
  rw [hRawξ]

theorem norm_h3SelectedInitialHeatSeventhRadialFourierL2OnCompact_le
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ‖h3SelectedInitialHeatSeventhRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha q i‖
      ≤
    h3HeatNatMomentCoefficient 7 ν a * A := by

  have hHeat :=
    norm_h3HeatRadialFourierL2OfLowerLag_le
      hν ha q.property.1 7
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
      0 ≤ h3HeatNatMomentCoefficient 7 ν a :=
    h3HeatNatMomentCoefficient_nonneg 7 ν a

  unfold h3SelectedInitialHeatSeventhRadialFourierL2OnCompact

  exact
    hHeat.trans
      (mul_le_mul_of_nonneg_left hRaw hCoeff0)

/-- Seventh-radial selected midpoint Duhamel head on a positive compact slab. -/
noncomputable def h3SelectedDuhamelHeadSeventhRadialFourierL2OnCompact
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
    hν hlag0 hlag 7 Dhalf

theorem h3SelectedDuhamelHeadSeventhRadialFourierL2OnCompact_ae
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ((h3SelectedDuhamelHeadSeventhRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha q i :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 7 : ℝ) : ℂ) *
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
      hν hlag0 hlag 7 Dhalf

  have hHead :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heat_mul_halfDuhamelRawFourierL2
      hν U₀ hA hU₀ hq0 i

  unfold h3SelectedDuhamelHeadSeventhRadialFourierL2OnCompact

  filter_upwards [hWeighted, hHead] with ξ hWeightedξ hHeadξ

  rw [hWeightedξ, hHeadξ]

theorem norm_h3SelectedDuhamelHeadSeventhRadialFourierL2OnCompact_le
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ‖h3SelectedDuhamelHeadSeventhRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha q i‖
      ≤
    h3HeatNatMomentCoefficient 7 ν (a / 2) * (3 * A) := by

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
          hν hlag0 hlag 7 Dhalf‖
        ≤
      h3HeatNatMomentCoefficient 7 ν (a / 2) *
        ‖Dhalf‖ :=
    norm_h3HeatRadialFourierL2OfLowerLag_le
      hν hlag0 hlag 7 Dhalf

  have hD :
      ‖Dhalf‖ ≤ 3 * A := by
    dsimp only [Dhalf]
    exact
      norm_h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_le_threeA
        hν U₀ hA hU₀ hhalf0 hhalfR i

  have hCoeff0 :
      0 ≤ h3HeatNatMomentCoefficient 7 ν (a / 2) :=
    h3HeatNatMomentCoefficient_nonneg 7 ν (a / 2)

  unfold h3SelectedDuhamelHeadSeventhRadialFourierL2OnCompact

  exact
    hHeat.trans
      (mul_le_mul_of_nonneg_left hD hCoeff0)

/-! ## Compact seventh-radial selected mild state -/

/-- Local quotient-safe seventh-radial selected mild coordinate. -/
noncomputable def h3PreterminalSelectedVelocitySeventhRadialFourierL2OnCompact
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
  h3SelectedInitialHeatSeventhRadialFourierL2OnCompact
      hν U₀ hA hU₀ ha q i
    -
  h3SelectedDuhamelHeadSeventhRadialFourierL2OnCompact
      hν U₀ hA hU₀ ha q i
    -
  h3SelectedDuhamelTailSeventhRadialFourierL2
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      i

/-- The local seventh-radial mild package is a.e. exactly `|ξ|⁷` times the
selected mild raw Fourier coordinate. -/
theorem h3PreterminalSelectedVelocitySeventhRadialFourierL2OnCompact_ae
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ((h3PreterminalSelectedVelocitySeventhRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha hbR q i :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 7 : ℝ) : ℂ) *
        (((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
            hν U₀ hA hU₀ (q : ℝ) i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)) := by

  let H7 : H3FourierComplexL2 :=
    h3SelectedInitialHeatSeventhRadialFourierL2OnCompact
      hν U₀ hA hU₀ ha q i

  let D7head : H3FourierComplexL2 :=
    h3SelectedDuhamelHeadSeventhRadialFourierL2OnCompact
      hν U₀ hA hU₀ ha q i

  let D7tail : H3FourierComplexL2 :=
    h3SelectedDuhamelTailSeventhRadialFourierL2
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

  have hH7 :=
    h3SelectedInitialHeatSeventhRadialFourierL2OnCompact_ae
      hν U₀ hA hU₀ ha q i

  have hDh7 :=
    h3SelectedDuhamelHeadSeventhRadialFourierL2OnCompact_ae
      hν U₀ hA hU₀ ha q i

  have hDt7 :=
    h3SelectedDuhamelTailSeventhRadialFourierL2_ae
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      i

  have hSub1 :=
    MeasureTheory.Lp.coeFn_sub H7 D7head

  have hSub2 :=
    MeasureTheory.Lp.coeFn_sub (H7 - D7head) D7tail

  unfold h3PreterminalSelectedVelocitySeventhRadialFourierL2OnCompact

  filter_upwards [
    hMild,
    hDsplit,
    hH7,
    hDh7,
    hDt7,
    hSub1,
    hSub2
  ] with ξ hMildξ hDsplitξ hH7ξ hDh7ξ hDt7ξ hSub1ξ hSub2ξ

  rw [hSub2ξ]
  simp only [Pi.sub_apply] at hSub1ξ ⊢
  rw [hSub1ξ]

  rw [hH7ξ, hDh7ξ, hDt7ξ]

  change
    ((‖ξ‖ ^ 7 : ℝ) : ℂ) * H0 ξ -
        ((‖ξ‖ ^ 7 : ℝ) : ℂ) * Dh0 ξ -
        ((‖ξ‖ ^ 7 : ℝ) : ℂ) * Dt0 ξ
      =
    ((‖ξ‖ ^ 7 : ℝ) : ℂ) * W0 ξ

  rw [hMildξ, hDsplitξ]
  ring

/-- One seventh-radial norm-square constant works for every selected coordinate
and target time in a positive compact restart slab. -/
theorem exists_norm_sq_bound_h3PreterminalSelectedVelocitySeventhRadialFourierL2OnCompact
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hab : a ≤ b)
    (hbR : b < h3FinHeatLerayRestartRadius ν A) :
    ∃ B7 : ℝ,
      0 ≤ B7 ∧
      ∀ q : Set.Icc a b,
        ∀ i : Fin 3,
          ‖h3PreterminalSelectedVelocitySeventhRadialFourierL2OnCompact
              hν U₀ hA hU₀ ha hbR q i‖ ^ 2
            ≤
          B7 := by

  obtain ⟨BTail, hBTail0, hBTail⟩ :=
    exists_norm_sq_bound_h3SelectedDuhamelTailSeventhRadialFourierL2OnCompact
      hν U₀ hA hU₀
      ha hab hbR

  let Cfree : ℝ :=
    h3HeatNatMomentCoefficient 7 ν a * A

  let Chead : ℝ :=
    h3HeatNatMomentCoefficient 7 ν (a / 2) * (3 * A)

  let B7 : ℝ :=
    3 * (Cfree ^ 2 + Chead ^ 2 + BTail)

  have hCfree0 :
      0 ≤ Cfree := by
    dsimp only [Cfree]
    exact
      mul_nonneg
        (h3HeatNatMomentCoefficient_nonneg 7 ν a)
        hA.le

  have hChead0 :
      0 ≤ Chead := by
    dsimp only [Chead]
    exact
      mul_nonneg
        (h3HeatNatMomentCoefficient_nonneg 7 ν (a / 2))
        (mul_nonneg (by norm_num) hA.le)

  have hB70 :
      0 ≤ B7 := by
    dsimp only [B7]
    positivity

  refine ⟨B7, hB70, ?_⟩

  intro q i

  let H7 : H3FourierComplexL2 :=
    h3SelectedInitialHeatSeventhRadialFourierL2OnCompact
      hν U₀ hA hU₀ ha q i

  let D7head : H3FourierComplexL2 :=
    h3SelectedDuhamelHeadSeventhRadialFourierL2OnCompact
      hν U₀ hA hU₀ ha q i

  let D7tail : H3FourierComplexL2 :=
    h3SelectedDuhamelTailSeventhRadialFourierL2
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      i

  have hFree :
      ‖H7‖ ≤ Cfree := by
    dsimp only [H7, Cfree]
    exact
      norm_h3SelectedInitialHeatSeventhRadialFourierL2OnCompact_le
        hν U₀ hA hU₀ ha q i

  have hHead :
      ‖D7head‖ ≤ Chead := by
    dsimp only [D7head, Chead]
    exact
      norm_h3SelectedDuhamelHeadSeventhRadialFourierL2OnCompact_le
        hν U₀ hA hU₀ ha hbR q i

  have hTailSq :
      ‖D7tail‖ ^ 2 ≤ BTail := by
    dsimp only [D7tail]
    exact hBTail q i

  have hFreeSq :
      ‖H7‖ ^ 2 ≤ Cfree ^ 2 :=
    pow_le_pow_left₀
      (norm_nonneg H7)
      hFree
      2

  have hHeadSq :
      ‖D7head‖ ^ 2 ≤ Chead ^ 2 :=
    pow_le_pow_left₀
      (norm_nonneg D7head)
      hHead
      2

  have hNorm :
      ‖H7 - D7head - D7tail‖
        ≤
      ‖H7‖ + ‖D7head‖ + ‖D7tail‖ := by
    calc
      ‖H7 - D7head - D7tail‖
          ≤
        ‖H7 - D7head‖ + ‖D7tail‖ :=
        norm_sub_le _ _
      _ ≤
        (‖H7‖ + ‖D7head‖) + ‖D7tail‖ :=
        add_le_add
          (norm_sub_le H7 D7head)
          (le_refl ‖D7tail‖)
      _ =
        ‖H7‖ + ‖D7head‖ + ‖D7tail‖ := by
        ring

  have hNormSq :
      ‖H7 - D7head - D7tail‖ ^ 2
        ≤
      (‖H7‖ + ‖D7head‖ + ‖D7tail‖) ^ 2 :=
    pow_le_pow_left₀
      (norm_nonneg (H7 - D7head - D7tail))
      hNorm
      2

  have hThree :
      (‖H7‖ + ‖D7head‖ + ‖D7tail‖) ^ 2
        ≤
      3 *
        (‖H7‖ ^ 2 +
          ‖D7head‖ ^ 2 +
          ‖D7tail‖ ^ 2) := by
    nlinarith [
      sq_nonneg (‖H7‖ - ‖D7head‖),
      sq_nonneg (‖H7‖ - ‖D7tail‖),
      sq_nonneg (‖D7head‖ - ‖D7tail‖)
    ]

  have hPieces :
      3 *
        (‖H7‖ ^ 2 +
          ‖D7head‖ ^ 2 +
          ‖D7tail‖ ^ 2)
        ≤
      B7 := by
    dsimp only [B7]
    exact
      mul_le_mul_of_nonneg_left
        (add_le_add
          (add_le_add hFreeSq hHeadSq)
          hTailSq)
        (by norm_num)

  change
    ‖h3PreterminalSelectedVelocitySeventhRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha hbR q i‖ ^ 2
      ≤
    B7

  unfold h3PreterminalSelectedVelocitySeventhRadialFourierL2OnCompact

  exact
    hNormSq.trans
      (hThree.trans hPieces)

end

end Euclidean
end Bridge
end PrimeTensor
