import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial

/-!
# Order-generic compact selected velocity radial Fourier L² bound

`Hilbert.Radial` packages the selected mild velocity state at every natural
radial order `m ≥ 2`.  The remaining continuity argument needs more than
pointwise-in-time membership: it needs one norm-square ceiling valid
simultaneously on a positive compact restart slab.

The old order-five, order-six, and order-seven proofs all use the same
mechanism.  This file extracts that mechanism once.

For the terminal-half Duhamel tail:

* the compact Fourier `L∞` envelope is independent of radial order;
* the order-`2m` selected moment slab bounds the tail's weighted `L¹` mass;
* therefore
      ∫ |ξ|^(2m) |Tail|²
    ≤ L∞ ∫ |ξ|^(2m) |Tail|,
  which gives a common order-`m` weighted `L²` norm-square bound.

The free heat and midpoint Duhamel head already have generic compact norm
bounds in `Hilbert.Radial`.  The three pieces then assemble into a generic
selected-velocity bound.

The final specialization at `m = 9` is the exact envelope needed for the next
frequency-splitting checkpoint proving continuity of the eighth-radial state.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalGenericVelocityRadialBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 3500000

/-! ## Generic terminal-tail norm identity -/

/--
The generic radial tail package has the expected weighted Fourier norm-square.
-/
theorem norm_sq_h3SelectedDuhamelTailNatRadialFourierL2
    (m : ℕ)
    (hm : 2 ≤ m)
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ‖h3SelectedDuhamelTailNatRadialFourierL2
        m hm hν U₀ hA hU₀ hq hqR i‖ ^ 2
      =
    ∫ ξ : H3FourierPoint3,
      ‖((‖ξ‖ ^ m : ℝ) : ℂ) *
        (((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := q) hν U₀ hA hU₀ i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)‖ ^ 2 := by

  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]

  apply integral_congr_ae

  filter_upwards [
    h3SelectedDuhamelTailNatRadialFourierL2_ae
      m hm hν U₀ hA hU₀ hq hqR i
  ] with ξ hξ

  rw [hξ]

/-! ## Compact terminal-tail envelope -/

/--
The explicit terminal-tail Fourier `L∞` envelope is uniformly bounded on a
compact target slab.  This estimate is independent of radial order.
-/
private theorem h3SelectedDuhamelTailFourierLinfEnvelope_le_compact_generic
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

/-! ## Generic doubled-moment tail mass -/

/--
On an order-`n` selected moment slab, with `n ≥ 3`, the named terminal tail
has order-`n` weighted `L¹` mass at most `2 * BDuhamel`.

This is the order-generic form of the old order-ten, order-twelve, and
order-fourteen tail estimates.
-/
private theorem h3SelectedDuhamelTail_natMoment_integral_le_twoBDuhamel
    (n : ℕ)
    (hn : 3 ≤ n)
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
        (n : ℝ) ν A (a / 2) b
        BState BDuhamel B0
        hν U₀ hA hU₀)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ n *
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
          h3FourierMomentWeight (n : ℝ) ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact hAtQ.2.2.1

  have hFullMass :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (n : ℝ) ξ * ‖D ξ‖)
        ≤
      BDuhamel := by
    dsimp only [D]
    exact hAtQ.2.2.2.1

  have hHalfInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (n : ℝ) ξ * ‖Dhalf ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Dhalf]
    exact hAtHalf.2.2.1

  have hHalfMass :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (n : ℝ) ξ * ‖Dhalf ξ‖)
        ≤
      BDuhamel := by
    dsimp only [Dhalf]
    exact hAtHalf.2.2.2.1

  have hWeightNonneg :
      ∀ ξ : H3FourierPoint3,
        0 ≤ h3FourierMomentWeight (n : ℝ) ξ := by
    intro ξ
    exact
      h3FourierMomentWeight_nonneg
        (n : ℝ) ξ

  have hHeadMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (n : ℝ) ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_h3FourierMomentWeight
      (Nat.cast_nonneg n)).aestronglyMeasurable.mul
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
          h3FourierMomentWeight (n : ℝ) ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by

    refine
      Integrable.mono
        (f := fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (n : ℝ) ξ * ‖H ξ‖)
        (g := fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (n : ℝ) ξ * ‖Dhalf ξ‖)
        hHalfInt
        hHeadMeas
        ?_

    filter_upwards [hHeadRep] with ξ hξ

    have hWeight0 :
        0 ≤ h3FourierMomentWeight (n : ℝ) ξ :=
      hWeightNonneg ξ

    have hHeat :
        ‖h3HeatFourierSymbol ν (q / 2) ξ‖ ≤ 1 :=
      norm_h3HeatFourierSymbol_le_one
        hν.le hhalf0.le ξ

    have hPoint :
        h3FourierMomentWeight (n : ℝ) ξ * ‖H ξ‖
          ≤
        h3FourierMomentWeight (n : ℝ) ξ * ‖Dhalf ξ‖ := by
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
        0 ≤ h3FourierMomentWeight (n : ℝ) ξ * ‖H ξ‖ :=
      mul_nonneg hWeight0 (norm_nonneg _)

    have hRight0 :
        0 ≤ h3FourierMomentWeight (n : ℝ) ξ * ‖Dhalf ξ‖ :=
      mul_nonneg hWeight0 (norm_nonneg _)

    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hLeft0,
      abs_of_nonneg hRight0
    ] using hPoint

  have hHeadMass :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (n : ℝ) ξ * ‖H ξ‖)
        ≤
      BDuhamel := by
    calc
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (n : ℝ) ξ * ‖H ξ‖)
          ≤
        ∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (n : ℝ) ξ * ‖Dhalf ξ‖ := by
            refine integral_mono_ae hHeadInt hHalfInt ?_
            filter_upwards [hHeadRep] with ξ hξ

            have hWeight0 :
                0 ≤ h3FourierMomentWeight (n : ℝ) ξ :=
              hWeightNonneg ξ

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
                        ≤
                      1 * ‖Dhalf ξ‖ :=
                      mul_le_mul_of_nonneg_right
                        hHeat (norm_nonneg _)
                    _ = ‖Dhalf ξ‖ := by ring)
                hWeight0
      _ ≤
        BDuhamel :=
        hHalfMass

  have hWeightNat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (n : ℝ) ξ = ‖ξ‖ ^ n := by
    intro ξ
    exact
      h3FourierMomentWeight_natCast n ξ

  have hTailInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (n : ℝ) ξ * ‖R ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [R]
    simpa only [hWeightNat] using
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_natMoment_integrable
        n hn
        hν U₀ hA hU₀ hq0 hqR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (n : ℝ) ξ * ‖D ξ‖ +
            h3FourierMomentWeight (n : ℝ) ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFullInt.add hHeadInt

  have hDecomp :
      ((D : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        H ξ + R ξ) := by
    dsimp only [D, H, R]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_head_add_tail
        hν U₀ hA hU₀ hq0 i

  have hTailToMajor :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (n : ℝ) ξ * ‖R ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierMomentWeight (n : ℝ) ξ * ‖D ξ‖ +
          h3FourierMomentWeight (n : ℝ) ξ * ‖H ξ‖) := by

    refine integral_mono_ae hTailInt hMajor ?_

    filter_upwards [hDecomp] with ξ hξ

    have hWeight0 :
        0 ≤ h3FourierMomentWeight (n : ℝ) ξ :=
      hWeightNonneg ξ

    have hR :
        R ξ = D ξ - H ξ := by
      rw [hξ]
      ring

    have hNorm :
        ‖R ξ‖ ≤ ‖D ξ‖ + ‖H ξ‖ := by
      rw [hR]
      exact norm_sub_le _ _

    calc
      h3FourierMomentWeight (n : ℝ) ξ * ‖R ξ‖
          ≤
        h3FourierMomentWeight (n : ℝ) ξ *
          (‖D ξ‖ + ‖H ξ‖) :=
        mul_le_mul_of_nonneg_left
          hNorm hWeight0
      _ =
        h3FourierMomentWeight (n : ℝ) ξ * ‖D ξ‖ +
          h3FourierMomentWeight (n : ℝ) ξ * ‖H ξ‖ := by
        ring

  have hGeneric :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (n : ℝ) ξ * ‖R ξ‖)
        ≤
      2 * BDuhamel := by
    calc
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (n : ℝ) ξ * ‖R ξ‖)
          ≤
        ∫ ξ : H3FourierPoint3,
          (h3FourierMomentWeight (n : ℝ) ξ * ‖D ξ‖ +
            h3FourierMomentWeight (n : ℝ) ξ * ‖H ξ‖) :=
        hTailToMajor
      _ =
        (∫ ξ : H3FourierPoint3,
            h3FourierMomentWeight (n : ℝ) ξ * ‖D ξ‖)
          +
        (∫ ξ : H3FourierPoint3,
            h3FourierMomentWeight (n : ℝ) ξ * ‖H ξ‖) := by
        rw [integral_add hFullInt hHeadInt]
      _ ≤
        BDuhamel + BDuhamel :=
        add_le_add hFullMass hHeadMass
      _ =
        2 * BDuhamel := by
        ring

  dsimp only [R] at hGeneric

  simpa only [hWeightNat] using hGeneric

/-! ## Generic terminal-tail compact norm-square bound -/

/--
At every natural radial order `m ≥ 2`, one norm-square constant controls all
selected terminal-tail coordinates and all target times in a positive compact
restart slab.
-/
theorem exists_norm_sq_bound_h3SelectedDuhamelTailNatRadialFourierL2OnCompact
    (m : ℕ)
    (hm : 2 ≤ m)
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hab : a ≤ b)
    (hbR : b < h3FinHeatLerayRestartRadius ν A) :
    ∃ Bm : ℝ,
      0 ≤ Bm ∧
      ∀ q : Set.Icc a b,
        ∀ i : Fin 3,
          ‖h3SelectedDuhamelTailNatRadialFourierL2
              m hm
              hν U₀ hA hU₀
              (lt_of_lt_of_le ha q.property.1)
              (le_trans q.property.2 hbR.le)
              i‖ ^ 2
            ≤
          Bm := by

  have hDouble :
      3 ≤ 2 * m := by
    omega

  have haHalf : 0 < a / 2 := by
    positivity

  have haHalfB : a / 2 ≤ b := by
    linarith

  obtain ⟨BState, BDuhamel, B0, hSlab⟩ :=
    h3SelectedMomentSlab_nat_ge_three
      (a := a / 2)
      (t := b)
      (2 * m) hDouble
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

  let Bm : ℝ :=
    Lcompact * (2 * BDuhamel)

  have hBm0 : 0 ≤ Bm := by
    dsimp only [Bm]
    exact
      mul_nonneg
        hLcompact0
        (mul_nonneg (by norm_num) hBD0)

  refine ⟨Bm, hBm0, ?_⟩

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
          ‖ξ‖ ^ (2 * m) * ‖F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_natMoment_integrable
        (2 * m) hDouble
        hν U₀ hA hU₀ hq0 hqR i

  have hTailMomentMass :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ (2 * m) * ‖F ξ‖)
        ≤
      2 * BDuhamel := by
    dsimp only [F]
    exact
      h3SelectedDuhamelTail_natMoment_integral_le_twoBDuhamel
        (2 * m) hDouble
        hν U₀ hA hU₀
        ha q.property hqR hSlab i

  have hEnvelope :
      h3SelectedDuhamelTailFourierLinfEnvelope A (q : ℝ)
        ≤
      Lcompact := by
    dsimp only [Lcompact]
    exact
      h3SelectedDuhamelTailFourierLinfEnvelope_le_compact_generic
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
          ((‖ξ‖ ^ m : ℝ) : ℂ) * F ξ)
        (volume : Measure H3FourierPoint3) :=
    (Complex.continuous_ofReal.comp
      (continuous_norm.pow m)).aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable F)

  have hWeightedInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ m : ℝ) : ℂ) * F ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by
    have hMem :=
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_radialWeight_memLp2
        m hm
        hν U₀ hA hU₀ hq0 hqR i
    rw [memLp_two_iff_integrable_sq_norm hWeightedMeas] at hMem
    exact hMem

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          Lcompact * (‖ξ‖ ^ (2 * m) * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hTailMomentInt.const_mul Lcompact

  have hIntegralBound :
      (∫ ξ : H3FourierPoint3,
          ‖((‖ξ‖ ^ m : ℝ) : ℂ) * F ξ‖ ^ 2)
        ≤
      ∫ ξ : H3FourierPoint3,
        Lcompact * (‖ξ‖ ^ (2 * m) * ‖F ξ‖) := by

    refine integral_mono_ae hWeightedInt hMajorInt ?_

    filter_upwards [hLinf] with ξ hBound

    have hr0 : 0 ≤ ‖ξ‖ :=
      norm_nonneg ξ

    have hrm : 0 ≤ ‖ξ‖ ^ m :=
      pow_nonneg hr0 m

    have hF0 : 0 ≤ ‖F ξ‖ :=
      norm_nonneg _

    have hPow :
        (‖ξ‖ ^ m) ^ 2 = ‖ξ‖ ^ (2 * m) := by
      rw [
        pow_two,
        ← pow_add,
        show m + m = 2 * m by omega
      ]

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hrm,
      mul_pow,
      hPow
    ]

    calc
      ‖ξ‖ ^ (2 * m) * ‖F ξ‖ ^ 2
          =
        ‖ξ‖ ^ (2 * m) * (‖F ξ‖ * ‖F ξ‖) := by
        rw [pow_two]
      _ ≤
        ‖ξ‖ ^ (2 * m) * (Lcompact * ‖F ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hBound hF0)
          (pow_nonneg hr0 (2 * m))
      _ =
        Lcompact * (‖ξ‖ ^ (2 * m) * ‖F ξ‖) := by
        ring

  rw [
    norm_sq_h3SelectedDuhamelTailNatRadialFourierL2
      m hm hν U₀ hA hU₀ hq0 hqR i
  ]

  calc
    (∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ m : ℝ) : ℂ) * F ξ‖ ^ 2)
        ≤
      ∫ ξ : H3FourierPoint3,
        Lcompact * (‖ξ‖ ^ (2 * m) * ‖F ξ‖) :=
      hIntegralBound
    _ =
      Lcompact *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ (2 * m) * ‖F ξ‖) := by
      rw [integral_const_mul]
    _ ≤
      Lcompact * (2 * BDuhamel) :=
      mul_le_mul_of_nonneg_left
        hTailMomentMass hLcompact0
    _ =
      Bm := by
      rfl

/-! ## Generic selected mild compact norm-square bound -/

/--
For every radial order `m ≥ 2`, one finite norm-square constant controls all
selected velocity coordinates on a positive compact restart slab.
-/
theorem exists_norm_sq_bound_h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
    (m : ℕ)
    (hm : 2 ≤ m)
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hab : a ≤ b)
    (hbR : b < h3FinHeatLerayRestartRadius ν A) :
    ∃ Bm : ℝ,
      0 ≤ Bm ∧
      ∀ q : Set.Icc a b,
        ∀ i : Fin 3,
          ‖h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
              m hm
              hν U₀ hA hU₀ ha hbR q i‖ ^ 2
            ≤
          Bm := by

  obtain ⟨BTail, hBTail0, hBTail⟩ :=
    exists_norm_sq_bound_h3SelectedDuhamelTailNatRadialFourierL2OnCompact
      m hm
      hν U₀ hA hU₀
      ha hab hbR

  let Cfree : ℝ :=
    h3HeatNatMomentCoefficient m ν a * A

  let Chead : ℝ :=
    h3HeatNatMomentCoefficient m ν (a / 2) * (3 * A)

  let Bm : ℝ :=
    3 * (Cfree ^ 2 + Chead ^ 2 + BTail)

  have hCfree0 :
      0 ≤ Cfree := by
    dsimp only [Cfree]
    exact
      mul_nonneg
        (h3HeatNatMomentCoefficient_nonneg m ν a)
        hA.le

  have hChead0 :
      0 ≤ Chead := by
    dsimp only [Chead]
    exact
      mul_nonneg
        (h3HeatNatMomentCoefficient_nonneg m ν (a / 2))
        (mul_nonneg (by norm_num) hA.le)

  have hBm0 :
      0 ≤ Bm := by
    dsimp only [Bm]
    positivity

  refine ⟨Bm, hBm0, ?_⟩

  intro q i

  let Hm : H3FourierComplexL2 :=
    h3SelectedInitialHeatNatRadialFourierL2OnCompact
      m hν U₀ hA hU₀ ha q i

  let DmHead : H3FourierComplexL2 :=
    h3SelectedDuhamelHeadNatRadialFourierL2OnCompact
      m hν U₀ hA hU₀ ha q i

  let DmTail : H3FourierComplexL2 :=
    h3SelectedDuhamelTailNatRadialFourierL2
      m hm
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      i

  have hFree :
      ‖Hm‖ ≤ Cfree := by
    dsimp only [Hm, Cfree]
    exact
      norm_h3SelectedInitialHeatNatRadialFourierL2OnCompact_le
        m hν U₀ hA hU₀ ha q i

  have hHead :
      ‖DmHead‖ ≤ Chead := by
    dsimp only [DmHead, Chead]
    exact
      norm_h3SelectedDuhamelHeadNatRadialFourierL2OnCompact_le
        m hν U₀ hA hU₀ ha hbR q i

  have hTailSq :
      ‖DmTail‖ ^ 2 ≤ BTail := by
    dsimp only [DmTail]
    exact
      hBTail q i

  have hFreeSq :
      ‖Hm‖ ^ 2 ≤ Cfree ^ 2 :=
    pow_le_pow_left₀
      (norm_nonneg Hm)
      hFree
      2

  have hHeadSq :
      ‖DmHead‖ ^ 2 ≤ Chead ^ 2 :=
    pow_le_pow_left₀
      (norm_nonneg DmHead)
      hHead
      2

  have hNorm :
      ‖Hm - DmHead - DmTail‖
        ≤
      ‖Hm‖ + ‖DmHead‖ + ‖DmTail‖ := by
    calc
      ‖Hm - DmHead - DmTail‖
          ≤
        ‖Hm - DmHead‖ + ‖DmTail‖ :=
        norm_sub_le _ _
      _ ≤
        (‖Hm‖ + ‖DmHead‖) + ‖DmTail‖ :=
        add_le_add
          (norm_sub_le Hm DmHead)
          (le_refl ‖DmTail‖)
      _ =
        ‖Hm‖ + ‖DmHead‖ + ‖DmTail‖ := by
        ring

  have hNormSq :
      ‖Hm - DmHead - DmTail‖ ^ 2
        ≤
      (‖Hm‖ + ‖DmHead‖ + ‖DmTail‖) ^ 2 :=
    pow_le_pow_left₀
      (norm_nonneg (Hm - DmHead - DmTail))
      hNorm
      2

  have hThree :
      (‖Hm‖ + ‖DmHead‖ + ‖DmTail‖) ^ 2
        ≤
      3 *
        (‖Hm‖ ^ 2 +
          ‖DmHead‖ ^ 2 +
          ‖DmTail‖ ^ 2) := by
    nlinarith [
      sq_nonneg (‖Hm‖ - ‖DmHead‖),
      sq_nonneg (‖Hm‖ - ‖DmTail‖),
      sq_nonneg (‖DmHead‖ - ‖DmTail‖)
    ]

  have hPieces :
      3 *
        (‖Hm‖ ^ 2 +
          ‖DmHead‖ ^ 2 +
          ‖DmTail‖ ^ 2)
        ≤
      Bm := by
    dsimp only [Bm]
    exact
      mul_le_mul_of_nonneg_left
        (add_le_add
          (add_le_add hFreeSq hHeadSq)
          hTailSq)
        (by norm_num)

  change
    ‖h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
        m hm hν U₀ hA hU₀ ha hbR q i‖ ^ 2
      ≤
    Bm

  unfold h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact

  exact
    hNormSq.trans
      (hThree.trans hPieces)

/-! ## Ninth-radial specialization -/

/--
One ninth-radial norm-square constant controls every selected coordinate and
target time on a positive compact restart slab.

This is the precise high-frequency envelope needed to prove continuity of the
eighth-radial selected velocity state.
-/
theorem exists_norm_sq_bound_h3PreterminalSelectedVelocityNinthRadialFourierL2OnCompact
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hab : a ≤ b)
    (hbR : b < h3FinHeatLerayRestartRadius ν A) :
    ∃ B9 : ℝ,
      0 ≤ B9 ∧
      ∀ q : Set.Icc a b,
        ∀ i : Fin 3,
          ‖h3PreterminalSelectedVelocityNinthRadialFourierL2OnCompact
              hν U₀ hA hU₀ ha hbR q i‖ ^ 2
            ≤
          B9 := by

  simpa only [
    h3PreterminalSelectedVelocityNinthRadialFourierL2OnCompact
  ] using
    (exists_norm_sq_bound_h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      9 (by norm_num)
      hν U₀ hA hU₀
      ha hab hbR)

end

end Euclidean
end Bridge
end PrimeTensor
