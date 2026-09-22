import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedDuhamelTailWeightedKernelL2Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedHighRadialDuhamelTailL2Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.Moment.Third.Seed

/-!
# Closure of the selected terminal-tail fourth/fifth radial Fourier L² frontier

The temporal weighted-source frontier is already closed.  For the actual named
terminal-tail state we can now use a still simpler spatial argument.

For every natural order `m ≥ 3`, the all-natural selected moment slab gives an
order-`m` moment of the complete Duhamel state at both `q/2` and `q`.  Heat
contraction preserves that same moment on the midpoint head.  The exact
decomposition

    D(q) = Head(q) + Tail(q)

therefore gives the same order-`m` weighted `L¹` moment for the named tail.

Independently, the selected nonlinear forcing has one frequency-independent
ceiling.  Since the terminal tail is its heat-contracted source-time integral,

    |Tail(q,ξ)| ≤ L_force(A) * volume((q/2,q)).

Combining the tail `L∞` ceiling with its doubled weighted `L¹` moment gives

    (|ξ|^m |Tail(q,ξ)|)^2
      ≤ L_tail(A,q) |ξ|^(2m) |Tail(q,ξ)|.

Hence every natural radial order `m ≥ 2` belongs to Fourier `L²`; in
particular orders four and five close the BKM terminal-tail frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedDuhamelTailRadialL2Closure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 800000

/-! ## A uniform Fourier L∞ ceiling for the integrated terminal tail -/

/-- Frequency-independent ceiling for one terminal-tail Fourier amplitude. -/
noncomputable def h3SelectedDuhamelTailFourierLinfEnvelope
    (A q : ℝ) : ℝ :=
  h3SelectedForcingFourierLinfEnvelope A *
    (volume : Measure ℝ).real (Set.Ioo (q / 2) q)

theorem h3SelectedDuhamelTailFourierLinfEnvelope_nonneg
    {A q : ℝ}
    (hA : 0 ≤ A) :
    0 ≤ h3SelectedDuhamelTailFourierLinfEnvelope A q := by
  unfold h3SelectedDuhamelTailFourierLinfEnvelope
  exact
    mul_nonneg
      (h3SelectedForcingFourierLinfEnvelope_nonneg hA)
      (by
        rw [Measure.real_def]
        exact ENNReal.toReal_nonneg)

/--
The explicit selected terminal-tail Fourier amplitude is uniformly bounded in
frequency by the source-time length times the already-uniform forcing ceiling.
-/
theorem norm_h3SelectedDuhamelTailRawFourierAmplitude_le_linfEnvelope
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3SelectedDuhamelTailRawFourierAmplitude
        ν A q hν U₀ hA hU₀ i ξ‖
      ≤
    h3SelectedDuhamelTailFourierLinfEnvelope A q := by

  let L : ℝ := h3SelectedForcingFourierLinfEnvelope A

  have hFinite :
      (volume : Measure ℝ) (Set.Ioo (q / 2) q) < ∞ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top

  have hBound :
      ∀ᵐ s : ℝ ∂(volume : Measure ℝ),
        s ∈ Set.Ioo (q / 2) q →
          ‖h3SelectedDuhamelTailComplexKernel
              ν A q hν U₀ hA hU₀ i (s, ξ)‖
            ≤
          L := by
    filter_upwards with s hs

    have hLag :
        0 ≤ q - s :=
      sub_nonneg.mpr hs.2.le

    have hHeat :
        ‖h3HeatFourierSymbol ν (q - s) ξ‖ ≤ 1 :=
      norm_h3HeatFourierSymbol_le_one
        hν.le hLag ξ

    have hForce :
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        ‖h3RawFinLerayOuterProductDivergence
            (W s) (W s) i ξ‖
          ≤
        L := by
      dsimp only [L]
      exact
        norm_h3RawFinLerayOuterProductDivergence_selectedRestart_le_uniformLinf
          hν U₀ hA hU₀ i ξ

    unfold h3SelectedDuhamelTailComplexKernel
    dsimp only

    rw [norm_mul]

    calc
      ‖h3HeatFourierSymbol ν (q - s) ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ s)
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ s)
            i ξ‖
          ≤
        1 *
          ‖h3RawFinLerayOuterProductDivergence
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ s)
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ s)
            i ξ‖ :=
        mul_le_mul_of_nonneg_right
          hHeat
          (norm_nonneg _)
      _ ≤ 1 * L :=
        mul_le_mul_of_nonneg_left
          hForce
          (by norm_num)
      _ = L := by
        ring

  have hRaw :
      ‖∫ s in Set.Ioo (q / 2) q,
          h3SelectedDuhamelTailComplexKernel
            ν A q hν U₀ hA hU₀ i (s, ξ)‖
        ≤
      L * (volume : Measure ℝ).real (Set.Ioo (q / 2) q) :=
    norm_setIntegral_le_of_norm_le_const_ae'
      hFinite hBound

  unfold
    h3SelectedDuhamelTailRawFourierAmplitude
    h3SelectedDuhamelTailFourierLinfEnvelope

  exact hRaw

/-- The quotient-safe named terminal-tail state inherits the same `L∞` bound
almost everywhere from its explicit raw representative. -/
theorem ae_norm_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_le_linfEnvelope
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (i : Fin 3) :
    ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
      ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := q) hν U₀ hA hU₀ i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ‖
        ≤
      h3SelectedDuhamelTailFourierLinfEnvelope A q := by

  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_ae_eq_rawAmplitude
      hν U₀ hA hU₀ hq i

  filter_upwards [hRep] with ξ hξ

  rw [hξ]

  exact
    norm_h3SelectedDuhamelTailRawFourierAmplitude_le_linfEnvelope
      hν U₀ hA hU₀ hq i ξ

/-! ## Arbitrary natural weighted L¹ moments of the named terminal tail -/

/--
Every natural moment of order at least three is integrable for the named
terminal-tail state.

The complete Duhamel moment comes from the all-natural slab.  At half time the
same slab moment is available; heat contraction transports it to the named
midpoint head.  The exact decomposition `D = Head + Tail` then gives the tail
moment by triangle inequality.
-/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_natMoment_integrable
    {ν A q : ℝ}
    (m : ℕ)
    (hm : 3 ≤ m)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ m *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
              (t := q) hν U₀ hA hU₀ i :
            H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by

  have hhalf : 0 < q / 2 := by
    positivity

  have hhalfLe : q / 2 ≤ q := by
    linarith

  obtain ⟨BState, BDuhamel, B0, hSlab⟩ :=
    h3SelectedMomentSlab_nat_ge_three
      (a := q / 2)
      (t := q)
      m hm
      hν U₀ hA hU₀
      hhalf hhalfLe hqR

  have hSlabData := hSlab
  unfold H3SelectedMomentSlab at hSlabData
  rcases hSlabData with
    ⟨_hBS, _hBD, _hB0, hData⟩

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := q) hν U₀ hA hU₀ i

  let Dhalf : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := q / 2) hν U₀ hA hU₀ i

  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
      hν U₀ hA hU₀ hq i

  let R : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
      (t := q) hν U₀ hA hU₀ i

  have hAtQ :=
    hData q
      ⟨hhalfLe, le_rfl⟩ i

  have hAtHalf :=
    hData (q / 2)
      ⟨le_rfl, hhalfLe⟩ i

  dsimp only at hAtQ hAtHalf

  have hFullGeneric :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (m : ℝ) ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact hAtQ.2.2.1

  have hHalfGeneric :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (m : ℝ) ξ * ‖Dhalf ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Dhalf]
    exact hAtHalf.2.2.1

  have hm0Real :
      0 ≤ (m : ℝ) := by
    positivity

  have hHeadMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (m : ℝ) ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_h3FourierMomentWeight hm0Real).aestronglyMeasurable.mul
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
        hν U₀ hA hU₀ hq i

  have hHeadGeneric :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (m : ℝ) ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by

    refine
      Integrable.mono
        (f := fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (m : ℝ) ξ * ‖H ξ‖)
        (g := fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (m : ℝ) ξ * ‖Dhalf ξ‖)
        hHalfGeneric
        hHeadMeas
        ?_

    filter_upwards [hHeadRep] with ξ hξ

    have hWeight0 :
        0 ≤ h3FourierMomentWeight (m : ℝ) ξ :=
      h3FourierMomentWeight_nonneg (m : ℝ) ξ

    have hHeat :
        ‖h3HeatFourierSymbol ν (q / 2) ξ‖ ≤ 1 :=
      norm_h3HeatFourierSymbol_le_one
        hν.le hhalf.le ξ

    have hPoint :
        h3FourierMomentWeight (m : ℝ) ξ * ‖H ξ‖
          ≤
        h3FourierMomentWeight (m : ℝ) ξ * ‖Dhalf ξ‖ := by
      rw [hξ, norm_mul]
      calc
        h3FourierMomentWeight (m : ℝ) ξ *
            (‖h3HeatFourierSymbol ν (q / 2) ξ‖ * ‖Dhalf ξ‖)
            ≤
          h3FourierMomentWeight (m : ℝ) ξ *
            (1 * ‖Dhalf ξ‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              hHeat
              (norm_nonneg _))
            hWeight0
        _ =
          h3FourierMomentWeight (m : ℝ) ξ * ‖Dhalf ξ‖ := by
          ring

    have hLeft0 :
        0 ≤ h3FourierMomentWeight (m : ℝ) ξ * ‖H ξ‖ :=
      mul_nonneg hWeight0 (norm_nonneg _)

    have hRight0 :
        0 ≤ h3FourierMomentWeight (m : ℝ) ξ * ‖Dhalf ξ‖ :=
      mul_nonneg hWeight0 (norm_nonneg _)

    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hLeft0,
      abs_of_nonneg hRight0
    ] using hPoint

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (m : ℝ) ξ * ‖D ξ‖ +
            h3FourierMomentWeight (m : ℝ) ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFullGeneric.add hHeadGeneric

  have hTailMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (m : ℝ) ξ * ‖R ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_h3FourierMomentWeight hm0Real).aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable R).norm

  have hDecomp :
      ((D : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        H ξ + R ξ) := by
    dsimp only [D, H, R]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_head_add_tail
        hν U₀ hA hU₀ hq i

  have hTailGeneric :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (m : ℝ) ξ * ‖R ξ‖)
        (volume : Measure H3FourierPoint3) := by

    refine
      Integrable.mono
        (f := fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (m : ℝ) ξ * ‖R ξ‖)
        (g := fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (m : ℝ) ξ * ‖D ξ‖ +
            h3FourierMomentWeight (m : ℝ) ξ * ‖H ξ‖)
        hMajor
        hTailMeas
        ?_

    filter_upwards [hDecomp] with ξ hξ

    have hWeight0 :
        0 ≤ h3FourierMomentWeight (m : ℝ) ξ :=
      h3FourierMomentWeight_nonneg (m : ℝ) ξ

    have hR :
        R ξ = D ξ - H ξ := by
      rw [hξ]
      ring

    have hNorm :
        ‖R ξ‖ ≤ ‖D ξ‖ + ‖H ξ‖ := by
      rw [hR]
      exact norm_sub_le _ _

    have hPoint :
        h3FourierMomentWeight (m : ℝ) ξ * ‖R ξ‖
          ≤
        h3FourierMomentWeight (m : ℝ) ξ * ‖D ξ‖ +
          h3FourierMomentWeight (m : ℝ) ξ * ‖H ξ‖ := by
      calc
        h3FourierMomentWeight (m : ℝ) ξ * ‖R ξ‖
            ≤
          h3FourierMomentWeight (m : ℝ) ξ *
            (‖D ξ‖ + ‖H ξ‖) :=
          mul_le_mul_of_nonneg_left hNorm hWeight0
        _ =
          h3FourierMomentWeight (m : ℝ) ξ * ‖D ξ‖ +
            h3FourierMomentWeight (m : ℝ) ξ * ‖H ξ‖ := by
          ring

    have hLeft0 :
        0 ≤ h3FourierMomentWeight (m : ℝ) ξ * ‖R ξ‖ :=
      mul_nonneg hWeight0 (norm_nonneg _)

    have hRight0 :
        0 ≤
          h3FourierMomentWeight (m : ℝ) ξ * ‖D ξ‖ +
            h3FourierMomentWeight (m : ℝ) ξ * ‖H ξ‖ :=
      add_nonneg
        (mul_nonneg hWeight0 (norm_nonneg _))
        (mul_nonneg hWeight0 (norm_nonneg _))

    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hLeft0,
      abs_of_nonneg hRight0
    ] using hPoint

  dsimp only [R] at hTailGeneric

  simpa only [h3FourierMomentWeight_natCast] using hTailGeneric

/-! ## L∞ × doubled moment -> weighted L² -/

/--
A named Fourier `L²` state with an a.e. frequency-independent ceiling and an
integrable doubled radial moment has radial order `m` in `L²`.
-/
private theorem h3FourierL2_radialWeight_memLp2_of_ae_linf_of_doubleMoment
    (m : ℕ)
    (F : H3FourierComplexL2)
    (L : ℝ)
    (hL0 : 0 ≤ L)
    (hLinf :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖F ξ‖ ≤ L)
    (hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ (2 * m) * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) * F ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ m : ℝ) : ℂ) * F ξ)
        (volume : Measure H3FourierPoint3) :=
    (Complex.continuous_ofReal.comp
      (continuous_norm.pow m)).aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable F)

  rw [memLp_two_iff_integrable_sq_norm hMeas]

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          L * (‖ξ‖ ^ (2 * m) * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul L

  refine
    hMajor.mono'
      ((hMeas.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
      ?_

  filter_upwards [hLinf] with ξ hBound

  have hr0 :
      0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  have hrm0 :
      0 ≤ ‖ξ‖ ^ m :=
    pow_nonneg hr0 m

  have hF0 :
      0 ≤ ‖F ξ‖ :=
    norm_nonneg _

  have hPow :
      (‖ξ‖ ^ m) ^ 2 = ‖ξ‖ ^ (2 * m) := by
    rw [pow_two, ← pow_add]
    congr 1
    omega

  rw [
    Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _),
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hrm0,
    mul_pow,
    hPow
  ]

  calc
    ‖ξ‖ ^ (2 * m) * ‖F ξ‖ ^ 2
        =
      ‖ξ‖ ^ (2 * m) * (‖F ξ‖ * ‖F ξ‖) := by
      rw [pow_two]
    _ ≤
      ‖ξ‖ ^ (2 * m) * (L * ‖F ξ‖) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hBound hF0)
          (pow_nonneg hr0 (2 * m))
    _ =
      L * (‖ξ‖ ^ (2 * m) * ‖F ξ‖) := by
      ring

/--
Every named selected terminal-tail coordinate has arbitrary natural radial
Fourier `L²` order `m ≥ 2`.
-/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_radialWeight_memLp2
    {ν A q : ℝ}
    (m : ℕ)
    (hm : 2 ≤ m)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          (((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
              (t := q) hν U₀ hA hU₀ i :
            H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ))
      2
      (volume : Measure H3FourierPoint3) := by

  let F : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
      (t := q) hν U₀ hA hU₀ i

  let L : ℝ :=
    h3SelectedDuhamelTailFourierLinfEnvelope A q

  have hL0 : 0 ≤ L := by
    dsimp only [L]
    exact
      h3SelectedDuhamelTailFourierLinfEnvelope_nonneg hA.le

  have hLinf :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖F ξ‖ ≤ L := by
    dsimp only [F, L]
    exact
      ae_norm_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_le_linfEnvelope
        hν U₀ hA hU₀ hq i

  have hDouble :
      3 ≤ 2 * m := by
    omega

  have hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ (2 * m) * ‖F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_natMoment_integrable
        (2 * m) hDouble
        hν U₀ hA hU₀ hq hqR i

  exact
    h3FourierL2_radialWeight_memLp2_of_ae_linf_of_doubleMoment
      m
      (h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
        (t := q) hν U₀ hA hU₀ i)
      L hL0 hLinf hMoment

/-! ## Closure of the named fourth/fifth terminal-tail frontier -/

/--
The selected fourth/fifth terminal-half radial Fourier `L²` frontier is
automatic.
-/
theorem h3CanonicalSelectedDuhamelTailFourthFifthRadialRawFourierMemLp2OnRestartRadius :
    H3CanonicalSelectedDuhamelTailFourthFifthRadialRawFourierMemLp2OnRestartRadius := by

  unfold
    H3CanonicalSelectedDuhamelTailFourthFifthRadialRawFourierMemLp2OnRestartRadius

  intro E u T t₀ hNS ht₀ hE hTail q hq

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  have hqR :
      q ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    hq.2.le

  dsimp only

  constructor

  · intro j
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_radialWeight_memLp2
        4 (by norm_num)
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ hq.1 hqR j

  · intro j
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_radialWeight_memLp2
        5 (by norm_num)
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ hq.1 hqR j

end

end Euclidean
end Bridge
end PrimeTensor
