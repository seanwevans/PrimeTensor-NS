import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalPhysicalHighHighLowH3Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowOuter
import Mathlib.Tactic

/-!
# Permute the exact solenoidal sixth-power H³ flux onto every minimum-frequency channel

The previous high-high-low theorem places the first Fourier moment on the middle
input q. This module uses the six *complex* ordered contributions and the
three physical solenoidality conditions to prove exact permutation invariance
of the corrected sixth-power flux. Therefore the same low-frequency gain holds
when either outer frequency p or r is the smallest. It is not permissible to
simply rename q in a single ordered term: the entire six-order symbol is needed.

The old measure-preserving outer-L¹ substitution then integrates the new
low-left and low-right sectors. No cutoff, favorable sign, or new spectral
moment assumption enters. In particular the separated radial factor remains
|high1|³ |high2|³ |low|, so the same native H³ L² mass and first Fourier L¹
moment control each sector. The overlapping sector boundaries are not yet
combined into a global partition; that is the next distinct measure step.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology FourierTransform
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev PairV := V3 × V3

noncomputable local instance axisFintypeOuterMinimumBudget244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The genuine complete SIX-order complex symbol is invariant under the
first transposition, before imposing solenoidality or momentum. -/
theorem thirdFullComplexSixSymbol_swapFirstTwo244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ) :
    thirdFullComplexSixSymbol244 p q r A B C =
      thirdFullComplexSixSymbol244 q p r B A C := by
  unfold thirdFullComplexSixSymbol244
  abel

/-- Same full six-symbol symmetry for exchanging the two last inputs. -/
theorem thirdFullComplexSixSymbol_swapLastTwo244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ) :
    thirdFullComplexSixSymbol244 p q r A B C =
      thirdFullComplexSixSymbol244 p r q A C B := by
  unfold thirdFullComplexSixSymbol244
  abel

/-- The *sixth-power flux*, unlike a single ordered component, inherits the
first permutation only on the true solenoidal momentum carrier. -/
theorem thirdFullComplexSixthPowerFlux_swapFirstTwo244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ)
    (hm : ∀ i, p i + q i + r i = 0)
    (hA : mixedDot p A = 0) (hB : mixedDot q B = 0)
    (hC : mixedDot r C = 0) :
    thirdFullComplexSixthPowerFlux244 p q r A B C =
      thirdFullComplexSixthPowerFlux244 q p r B A C := by
  have hm' : ∀ i, q i + p i + r i = 0 := by
    intro i
    have hi := hm i
    linarith only [hi]
  calc
    thirdFullComplexSixthPowerFlux244 p q r A B C =
        thirdFullComplexSixSymbol244 p q r A B C :=
          (thirdFullComplexSix_sixthPowerFlux244 p q r A B C hm hA hB hC).symm
    _ = thirdFullComplexSixSymbol244 q p r B A C :=
      thirdFullComplexSixSymbol_swapFirstTwo244 p q r A B C
    _ = thirdFullComplexSixthPowerFlux244 q p r B A C :=
      thirdFullComplexSix_sixthPowerFlux244 q p r B A C hm' hB hA hC

/-- The true complex sixth-power flux also survives exchange of the last
two input frequency-polarization pairs. -/
theorem thirdFullComplexSixthPowerFlux_swapLastTwo244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ)
    (hm : ∀ i, p i + q i + r i = 0)
    (hA : mixedDot p A = 0) (hB : mixedDot q B = 0)
    (hC : mixedDot r C = 0) :
    thirdFullComplexSixthPowerFlux244 p q r A B C =
      thirdFullComplexSixthPowerFlux244 p r q A C B := by
  have hm' : ∀ i, p i + r i + q i = 0 := by
    intro i
    have hi := hm i
    linarith only [hi]
  calc
    thirdFullComplexSixthPowerFlux244 p q r A B C =
        thirdFullComplexSixSymbol244 p q r A B C :=
          (thirdFullComplexSix_sixthPowerFlux244 p q r A B C hm hA hB hC).symm
    _ = thirdFullComplexSixSymbol244 p r q A C B :=
      thirdFullComplexSixSymbol_swapLastTwo244 p q r A B C
    _ = thirdFullComplexSixthPowerFlux244 p r q A C B :=
      thirdFullComplexSix_sixthPowerFlux244 p r q A C B hm' hA hC hB

/-- If p is the smallest frequency, the native H³ allocation applies with
p in the L¹ factor; the other two frequencies pay three derivatives each. -/
theorem thirdFullComplexSixthPowerFlux_lowFirstH3Bound244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ)
    (hm : ∀ i, p i + q i + r i = 0)
    (hA : mixedDot p A = 0) (hB : mixedDot q B = 0)
    (hC : mixedDot r C = 0)
    (hLow : frequencyNorm p ≤ min (frequencyNorm q) (frequencyNorm r)) :
    ‖thirdFullComplexSixthPowerFlux244 p q r A B C‖ ≤
      52 * (frequencyNorm q ^ 3 * h3TriadPolarizationNorm B) *
        (frequencyNorm r ^ 3 * h3TriadPolarizationNorm C) *
        (frequencyNorm p * h3TriadPolarizationNorm A) := by
  rw [thirdFullComplexSixthPowerFlux_swapFirstTwo244 p q r A B C hm hA hB hC]
  have hm' : ∀ i, q i + p i + r i = 0 := by
    intro i
    have hi := hm i
    linarith only [hi]
  exact thirdFullComplexSixthPowerFlux_lowMiddleH3Bound244
    q p r B A C hm' hB hLow

/-- If r is the smallest frequency, switch the second and third inputs
before applying the already proved high-high-low cubic-factor estimate. -/
theorem thirdFullComplexSixthPowerFlux_lowLastH3Bound244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ)
    (hm : ∀ i, p i + q i + r i = 0)
    (hA : mixedDot p A = 0) (hB : mixedDot q B = 0)
    (hC : mixedDot r C = 0)
    (hLow : frequencyNorm r ≤ min (frequencyNorm p) (frequencyNorm q)) :
    ‖thirdFullComplexSixthPowerFlux244 p q r A B C‖ ≤
      52 * (frequencyNorm p ^ 3 * h3TriadPolarizationNorm A) *
        (frequencyNorm q ^ 3 * h3TriadPolarizationNorm B) *
        (frequencyNorm r * h3TriadPolarizationNorm C) := by
  rw [thirdFullComplexSixthPowerFlux_swapLastTwo244 p q r A B C hm hA hB hC]
  have hm' : ∀ i, p i + r i + q i = 0 := by
    intro i
    have hi := hm i
    linarith only [hi]
  exact thirdFullComplexSixthPowerFlux_lowMiddleH3Bound244
    p r q A C B hm' hA hLow

/-- The right-outer analogue of the already-proved measure-preserving
outer-L¹ inequality is exactly its product-swap image. No extra Jacobian. -/
theorem thirdFull_integral_norm_le_rightOuter_L1244
    (K : PairV → ℂ) (F H : V3 → ℝ)
    (hK : Integrable K (volume.prod volume))
    (hF : Integrable (fun p => F p ^ 2)) (hH : Integrable H)
    (hHnonneg : ∀ p, 0 ≤ H p)
    (hBound : ∀ z, ‖K z‖ ≤
      2 * F z.1 * F (-(z.1 + z.2)) * H z.2) :
    ‖∫ z, K z ∂volume.prod volume‖ ≤
      2 * (∫ p, F p ^ 2) * ∫ q, H q := by
  let swap : PairV ≃ᵐ PairV := MeasurableEquiv.prodComm
  have hSwapInt : Integrable (fun z : PairV => K (swap z))
      (volume.prod volume) :=
    ((Measure.measurePreserving_swap (μ := (volume : Measure V3))
      (ν := (volume : Measure V3))).integrable_comp
      hK.aestronglyMeasurable).mpr hK
  have hBoundSwap : ∀ z : PairV, ‖K (swap z)‖ ≤
      2 * F z.2 * F (-(z.1 + z.2)) * H z.1 := by
    intro z
    have h := hBound (swap z)
    change ‖K (z.2, z.1)‖ ≤
      2 * F z.2 * F (-(z.2 + z.1)) * H z.1 at h
    change ‖K (z.2, z.1)‖ ≤
      2 * F z.2 * F (-(z.1 + z.2)) * H z.1
    simpa only [add_comm] using h
  have h := h3Triad_integral_norm_le_outer_L1
    (fun z => K (swap z)) F H hSwapInt hF hH hHnonneg hBoundSwap
  have hEq : (∫ z : PairV, K (swap z) ∂volume.prod volume) =
      ∫ z : PairV, K z ∂volume.prod volume := by
    exact (Measure.measurePreserving_swap (μ := (volume : Measure V3))
      (ν := (volume : Measure V3))).integral_comp swap.measurableEmbedding K
  rw [hEq] at h
  exact h

/-! The estimates below deliberately use a local sector `s`, not the entire
momentum plane: outside the sector the indicator contributes exactly zero. -/

/-- The high-high-low physical Fourier moment bound is equally valid when
the FIRST momentum is minimal, by the genuine outer-L¹ variable change. -/
theorem thirdFullSchwartzSixthPowerFlux_lowFirstIntegral_le_H3Moments244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (s : Set PairV) (hs : MeasurableSet s)
    (hLow : ∀ z ∈ s,
      ‖z.1‖ ≤ min ‖-(z.1 + z.2)‖ ‖z.2‖) :
    ‖∫ z in s, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ ≤
      72 * thirdFullBudgetSixthMoment244 v * thirdFullBudgetFirstMoment244 v := by
  let F : V3 → ℝ := fun ξ => 6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ)
  let H : V3 → ℝ := fun ξ => ‖ξ‖ * h3TriadSpectralAmplitude v ξ
  let K : PairV → ℂ := s.indicator (thirdFullSchwartzComplexSixthPowerFlux244 v)
  have hFlux : Integrable (thirdFullSchwartzComplexSixthPowerFlux244 v)
      (volume.prod volume) :=
    thirdFullSchwartzSixthPowerFlux_integrable_of_complexDivergence244 v hDiv
  have hK : Integrable K (volume.prod volume) := hFlux.indicator hs
  have hF : Integrable (fun ξ : V3 => F ξ ^ 2) volume := by
    have h := (h3TriadSpectralAmplitude_integrable_pow_mul_sq v 6).const_mul 36
    apply h.congr
    filter_upwards with ξ
    dsimp only [F]
    ring
  have hH : Integrable H volume := by
    simpa only [H, pow_one] using
      (h3TriadSpectralAmplitude_integrable_pow_mul v 1)
  have hH0 : ∀ ξ, 0 ≤ H ξ := by
    intro ξ
    exact mul_nonneg (norm_nonneg ξ) (h3TriadSpectralAmplitude_nonneg v ξ)
  have hBound : ∀ z : PairV,
      ‖K z‖ ≤ 2 * F z.2 * F (-(z.1 + z.2)) * H z.1 := by
    intro z
    have hRHS : 0 ≤ 2 * F z.2 * F (-(z.1 + z.2)) * H z.1 := by
      dsimp only [F]
      have hr : 0 ≤ h3TriadSpectralAmplitude v z.2 :=
        h3TriadSpectralAmplitude_nonneg v z.2
      have hq : 0 ≤ h3TriadSpectralAmplitude v (-(z.1 + z.2)) :=
        h3TriadSpectralAmplitude_nonneg v (-(z.1 + z.2))
      have hp : 0 ≤ H z.1 := hH0 _
      positivity
    by_cases hz : z ∈ s
    · rw [show K z = thirdFullSchwartzComplexSixthPowerFlux244 v z by
        simp only [K, Set.indicator_of_mem hz]]
      let p : A3 → ℝ := WithLp.ofLp z.1
      let q : A3 → ℝ := WithLp.ofLp (-(z.1 + z.2))
      let r : A3 → ℝ := WithLp.ofLp z.2
      let U := h3SchwartzTriadPolarization v
      have hm : ∀ i, p i + q i + r i = 0 := by
        intro i
        change (WithLp.ofLp z.1) i +
          (WithLp.ofLp (-(z.1 + z.2))) i + (WithLp.ofLp z.2) i = 0
        simp only [WithLp.ofLp_neg, WithLp.ofLp_add, Pi.neg_apply, Pi.add_apply]
        abel
      have hA : mixedDot p (U p) = 0 :=
        h3SchwartzTriadPolarization_divergence_zero v hDiv p
      have hB : mixedDot q (U q) = 0 :=
        h3SchwartzTriadPolarization_divergence_zero v hDiv q
      have hC : mixedDot r (U r) = 0 :=
        h3SchwartzTriadPolarization_divergence_zero v hDiv r
      have hLowP : frequencyNorm p ≤ min (frequencyNorm q) (frequencyNorm r) := by
        simpa only [frequencyNorm, p, q, r, WithLp.toLp_ofLp]
          using (hLow z hz)
      have hPoint := thirdFullComplexSixthPowerFlux_lowFirstH3Bound244
        p q r (U p) (U q) (U r) hm hA hB hC hLowP
      have hPoint' :
          ‖thirdFullSchwartzComplexSixthPowerFlux244 v z‖ ≤
            52 * (‖-(z.1 + z.2)‖ ^ 3 *
              h3TriadSpectralAmplitude v (-(z.1 + z.2))) *
              (‖z.2‖ ^ 3 * h3TriadSpectralAmplitude v z.2) *
              (‖z.1‖ * h3TriadSpectralAmplitude v z.1) := by
        simpa only [thirdFullSchwartzComplexSixthPowerFlux244,
          h3TriadSpectralAmplitude, h3TriadPolarizationNorm,
          frequencyNorm, WithLp.toLp_ofLp, p, q, r, U] using hPoint
      calc
        _ ≤ 52 * (‖-(z.1 + z.2)‖ ^ 3 *
            h3TriadSpectralAmplitude v (-(z.1 + z.2))) *
            (‖z.2‖ ^ 3 * h3TriadSpectralAmplitude v z.2) *
            (‖z.1‖ * h3TriadSpectralAmplitude v z.1) := hPoint'
        _ ≤ 2 * F z.2 * F (-(z.1 + z.2)) * H z.1 := by
          have hq : 0 ≤ ‖-(z.1 + z.2)‖ ^ 3 *
              h3TriadSpectralAmplitude v (-(z.1 + z.2)) :=
            mul_nonneg (pow_nonneg (norm_nonneg _) _)
              (h3TriadSpectralAmplitude_nonneg v _)
          have hr : 0 ≤ ‖z.2‖ ^ 3 * h3TriadSpectralAmplitude v z.2 :=
            mul_nonneg (pow_nonneg (norm_nonneg _) _)
              (h3TriadSpectralAmplitude_nonneg v z.2)
          have hp : 0 ≤ H z.1 := hH0 _
          dsimp only [F, H]
          nlinarith only [mul_nonneg hq (mul_nonneg hr hp)]
    · rw [show K z = (0 : ℂ) by
        simp only [K, Set.indicator_of_notMem hz]]
      simp only [norm_zero]
      exact hRHS
  have hEstimate := h3Triad_integral_norm_le_outer_L1
    K F H hK hF hH hH0 hBound
  have hFIntegral : (∫ ξ : V3, F ξ ^ 2 ∂volume) =
      36 * thirdFullBudgetSixthMoment244 v := by
    have hEq : (fun ξ : V3 => F ξ ^ 2) =
        (fun ξ : V3 => 36 * (‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2)) := by
      funext ξ
      dsimp only [F]
      ring
    rw [hEq, integral_const_mul]
    rfl
  have hHIntegral : (∫ ξ : V3, H ξ ∂volume) =
      thirdFullBudgetFirstMoment244 v := rfl
  have hKIntegral : (∫ z : PairV, K z ∂volume.prod volume) =
      ∫ z in s, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume := integral_indicator hs
  rw [← hKIntegral]
  calc
    ‖∫ z : PairV, K z ∂volume.prod volume‖ ≤
        2 * (∫ ξ : V3, F ξ ^ 2 ∂volume) *
          (∫ ξ : V3, H ξ ∂volume) := hEstimate
    _ = _ := by rw [hFIntegral, hHIntegral]; ring

/-- Same actual H³ integral budget when r is the smallest Fourier frequency.
The right-outer variable carries L¹, preserving the natural derivative count. -/
theorem thirdFullSchwartzSixthPowerFlux_lowLastIntegral_le_H3Moments244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (s : Set PairV) (hs : MeasurableSet s)
    (hLow : ∀ z ∈ s,
      ‖z.2‖ ≤ min ‖z.1‖ ‖-(z.1 + z.2)‖) :
    ‖∫ z in s, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ ≤
      72 * thirdFullBudgetSixthMoment244 v * thirdFullBudgetFirstMoment244 v := by
  let F : V3 → ℝ := fun ξ => 6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ)
  let H : V3 → ℝ := fun ξ => ‖ξ‖ * h3TriadSpectralAmplitude v ξ
  let K : PairV → ℂ := s.indicator (thirdFullSchwartzComplexSixthPowerFlux244 v)
  have hFlux : Integrable (thirdFullSchwartzComplexSixthPowerFlux244 v)
      (volume.prod volume) :=
    thirdFullSchwartzSixthPowerFlux_integrable_of_complexDivergence244 v hDiv
  have hK : Integrable K (volume.prod volume) := hFlux.indicator hs
  have hF : Integrable (fun ξ : V3 => F ξ ^ 2) volume := by
    have h := (h3TriadSpectralAmplitude_integrable_pow_mul_sq v 6).const_mul 36
    apply h.congr
    filter_upwards with ξ
    dsimp only [F]
    ring
  have hH : Integrable H volume := by
    simpa only [H, pow_one] using
      (h3TriadSpectralAmplitude_integrable_pow_mul v 1)
  have hH0 : ∀ ξ, 0 ≤ H ξ := by
    intro ξ
    exact mul_nonneg (norm_nonneg ξ) (h3TriadSpectralAmplitude_nonneg v ξ)
  have hBound : ∀ z : PairV,
      ‖K z‖ ≤ 2 * F z.1 * F (-(z.1 + z.2)) * H z.2 := by
    intro z
    have hRHS : 0 ≤ 2 * F z.1 * F (-(z.1 + z.2)) * H z.2 := by
      dsimp only [F]
      have hp : 0 ≤ h3TriadSpectralAmplitude v z.1 :=
        h3TriadSpectralAmplitude_nonneg v z.1
      have hq : 0 ≤ h3TriadSpectralAmplitude v (-(z.1 + z.2)) :=
        h3TriadSpectralAmplitude_nonneg v (-(z.1 + z.2))
      have hr : 0 ≤ H z.2 := hH0 _
      positivity
    by_cases hz : z ∈ s
    · rw [show K z = thirdFullSchwartzComplexSixthPowerFlux244 v z by
        simp only [K, Set.indicator_of_mem hz]]
      let p : A3 → ℝ := WithLp.ofLp z.1
      let q : A3 → ℝ := WithLp.ofLp (-(z.1 + z.2))
      let r : A3 → ℝ := WithLp.ofLp z.2
      let U := h3SchwartzTriadPolarization v
      have hm : ∀ i, p i + q i + r i = 0 := by
        intro i
        change (WithLp.ofLp z.1) i +
          (WithLp.ofLp (-(z.1 + z.2))) i + (WithLp.ofLp z.2) i = 0
        simp only [WithLp.ofLp_neg, WithLp.ofLp_add, Pi.neg_apply, Pi.add_apply]
        abel
      have hA : mixedDot p (U p) = 0 :=
        h3SchwartzTriadPolarization_divergence_zero v hDiv p
      have hB : mixedDot q (U q) = 0 :=
        h3SchwartzTriadPolarization_divergence_zero v hDiv q
      have hC : mixedDot r (U r) = 0 :=
        h3SchwartzTriadPolarization_divergence_zero v hDiv r
      have hLowP : frequencyNorm r ≤ min (frequencyNorm p) (frequencyNorm q) := by
        simpa only [frequencyNorm, p, q, r, WithLp.toLp_ofLp]
          using (hLow z hz)
      have hPoint := thirdFullComplexSixthPowerFlux_lowLastH3Bound244
        p q r (U p) (U q) (U r) hm hA hB hC hLowP
      have hPoint' :
          ‖thirdFullSchwartzComplexSixthPowerFlux244 v z‖ ≤
            52 * (‖z.1‖ ^ 3 * h3TriadSpectralAmplitude v z.1) *
              (‖-(z.1 + z.2)‖ ^ 3 *
                h3TriadSpectralAmplitude v (-(z.1 + z.2))) *
              (‖z.2‖ * h3TriadSpectralAmplitude v z.2) := by
        simpa only [thirdFullSchwartzComplexSixthPowerFlux244,
          h3TriadSpectralAmplitude, h3TriadPolarizationNorm,
          frequencyNorm, WithLp.toLp_ofLp, p, q, r, U] using hPoint
      calc
        _ ≤ 52 * (‖z.1‖ ^ 3 * h3TriadSpectralAmplitude v z.1) *
            (‖-(z.1 + z.2)‖ ^ 3 *
              h3TriadSpectralAmplitude v (-(z.1 + z.2))) *
            (‖z.2‖ * h3TriadSpectralAmplitude v z.2) := hPoint'
        _ ≤ 2 * F z.1 * F (-(z.1 + z.2)) * H z.2 := by
          have hp : 0 ≤ ‖z.1‖ ^ 3 * h3TriadSpectralAmplitude v z.1 :=
            mul_nonneg (pow_nonneg (norm_nonneg _) _)
              (h3TriadSpectralAmplitude_nonneg v z.1)
          have hq : 0 ≤ ‖-(z.1 + z.2)‖ ^ 3 *
              h3TriadSpectralAmplitude v (-(z.1 + z.2)) :=
            mul_nonneg (pow_nonneg (norm_nonneg _) _)
              (h3TriadSpectralAmplitude_nonneg v _)
          have hr : 0 ≤ H z.2 := hH0 _
          dsimp only [F, H]
          nlinarith only [mul_nonneg hp (mul_nonneg hq hr)]
    · rw [show K z = (0 : ℂ) by
        simp only [K, Set.indicator_of_notMem hz]]
      simp only [norm_zero]
      exact hRHS
  have hEstimate := thirdFull_integral_norm_le_rightOuter_L1244
    K F H hK hF hH hH0 hBound
  have hFIntegral : (∫ ξ : V3, F ξ ^ 2 ∂volume) =
      36 * thirdFullBudgetSixthMoment244 v := by
    have hEq : (fun ξ : V3 => F ξ ^ 2) =
        (fun ξ : V3 => 36 * (‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2)) := by
      funext ξ
      dsimp only [F]
      ring
    rw [hEq, integral_const_mul]
    rfl
  have hHIntegral : (∫ ξ : V3, H ξ ∂volume) =
      thirdFullBudgetFirstMoment244 v := rfl
  have hKIntegral : (∫ z : PairV, K z ∂volume.prod volume) =
      ∫ z in s, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume := integral_indicator hs
  rw [← hKIntegral]
  calc
    ‖∫ z : PairV, K z ∂volume.prod volume‖ ≤
        2 * (∫ ξ : V3, F ξ ^ 2 ∂volume) *
          (∫ ξ : V3, H ξ ∂volume) := hEstimate
    _ = _ := by rw [hFIntegral, hHIntegral]; ring


/-- The first-minimal region needs no new physical moment premise: the exact
sixth homogeneous Fourier moment and first L¹ moment both come from the
same genuine weighted H³ components. -/
theorem thirdFullWeightedSchwartz_lowFirstIntegral_le_coordinateBound244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (G : A3 → H3SpectralScalarState)
    (hG : ∀ j : A3, (G j : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (K : ℝ) (hK : 0 ≤ K) (hBound : ∀ j, ‖G j‖ ≤ K)
    (s : Set PairV) (hs : MeasurableSet s)
    (hLow : ∀ z ∈ s,
      ‖z.1‖ ≤ min ‖-(z.1 + z.2)‖ ‖z.2‖) :
    ‖∫ z in s, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ ≤
      648 * h3SobolevFirstMomentDeweightingConstant * K ^ 3 := by
  have hSix := thirdFullWeightedSchwartz_sixthMoment_le_coordinateBound244
    v G hG K hK hBound
  have hFirst := (thirdFullWeightedSchwartz_moments_le_coordinateBound244
    v G hG K hK hBound).2
  have hFirst0 := (thirdFullBudgetMoments_nonneg244 v).2
  calc
    ‖∫ z in s, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ ≤
      72 * thirdFullBudgetSixthMoment244 v *
        thirdFullBudgetFirstMoment244 v :=
          thirdFullSchwartzSixthPowerFlux_lowFirstIntegral_le_H3Moments244
            v hDiv s hs hLow
    _ ≤ 72 * (3 * K ^ 2) * thirdFullBudgetFirstMoment244 v := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hSix (by norm_num)) hFirst0
    _ ≤ 72 * (3 * K ^ 2) *
        (3 * h3SobolevFirstMomentDeweightingConstant * K) := by
      exact mul_le_mul_of_nonneg_left hFirst (by positivity)
    _ = 648 * h3SobolevFirstMomentDeweightingConstant * K ^ 3 := by ring

/-- The same fixed-snapshot weighted H³ bound holds when the last momentum
is minimal, independently of the angular profile of the complex amplitudes. -/
theorem thirdFullWeightedSchwartz_lowLastIntegral_le_coordinateBound244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (G : A3 → H3SpectralScalarState)
    (hG : ∀ j : A3, (G j : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (K : ℝ) (hK : 0 ≤ K) (hBound : ∀ j, ‖G j‖ ≤ K)
    (s : Set PairV) (hs : MeasurableSet s)
    (hLow : ∀ z ∈ s,
      ‖z.2‖ ≤ min ‖z.1‖ ‖-(z.1 + z.2)‖) :
    ‖∫ z in s, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ ≤
      648 * h3SobolevFirstMomentDeweightingConstant * K ^ 3 := by
  have hSix := thirdFullWeightedSchwartz_sixthMoment_le_coordinateBound244
    v G hG K hK hBound
  have hFirst := (thirdFullWeightedSchwartz_moments_le_coordinateBound244
    v G hG K hK hBound).2
  have hFirst0 := (thirdFullBudgetMoments_nonneg244 v).2
  calc
    ‖∫ z in s, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ ≤
      72 * thirdFullBudgetSixthMoment244 v *
        thirdFullBudgetFirstMoment244 v :=
          thirdFullSchwartzSixthPowerFlux_lowLastIntegral_le_H3Moments244
            v hDiv s hs hLow
    _ ≤ 72 * (3 * K ^ 2) * thirdFullBudgetFirstMoment244 v := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hSix (by norm_num)) hFirst0
    _ ≤ 72 * (3 * K ^ 2) *
        (3 * h3SobolevFirstMomentDeweightingConstant * K) := by
      exact mul_le_mul_of_nonneg_left hFirst (by positivity)
    _ = 648 * h3SobolevFirstMomentDeweightingConstant * K ^ 3 := by ring

/-- The exact physical recovery simultaneously controls BOTH remaining
minimum-frequency orientations. The signed full physical H³ transport still
uses this SAME solenoidal real Schwartz sequence. This is snapshot-uniform in
approximation index, NOT uniform as physical time approaches the endpoint. -/
theorem exists_thirdFullPhysicalSnapshot_outerMinimumH3Budgets244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (htNS : t ∈ Set.Ioo (0 : ℝ) T)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (sFirst sLast : ℕ → Set PairV)
    (hsFirst : ∀ n, MeasurableSet (sFirst n))
    (hsLast : ∀ n, MeasurableSet (sLast n))
    (hFirst : ∀ n z, z ∈ sFirst n →
      ‖z.1‖ ≤ min ‖-(z.1 + z.2)‖ ‖z.2‖)
    (hLast : ∀ n z, z ∈ sLast n →
      ‖z.2‖ ≤ min ‖z.1‖ ‖-(z.1 + z.2)‖) :
    ∃ (V : ℕ → H3SpectralVelocityState)
      (Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ) (K : ℝ),
      0 ≤ K ∧
      Tendsto V atTop
        (𝓝 (velocityH3SpectralStateAt u t hInt hMeas hFourier)) ∧
      (∀ (n : ℕ) (x : V3), ∑ j : A3,
        fderiv ℝ (h3SchwartzComplexify
          (Ψ n (h3ClassicalizationFinOfAxis j))) x
            (h3FourierAxisDirection j) = 0) ∧
      (∀ n : ℕ,
        let v : A3 → SchwartzMap V3 ℂ :=
          fun j => h3SchwartzComplexify
            (Ψ n (h3ClassicalizationFinOfAxis j))
        thirdFullBudgetSixthMoment244 v ≤ 3 * K ^ 2 ∧
        ‖∫ z in sFirst n, thirdFullSchwartzComplexSixthPowerFlux244 v z
            ∂volume.prod volume‖ ≤
          648 * h3SobolevFirstMomentDeweightingConstant * K ^ 3 ∧
        ‖∫ z in sLast n, thirdFullSchwartzComplexSixthPowerFlux244 v z
            ∂volume.prod volume‖ ≤
          648 * h3SobolevFirstMomentDeweightingConstant * K ^ 3) ∧
      Tendsto (fun n : ℕ =>
        ((2 * Real.pi) ^ 7 / 3) *
          (∫ z : PairV,
            thirdFullSchwartzComplexSixthPowerFlux244
              (fun j : A3 => h3SchwartzComplexify
                (Ψ n (h3ClassicalizationFinOfAxis j))) z
              ∂volume.prod volume).im)
        atTop (𝓝 (velocityH3TransportDerivative3At u t)) := by
  obtain ⟨V, Ψ, hV, hAE, hDiv, _hDefect, _hE2, _hE3, hFlux⟩ :=
    exists_thirdFullPhysicalSnapshot_solenoidalPureSixthPowerFlux244
      hNS htNS hH3 hClass ht hFourier
  obtain ⟨K, hK, hBound⟩ :=
    thirdFullWeightedRecovery_normBound_of_tendsto244
      V (velocityH3SpectralStateAt u t hInt hMeas hFourier) hV
  refine ⟨V, Ψ, K, hK, hV, hDiv, ?_, hFlux⟩
  intro n
  let v : A3 → SchwartzMap V3 ℂ :=
    fun j => h3SchwartzComplexify
      (Ψ n (h3ClassicalizationFinOfAxis j))
  let G : A3 → H3SpectralScalarState :=
    fun j => V n (h3ClassicalizationFinOfAxis j)
  have hRep : ∀ j : A3, (G j : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ) := by
    intro j
    exact hAE n (h3ClassicalizationFinOfAxis j)
  have hCoord : ∀ j : A3, ‖G j‖ ≤ K := by
    intro j
    exact (h3SpectralFinVector_coordinate_norm_le
      (V n) (h3ClassicalizationFinOfAxis j)).trans (hBound n)
  have hSix := thirdFullWeightedSchwartz_sixthMoment_le_coordinateBound244
    v G hRep K hK hCoord
  have hP := thirdFullWeightedSchwartz_lowFirstIntegral_le_coordinateBound244
    v (hDiv n) G hRep K hK hCoord (sFirst n) (hsFirst n) (hFirst n)
  have hR := thirdFullWeightedSchwartz_lowLastIntegral_le_coordinateBound244
    v (hDiv n) G hRep K hK hCoord (sLast n) (hsLast n) (hLast n)
  exact ⟨hSix, hP, hR⟩

end
end PrimeTensor.FirstMonomialTriad
