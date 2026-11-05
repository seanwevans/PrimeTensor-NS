import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalMiddleHighMaxTail
import Mathlib.Tactic

/-!
# Outer-minimum high-maximum Fourier flux tails

On the exact conservation plane p+q+r=0, either outer minimum forces
both remaining frequencies to be comparable within factor two. Above the
max-gradient threshold 2(R+1), both cubic Fourier slots belong to the
natural high-radial region. The old outer-L¹ changes of variables then
provide a genuinely small complex trilinear integral, without introducing
separate moment assumptions or assuming that permutation preserves a signed
flux integral. The individual complex symbols are bounded before integration.
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

noncomputable local instance axisFintypeOuterHighMaxTail244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- A common high maximum among the three conserving Fourier frequencies. -/
def thirdFullHighMaxSet244 (R : ℕ) : Set PairV :=
  {z | 2 * ((R : ℝ) + 1) ≤
    max (h3FourierGradientMagnitude z.1)
      (max (h3FourierGradientMagnitude (-(z.1 + z.2)))
        (h3FourierGradientMagnitude z.2))}

/-- The maximum-frequency condition is measurable including equality. -/
theorem thirdFullHighMaxSet_measurable244 (R : ℕ) :
    MeasurableSet (thirdFullHighMaxSet244 R) := by
  have hP : Continuous (fun z : PairV => h3FourierGradientMagnitude z.1) := by
    change Continuous (fun z : PairV => (2 * Real.pi) * ‖z.1‖)
    exact continuous_const.mul continuous_fst.norm
  have hQ : Continuous (fun z : PairV =>
      h3FourierGradientMagnitude (-(z.1 + z.2))) := by
    change Continuous (fun z : PairV => (2 * Real.pi) * ‖-(z.1 + z.2)‖)
    exact continuous_const.mul ((continuous_fst.add continuous_snd).neg.norm)
  have hR : Continuous (fun z : PairV => h3FourierGradientMagnitude z.2) := by
    change Continuous (fun z : PairV => (2 * Real.pi) * ‖z.2‖)
    exact continuous_const.mul continuous_snd.norm
  exact (isClosed_le continuous_const (hP.max (hQ.max hR))).measurableSet

/-- The tie-broken low-first sector, restricted to high maximum radius. -/
def thirdFullMinFirstHighMaxSector244 (R : ℕ) : Set PairV :=
  thirdFullMinFirstSector244 ∩ thirdFullHighMaxSet244 R

/-- The tie-broken low-last sector, restricted to high maximum radius. -/
def thirdFullMinLastHighMaxSector244 (R : ℕ) : Set PairV :=
  thirdFullMinLastSector244 ∩ thirdFullHighMaxSet244 R

theorem thirdFullMinFirstHighMaxSector_measurable244 (R : ℕ) :
    MeasurableSet (thirdFullMinFirstHighMaxSector244 R) :=
  thirdFullMinFirstSector_measurable244.inter (thirdFullHighMaxSet_measurable244 R)

theorem thirdFullMinLastHighMaxSector_measurable244 (R : ℕ) :
    MeasurableSet (thirdFullMinLastHighMaxSector244 R) :=
  thirdFullMinLastSector_measurable244.inter (thirdFullHighMaxSet_measurable244 R)

/-- Permute the middle-sector geometry to the genuinely first-minimal case:
if p is minimal, the cubic slots q and r must both be high. -/
theorem thirdFull_lowFirst_highMax_forces_middleLastHigh244
    (z : PairV) (R : ℕ)
    (hLow : ‖z.1‖ ≤ min ‖-(z.1 + z.2)‖ ‖z.2‖)
    (hMax : 2 * ((R : ℝ) + 1) ≤
      max (h3FourierGradientMagnitude z.1)
        (max (h3FourierGradientMagnitude (-(z.1 + z.2)))
          (h3FourierGradientMagnitude z.2))) :
    (-(z.1 + z.2)) ∈ h3TopTailNaturalHighRadialSet R ∧
      z.2 ∈ h3TopTailNaturalHighRadialSet R := by
  let q : V3 := -(z.1 + z.2)
  let w : PairV := (q, z.2)
  have hp : -(q + z.2) = z.1 := by dsimp only [q]; abel
  have hLow' : ‖-(w.1 + w.2)‖ ≤ min ‖w.1‖ ‖w.2‖ := by
    change ‖-(q + z.2)‖ ≤ min ‖q‖ ‖z.2‖
    rw [hp]
    exact hLow
  have hMax' : 2 * ((R : ℝ) + 1) ≤
      max (h3FourierGradientMagnitude w.1)
        (max (h3FourierGradientMagnitude (-(w.1 + w.2)))
          (h3FourierGradientMagnitude w.2)) := by
    change 2 * ((R : ℝ) + 1) ≤
      max (h3FourierGradientMagnitude q)
        (max (h3FourierGradientMagnitude (-(q + z.2)))
          (h3FourierGradientMagnitude z.2))
    rw [hp]
    rcases le_max_iff.mp hMax with hp' | hqr
    · exact le_max_iff.mpr (Or.inr (le_max_iff.mpr (Or.inl hp')))
    · rcases le_max_iff.mp hqr with hq' | hr'
      · exact le_max_iff.mpr (Or.inl hq')
      · exact le_max_iff.mpr (Or.inr (le_max_iff.mpr (Or.inr hr')))
  have hBoth := thirdFull_lowMiddle_highMax_forces_outerHigh244 w R hLow' hMax'
  exact hBoth

/-- The same geometric argument when r is minimal: p and q are high. -/
theorem thirdFull_lowLast_highMax_forces_firstMiddleHigh244
    (z : PairV) (R : ℕ)
    (hLow : ‖z.2‖ ≤ min ‖z.1‖ ‖-(z.1 + z.2)‖)
    (hMax : 2 * ((R : ℝ) + 1) ≤
      max (h3FourierGradientMagnitude z.1)
        (max (h3FourierGradientMagnitude (-(z.1 + z.2)))
          (h3FourierGradientMagnitude z.2))) :
    z.1 ∈ h3TopTailNaturalHighRadialSet R ∧
      (-(z.1 + z.2)) ∈ h3TopTailNaturalHighRadialSet R := by
  let q : V3 := -(z.1 + z.2)
  let w : PairV := (z.1, q)
  have hr : -(z.1 + q) = z.2 := by dsimp only [q]; abel
  have hLow' : ‖-(w.1 + w.2)‖ ≤ min ‖w.1‖ ‖w.2‖ := by
    change ‖-(z.1 + q)‖ ≤ min ‖z.1‖ ‖q‖
    rw [hr]
    exact hLow
  have hMax' : 2 * ((R : ℝ) + 1) ≤
      max (h3FourierGradientMagnitude w.1)
        (max (h3FourierGradientMagnitude (-(w.1 + w.2)))
          (h3FourierGradientMagnitude w.2)) := by
    change 2 * ((R : ℝ) + 1) ≤
      max (h3FourierGradientMagnitude z.1)
        (max (h3FourierGradientMagnitude (-(z.1 + q)))
          (h3FourierGradientMagnitude q))
    rw [hr]
    rcases le_max_iff.mp hMax with hp' | hqr
    · exact le_max_iff.mpr (Or.inl hp')
    · rcases le_max_iff.mp hqr with hq' | hr'
      · exact le_max_iff.mpr (Or.inr (le_max_iff.mpr (Or.inr hq')))
      · exact le_max_iff.mpr (Or.inr (le_max_iff.mpr (Or.inl hr')))
  have hBoth := thirdFull_lowMiddle_highMax_forces_outerHigh244 w R hLow' hMax'
  exact hBoth

/-- The low-first high-maximum sector has two genuinely high cubic
Fourier factors. This is an estimate on the exact complex symbol. -/
theorem thirdFullSchwartzSixthPowerFlux_firstHighMaxIntegral_le_H3Tail244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (R : ℕ) :
    ‖∫ z in thirdFullMinFirstHighMaxSector244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume‖ ≤
      72 * (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) *
      thirdFullBudgetFirstMoment244 v := by
  let S : Set PairV := thirdFullMinFirstHighMaxSector244 R
  let T : Set V3 := h3TopTailNaturalHighRadialSet R
  let F : V3 → ℝ := T.indicator
    (fun ξ => 6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ))
  let H : V3 → ℝ := fun ξ => ‖ξ‖ * h3TriadSpectralAmplitude v ξ
  let K : PairV → ℂ := S.indicator (thirdFullSchwartzComplexSixthPowerFlux244 v)
  have hS : MeasurableSet S := thirdFullMinFirstHighMaxSector_measurable244 R
  have hT : MeasurableSet T := measurableSet_h3TopTailNaturalHighRadialSet R
  have hFlux : Integrable (thirdFullSchwartzComplexSixthPowerFlux244 v)
      (volume.prod volume) :=
    thirdFullSchwartzSixthPowerFlux_integrable_of_complexDivergence244 v hDiv
  have hK : Integrable K (volume.prod volume) := hFlux.indicator hS
  have hSixInt : Integrable (fun ξ : V3 =>
      36 * (‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2)) volume :=
    (h3TriadSpectralAmplitude_integrable_pow_mul_sq v 6).const_mul 36
  have hFEq : (fun ξ : V3 => F ξ ^ 2) =
      T.indicator (fun ξ => 36 * (‖ξ‖ ^ 6 *
        h3TriadSpectralAmplitude v ξ ^ 2)) := by
    funext ξ
    by_cases hξ : ξ ∈ T
    · simp only [F, Set.indicator_of_mem hξ]
      ring
    · simp [F, Set.indicator_of_notMem hξ]
  have hF : Integrable (fun ξ : V3 => F ξ ^ 2) volume := by
    rw [hFEq]
    exact hSixInt.indicator hT
  have hH : Integrable H volume := by
    simpa only [H, pow_one] using
      (h3TriadSpectralAmplitude_integrable_pow_mul v 1)
  have hH0 : ∀ ξ, 0 ≤ H ξ := by
    intro ξ
    exact mul_nonneg (norm_nonneg ξ) (h3TriadSpectralAmplitude_nonneg v ξ)
  have hF0 : ∀ ξ, 0 ≤ F ξ := by
    intro ξ
    by_cases hξ : ξ ∈ T
    · simp only [F, Set.indicator_of_mem hξ]
      exact mul_nonneg (by norm_num)
        (mul_nonneg (pow_nonneg (norm_nonneg ξ) 3)
          (h3TriadSpectralAmplitude_nonneg v ξ))
    · simp [F, Set.indicator_of_notMem hξ]
  have hBound : ∀ z : PairV,
      ‖K z‖ ≤ 2 * F z.2 * F (-(z.1 + z.2)) * H z.1 := by
    intro z
    have hRHS : 0 ≤ 2 * F z.2 * F (-(z.1 + z.2)) * H z.1 := by
      have hp := hF0 z.1
      have hq := hF0 (-(z.1 + z.2))
      have hr := hF0 z.2
      have hs := hH0 z.1
      have ht := hH0 z.2
      positivity
    by_cases hz : z ∈ S
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
      have hLow : ‖z.1‖ ≤ min ‖-(z.1 + z.2)‖ ‖z.2‖ :=
        thirdFullMinFirstSector_isLow244 z hz.1
      have hLowP : frequencyNorm p ≤ min (frequencyNorm q) (frequencyNorm r) := by
        simpa only [frequencyNorm, p, q, r, WithLp.toLp_ofLp] using hLow
      have hHigh := thirdFull_lowFirst_highMax_forces_middleLastHigh244 z R hLow hz.2
      have hqHigh : F (-(z.1 + z.2)) =
          6 * (‖-(z.1 + z.2)‖ ^ 3 * h3TriadSpectralAmplitude v (-(z.1 + z.2))) := by
        change (T.indicator (fun ξ : V3 =>
          6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ))) (-(z.1 + z.2)) = _
        exact Set.indicator_of_mem hHigh.1
          (fun ξ : V3 => 6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ))
      have hrHigh : F z.2 =
          6 * (‖z.2‖ ^ 3 * h3TriadSpectralAmplitude v z.2) := by
        change (T.indicator (fun ξ : V3 =>
          6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ))) z.2 = _
        exact Set.indicator_of_mem hHigh.2
          (fun ξ : V3 => 6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ))
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
          rw [hrHigh, hqHigh]
          dsimp only [H]
          nlinarith only [mul_nonneg hq (mul_nonneg hr hp)]
    · rw [show K z = (0 : ℂ) by
        simp only [K, Set.indicator_of_notMem hz]]
      simp only [norm_zero]
      exact hRHS
  have hEstimate := h3Triad_integral_norm_le_outer_L1
    K F H hK hF hH hH0 hBound
  have hFIntegral : (∫ ξ : V3, F ξ ^ 2 ∂volume) =
      36 * (∫ ξ in T, ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2
        ∂volume) := by
    rw [hFEq, integral_indicator hT, integral_const_mul]
  have hHIntegral : (∫ ξ : V3, H ξ ∂volume) =
      thirdFullBudgetFirstMoment244 v := rfl
  have hKIntegral : (∫ z : PairV, K z ∂volume.prod volume) =
      ∫ z in S, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume := integral_indicator hS
  rw [← hKIntegral]
  calc
    ‖∫ z : PairV, K z ∂volume.prod volume‖ ≤
        2 * (∫ ξ : V3, F ξ ^ 2 ∂volume) *
          (∫ ξ : V3, H ξ ∂volume) := hEstimate
    _ = _ := by rw [hFIntegral, hHIntegral]; ring

/-- The low-last high-maximum sector has two genuinely high cubic
Fourier factors. This is an estimate on the exact complex symbol. -/
theorem thirdFullSchwartzSixthPowerFlux_lastHighMaxIntegral_le_H3Tail244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (R : ℕ) :
    ‖∫ z in thirdFullMinLastHighMaxSector244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume‖ ≤
      72 * (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) *
      thirdFullBudgetFirstMoment244 v := by
  let S : Set PairV := thirdFullMinLastHighMaxSector244 R
  let T : Set V3 := h3TopTailNaturalHighRadialSet R
  let F : V3 → ℝ := T.indicator
    (fun ξ => 6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ))
  let H : V3 → ℝ := fun ξ => ‖ξ‖ * h3TriadSpectralAmplitude v ξ
  let K : PairV → ℂ := S.indicator (thirdFullSchwartzComplexSixthPowerFlux244 v)
  have hS : MeasurableSet S := thirdFullMinLastHighMaxSector_measurable244 R
  have hT : MeasurableSet T := measurableSet_h3TopTailNaturalHighRadialSet R
  have hFlux : Integrable (thirdFullSchwartzComplexSixthPowerFlux244 v)
      (volume.prod volume) :=
    thirdFullSchwartzSixthPowerFlux_integrable_of_complexDivergence244 v hDiv
  have hK : Integrable K (volume.prod volume) := hFlux.indicator hS
  have hSixInt : Integrable (fun ξ : V3 =>
      36 * (‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2)) volume :=
    (h3TriadSpectralAmplitude_integrable_pow_mul_sq v 6).const_mul 36
  have hFEq : (fun ξ : V3 => F ξ ^ 2) =
      T.indicator (fun ξ => 36 * (‖ξ‖ ^ 6 *
        h3TriadSpectralAmplitude v ξ ^ 2)) := by
    funext ξ
    by_cases hξ : ξ ∈ T
    · simp only [F, Set.indicator_of_mem hξ]
      ring
    · simp [F, Set.indicator_of_notMem hξ]
  have hF : Integrable (fun ξ : V3 => F ξ ^ 2) volume := by
    rw [hFEq]
    exact hSixInt.indicator hT
  have hH : Integrable H volume := by
    simpa only [H, pow_one] using
      (h3TriadSpectralAmplitude_integrable_pow_mul v 1)
  have hH0 : ∀ ξ, 0 ≤ H ξ := by
    intro ξ
    exact mul_nonneg (norm_nonneg ξ) (h3TriadSpectralAmplitude_nonneg v ξ)
  have hF0 : ∀ ξ, 0 ≤ F ξ := by
    intro ξ
    by_cases hξ : ξ ∈ T
    · simp only [F, Set.indicator_of_mem hξ]
      exact mul_nonneg (by norm_num)
        (mul_nonneg (pow_nonneg (norm_nonneg ξ) 3)
          (h3TriadSpectralAmplitude_nonneg v ξ))
    · simp [F, Set.indicator_of_notMem hξ]
  have hBound : ∀ z : PairV,
      ‖K z‖ ≤ 2 * F z.1 * F (-(z.1 + z.2)) * H z.2 := by
    intro z
    have hRHS : 0 ≤ 2 * F z.1 * F (-(z.1 + z.2)) * H z.2 := by
      have hp := hF0 z.1
      have hq := hF0 (-(z.1 + z.2))
      have hr := hF0 z.2
      have hs := hH0 z.1
      have ht := hH0 z.2
      positivity
    by_cases hz : z ∈ S
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
      have hLow : ‖z.2‖ ≤ min ‖z.1‖ ‖-(z.1 + z.2)‖ :=
        thirdFullMinLastSector_isLow244 z hz.1
      have hLowP : frequencyNorm r ≤ min (frequencyNorm p) (frequencyNorm q) := by
        simpa only [frequencyNorm, p, q, r, WithLp.toLp_ofLp] using hLow
      have hHigh := thirdFull_lowLast_highMax_forces_firstMiddleHigh244 z R hLow hz.2
      have hpHigh : F z.1 =
          6 * (‖z.1‖ ^ 3 * h3TriadSpectralAmplitude v z.1) := by
        change (T.indicator (fun ξ : V3 =>
          6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ))) z.1 = _
        exact Set.indicator_of_mem hHigh.1
          (fun ξ : V3 => 6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ))
      have hqHigh : F (-(z.1 + z.2)) =
          6 * (‖-(z.1 + z.2)‖ ^ 3 * h3TriadSpectralAmplitude v (-(z.1 + z.2))) := by
        change (T.indicator (fun ξ : V3 =>
          6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ))) (-(z.1 + z.2)) = _
        exact Set.indicator_of_mem hHigh.2
          (fun ξ : V3 => 6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ))
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
          rw [hpHigh, hqHigh]
          dsimp only [H]
          nlinarith only [mul_nonneg hp (mul_nonneg hq hr)]
    · rw [show K z = (0 : ℂ) by
        simp only [K, Set.indicator_of_notMem hz]]
      simp only [norm_zero]
      exact hRHS
  have hEstimate := thirdFull_integral_norm_le_rightOuter_L1244
    K F H hK hF hH hH0 hBound
  have hFIntegral : (∫ ξ : V3, F ξ ^ 2 ∂volume) =
      36 * (∫ ξ in T, ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2
        ∂volume) := by
    rw [hFEq, integral_indicator hT, integral_const_mul]
  have hHIntegral : (∫ ξ : V3, H ξ ∂volume) =
      thirdFullBudgetFirstMoment244 v := rfl
  have hKIntegral : (∫ z : PairV, K z ∂volume.prod volume) =
      ∫ z in S, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume := integral_indicator hS
  rw [← hKIntegral]
  calc
    ‖∫ z : PairV, K z ∂volume.prod volume‖ ≤
        2 * (∫ ξ : V3, F ξ ^ 2 ∂volume) *
          (∫ ξ : V3, H ξ ∂volume) := hEstimate
    _ = _ := by rw [hFIntegral, hHIntegral]; ring

/-- Quantitative high-maximum flux tail on the original complex solenoidal
Schwartz profile in the tie-broken low-first sector. -/
theorem thirdFullWeightedSchwartz_firstHighMaxIntegral_le244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (V : H3SpectralVelocityState)
    (hRep : ∀ j : A3,
      (V (h3ClassicalizationFinOfAxis j) : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (K : ℝ) (hK : 0 ≤ K) (hBound : ‖V‖ ≤ K)
    (R : ℕ) :
    ‖∫ z in thirdFullMinFirstHighMaxSector244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume‖ ≤
      648 * h3SobolevFirstMomentDeweightingConstant * K *
        ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2 := by
  have hMoment := thirdFullWeightedSchwartz_highRadialSixthMoment_le_velocityTail244
    v V hRep R
  have hCoord : ∀ j : A3,
      ‖V (h3ClassicalizationFinOfAxis j)‖ ≤ K := by
    intro j
    exact (h3SpectralFinVector_coordinate_norm_le
      V (h3ClassicalizationFinOfAxis j)).trans hBound
  have hFirst := (thirdFullWeightedSchwartz_moments_le_coordinateBound244
    v (fun j : A3 => V (h3ClassicalizationFinOfAxis j))
    hRep K hK hCoord).2
  have hMoment0 : 0 ≤ (∫ ξ in h3TopTailNaturalHighRadialSet R,
      ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) := by
    exact integral_nonneg (fun ξ => mul_nonneg
      (pow_nonneg (norm_nonneg ξ) 6)
      (sq_nonneg _))
  have hFirst0 := (thirdFullBudgetMoments_nonneg244 v).2
  calc
    ‖∫ z in thirdFullMinFirstHighMaxSector244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume‖ ≤
      72 * (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) *
      thirdFullBudgetFirstMoment244 v :=
        thirdFullSchwartzSixthPowerFlux_firstHighMaxIntegral_le_H3Tail244 v hDiv R
    _ ≤ 72 * (3 * ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2) *
      thirdFullBudgetFirstMoment244 v :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hMoment (by norm_num)) hFirst0
    _ ≤ 72 * (3 * ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2) *
      (3 * h3SobolevFirstMomentDeweightingConstant * K) :=
        mul_le_mul_of_nonneg_left hFirst (by positivity)
    _ = 648 * h3SobolevFirstMomentDeweightingConstant * K *
      ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2 := by ring


/-- Quantitative high-maximum flux tail on the original complex solenoidal
Schwartz profile in the tie-broken low-last sector. -/
theorem thirdFullWeightedSchwartz_lastHighMaxIntegral_le244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (V : H3SpectralVelocityState)
    (hRep : ∀ j : A3,
      (V (h3ClassicalizationFinOfAxis j) : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (K : ℝ) (hK : 0 ≤ K) (hBound : ‖V‖ ≤ K)
    (R : ℕ) :
    ‖∫ z in thirdFullMinLastHighMaxSector244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume‖ ≤
      648 * h3SobolevFirstMomentDeweightingConstant * K *
        ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2 := by
  have hMoment := thirdFullWeightedSchwartz_highRadialSixthMoment_le_velocityTail244
    v V hRep R
  have hCoord : ∀ j : A3,
      ‖V (h3ClassicalizationFinOfAxis j)‖ ≤ K := by
    intro j
    exact (h3SpectralFinVector_coordinate_norm_le
      V (h3ClassicalizationFinOfAxis j)).trans hBound
  have hFirst := (thirdFullWeightedSchwartz_moments_le_coordinateBound244
    v (fun j : A3 => V (h3ClassicalizationFinOfAxis j))
    hRep K hK hCoord).2
  have hMoment0 : 0 ≤ (∫ ξ in h3TopTailNaturalHighRadialSet R,
      ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) := by
    exact integral_nonneg (fun ξ => mul_nonneg
      (pow_nonneg (norm_nonneg ξ) 6)
      (sq_nonneg _))
  have hFirst0 := (thirdFullBudgetMoments_nonneg244 v).2
  calc
    ‖∫ z in thirdFullMinLastHighMaxSector244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume‖ ≤
      72 * (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) *
      thirdFullBudgetFirstMoment244 v :=
        thirdFullSchwartzSixthPowerFlux_lastHighMaxIntegral_le_H3Tail244 v hDiv R
    _ ≤ 72 * (3 * ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2) *
      thirdFullBudgetFirstMoment244 v :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hMoment (by norm_num)) hFirst0
    _ ≤ 72 * (3 * ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2) *
      (3 * h3SobolevFirstMomentDeweightingConstant * K) :=
        mul_le_mul_of_nonneg_left hFirst (by positivity)
    _ = 648 * h3SobolevFirstMomentDeweightingConstant * K *
      ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2 := by ring

end
end PrimeTensor.FirstMonomialTriad
