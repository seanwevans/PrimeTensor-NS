import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalUniformSixthMomentTail
import Mathlib.Tactic

/-!
# High-maximum trilinear H3 flux tail on the low-middle sector

On a momentum triad p+q+r=0 with q the smallest frequency, the two
outer frequencies p and r are comparable within a factor two. If the
maximum Fourier gradient magnitude exceeds twice a radial cutoff, BOTH
outer frequencies are in the corresponding high-radial tail. This lets
us put the same high-radial L2 profile in both outer factors of the
existing L2-L2-L1 convolution estimate. There is therefore a genuinely
small trilinear flux tail, not just a small quadratic Fourier moment.

The initial theorem treats the middle-minimum sector; the other two
orientations require the same geometric argument after permutation.
All statements concern fixed interior physical times, not uniform endpoint
regularity or a favorable sign of the transport.
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

noncomputable local instance axisFintypeMiddleHighMaxTail244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The true tie-broken middle-minimum sector, restricted to a maximum
Fourier derivative magnitude at least twice the natural radial cutoff. -/
def thirdFullMinMiddleHighMaxSector244 (R : ℕ) : Set PairV :=
  { z | z ∈ thirdFullMinMiddleSector244 ∧
    2 * ((R : ℝ) + 1) ≤
      max (h3FourierGradientMagnitude z.1)
        (max (h3FourierGradientMagnitude (-(z.1 + z.2)))
          (h3FourierGradientMagnitude z.2)) }

/-- The max-high restriction is measurable even at the exact threshold. -/
theorem thirdFullMinMiddleHighMaxSector_measurable244 (R : ℕ) :
    MeasurableSet (thirdFullMinMiddleHighMaxSector244 R) := by
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
  exact thirdFullMinMiddleSector_measurable244.inter
    (isClosed_le continuous_const (hP.max (hQ.max hR))).measurableSet

/-- HIGH-MAX GEOMETRY: if q is minimal, a maximum gradient frequency of
2(R+1) forces BOTH outer frequencies p,r beyond R+1. This is the precise
reason no mixed-input L2 convolution inequality is necessary here. -/
theorem thirdFull_lowMiddle_highMax_forces_outerHigh244
    (z : PairV) (R : ℕ)
    (hLow : ‖-(z.1 + z.2)‖ ≤ min ‖z.1‖ ‖z.2‖)
    (hMax : 2 * ((R : ℝ) + 1) ≤
      max (h3FourierGradientMagnitude z.1)
        (max (h3FourierGradientMagnitude (-(z.1 + z.2)))
          (h3FourierGradientMagnitude z.2))) :
    z.1 ∈ h3TopTailNaturalHighRadialSet R ∧
      z.2 ∈ h3TopTailNaturalHighRadialSet R := by
  let q : V3 := -(z.1 + z.2)
  let P : ℝ := h3FourierGradientMagnitude z.1
  let Q : ℝ := h3FourierGradientMagnitude q
  let S : ℝ := h3FourierGradientMagnitude z.2
  let ρ : ℝ := (R : ℝ) + 1
  have hqP : ‖q‖ ≤ ‖z.1‖ := (le_min_iff.mp hLow).1
  have hqS : ‖q‖ ≤ ‖z.2‖ := (le_min_iff.mp hLow).2
  have hpTri : ‖z.1‖ ≤ ‖q‖ + ‖z.2‖ := by
    have hp : z.1 = -(q + z.2) := by dsimp [q]; abel
    rw [hp, norm_neg]
    exact norm_add_le q z.2
  have hsTri : ‖z.2‖ ≤ ‖z.1‖ + ‖q‖ := by
    have hs : z.2 = -(z.1 + q) := by dsimp [q]; abel
    rw [hs, norm_neg]
    exact norm_add_le z.1 q
  have hpS : ‖z.1‖ ≤ 2 * ‖z.2‖ := by linarith only [hpTri, hqS]
  have hsP : ‖z.2‖ ≤ 2 * ‖z.1‖ := by linarith only [hsTri, hqP]
  have hQS : Q ≤ S := by
    dsimp only [Q, S, h3FourierGradientMagnitude]
    exact mul_le_mul_of_nonneg_left hqS (by positivity)
  have hQP : Q ≤ P := by
    dsimp only [Q, P, h3FourierGradientMagnitude]
    exact mul_le_mul_of_nonneg_left hqP (by positivity)
  have hPS : P ≤ 2 * S := by
    dsimp only [P, S, h3FourierGradientMagnitude]
    calc
      (2 * Real.pi) * ‖z.1‖ ≤ (2 * Real.pi) * (2 * ‖z.2‖) :=
        mul_le_mul_of_nonneg_left hpS (by positivity)
      _ = 2 * ((2 * Real.pi) * ‖z.2‖) := by ring
  have hSP : S ≤ 2 * P := by
    dsimp only [S, P, h3FourierGradientMagnitude]
    calc
      (2 * Real.pi) * ‖z.2‖ ≤ (2 * Real.pi) * (2 * ‖z.1‖) :=
        mul_le_mul_of_nonneg_left hsP (by positivity)
      _ = 2 * ((2 * Real.pi) * ‖z.1‖) := by ring
  have hMax' : 2 * ρ ≤ max P (max Q S) := hMax
  have hOuterMax : 2 * ρ ≤ max P S := by
    rcases le_max_iff.mp hMax' with hp | hqs
    · exact hp.trans (le_max_left P S)
    · rcases le_max_iff.mp hqs with hq | hs
      · exact (hq.trans hQP).trans (le_max_left P S)
      · exact hs.trans (le_max_right P S)
  have hρ : 0 ≤ ρ := by
    dsimp only [ρ]
    positivity
  have hBoth : ρ ≤ P ∧ ρ ≤ S := by
    rcases le_max_iff.mp hOuterMax with hp | hs
    · constructor <;> linarith only [hp, hPS, hρ]
    · constructor <;> linarith only [hs, hSP, hρ]
  constructor
  · simp only [h3TopTailNaturalHighRadialSet, Set.mem_compl_iff,
      h3TerminalRadialFrequencyBelow, Set.mem_ofPred_eq]
    exact not_lt.mpr hBoth.1
  · simp only [h3TopTailNaturalHighRadialSet, Set.mem_compl_iff,
      h3TerminalRadialFrequencyBelow, Set.mem_ofPred_eq]
    exact not_lt.mpr hBoth.2

/-- Tail-localized genuine complex high-high-low trilinear flux. Both
outer cubic Fourier factors lie on the high-radial tail; the remaining
first Fourier moment is global. The coefficient is the same 72 as in the
unrestricted middle-minimum estimate. -/
theorem thirdFullSchwartzSixthPowerFlux_middleHighMaxIntegral_le_H3Tail244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (R : ℕ) :
    ‖∫ z in thirdFullMinMiddleHighMaxSector244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume‖ ≤
      72 * (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) *
      thirdFullBudgetFirstMoment244 v := by
  let S : Set PairV := thirdFullMinMiddleHighMaxSector244 R
  let T : Set V3 := h3TopTailNaturalHighRadialSet R
  let F : V3 → ℝ := T.indicator
    (fun ξ => 6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ))
  let H : V3 → ℝ := fun ξ => ‖ξ‖ * h3TriadSpectralAmplitude v ξ
  let K : PairV → ℂ := S.indicator (thirdFullSchwartzComplexSixthPowerFlux244 v)
  have hS : MeasurableSet S := thirdFullMinMiddleHighMaxSector_measurable244 R
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
      ‖K z‖ ≤ 2 * F z.1 * F z.2 * H (-(z.1 + z.2)) := by
    intro z
    have hRHS : 0 ≤ 2 * F z.1 * F z.2 * H (-(z.1 + z.2)) := by
      have hp := hF0 z.1
      have hr := hF0 z.2
      have hq := hH0 (-(z.1 + z.2))
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
      have hLow : ‖-(z.1 + z.2)‖ ≤ min ‖z.1‖ ‖z.2‖ :=
        thirdFullMinMiddleSector_isLow244 z hz.1
      have hLowP : frequencyNorm q ≤ min (frequencyNorm p) (frequencyNorm r) := by
        simpa only [frequencyNorm, p, q, r, WithLp.toLp_ofLp] using hLow
      have hHigh := thirdFull_lowMiddle_highMax_forces_outerHigh244 z R hLow hz.2
      have hpHigh : F z.1 =
          6 * (‖z.1‖ ^ 3 * h3TriadSpectralAmplitude v z.1) := by
        change (T.indicator (fun ξ : V3 =>
          6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ))) z.1 = _
        exact Set.indicator_of_mem hHigh.1
          (fun ξ : V3 => 6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ))
      have hrHigh : F z.2 =
          6 * (‖z.2‖ ^ 3 * h3TriadSpectralAmplitude v z.2) := by
        change (T.indicator (fun ξ : V3 =>
          6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ))) z.2 = _
        exact Set.indicator_of_mem hHigh.2
          (fun ξ : V3 => 6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ))
      have hPoint := thirdFullComplexSixthPowerFlux_lowMiddleH3Bound244
        p q r (U p) (U q) (U r) hm hA hLowP
      have hPoint' :
          ‖thirdFullSchwartzComplexSixthPowerFlux244 v z‖ ≤
            52 * (‖z.1‖ ^ 3 * h3TriadSpectralAmplitude v z.1) *
              (‖z.2‖ ^ 3 * h3TriadSpectralAmplitude v z.2) *
              (‖-(z.1 + z.2)‖ *
                h3TriadSpectralAmplitude v (-(z.1 + z.2))) := by
        simpa only [thirdFullSchwartzComplexSixthPowerFlux244,
          h3TriadSpectralAmplitude, h3TriadPolarizationNorm,
          frequencyNorm, WithLp.toLp_ofLp, p, q, r, U] using hPoint
      calc
        _ ≤ 52 * (‖z.1‖ ^ 3 * h3TriadSpectralAmplitude v z.1) *
          (‖z.2‖ ^ 3 * h3TriadSpectralAmplitude v z.2) *
          (‖-(z.1 + z.2)‖ *
            h3TriadSpectralAmplitude v (-(z.1 + z.2))) := hPoint'
        _ ≤ 2 * F z.1 * F z.2 * H (-(z.1 + z.2)) := by
          have hp : 0 ≤ ‖z.1‖ ^ 3 * h3TriadSpectralAmplitude v z.1 :=
            mul_nonneg (pow_nonneg (norm_nonneg _) _)
              (h3TriadSpectralAmplitude_nonneg v z.1)
          have hr : 0 ≤ ‖z.2‖ ^ 3 * h3TriadSpectralAmplitude v z.2 :=
            mul_nonneg (pow_nonneg (norm_nonneg _) _)
              (h3TriadSpectralAmplitude_nonneg v z.2)
          have hq : 0 ≤ H (-(z.1 + z.2)) := hH0 _
          rw [hpHigh, hrHigh]
          dsimp only [H]
          nlinarith only [mul_nonneg hp (mul_nonneg hr hq)]
    · rw [show K z = (0 : ℂ) by
        simp only [K, Set.indicator_of_notMem hz]]
      simp only [norm_zero]
      exact hRHS
  have hEstimate := h3Triad_integral_norm_le_L2_L1
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
Schwartz profile in the tie-broken low-middle sector. -/
theorem thirdFullWeightedSchwartz_middleHighMaxIntegral_le244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (V : H3SpectralVelocityState)
    (hRep : ∀ j : A3,
      (V (h3ClassicalizationFinOfAxis j) : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (K : ℝ) (hK : 0 ≤ K) (hBound : ‖V‖ ≤ K)
    (R : ℕ) :
    ‖∫ z in thirdFullMinMiddleHighMaxSector244 R,
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
    ‖∫ z in thirdFullMinMiddleHighMaxSector244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 v z ∂volume.prod volume‖ ≤
      72 * (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) *
      thirdFullBudgetFirstMoment244 v :=
        thirdFullSchwartzSixthPowerFlux_middleHighMaxIntegral_le_H3Tail244 v hDiv R
    _ ≤ 72 * (3 * ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2) *
      thirdFullBudgetFirstMoment244 v :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hMoment (by norm_num)) hFirst0
    _ ≤ 72 * (3 * ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2) *
      (3 * h3SobolevFirstMomentDeweightingConstant * K) :=
        mul_le_mul_of_nonneg_left hFirst (by positivity)
    _ = 648 * h3SobolevFirstMomentDeweightingConstant * K *
      ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2 := by ring

/-- A genuine trilinear high-maximum tail vanishes uniformly along
the SAME physical, real-solenoidal Schwartz recovery. The quantifiers run
over sufficiently late recovery indices at one fixed interior time; no
claim is made about uniformity as t approaches the terminal endpoint. -/
theorem exists_thirdFullPhysicalSnapshot_middleHighMaxTailVanishing244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (htNS : t ∈ Set.Ioo (0 : ℝ) T)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    ∃ (V : ℕ → H3SpectralVelocityState)
      (Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ),
      Tendsto V atTop
        (𝓝 (velocityH3SpectralStateAt u t hInt hMeas hFourier)) ∧
      (∀ (n : ℕ) (x : V3), ∑ j : A3,
        fderiv ℝ (h3SchwartzComplexify
          (Ψ n (h3ClassicalizationFinOfAxis j))) x
            (h3FourierAxisDirection j) = 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R N : ℕ, ∀ m : ℕ, N ≤ m →
        ‖∫ z in thirdFullMinMiddleHighMaxSector244 R,
          thirdFullSchwartzComplexSixthPowerFlux244
            (fun j : A3 => h3SchwartzComplexify
              (Ψ m (h3ClassicalizationFinOfAxis j))) z
            ∂volume.prod volume‖ < ε) ∧
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
  let v : ℕ → A3 → SchwartzMap V3 ℂ := fun n j =>
    h3SchwartzComplexify (Ψ n (h3ClassicalizationFinOfAxis j))
  have hRep : ∀ (n : ℕ) (j : A3),
      (V n (h3ClassicalizationFinOfAxis j) : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v n j)) ξ) := by
    intro n j
    exact hAE n (h3ClassicalizationFinOfAxis j)
  have hSix := thirdFullWeightedRecovery_eventuallyUniformHighSixthMoment244
    V (velocityH3SpectralStateAt u t hInt hMeas hFourier) hV v hRep
  let B : ℝ := 216 * h3SobolevFirstMomentDeweightingConstant * K
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity [h3SobolevFirstMomentDeweightingConstant_nonneg]
  refine ⟨V, Ψ, hV, hDiv, ?_, hFlux⟩
  intro ε hε
  let δ : ℝ := ε / (1 + B)
  have hOneB : 0 < 1 + B := by linarith
  have hδ : 0 < δ := div_pos hε hOneB
  have hδeq : (1 + B) * δ = ε := by
    calc
      (1 + B) * δ = (ε / (1 + B)) * (1 + B) := by
        dsimp only [δ]
        ring
      _ = ε := div_mul_cancel₀ ε hOneB.ne'
  obtain ⟨R, N, hSmall⟩ := hSix δ hδ
  refine ⟨R, N, ?_⟩
  intro m hm
  let G : A3 → H3SpectralScalarState :=
    fun j => V m (h3ClassicalizationFinOfAxis j)
  have hCoord : ∀ j : A3, ‖G j‖ ≤ K := by
    intro j
    exact (h3SpectralFinVector_coordinate_norm_le
      (V m) (h3ClassicalizationFinOfAxis j)).trans (hBound m)
  have hFirst := (thirdFullWeightedSchwartz_moments_le_coordinateBound244
    (v m) G (hRep m) K hK hCoord).2
  have hSmallM := hSmall m hm
  have hNonneg : 0 ≤ (∫ ξ in h3TopTailNaturalHighRadialSet R,
      ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude (v m) ξ ^ 2 ∂volume) :=
    integral_nonneg (fun ξ => mul_nonneg
      (pow_nonneg (norm_nonneg ξ) 6) (sq_nonneg _))
  have hStrict : B * δ < ε := by
    calc
      B * δ < (1 + B) * δ :=
        mul_lt_mul_of_pos_right (by linarith) hδ
      _ = ε := hδeq
  calc
    ‖∫ z in thirdFullMinMiddleHighMaxSector244 R,
        thirdFullSchwartzComplexSixthPowerFlux244 (v m) z
        ∂volume.prod volume‖ ≤
      72 * (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude (v m) ξ ^ 2 ∂volume) *
        thirdFullBudgetFirstMoment244 (v m) :=
          thirdFullSchwartzSixthPowerFlux_middleHighMaxIntegral_le_H3Tail244
            (v m) (hDiv m) R
    _ ≤ 72 * (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude (v m) ξ ^ 2 ∂volume) *
        (3 * h3SobolevFirstMomentDeweightingConstant * K) :=
          mul_le_mul_of_nonneg_left hFirst
            (mul_nonneg (by norm_num) hNonneg)
    _ = B * (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude (v m) ξ ^ 2 ∂volume) := by
          dsimp only [B]
          ring
    _ ≤ B * δ := mul_le_mul_of_nonneg_left hSmallM.le hB
    _ < ε := hStrict

end
end PrimeTensor.FirstMonomialTriad
