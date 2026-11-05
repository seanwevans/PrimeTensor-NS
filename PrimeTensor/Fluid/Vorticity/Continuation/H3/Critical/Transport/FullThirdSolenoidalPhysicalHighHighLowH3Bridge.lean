import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalHighHighLowH3Budget
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalPhysicalMomentBridge
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Duhamel.Tail.Cubic.L2.Baseline
import Mathlib.Tactic

/-!
# The high-high-low H³ flux is controlled by the exact physical spectral recovery

The previous genuine complex solenoidal high-high-low estimate needs a sixth
radial Fourier L² moment and a first radial Fourier L¹ moment.  Neither is an
extra assumption on the actual physical approximation: the exact weighted H³
state contains both. In particular, the H³ spectral square weight is

  1 + q + q² + q³, with q = (2π)² |ξ|²,

and an already-proved theorem yields |ξ|³ ≤ W₃(ξ). Thus the SIXTH
unweighted radial moment is contractive against the *same* weighted L² state.
The earlier physical bridge gives the first L¹ moment on that same sequence.

For every complex solenoidal Schwartz field whose three true weighted
representatives satisfy ‖G_j‖ ≤ K, the high-high-low sector flux is bounded by

  72 * (3 K²) * (3 C₁ K) = 648 C₁ K³.

We then apply this inequality to the actual physical Schwartz recovery family
at a fixed interior Navier--Stokes snapshot.  K is uniform in recovery index,
not in physical time. No sign, coercivity, smallness of the comparable-frequency
sector, or endpoint regularity statement is inferred.
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

noncomputable local instance axisFintypePhysicalHighHighLow244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact sixth radial Fourier moment in the preceding high-high-low
integral estimate, with NO `2π` inserted into the raw frequency variable. -/
noncomputable def thirdFullBudgetSixthMoment244
    (v : A3 → SchwartzMap V3 ℂ) : ℝ :=
  ∫ ξ : V3, ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume

/-- A genuine Schwartz Fourier component represented by `G = W₃ * 𝓕f`
has its homogeneous cubic L² norm bounded by the weighted H³ norm. -/
theorem thirdFullWeightedSchwartz_sixthMoment_le244
    (G : H3SpectralScalarState) (f : SchwartzMap V3 ℂ)
    (hG : (G : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 f) ξ)) :
    (∫ ξ : V3, ‖ξ‖ ^ 6 * ‖(𝓕 f) ξ‖ ^ 2 ∂volume) ≤ ‖G‖ ^ 2 := by
  have hSixInt : Integrable
      (fun ξ : V3 => ‖ξ‖ ^ 6 * ‖(𝓕 f) ξ‖ ^ 2) volume := by
    let P : SchwartzMap V3 ℂ :=
      SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 f)
    have h := P.integrable_pow_mul volume 6
    change Integrable (fun ξ : V3 =>
      ‖ξ‖ ^ 6 * ‖(𝓕 f) ξ * (𝓕 f) ξ‖) volume at h
    simpa only [norm_mul, pow_two] using h
  have hGInt : Integrable
      (fun ξ : V3 => ‖(G : V3 → ℂ) ξ‖ ^ 2) volume :=
    (MeasureTheory.Lp.memLp G).norm.integrable_sq
  calc
    (∫ ξ : V3, ‖ξ‖ ^ 6 * ‖(𝓕 f) ξ‖ ^ 2 ∂volume) ≤
      ∫ ξ : V3, ‖(G : V3 → ℂ) ξ‖ ^ 2 ∂volume := by
        refine integral_mono_ae hSixInt hGInt ?_
        filter_upwards [hG] with ξ hξ
        rw [hξ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (h3SobolevFrequencyWeight_pos ξ).le]
        have hCube : ‖ξ‖ ^ 3 ≤ h3SobolevFrequencyWeight ξ :=
          h3FourierNorm_cubed_le_h3SobolevFrequencyWeight ξ
        have hSquare := pow_le_pow_left₀
          (pow_nonneg (norm_nonneg ξ) 3) hCube 2
        have hRadial : ‖ξ‖ ^ 6 ≤ (h3SobolevFrequencyWeight ξ) ^ 2 := by
          nlinarith only [hSquare]
        calc
          ‖ξ‖ ^ 6 * ‖(𝓕 f) ξ‖ ^ 2 ≤
            (h3SobolevFrequencyWeight ξ) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hRadial (sq_nonneg _)
          _ = (h3SobolevFrequencyWeight ξ * ‖(𝓕 f) ξ‖) ^ 2 := by ring
    _ = ‖G‖ ^ 2 :=
      (h3FourierComplexL2_norm_sq_eq_integral_norm_sq G).symm

/-- All three sixth-order Fourier moments sum exactly to the squared
Euclidean Fourier amplitude, then are bounded by the genuine three weighted
H³ components. No separate homogeneous moment hypothesis is introduced. -/
theorem thirdFullWeightedSchwartz_vectorSixthMoment_le244
    (v : A3 → SchwartzMap V3 ℂ)
    (G : A3 → H3SpectralScalarState)
    (hG : ∀ j : A3, (G j : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ)) :
    thirdFullBudgetSixthMoment244 v ≤ ∑ j : A3, ‖G j‖ ^ 2 := by
  have hSix (j : A3) : Integrable
      (fun ξ : V3 => ‖ξ‖ ^ 6 * ‖(𝓕 (v j)) ξ‖ ^ 2) volume := by
    let P : SchwartzMap V3 ℂ :=
      SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
        (𝓕 (v j)) (𝓕 (v j))
    have h := P.integrable_pow_mul volume 6
    change Integrable (fun ξ : V3 =>
      ‖ξ‖ ^ 6 * ‖(𝓕 (v j)) ξ * (𝓕 (v j)) ξ‖) volume at h
    simpa only [norm_mul, pow_two] using h
  calc
    thirdFullBudgetSixthMoment244 v =
        ∫ ξ : V3, ∑ j : A3,
          ‖ξ‖ ^ 6 * ‖(𝓕 (v j)) ξ‖ ^ 2 ∂volume := by
            unfold thirdFullBudgetSixthMoment244
            simp_rw [h3TriadSpectralAmplitude_sq, Finset.mul_sum]
    _ = ∑ j : A3,
          ∫ ξ : V3, ‖ξ‖ ^ 6 * ‖(𝓕 (v j)) ξ‖ ^ 2 ∂volume := by
            simpa using
              (integral_finsetSum (μ := (volume : Measure V3))
                (Finset.univ : Finset A3) (fun j _ => hSix j))
    _ ≤ ∑ j : A3, ‖G j‖ ^ 2 :=
      Finset.sum_le_sum (fun j _ =>
        thirdFullWeightedSchwartz_sixthMoment_le244 (G j) (v j) (hG j))

/-- Each weighted component bounded by K gives the native sixth moment
ceiling 3 K², using the repository's genuine three-axis cardinality. -/
theorem thirdFullWeightedSchwartz_sixthMoment_le_coordinateBound244
    (v : A3 → SchwartzMap V3 ℂ)
    (G : A3 → H3SpectralScalarState)
    (hG : ∀ j : A3, (G j : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (K : ℝ) (hK : 0 ≤ K) (hBound : ∀ j, ‖G j‖ ≤ K) :
    thirdFullBudgetSixthMoment244 v ≤ 3 * K ^ 2 := by
  calc
    thirdFullBudgetSixthMoment244 v ≤ ∑ j : A3, ‖G j‖ ^ 2 :=
      thirdFullWeightedSchwartz_vectorSixthMoment_le244 v G hG
    _ ≤ ∑ _j : A3, K ^ 2 :=
      Finset.sum_le_sum (fun j _ =>
        (sq_le_sq₀ (norm_nonneg (G j)) hK).mpr (hBound j))
    _ = 3 * K ^ 2 := by rw [axis_sum_three]; ring

/-- The genuine integrated high-high-low sixth-power flux is controlled
solely by the weighted H³ spectral coordinate ceiling. The first moment is
from the existing physical moment bridge, while the sixth L² moment is proved
above; no new Schwartz seminorm or fixed outer-frequency cutoff is assumed. -/
theorem thirdFullWeightedSchwartz_lowMiddleIntegral_le_coordinateBound244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (G : A3 → H3SpectralScalarState)
    (hG : ∀ j : A3, (G j : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (K : ℝ) (hK : 0 ≤ K) (hBound : ∀ j, ‖G j‖ ≤ K)
    (s : Set PairV) (hs : MeasurableSet s)
    (hLow : ∀ z ∈ s,
      ‖-(z.1 + z.2)‖ ≤ min ‖z.1‖ ‖z.2‖) :
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
        thirdFullBudgetFirstMoment244 v := by
          simpa only [thirdFullBudgetSixthMoment244,
            thirdFullBudgetFirstMoment244, thirdFullBudgetMomentAmplitude244]
            using (thirdFullSchwartzSixthPowerFlux_lowMiddleIntegral_le_H3Moments244
              v hDiv s hs hLow)
    _ ≤ 72 * (3 * K ^ 2) * thirdFullBudgetFirstMoment244 v := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hSix (by norm_num)) hFirst0
    _ ≤ 72 * (3 * K ^ 2) *
        (3 * h3SobolevFirstMomentDeweightingConstant * K) := by
      exact mul_le_mul_of_nonneg_left hFirst (by positivity)
    _ = 648 * h3SobolevFirstMomentDeweightingConstant * K ^ 3 := by
      ring

/-- The exact physical snapshot recovery has a UNIFORM high-high-low
Fourier flux bound along the SAME real solenoidal Schwartz sequence that
recovers the original signed physical H³ transport. This is a fixed-time
statement: the constant K is not asserted uniform as t approaches T. -/
theorem exists_thirdFullPhysicalSnapshot_lowMiddleH3Budget244
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
    (s : ℕ → Set PairV) (hs : ∀ n, MeasurableSet (s n))
    (hLow : ∀ n z, z ∈ s n →
      ‖-(z.1 + z.2)‖ ≤ min ‖z.1‖ ‖z.2‖) :
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
          fun j => h3SchwartzComplexify (Ψ n (h3ClassicalizationFinOfAxis j))
        thirdFullBudgetSixthMoment244 v ≤ 3 * K ^ 2 ∧
        ‖∫ z in s n, thirdFullSchwartzComplexSixthPowerFlux244 v z
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
    fun j => h3SchwartzComplexify (Ψ n (h3ClassicalizationFinOfAxis j))
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
  have hSector := thirdFullWeightedSchwartz_lowMiddleIntegral_le_coordinateBound244
    v (hDiv n) G hRep K hK hCoord (s n) (hs n) (hLow n)
  exact ⟨hSix, hSector⟩

end
end PrimeTensor.FirstMonomialTriad
