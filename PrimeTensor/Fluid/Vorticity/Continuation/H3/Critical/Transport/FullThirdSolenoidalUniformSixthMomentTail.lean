import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalUniformHighRadialRecovery
import Mathlib.Tactic

/-!
# Uniform sixth Fourier moment tails of the exact physical solenoidal recovery

The high-radial cutoff on the genuine weighted H3 state has norm tending to
zero uniformly over sufficiently late recovery indices.  The localized raw
homogeneous sixth moment is bounded by the squares of those same weighted
coordinate tails, hence it too vanishes uniformly in the approximation index.
No time-uniform bound or extra Schwartz seminorm is assumed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology FourierTransform
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeUniformSixthMomentTail244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The high-radial homogeneous-sixth Fourier moment of a three-component
Schwartz profile is controlled by the tail of its genuine vector H3 state. -/
theorem thirdFullWeightedSchwartz_highRadialSixthMoment_le_velocityTail244
    (v : A3 → SchwartzMap V3 ℂ)
    (V : H3SpectralVelocityState)
    (hRep : ∀ j : A3,
      (V (h3ClassicalizationFinOfAxis j) : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (R : ℕ) :
    (∫ ξ in h3TopTailNaturalHighRadialSet R,
      ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) ≤
      3 * ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2 := by
  let G : A3 → H3SpectralScalarState :=
    fun j => V (h3ClassicalizationFinOfAxis j)
  have hG : ∀ j : A3, (G j : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ) :=
    hRep
  have hComponent (j : A3) :
      ‖thirdFullSpectralHighRadialApply244 R (G j)‖ ≤
        ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ := by
    exact h3SpectralFinVector_coordinate_norm_le
      (thirdFullSpectralVelocityHighRadialApply244 R V)
      (h3ClassicalizationFinOfAxis j)
  calc
    (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) ≤
      ∑ j : A3, ‖thirdFullSpectralHighRadialApply244 R (G j)‖ ^ 2 :=
        thirdFullWeightedSchwartz_vectorHighRadialSixthMoment_le244 v G hG R
    _ ≤ ∑ _j : A3, ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2 :=
      Finset.sum_le_sum (fun j _ =>
        (sq_le_sq₀
          (norm_nonneg (thirdFullSpectralHighRadialApply244 R (G j)))
          (norm_nonneg (thirdFullSpectralVelocityHighRadialApply244 R V))).mpr
            (hComponent j))
    _ = 3 * ‖thirdFullSpectralVelocityHighRadialApply244 R V‖ ^ 2 := by
      rw [axis_sum_three]
      ring

/-- Strong weighted H3 recovery excludes escape of the exact homogeneous
sixth Fourier moment, uniformly for all sufficiently late approximants. -/
theorem thirdFullWeightedRecovery_eventuallyUniformHighSixthMoment244
    (V : ℕ → H3SpectralVelocityState)
    (U : H3SpectralVelocityState)
    (hV : Tendsto V atTop (𝓝 U))
    (v : ℕ → A3 → SchwartzMap V3 ℂ)
    (hRep : ∀ (n : ℕ) (j : A3),
      (V n (h3ClassicalizationFinOfAxis j) : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v n j)) ξ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R N : ℕ, ∀ m : ℕ, N ≤ m →
      (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude (v m) ξ ^ 2 ∂volume) < ε := by
  let δ : ℝ := min (1 / 2) (ε / 12)
  have hδpos : 0 < δ := by
    dsimp only [δ]
    exact lt_min_iff.mpr ⟨by norm_num, by positivity⟩
  have hδone : δ ≤ 1 := by
    dsimp only [δ]
    have h := min_le_left (1 / 2 : ℝ) (ε / 12)
    linarith
  have hδeps : 3 * δ ≤ ε / 4 := by
    dsimp only [δ]
    have h := min_le_right (1 / 2 : ℝ) (ε / 12)
    linarith
  obtain ⟨R, N, hTail⟩ :=
    thirdFullWeightedRecovery_eventuallyUniformHighRadial244 V U hV δ hδpos
  refine ⟨R, N, ?_⟩
  intro m hm
  have hM := thirdFullWeightedSchwartz_highRadialSixthMoment_le_velocityTail244
    (v m) (V m) (hRep m) R
  have hSmall : ‖thirdFullSpectralVelocityHighRadialApply244 R (V m)‖ < δ :=
    hTail m hm
  have hSq : ‖thirdFullSpectralVelocityHighRadialApply244 R (V m)‖ ^ 2 ≤
      δ ^ 2 :=
    pow_le_pow_left₀
      (norm_nonneg (thirdFullSpectralVelocityHighRadialApply244 R (V m)))
      hSmall.le 2
  have hδsq : δ ^ 2 ≤ δ := by
    have hMul := mul_le_mul_of_nonneg_left hδone hδpos.le
    nlinarith only [hMul]
  calc
    (∫ ξ in h3TopTailNaturalHighRadialSet R,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude (v m) ξ ^ 2 ∂volume) ≤
      3 * ‖thirdFullSpectralVelocityHighRadialApply244 R (V m)‖ ^ 2 := hM
    _ ≤ 3 * δ ^ 2 := mul_le_mul_of_nonneg_left hSq (by norm_num)
    _ ≤ 3 * δ := mul_le_mul_of_nonneg_left hδsq (by norm_num)
    _ ≤ ε / 4 := hδeps
    _ < ε := by linarith

/-- The exact real solenoidal Schwartz recovery at an interior physical
snapshot has uniformly vanishing high-radial sixth moments, while it still
recovers the genuinely signed physical H3 transport. -/
theorem exists_thirdFullPhysicalSnapshot_uniformHighSixthMoment244
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
      (Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ) (K : ℝ),
      0 ≤ K ∧
      Tendsto V atTop
        (𝓝 (velocityH3SpectralStateAt u t hInt hMeas hFourier)) ∧
      (∀ (n : ℕ) (x : V3), ∑ j : A3,
        fderiv ℝ (h3SchwartzComplexify
          (Ψ n (h3ClassicalizationFinOfAxis j))) x
            (h3FourierAxisDirection j) = 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R N : ℕ, ∀ m : ℕ, N ≤ m →
        (∫ ξ in h3TopTailNaturalHighRadialSet R,
          ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude
            (fun j : A3 => h3SchwartzComplexify
              (Ψ m (h3ClassicalizationFinOfAxis j))) ξ ^ 2 ∂volume) < ε) ∧
      (∀ n : ℕ,
        let v : A3 → SchwartzMap V3 ℂ :=
          fun j => h3SchwartzComplexify (Ψ n (h3ClassicalizationFinOfAxis j))
        ‖∫ z : V3 × V3, thirdFullSchwartzComplexSixthPowerFlux244 v z
            ∂volume.prod volume‖ ≤
          1944 * h3SobolevFirstMomentDeweightingConstant * K ^ 3) ∧
      Tendsto (fun n : ℕ =>
        ((2 * Real.pi) ^ 7 / 3) *
          (∫ z : V3 × V3,
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
  have hSmall := thirdFullWeightedRecovery_eventuallyUniformHighSixthMoment244
    V (velocityH3SpectralStateAt u t hInt hMeas hFourier) hV v hRep
  refine ⟨V, Ψ, K, hK, hV, hDiv, ?_, ?_, hFlux⟩
  · intro ε hε
    exact hSmall ε hε
  · intro n
    have hCoord : ∀ j : A3,
        ‖V n (h3ClassicalizationFinOfAxis j)‖ ≤ K := by
      intro j
      exact (h3SpectralFinVector_coordinate_norm_le
        (V n) (h3ClassicalizationFinOfAxis j)).trans (hBound n)
    exact thirdFullWeightedSchwartz_globalMinSectorIntegral_le244
      (v n) (hDiv n)
      (fun j : A3 => V n (h3ClassicalizationFinOfAxis j))
      (hRep n) K hK hCoord

end
end PrimeTensor.FirstMonomialTriad
