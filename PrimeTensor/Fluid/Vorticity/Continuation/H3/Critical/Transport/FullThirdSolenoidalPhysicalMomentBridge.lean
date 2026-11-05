import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalBudgetMomentControl
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalPureSixthPowerFluxLimit
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Raw.Fourier.L2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Heat.Path
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Vorticity.Flux
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.L1.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Round.Trip
import Mathlib.Tactic

/-!
# Physical weighted-H³ bridge for the genuine solenoidal Fourier flux budget

The unsigned sixth-power flux estimate of `FullThirdSolenoidalBudgetMomentControl`
uses raw Fourier mass M₀ and first L¹ moment M₁.  The old physical
solenoidal recovery has *weighted* Fourier representatives, not free raw
moment assumptions.  We connect those exact representatives, a.e., to
`h3SpectralScalarRawFourier`, and transfer the existing scalar H³ bounds to
the actual vector amplitude.

If all three weighted components have norm at most K, then
  M₀ ≤ 3 K²,   M₁ ≤ 3 C₁ K,   B₆ ≤ 27 C₁ K³,
where C₁ is the existing H³ first-moment deweighting constant.

The same statement applies to the solenoidal physical snapshot density
witness, since its weighted states converge strongly and are therefore
uniformly bounded.  It does not control the off-shell flux or prove an
endpoint H³ a priori estimate.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology FourierTransform
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypePhysicalMomentBridge244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The weighted spectral representative is deweighted to the ACTUAL Fourier
transform of the given Schwartz field, not to an arbitrary completion. -/
theorem thirdFullWeightedSchwartz_rawFourier_ae244
    (G : H3SpectralScalarState) (f : SchwartzMap V3 ℂ)
    (hG : (G : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 f) ξ)) :
    (fun ξ : V3 => (𝓕 f) ξ) =ᵐ[volume]
      h3SpectralScalarRawFourier G := by
  filter_upwards [hG] with ξ hξ
  change (𝓕 f) ξ = h3SobolevFrequencyWeightInvComplex ξ * G ξ
  rw [hξ, ← mul_assoc, h3SobolevFrequencyWeightInvComplex_mul_weight ξ,
    one_mul]

/-- The raw Schwartz Fourier kinetic mass is contractively controlled by its
exact weighted H³ L² representative. -/
theorem thirdFullWeightedSchwartz_fourierMass_le244
    (G : H3SpectralScalarState) (f : SchwartzMap V3 ℂ)
    (hG : (G : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 f) ξ)) :
    (∫ ξ : V3, ‖(𝓕 f) ξ‖ ^ 2 ∂volume) ≤ ‖G‖ ^ 2 := by
  have hRaw := thirdFullWeightedSchwartz_rawFourier_ae244 G f hG
  have hL2 := h3SpectralScalarRawFourierL2_ae G
  calc
    (∫ ξ : V3, ‖(𝓕 f) ξ‖ ^ 2 ∂volume) =
        ∫ ξ : V3, ‖(h3SpectralScalarRawFourierL2 G : V3 → ℂ) ξ‖ ^ 2
          ∂volume := by
            apply integral_congr_ae
            filter_upwards [hRaw, hL2] with ξ hξ hL2ξ
            rw [hξ, ← hL2ξ]
    _ = ‖h3SpectralScalarRawFourierL2 G‖ ^ 2 :=
      (h3FourierComplexL2_norm_sq_eq_integral_norm_sq
        (h3SpectralScalarRawFourierL2 G)).symm
    _ ≤ ‖G‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (norm_h3SpectralScalarRawFourierL2_le G) 2

/-- The existing first-moment deweighting estimate holds for the SAME
Schwartz Fourier transform under its a.e. weighted representative. -/
theorem thirdFullWeightedSchwartz_firstMoment_le244
    (G : H3SpectralScalarState) (f : SchwartzMap V3 ℂ)
    (hG : (G : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 f) ξ)) :
    (∫ ξ : V3, ‖ξ‖ * ‖(𝓕 f) ξ‖ ∂volume) ≤
      h3SobolevFirstMomentDeweightingConstant * ‖G‖ := by
  calc
    (∫ ξ : V3, ‖ξ‖ * ‖(𝓕 f) ξ‖ ∂volume) =
        ∫ ξ : V3, ‖ξ‖ * ‖h3SpectralScalarRawFourier G ξ‖
          ∂volume := by
            apply integral_congr_ae
            filter_upwards [thirdFullWeightedSchwartz_rawFourier_ae244 G f hG]
              with ξ hξ
            rw [hξ]
    _ ≤ _ := h3SpectralScalarRawFourier_firstMoment_integral_le G

/-- Exact finite-coordinate mass and first-moment bounds for the vector
amplitude used by the three sixth-power flux contractions. -/
theorem thirdFullWeightedSchwartz_vectorMoments_le244
    (v : A3 → SchwartzMap V3 ℂ)
    (G : A3 → H3SpectralScalarState)
    (hG : ∀ j : A3, (G j : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ)) :
    thirdFullBudgetFourierMass244 v ≤ ∑ j : A3, ‖G j‖ ^ 2 ∧
      thirdFullBudgetFirstMoment244 v ≤
        ∑ j : A3, h3SobolevFirstMomentDeweightingConstant * ‖G j‖ := by
  have hSquare (j : A3) :
      Integrable (fun ξ : V3 => ‖(𝓕 (v j)) ξ‖ ^ 2) volume := by
    let P : SchwartzMap V3 ℂ :=
      SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
        (𝓕 (v j)) (𝓕 (v j))
    have h := P.integrable_pow_mul volume 0
    change Integrable
      (fun ξ : V3 => ‖ξ‖ ^ 0 * ‖(𝓕 (v j)) ξ * (𝓕 (v j)) ξ‖)
        volume at h
    simpa only [pow_zero, one_mul, norm_mul, pow_two] using h
  have hFirst (j : A3) :
      Integrable (fun ξ : V3 => ‖ξ‖ * ‖(𝓕 (v j)) ξ‖) volume := by
    have h := (𝓕 (v j)).integrable_pow_mul volume 1
    simpa only [pow_one] using h
  constructor
  · calc
      thirdFullBudgetFourierMass244 v =
          ∫ ξ : V3, ∑ j : A3, ‖(𝓕 (v j)) ξ‖ ^ 2 ∂volume := by
            unfold thirdFullBudgetFourierMass244
              thirdFullBudgetMomentAmplitude244
            simp_rw [h3TriadSpectralAmplitude_sq]
      _ = ∑ j : A3, ∫ ξ : V3, ‖(𝓕 (v j)) ξ‖ ^ 2 ∂volume := by
            simpa using
              (integral_finsetSum (μ := (volume : Measure V3))
                (Finset.univ : Finset A3) (fun j _ => hSquare j))
      _ ≤ ∑ j : A3, ‖G j‖ ^ 2 := by
            exact Finset.sum_le_sum (fun j _ =>
              thirdFullWeightedSchwartz_fourierMass_le244 (G j) (v j) (hG j))
  · have hMajor : Integrable
        (fun ξ : V3 => ∑ j : A3, ‖ξ‖ * ‖(𝓕 (v j)) ξ‖)
          volume :=
      integrable_finsetSum Finset.univ (fun j _ => hFirst j)
    calc
      thirdFullBudgetFirstMoment244 v ≤
          ∫ ξ : V3, ∑ j : A3, ‖ξ‖ * ‖(𝓕 (v j)) ξ‖
            ∂volume := by
              refine integral_mono (thirdFullBudgetMoments_integrable244 v).2
                hMajor ?_
              intro ξ
              change ‖ξ‖ * h3TriadSpectralAmplitude v ξ ≤
                ∑ j : A3, ‖ξ‖ * ‖(𝓕 (v j)) ξ‖
              rw [← Finset.mul_sum]
              exact mul_le_mul_of_nonneg_left
                (h3TriadSpectralAmplitude_le_sum v ξ) (norm_nonneg ξ)
      _ = ∑ j : A3,
          ∫ ξ : V3, ‖ξ‖ * ‖(𝓕 (v j)) ξ‖ ∂volume := by
            simpa using
              (integral_finsetSum (μ := (volume : Measure V3))
                (Finset.univ : Finset A3) (fun j _ => hFirst j))
      _ ≤ ∑ j : A3, h3SobolevFirstMomentDeweightingConstant * ‖G j‖ := by
            exact Finset.sum_le_sum (fun j _ =>
              thirdFullWeightedSchwartz_firstMoment_le244 (G j) (v j) (hG j))

/-- All three coordinate weighted bounds imply a genuine quantitative
uniform raw-moment bound; no separate Fourier moment hypotheses. -/
theorem thirdFullWeightedSchwartz_moments_le_coordinateBound244
    (v : A3 → SchwartzMap V3 ℂ)
    (G : A3 → H3SpectralScalarState)
    (hG : ∀ j : A3, (G j : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (K : ℝ) (hK : 0 ≤ K) (hBound : ∀ j, ‖G j‖ ≤ K) :
    thirdFullBudgetFourierMass244 v ≤ 3 * K ^ 2 ∧
      thirdFullBudgetFirstMoment244 v ≤
        3 * h3SobolevFirstMomentDeweightingConstant * K := by
  obtain ⟨hMass, hMoment⟩ :=
    thirdFullWeightedSchwartz_vectorMoments_le244 v G hG
  have hC : 0 ≤ h3SobolevFirstMomentDeweightingConstant :=
    h3SobolevFirstMomentDeweightingConstant_nonneg
  constructor
  · calc
      thirdFullBudgetFourierMass244 v ≤ ∑ j : A3, ‖G j‖ ^ 2 := hMass
      _ ≤ ∑ _j : A3, K ^ 2 :=
        Finset.sum_le_sum (fun j _ =>
          (sq_le_sq₀ (norm_nonneg (G j)) hK).mpr (hBound j))
      _ = 3 * K ^ 2 := by rw [axis_sum_three]; ring
  · calc
      thirdFullBudgetFirstMoment244 v ≤
        ∑ j : A3, h3SobolevFirstMomentDeweightingConstant * ‖G j‖ := hMoment
      _ ≤ ∑ _j : A3, h3SobolevFirstMomentDeweightingConstant * K :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hBound j) hC)
      _ = 3 * h3SobolevFirstMomentDeweightingConstant * K := by
        rw [axis_sum_three]
        ring

/-- Physical weighted H³ control gives a cubic ceiling on the exact
unsigned sixth-power Fourier flux budget, without any spectral cutoff. -/
theorem thirdFullWeightedSchwartz_fluxBudget_le_coordinateBound244
    (v : A3 → SchwartzMap V3 ℂ)
    (G : A3 → H3SpectralScalarState)
    (hG : ∀ j : A3, (G j : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (K : ℝ) (hK : 0 ≤ K) (hBound : ∀ j, ‖G j‖ ≤ K) :
    thirdFullSchwartzSixthFluxTotalBudget244 v ≤
      27 * h3SobolevFirstMomentDeweightingConstant * K ^ 3 := by
  obtain ⟨hMass, hFirst⟩ :=
    thirdFullWeightedSchwartz_moments_le_coordinateBound244
      v G hG K hK hBound
  have hNonneg := (thirdFullBudgetMoments_nonneg244 v).2
  calc
    thirdFullSchwartzSixthFluxTotalBudget244 v ≤
        3 * thirdFullBudgetFourierMass244 v * thirdFullBudgetFirstMoment244 v :=
          thirdFullSchwartzSixthFluxTotalBudget_le_L2FirstMoment244 v
    _ ≤ 3 * (3 * K ^ 2) * thirdFullBudgetFirstMoment244 v := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hMass (by norm_num)) hNonneg
    _ ≤ 3 * (3 * K ^ 2) *
        (3 * h3SobolevFirstMomentDeweightingConstant * K) := by
      exact mul_le_mul_of_nonneg_left hFirst (by positivity)
    _ = 27 * h3SobolevFirstMomentDeweightingConstant * K ^ 3 := by
      ring

/-- Strong convergence of the actual vector H³ approximants supplies a
single norm ceiling, including the finite initial segment. -/
theorem thirdFullWeightedRecovery_normBound_of_tendsto244
    (V : ℕ → H3SpectralVelocityState) (U : H3SpectralVelocityState)
    (hV : Tendsto V atTop (𝓝 U)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, ‖V n‖ ≤ K := by
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.mp hV) 1 (by norm_num)
  let S : ℝ := ∑ k ∈ Finset.range N, ‖V k‖
  have hS : 0 ≤ S :=
    Finset.sum_nonneg (fun k _ => norm_nonneg (V k))
  refine ⟨S + ‖U‖ + 1, by linarith [norm_nonneg U], ?_⟩
  intro n
  by_cases hn : n < N
  · have hTerm : ‖V n‖ ≤ S := by
      dsimp only [S]
      exact Finset.single_le_sum (fun k _ => norm_nonneg (V k))
        (Finset.mem_range.mpr hn)
    linarith [norm_nonneg U]
  · have hDist : ‖V n - U‖ < 1 := by
      simpa only [dist_eq_norm] using hN n (Nat.le_of_not_gt hn)
    have hTriangle : ‖V n‖ ≤ ‖V n - U‖ + ‖U‖ := by
      simpa only [sub_add_cancel] using norm_add_le (V n - U) U
    linarith

/-- Apply the coordinate estimates to the exact physical three-component
weighted spectral state (product sup norm). -/
theorem thirdFullWeightedVelocity_fluxBudget_le244
    (v : A3 → SchwartzMap V3 ℂ)
    (V : H3SpectralVelocityState)
    (hV : ∀ j : A3,
      (V (h3ClassicalizationFinOfAxis j) : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (K : ℝ) (hK : 0 ≤ K) (hBound : ‖V‖ ≤ K) :
    thirdFullBudgetFourierMass244 v ≤ 3 * K ^ 2 ∧
      thirdFullBudgetFirstMoment244 v ≤
        3 * h3SobolevFirstMomentDeweightingConstant * K ∧
      thirdFullSchwartzSixthFluxTotalBudget244 v ≤
        27 * h3SobolevFirstMomentDeweightingConstant * K ^ 3 := by
  let G : A3 → H3SpectralScalarState :=
    fun j => V (h3ClassicalizationFinOfAxis j)
  have hCoord : ∀ j : A3, ‖G j‖ ≤ K := by
    intro j
    exact (h3SpectralFinVector_coordinate_norm_le
      V (h3ClassicalizationFinOfAxis j)).trans hBound
  have hAE : ∀ j : A3, (G j : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ) := by
    intro j
    exact hV j
  obtain ⟨h0, h1⟩ :=
    thirdFullWeightedSchwartz_moments_le_coordinateBound244 v G hAE K hK hCoord
  exact ⟨h0, h1,
    thirdFullWeightedSchwartz_fluxBudget_le_coordinateBound244
      v G hAE K hK hCoord⟩

/-- The OLD physical Navier–Stokes snapshot has one solenoidal Schwartz
recovery family with uniformly controlled raw moments AND unsigned flux.
The weighted norm ceiling is a consequence of strong convergence, not an
additional analytic assumption.  The signed physical transport limit is
retained along precisely the same family. -/
theorem exists_thirdFullPhysicalSnapshot_solenoidalUniformMomentBudget244
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
      (∀ n : ℕ,
        let v : A3 → SchwartzMap V3 ℂ :=
          fun j => h3SchwartzComplexify (Ψ n (h3ClassicalizationFinOfAxis j))
        thirdFullBudgetFourierMass244 v ≤ 3 * K ^ 2 ∧
        thirdFullBudgetFirstMoment244 v ≤
          3 * h3SobolevFirstMomentDeweightingConstant * K ∧
        thirdFullSchwartzSixthFluxTotalBudget244 v ≤
          27 * h3SobolevFirstMomentDeweightingConstant * K ^ 3) ∧
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
  refine ⟨V, Ψ, K, hK, hV, hDiv, ?_, hFlux⟩
  intro n
  let v : A3 → SchwartzMap V3 ℂ :=
    fun j => h3SchwartzComplexify (Ψ n (h3ClassicalizationFinOfAxis j))
  have hRep : ∀ j : A3,
      (V n (h3ClassicalizationFinOfAxis j) : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ) := by
    intro j
    exact hAE n (h3ClassicalizationFinOfAxis j)
  exact thirdFullWeightedVelocity_fluxBudget_le244 v (V n) hRep
    K hK (hBound n)

end
end PrimeTensor.FirstMonomialTriad
