import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalMinimumFrequencyPartition
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Truncation.Convergence
import Mathlib.Tactic

/-!
# Strong H³ recovery excludes fixed-snapshot high-radial square-mass escape

The complete complex sixth-power flux has now been partitioned by its
minimum frequency. The next mathematical obstacle is to control high radial
Fourier tails *along the same physical Schwartz recovery*, not just for each
approximant separately.

For the exact solver's weighted Fourier L² representatives, introduce the
orthogonal high-radial projection with natural cutoffs. It has norm ≤ 1,
is additive, and its norm tends to zero on each fixed state. Strong
convergence then gives a common radius and an index after which all recovery
states have small high-radial L² mass. The conclusion is a fixed-time uniform
integrability statement, not a bound uniform toward a potential singular time.

This checkpoint is a state-space foundation. It does not yet assert high-tail
smallness for the *trilinear flux* or endpoint H³ continuation.
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

noncomputable local instance axisFintypeUniformHighRadial244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact high-radial Fourier L² cutoff on the solver's weighted state.
The cutoff is applied AFTER storing W₃(ξ) û(ξ), not to a raw Fourier
representative, so no uncontrolled multiplier enters. -/
noncomputable def thirdFullSpectralHighRadialApply244
    (n : ℕ) (G : H3SpectralScalarState) : H3SpectralScalarState :=
  ((MeasureTheory.Lp.memLp G).indicator
      (measurableSet_h3TopTailNaturalHighRadialSet n)).toLp
    ((h3TopTailNaturalHighRadialSet n).indicator G)

/-- Exact a.e. representative for the solver-state high-radial projection. -/
theorem thirdFullSpectralHighRadialApply_ae244
    (n : ℕ) (G : H3SpectralScalarState) :
    (thirdFullSpectralHighRadialApply244 n G : V3 → ℂ) =ᵐ[volume]
      (h3TopTailNaturalHighRadialSet n).indicator G := by
  let S : Set V3 := h3TopTailNaturalHighRadialSet n
  let f : V3 → ℂ := G
  have hf : MemLp (S.indicator f) 2 (volume : Measure V3) :=
    (MeasureTheory.Lp.memLp G).indicator
      (measurableSet_h3TopTailNaturalHighRadialSet n)
  have hRep : ((hf.toLp (S.indicator f) : H3SpectralScalarState) : V3 → ℂ)
      =ᵐ[volume] S.indicator f := MeasureTheory.MemLp.coeFn_toLp hf
  change ((hf.toLp (S.indicator f) : H3SpectralScalarState) : V3 → ℂ)
      =ᵐ[volume] S.indicator f
  exact hRep

/-- High-radial projection is a contraction in the actual Fourier L² norm. -/
theorem thirdFullSpectralHighRadialApply_norm_le244
    (n : ℕ) (G : H3SpectralScalarState) :
    ‖thirdFullSpectralHighRadialApply244 n G‖ ≤ ‖G‖ := by
  unfold thirdFullSpectralHighRadialApply244
  rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_def]
  exact ENNReal.toReal_mono (MeasureTheory.Lp.eLpNorm_ne_top G)
    (MeasureTheory.eLpNorm_indicator_le
      (s := h3TopTailNaturalHighRadialSet n)
      (f := (G : V3 → ℂ)))

/-- High-radial projection is additive on L² equivalence classes. -/
theorem thirdFullSpectralHighRadialApply_add244
    (n : ℕ) (F G : H3SpectralScalarState) :
    thirdFullSpectralHighRadialApply244 n (F + G) =
      thirdFullSpectralHighRadialApply244 n F +
        thirdFullSpectralHighRadialApply244 n G := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    thirdFullSpectralHighRadialApply_ae244 n (F + G),
    thirdFullSpectralHighRadialApply_ae244 n F,
    thirdFullSpectralHighRadialApply_ae244 n G,
    MeasureTheory.Lp.coeFn_add F G,
    MeasureTheory.Lp.coeFn_add
      (thirdFullSpectralHighRadialApply244 n F)
      (thirdFullSpectralHighRadialApply244 n G)
  ] with ξ hFG hF hG hIn hOut
  rw [hFG, hOut]
  by_cases hξ : ξ ∈ h3TopTailNaturalHighRadialSet n
  · simp only [Set.indicator_of_mem hξ, hIn, Pi.add_apply, hF, hG]
  · simp only [Set.indicator_of_notMem hξ, hF, hG, Pi.add_apply, add_zero]

/-- The square of the projected L² norm is exactly the high-radial
square mass. This is an identity, not an inequality. -/
theorem thirdFullSpectralHighRadialApply_norm_sq244
    (n : ℕ) (G : H3SpectralScalarState) :
    ‖thirdFullSpectralHighRadialApply244 n G‖ ^ 2 =
      ∫ ξ in h3TopTailNaturalHighRadialSet n, ‖G ξ‖ ^ 2 ∂volume := by
  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq,
    ← integral_indicator (measurableSet_h3TopTailNaturalHighRadialSet n)]
  apply integral_congr_ae
  filter_upwards [thirdFullSpectralHighRadialApply_ae244 n G]
    with ξ hξ
  rw [hξ]
  by_cases hz : ξ ∈ h3TopTailNaturalHighRadialSet n
  · simp only [Set.indicator_of_mem hz]
  · simp only [Set.indicator_of_notMem hz, norm_zero]
    norm_num

/-- Every fixed weighted spectral H³ state loses all high-radial L²
mass as the radius increases. -/
theorem thirdFullSpectralHighRadialApply_norm_tendsto_zero244
    (G : H3SpectralScalarState) :
    Tendsto (fun n : ℕ => ‖thirdFullSpectralHighRadialApply244 n G‖)
      atTop (𝓝 0) := by
  have hTail := tendsto_h3FourierComplexL2_highRadial_squareMass_zero G
  have hSq : Tendsto
      (fun n : ℕ => ‖thirdFullSpectralHighRadialApply244 n G‖ ^ 2)
      atTop (𝓝 0) := by
    apply hTail.congr'
    filter_upwards with n
    exact (thirdFullSpectralHighRadialApply_norm_sq244 n G).symm
  have hSqrt := (Real.continuous_sqrt.tendsto 0).comp hSq
  change Tendsto
    (fun n : ℕ => Real.sqrt (‖thirdFullSpectralHighRadialApply244 n G‖ ^ 2))
      atTop (𝓝 (Real.sqrt 0)) at hSqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg,
    norm_nonneg, Real.sqrt_zero] using hSqrt

/-- Apply the same cutoff to each of the three genuine Fourier components. -/
noncomputable def thirdFullSpectralVelocityHighRadialApply244
    (n : ℕ) (U : H3SpectralVelocityState) : H3SpectralVelocityState :=
  fun j => thirdFullSpectralHighRadialApply244 n (U j)

/-- Three-component high-radial cutoff is additive. -/
theorem thirdFullSpectralVelocityHighRadialApply_add244
    (n : ℕ) (U V : H3SpectralVelocityState) :
    thirdFullSpectralVelocityHighRadialApply244 n (U + V) =
      thirdFullSpectralVelocityHighRadialApply244 n U +
        thirdFullSpectralVelocityHighRadialApply244 n V := by
  funext j
  exact thirdFullSpectralHighRadialApply_add244 n (U j) (V j)

/-- The weighted three-component sup norm is not increased by
high-radial Fourier projection. -/
theorem thirdFullSpectralVelocityHighRadialApply_norm_le244
    (n : ℕ) (U : H3SpectralVelocityState) :
    ‖thirdFullSpectralVelocityHighRadialApply244 n U‖ ≤ ‖U‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg U)).2
  intro j
  exact (thirdFullSpectralHighRadialApply_norm_le244 n (U j)).trans
    (h3SpectralFinVector_coordinate_norm_le U j)

/-- A single fixed vector H³ state has vanishing full-vector high radial
norm, not merely separate coordinatewise bounds. -/
theorem thirdFullSpectralVelocityHighRadialApply_norm_tendsto_zero244
    (U : H3SpectralVelocityState) :
    Tendsto (fun n : ℕ => ‖thirdFullSpectralVelocityHighRadialApply244 n U‖)
      atTop (𝓝 0) := by
  have hScalar (j : Fin 3) :
      Tendsto (fun n : ℕ => thirdFullSpectralHighRadialApply244 n (U j))
        atTop (𝓝 (0 : H3SpectralScalarState)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero] using
      (thirdFullSpectralHighRadialApply_norm_tendsto_zero244 (U j))
  have hVec : Tendsto (fun n : ℕ =>
      thirdFullSpectralVelocityHighRadialApply244 n U)
      atTop (𝓝 (0 : H3SpectralVelocityState)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    change Tendsto (fun n : ℕ => thirdFullSpectralHighRadialApply244 n (U j))
      atTop (𝓝 (0 : H3SpectralScalarState))
    exact hScalar j
  -- The continuous norm map tends to the norm of zero, not to zero
  -- definitionally. Give the intermediate statement its exact codomain
  -- before simplifying `norm_zero`.
  have hNorm : Tendsto
      (fun n : ℕ => ‖thirdFullSpectralVelocityHighRadialApply244 n U‖)
      atTop (𝓝 ‖(0 : H3SpectralVelocityState)‖) :=
    (continuous_norm.tendsto (0 : H3SpectralVelocityState)).comp hVec
  simpa only [norm_zero] using hNorm

/-- HARD-MATH COMPACTNESS STEP: a strongly convergent sequence of actual
weighted H³ velocity states has a common high-frequency radius on which
all sufficiently late approximants have arbitrarily small Fourier L² tail.

The radius is chosen only from the limiting state and ε; the index is
chosen from strong convergence. No Schwartz seminorm bound is assumed. -/
theorem thirdFullWeightedRecovery_eventuallyUniformHighRadial244
    (V : ℕ → H3SpectralVelocityState) (U : H3SpectralVelocityState)
    (hV : Tendsto V atTop (𝓝 U))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R N : ℕ, ∀ m : ℕ, N ≤ m →
      ‖thirdFullSpectralVelocityHighRadialApply244 R (V m)‖ < ε := by
  have hTail := thirdFullSpectralVelocityHighRadialApply_norm_tendsto_zero244 U
  obtain ⟨R, hR⟩ := (Metric.tendsto_atTop.mp hTail)
    (ε / 2) (by positivity)
  have hRSmall :
      ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ < ε / 2 := by
    have h := hR R le_rfl
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using h
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hV)
    (ε / 2) (by positivity)
  refine ⟨R, N, ?_⟩
  intro m hm
  have hDiff : ‖V m - U‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hN m hm
  calc
    ‖thirdFullSpectralVelocityHighRadialApply244 R (V m)‖ =
        ‖thirdFullSpectralVelocityHighRadialApply244 R ((V m - U) + U)‖ := by
          rw [sub_add_cancel]
    _ = ‖thirdFullSpectralVelocityHighRadialApply244 R (V m - U) +
          thirdFullSpectralVelocityHighRadialApply244 R U‖ := by
            rw [thirdFullSpectralVelocityHighRadialApply_add244]
    _ ≤ ‖thirdFullSpectralVelocityHighRadialApply244 R (V m - U)‖ +
          ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ := norm_add_le _ _
    _ ≤ ‖V m - U‖ +
          ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ := by
            exact add_le_add
              (thirdFullSpectralVelocityHighRadialApply_norm_le244 R (V m - U))
              le_rfl
    _ < ε := by linarith only [hDiff, hRSmall]

/-- The raw homogeneous sixth moment on any natural high-radial tail is
bounded by the *same-region* weighted H³ square energy. This is the
frequency-localized version of the earlier global sixth-moment bridge. -/
theorem thirdFullWeightedSchwartz_highRadialSixthMoment_le244
    (G : H3SpectralScalarState) (f : SchwartzMap V3 ℂ)
    (hG : (G : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 f) ξ))
    (n : ℕ) :
    (∫ ξ in h3TopTailNaturalHighRadialSet n,
      ‖ξ‖ ^ 6 * ‖(𝓕 f) ξ‖ ^ 2 ∂volume) ≤
      ‖thirdFullSpectralHighRadialApply244 n G‖ ^ 2 := by
  let S : Set V3 := h3TopTailNaturalHighRadialSet n
  have hSixInt : Integrable (fun ξ : V3 =>
      ‖ξ‖ ^ 6 * ‖(𝓕 f) ξ‖ ^ 2) volume := by
    let P : SchwartzMap V3 ℂ :=
      SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 f)
    have h := P.integrable_pow_mul volume 6
    change Integrable (fun ξ : V3 =>
      ‖ξ‖ ^ 6 * ‖(𝓕 f) ξ * (𝓕 f) ξ‖) volume at h
    simpa only [norm_mul, pow_two] using h
  have hGInt : Integrable
      (fun ξ : V3 => ‖(G : V3 → ℂ) ξ‖ ^ 2) volume :=
    (MeasureTheory.Lp.memLp G).norm.integrable_sq
  have hAE : ∀ᵐ ξ ∂(volume.restrict S),
      ‖ξ‖ ^ 6 * ‖(𝓕 f) ξ‖ ^ 2 ≤ ‖(G : V3 → ℂ) ξ‖ ^ 2 := by
    filter_upwards [ae_restrict_of_ae (s := S) hG] with ξ hξ
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
  have hSixTailInt : Integrable
      (fun ξ : V3 => ‖ξ‖ ^ 6 * ‖(𝓕 f) ξ‖ ^ 2)
      ((volume : Measure V3).restrict S) :=
    hSixInt.mono_measure Measure.restrict_le_self
  have hGTailInt : Integrable
      (fun ξ : V3 => ‖(G : V3 → ℂ) ξ‖ ^ 2)
      ((volume : Measure V3).restrict S) :=
    hGInt.mono_measure Measure.restrict_le_self
  calc
    (∫ ξ in S, ‖ξ‖ ^ 6 * ‖(𝓕 f) ξ‖ ^ 2 ∂volume) ≤
      ∫ ξ in S, ‖(G : V3 → ℂ) ξ‖ ^ 2 ∂volume := by
        -- Apply the integral theorem to the *already specified goal*, so
        -- its implicit integrands cannot be inferred as fresh metavariables.
        change (∫ ξ : V3, ‖ξ‖ ^ 6 * ‖(𝓕 f) ξ‖ ^ 2
            ∂((volume : Measure V3).restrict S)) ≤
          (∫ ξ : V3, ‖(G : V3 → ℂ) ξ‖ ^ 2
            ∂((volume : Measure V3).restrict S))
        apply integral_mono_ae
        · exact hSixTailInt
        · exact hGTailInt
        · exact hAE
    _ = ‖thirdFullSpectralHighRadialApply244 n G‖ ^ 2 :=
      (thirdFullSpectralHighRadialApply_norm_sq244 n G).symm

/-- Exact Euclidean three-component Fourier amplitude inherits the
high-radial sixth-moment bound, component by component. -/
theorem thirdFullWeightedSchwartz_vectorHighRadialSixthMoment_le244
    (v : A3 → SchwartzMap V3 ℂ)
    (G : A3 → H3SpectralScalarState)
    (hG : ∀ j : A3, (G j : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (n : ℕ) :
    (∫ ξ in h3TopTailNaturalHighRadialSet n,
      ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) ≤
      ∑ j : A3, ‖thirdFullSpectralHighRadialApply244 n (G j)‖ ^ 2 := by
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
    (∫ ξ in h3TopTailNaturalHighRadialSet n,
        ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) =
      ∫ ξ in h3TopTailNaturalHighRadialSet n,
        ∑ j : A3, ‖ξ‖ ^ 6 * ‖(𝓕 (v j)) ξ‖ ^ 2 ∂volume := by
          simp_rw [h3TriadSpectralAmplitude_sq, Finset.mul_sum]
    _ = ∑ j : A3, ∫ ξ in h3TopTailNaturalHighRadialSet n,
          ‖ξ‖ ^ 6 * ‖(𝓕 (v j)) ξ‖ ^ 2 ∂volume := by
            simpa using
              (integral_finsetSum
                (μ := (volume : Measure V3).restrict
                  (h3TopTailNaturalHighRadialSet n))
                (Finset.univ : Finset A3)
                (fun j _ => (hSix j).integrableOn))
    _ ≤ ∑ j : A3, ‖thirdFullSpectralHighRadialApply244 n (G j)‖ ^ 2 :=
      Finset.sum_le_sum (fun j _ =>
        thirdFullWeightedSchwartz_highRadialSixthMoment_le244
          (G j) (v j) (hG j) n)

/-- The ORIGINAL physical solenoidal Schwartz recovery, already known to
converge in weighted H³ and to recover the exact signed transport, also has
uniformly vanishing high-frequency square tails for sufficiently late indices.
No new realization or extra Fourier-moment hypothesis is chosen. -/
theorem exists_thirdFullPhysicalSnapshot_globalFluxAndUniformHighRadial244
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
        ‖thirdFullSpectralVelocityHighRadialApply244 R (V m)‖ < ε) ∧
      (∀ n : ℕ,
        let v : A3 → SchwartzMap V3 ℂ :=
          fun j => h3SchwartzComplexify
            (Ψ n (h3ClassicalizationFinOfAxis j))
        ‖∫ z : PairV, thirdFullSchwartzComplexSixthPowerFlux244 v z
            ∂volume.prod volume‖ ≤
          1944 * h3SobolevFirstMomentDeweightingConstant * K ^ 3) ∧
      Tendsto (fun n : ℕ =>
        ((2 * Real.pi) ^ 7 / 3) *
          (∫ z : PairV,
            thirdFullSchwartzComplexSixthPowerFlux244
              (fun j : A3 => h3SchwartzComplexify
                (Ψ n (h3ClassicalizationFinOfAxis j))) z
              ∂volume.prod volume).im)
        atTop (𝓝 (velocityH3TransportDerivative3At u t)) := by
  obtain ⟨V, Ψ, K, hK, hV, hDiv, hBudget, hFlux⟩ :=
    exists_thirdFullPhysicalSnapshot_globalMinSectorH3Bound244
      hNS htNS hH3 hClass ht hFourier
  refine ⟨V, Ψ, K, hK, hV, hDiv, ?_, hBudget, hFlux⟩
  intro ε hε
  exact thirdFullWeightedRecovery_eventuallyUniformHighRadial244
    V (velocityH3SpectralStateAt u t hInt hMeas hFourier) hV ε hε

end
end PrimeTensor.FirstMonomialTriad
