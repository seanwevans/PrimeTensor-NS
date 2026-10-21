import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdTopFourierVarianceGain244
import Mathlib.Tactic

/-!
# A physical middle-moment barrier after sharp Fourier variance absorption

The first-Cauchy variance correction replaces the old sharp Young price
`(27/256) K⁴ E₀` by the smaller quantity `(27/256) K⁴ E₂²/D₃`.
This module transfers that reduction to the actual normalized H³ PDE budget
and its essential-time continuation obstruction.

The zero-dissipation case is resolved from the second Fourier Cauchy inequality:
`D₃ = 0` forces `E₃ = 0`, so both the Landau/dissipation margin and the
reduced middle-moment remainder vanish.  No global hypothesis `0<D₃` is used.

The conclusion is a necessary nonextension condition, not an independent
bound on the middle moment or an unconditional regularity result.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

/-- Sharp top-Landau cost after retaining the first Fourier Cauchy defect.
Lean's total division makes this zero at `D₃=0`, consistently with `E₃=0`. -/
noncomputable def h3PathTopFourierReducedMiddleMargin244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : ℝ :=
  ((27 / 256 : ℝ) *
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) ^ 4 *
      (velocityH3Energy2At u t ^ 2 / velocityH3Dissipation3At u t)) /
    velocityH3EnergyAt u t

/-- Vanishing physical third-order dissipation forces vanishing third-order
energy, by the *second*, uneliminated Fourier Cauchy estimate. -/
theorem h3Path_topFourier_zeroDissipation_forces_zeroThirdEnergy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hZero : velocityH3Dissipation3At u t = 0) :
    velocityH3Energy3At u t = 0 := by
  have hCS := h3Path_topFourier_secondCauchy_le244 hH3 hClass ht
  rw [hZero, mul_zero] at hCS
  have hNonneg := velocityH3Energy3At_nonneg u t
  nlinarith only [hCS, hNonneg]

/-- The actual Fourier Landau-minus-top-dissipation margin never exceeds
its sharper *middle moment* envelope, even when `D₃=0`. -/
theorem h3Path_topLandauMargin_le_reducedMiddleMoment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathKineticTopLandauMargin244 u t ≤
      h3PathTopFourierReducedMiddleMargin244 u t := by
  let K : ℝ := 4398 *
    (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t))
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by norm_num)
      (mul_nonneg h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
        (Real.sqrt_nonneg _))
  have hEpos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  by_cases hD : 0 < velocityH3Dissipation3At u t
  · have hReduced := h3Path_topFourier_reducedSharpYoung244
      hH3 hClass ht hK hD
    unfold h3PathKineticTopLandauMargin244
      h3PathTopFourierReducedMiddleMargin244
    apply (div_le_div_iff_of_pos_right hEpos).2
    dsimp only [K] at hReduced
    -- `linarith` regards differently associated division terms as
    -- unrelated atoms. Reassociate the quotient in the previously proved
    -- sharp Young estimate before applying the additive order equivalence.
    have hCost :
        (27 / 256 : ℝ) *
          ((4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t))) ^ 4 *
            velocityH3Energy2At u t ^ 2 /
            velocityH3Dissipation3At u t) =
        (27 / 256 : ℝ) *
          (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t))) ^ 4 *
          (velocityH3Energy2At u t ^ 2 /
            velocityH3Dissipation3At u t) := by
      ring
    rw [hCost] at hReduced
    exact (sub_le_iff_le_add).2 (by
      simpa only [add_comm] using hReduced)
  · have hDnonneg := velocityH3Dissipation3At_nonneg u t
    have hDzero : velocityH3Dissipation3At u t = 0 :=
      le_antisymm (le_of_not_gt hD) hDnonneg
    have hE3zero := h3Path_topFourier_zeroDissipation_forces_zeroThirdEnergy244
      hH3 hClass ht hDzero
    simp [h3PathKineticTopLandauMargin244,
      h3PathTopFourierReducedMiddleMargin244, hDzero, hE3zero]

/-- The sharp middle-moment Fourier price bounds normalized physical
H³ growth after freezing the kinetic anchor. -/
theorem h3Path_kineticAnchor_growth_le_reducedMiddleMoment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t ≤
      h3PathKineticAnchorSignedCost244 u b +
        h3PathTopFourierReducedMiddleMargin244 u t := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hGrowth := h3Path_kineticAnchor_normalizedGrowth_le_topLandauMargin244
    hH3 hClass hb ht
  have hReduced := h3Path_topLandauMargin_le_reducedMiddleMoment244
    hH3 hClass htClass
  linarith only [hGrowth, hReduced]

/-- Nonextension prevents any a.e. integrable upper envelope on the
*reduced middle-moment* remainder on every strict post-anchor subtail. -/
theorem h3Path_reducedMiddleMoment_not_ae_integrableMajorant244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (r : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hr : IntegrableOn r (Set.Ioo d T)) :
    ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        h3PathTopFourierReducedMiddleMargin244 u t ≤ r t) := by
  intro hAe
  have hMajor : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      h3PathKineticTopLandauMargin244 u t ≤ r t := by
    filter_upwards [hAe, ae_restrict_mem measurableSet_Ioo]
      with t hBound ht
    have htClass : t ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
    exact (h3Path_topLandauMargin_le_reducedMiddleMoment244
      hH3 hClass htClass).trans hBound
  exact (h3Path_kineticTopLandauMargin_not_ae_integrableMajorant244
    r hH3 hNoExtension hClass hb hd hr) hMajor

/-- The reduced middle-moment remainder is essentially unbounded above on
every strict post-anchor tail if the H³ path does not continue. -/
theorem h3Path_reducedMiddleMoment_essentialHighRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T) :
    ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      h3PathTopFourierReducedMiddleMargin244 u t ≤ M) := by
  have hConst : IntegrableOn (fun _ : ℝ => M) (Set.Ioo d T) :=
    integrableOn_const measure_Ioo_lt_top.ne
  exact h3Path_reducedMiddleMoment_not_ae_integrableMajorant244
    (fun _ : ℝ => M) hH3 hNoExtension hClass hb hd hConst

/-- Time integrability of the actual middle-to-top Fourier ratio with its
Landau multiplier is a sufficient H³ smooth continuation criterion. -/
theorem h3Path_extension_of_integrable_reducedMiddleMoment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hInt : IntegrableOn (h3PathTopFourierReducedMiddleMargin244 u)
      (Set.Ioo d T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  have hAe : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      h3PathTopFourierReducedMiddleMargin244 u t ≤
        h3PathTopFourierReducedMiddleMargin244 u t := by
    filter_upwards with t
    exact le_refl _
  exact (h3Path_reducedMiddleMoment_not_ae_integrableMajorant244
    (h3PathTopFourierReducedMiddleMargin244 u)
    hH3 hNoExtension hClass hb hd hInt) hAe

end
end PrimeTensor.FirstMonomialTriad
