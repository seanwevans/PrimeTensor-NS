import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdKineticEssentialNegativeChannel244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedTopSpectralCorridor
import Mathlib.Tactic

/-!
# Essential top Fourier corridor after kinetic-anchored absorption

The fixed kinetic anchor absorbs the first and second transport orders into
one physical viscous share plus a bounded multiple of H³ energy. The actual
third-order signed transport is controlled by the existing physical Landau
estimate. These two INDEPENDENT PDE estimates yield a quantitative upper
bound for the measurable physical growth rate involving the top H³ energy E₃,
top H³ dissipation D₃, and the kinetic anchor b:

  E'/E <= K(b) + (4398 C₁ sqrt(E) E₃ - D₃)/E.

Under hypothetical nonextension, the normalized Landau/dissipation margin
cannot be almost-everywhere bounded by ANY integrable time function on ANY
strict post-anchor terminal subtail. In particular, at positive outer
measure of times it exceeds EVERY prescribed finite constant. Thus the
pointwise physical top-frequency corridor from the earlier project is upgraded
to an essential-time obstruction, without assuming spectral-path measurability.

This is a necessary condition under hypothetical nonextension; the genuine
high-frequency estimate needed for continuation remains unproved.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

/-- Normalized excess of the canonical third-order Landau ceiling over
ACTUAL third-order Fourier dissipation. Unlike a signed cubic, it contains
only physical H³ energy and dissipation quantities. -/
noncomputable def h3PathKineticTopLandauMargin244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : ℝ :=
  ((4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t))) * velocityH3Energy3At u t -
      velocityH3Dissipation3At u t) / velocityH3EnergyAt u t

/-- The exact signed gradient/interpolation adverse sum stays below the
physical Landau-top margin: there is no assumption about the signs of G₃ or
3 M₃, and the inequality retains the actual top viscous dissipation. -/
theorem h3Path_kineticSignedAdverseSum_le_topLandauMargin244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathKineticGradientAdverseRatio244 u T hH3 t +
      h3PathKineticInterpolationAdverseRatio244 u T hH3 t ≤
      h3PathKineticTopLandauMargin244 u t := by
  have hEpos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hEne : velocityH3EnergyAt u t ≠ 0 := ne_of_gt hEpos
  have hTop := h3PathCanonical_abs_thirdTransport_le_kineticGradientTopEnergy
    hH3 hClass ht
  have hD3 : velocityH3Dissipation3At u t ≤
      velocityH3DissipationAt u t :=
    velocityH3Dissipation3At_le_dissipationAt u t
  have hSigned : -velocityH3TransportDerivative3At u t ≤
      |velocityH3TransportDerivative3At u t| := neg_le_abs _
  have hNum :
      -(velocityH3TransportDerivative3At u t +
        velocityH3DissipationAt u t) ≤
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) * velocityH3Energy3At u t -
        velocityH3Dissipation3At u t := by
    linarith only [hTop, hD3, hSigned]
  have hPhysical := h3Path_weightedFullThird_eq_physical244
    hH3 hClass ht
  have hSum :
      h3PathKineticGradientAdverseRatio244 u T hH3 t +
        h3PathKineticInterpolationAdverseRatio244 u T hH3 t =
      -(velocityH3TransportDerivative3At u t +
        velocityH3DissipationAt u t) / velocityH3EnergyAt u t := by
    rw [hPhysical]
    unfold h3PathKineticGradientAdverseRatio244
      h3PathKineticInterpolationAdverseRatio244
      weightedH3CanonicalFullThirdCommutator244
    field_simp [hEne]
    <;> ring
  rw [hSum]
  unfold h3PathKineticTopLandauMargin244
  exact (div_le_div_iff_of_pos_right hEpos).2 hNum

/-- The genuine physical logarithmic growth is bounded by a FIXED kinetic
anchor cost plus the physical top-frequency Landau/dissipation margin. This
combines lower-order Young absorption with the actual third-order Landau
estimate, instead of introducing a new cubic majorant hypothesis. -/
theorem h3Path_kineticAnchor_normalizedGrowth_le_topLandauMargin244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t ≤
      h3PathKineticAnchorSignedCost244 u b +
        h3PathKineticTopLandauMargin244 u t := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hGrowth := h3Path_kineticAnchor_signedCubic_normalizedGrowth244
    hH3 hClass hb ht
  have hLandau := h3Path_kineticSignedAdverseSum_le_topLandauMargin244
    hH3 hClass htClass
  linarith only [hGrowth, hLandau]

/-- The PHYSICAL measurable unabsorbed Riccati rate is controlled by the
positive part of the kinetic-anchored top Fourier Landau margin. -/
theorem h3Path_unabsorbed_le_kineticTopLandauRemainder244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    h3PathCanonicalUnabsorbedRiccatiRate u t ≤
      max 0 (h3PathKineticAnchorSignedCost244 u b - 4422 +
        h3PathKineticTopLandauMargin244 u t) := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  rw [h3PathCanonical_unabsorbedRiccatiRate_eq_positiveAboveBaseline
    hH3 hClass htClass]
  have hGrowth := h3Path_kineticAnchor_normalizedGrowth_le_topLandauMargin244
    hH3 hClass hb ht
  have hShift :
      deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t - 4422 ≤
        h3PathKineticAnchorSignedCost244 u b - 4422 +
          h3PathKineticTopLandauMargin244 u t := by
    linarith only [hGrowth]
  exact max_le_max_left 0 hShift

/-- The top Landau-minus-dissipation margin defeats every integrable a.e.
upper envelope on every strict post-kinetic-anchor terminal subtail under
nonextension. In contrast with earlier pointwise corridor witnesses, the
failure of domination is essential in the physical-time measure. -/
theorem h3Path_kineticTopLandauMargin_not_ae_integrableMajorant244
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
      h3PathKineticTopLandauMargin244 u t ≤ r t) := by
  intro hAe
  have hdClass : d ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hd.1, hd.2⟩
  have hConst : IntegrableOn
      (fun _ : ℝ => |h3PathKineticAnchorSignedCost244 u b - 4422|)
      (Set.Ioo d T) := integrableOn_const measure_Ioo_lt_top.ne
  have hMajor : IntegrableOn
      (fun t : ℝ => |h3PathKineticAnchorSignedCost244 u b - 4422| +
        ‖r t‖) (Set.Ioo d T) := hConst.add hr.norm
  apply h3PathCanonical_unabsorbedRate_not_ae_le_integrable_on_subtail
    (r := fun t : ℝ => |h3PathKineticAnchorSignedCost244 u b - 4422| +
      ‖r t‖) hH3 hNoExtension hClass hdClass hMajor
  filter_upwards [hAe, ae_restrict_mem measurableSet_Ioo]
    with t hBound ht
  have htAnchor : t ∈ Set.Ioo b T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  have hPhysical := h3Path_unabsorbed_le_kineticTopLandauRemainder244
    hH3 hClass hb htAnchor
  have hR : r t ≤ ‖r t‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  have hC : h3PathKineticAnchorSignedCost244 u b - 4422 ≤
      |h3PathKineticAnchorSignedCost244 u b - 4422| :=
    le_abs_self _
  have hNonneg : 0 ≤
      |h3PathKineticAnchorSignedCost244 u b - 4422| + ‖r t‖ := by
    positivity
  have hCeil : h3PathKineticAnchorSignedCost244 u b - 4422 +
      h3PathKineticTopLandauMargin244 u t ≤
        |h3PathKineticAnchorSignedCost244 u b - 4422| + ‖r t‖ := by
    linarith only [hBound, hR, hC]
  exact hPhysical.trans (max_le hNonneg hCeil)

/-- Under nonextension, for EVERY finite M and every strict post-anchor
tail, the Landau ceiling cannot be almost everywhere absorbed by D₃+M E.
This is an essential-time strengthening of the prior pointwise Fourier
corridor theorem. The spectral margin need not be assumed measurable. -/
theorem h3Path_kineticTopLandau_essentialFrequencyCorridor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T) :
    ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) * velocityH3Energy3At u t ≤
          velocityH3Dissipation3At u t + M * velocityH3EnergyAt u t) := by
  intro hAe
  have hConst : IntegrableOn (fun _ : ℝ => M) (Set.Ioo d T) :=
    integrableOn_const measure_Ioo_lt_top.ne
  apply h3Path_kineticTopLandauMargin_not_ae_integrableMajorant244
    (r := fun _ : ℝ => M) hH3 hNoExtension hClass hb hd hConst
  filter_upwards [hAe] with t ht
  have hEpos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  unfold h3PathKineticTopLandauMargin244
  apply (div_le_iff₀ hEpos).2
  linarith only [ht]

/-- A time-integrable, a.e. upper envelope for the top Fourier
Landau-minus-dissipation margin on ONE post-anchor tail suffices for smooth
continuation. The majorant is allowed to change sign and vary with time. -/
theorem h3Path_extension_of_ae_integrable_topLandauMargin_majorant244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (r : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hr : IntegrableOn r (Set.Ioo d T))
    (hAe : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      h3PathKineticTopLandauMargin244 u t ≤ r t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  exact (h3Path_kineticTopLandauMargin_not_ae_integrableMajorant244
    r hH3 hNoExtension hClass hb hd hr) hAe

/-- A *time-almost-everywhere* spectral dissipation criterion. If the
actual top H³ viscous block absorbs the Landau ceiling outside a null
set on just one strict post-kinetic-anchor terminal tail, smooth H³
continuation follows. This genuinely relaxes the earlier everywhere-in-
time criterion; it is still an unproved premise for general solutions. -/
theorem h3Path_extension_of_ae_topSpectralDissipationDominance244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hDominance : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) * velocityH3Energy3At u t ≤
          velocityH3Dissipation3At u t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  have hAe : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) * velocityH3Energy3At u t ≤
          velocityH3Dissipation3At u t + (0 : ℝ) * velocityH3EnergyAt u t := by
    filter_upwards [hDominance] with t ht
    simpa only [zero_mul, add_zero] using ht
  exact (h3Path_kineticTopLandau_essentialFrequencyCorridor244
    (M := 0) hH3 hNoExtension hClass hb hd) hAe

end
end PrimeTensor.FirstMonomialTriad
