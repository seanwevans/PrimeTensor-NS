import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdKineticAnchoredNegativeChannel244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalUnabsorbedEssentialBarrier
import Mathlib.Tactic

/-!
# Kinetic-anchored essential signed spectral cubic obstruction

The kinetic-anchor Young absorption estimate controls actual H³ growth by
one time-independent anchored coefficient plus the NEGATIVE full third-order
signed cubic and one unit of physical dissipation:

  E'(t)/E(t) ≤ K(b) - (G₃(t) + 3 M₃(t) + D(t))/E(t).

Split the dissipatively adjusted adverse cubic into two spectral channels

  A_G(t) = -(G₃(t) + D(t)/2)/E(t),
  A_I(t) = -(3 M₃(t) + D(t)/2)/E(t).

Then the physical unabsorbed rate satisfies

  U(t) ≤ max(0, K(b) - 4422 + A_G(t) + A_I(t)).

Unlike the previous pointwise cofinal negative-channel theorem, the existing
PHYSICAL essential Riccati barrier lets us rule out any pair of integrable
a.e. upper envelopes for the adverse channels. A nested-tail argument selects
ONE SAME spectral channel whose adverse ratio defeats every integrable
majorant on every strict post-anchor terminal subtail.

No measurability of the spectral channel functions is assumed, and no
unconditional estimate or regularity conclusion is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

/-- The finite, time-independent lower-order Young expense at kinetic
anchor `b`; it is not an assumption that the third-order cubic is bounded. -/
noncomputable def h3PathKineticAnchorSignedCost244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (b : ℝ) : ℝ :=
  (3 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient +
    441 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient ^ 2) *
      velocityH3Energy0At u b

/-- Negative physical spectral gradient transport after paying exactly
half of the full physical viscosity, normalized by the actual H³ energy. -/
noncomputable def h3PathKineticGradientAdverseRatio244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : ℝ :=
  -(weightedH3CanonicalGradientTransport244
      (h3PathWeightedSpectralState244 u T hH3 t) +
      velocityH3DissipationAt u t / 2) / velocityH3EnergyAt u t

/-- The signed interpolation channel keeps its exact cyclic multiplicity
three and pays the remaining one-half of physical viscosity. -/
noncomputable def h3PathKineticInterpolationAdverseRatio244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : ℝ :=
  -(3 * weightedH3CanonicalSignedFirstMonomial244
      (h3PathWeightedSpectralState244 u T hH3 t) +
      velocityH3DissipationAt u t / 2) / velocityH3EnergyAt u t

/-- Kinetic energy and the already proved PDE Young absorption turn the
whole signed physical cubic into a growth bound with a FINITE coefficient
independent of the current high H³ energy. -/
theorem h3Path_kineticAnchor_signedCubic_normalizedGrowth244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t ≤
      h3PathKineticAnchorSignedCost244 u b +
        h3PathKineticGradientAdverseRatio244 u T hH3 t +
        h3PathKineticInterpolationAdverseRatio244 u T hH3 t := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hEone : 1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t
  have hEpos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one hEone
  have hEne : velocityH3EnergyAt u t ≠ 0 := ne_of_gt hEpos
  have hRoot : Real.sqrt (velocityH3EnergyAt u t) ≤
      velocityH3EnergyAt u t := by
    have hRootOne : 1 ≤ Real.sqrt (velocityH3EnergyAt u t) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hEone
    calc
      Real.sqrt (velocityH3EnergyAt u t) =
          1 * Real.sqrt (velocityH3EnergyAt u t) := by ring
      _ ≤ Real.sqrt (velocityH3EnergyAt u t) *
          Real.sqrt (velocityH3EnergyAt u t) :=
        mul_le_mul_of_nonneg_right hRootOne (Real.sqrt_nonneg _)
      _ = velocityH3EnergyAt u t := by
        nlinarith only [Real.sq_sqrt (le_trans zero_le_one hEone)]
  have hC : 0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
  have hK : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hScale :
      (3 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        velocityH3Energy0At u b) * Real.sqrt (velocityH3EnergyAt u t) ≤
      (3 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        velocityH3Energy0At u b) * velocityH3EnergyAt u t :=
    mul_le_mul_of_nonneg_left hRoot (by positivity)
  have hPDE := h3PathCanonical_deriv_add_oneDissipation_le_signedTop_only
    hH3 hClass hb ht
  rw [h3PathCanonical_twentyOneYoungAnchor_eq_linearEnergy u b t] at hPDE
  have hFinite :
      deriv (velocityH3EnergyAt u) t +
        velocityH3DissipationAt u t +
        velocityH3TransportDerivative3At u t ≤
          h3PathKineticAnchorSignedCost244 u b * velocityH3EnergyAt u t := by
    unfold h3PathKineticAnchorSignedCost244
    nlinarith only [hPDE, hScale]
  have hDiv :
      (deriv (velocityH3EnergyAt u) t +
        velocityH3DissipationAt u t +
        velocityH3TransportDerivative3At u t) / velocityH3EnergyAt u t ≤
          h3PathKineticAnchorSignedCost244 u b :=
    (div_le_iff₀ hEpos).2 hFinite
  have hPhysical := h3Path_weightedFullThird_eq_physical244
    hH3 hClass htClass
  have hAlgebra :
      (deriv (velocityH3EnergyAt u) t +
        velocityH3DissipationAt u t +
        velocityH3TransportDerivative3At u t) / velocityH3EnergyAt u t =
      deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t -
        (h3PathKineticGradientAdverseRatio244 u T hH3 t +
          h3PathKineticInterpolationAdverseRatio244 u T hH3 t) := by
    rw [hPhysical]
    unfold h3PathKineticGradientAdverseRatio244
      h3PathKineticInterpolationAdverseRatio244
      weightedH3CanonicalFullThirdCommutator244
    field_simp [hEne]
    <;> ring
  rw [hAlgebra] at hDiv
  linarith only [hDiv]

/-- The genuine measurable physical Riccati rate is dominated by an
anchored constant plus the TWO signed, dissipation-adjusted adverse ratios.
No spectral path measurability is needed for this pointwise bound. -/
theorem h3Path_unabsorbed_le_kineticSignedChannelRemainder244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    h3PathCanonicalUnabsorbedRiccatiRate u t ≤
      max 0 (h3PathKineticAnchorSignedCost244 u b - 4422 +
        h3PathKineticGradientAdverseRatio244 u T hH3 t +
        h3PathKineticInterpolationAdverseRatio244 u T hH3 t) := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  rw [h3PathCanonical_unabsorbedRiccatiRate_eq_positiveAboveBaseline
    hH3 hClass htClass]
  have hSlope := h3Path_kineticAnchor_signedCubic_normalizedGrowth244
    hH3 hClass hb ht
  have hShift :
      deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t - 4422 ≤
        h3PathKineticAnchorSignedCost244 u b - 4422 +
          h3PathKineticGradientAdverseRatio244 u T hH3 t +
          h3PathKineticInterpolationAdverseRatio244 u T hH3 t := by
    linarith only [hSlope]
  exact max_le_max_left 0 hShift

/-- Hypothetical nonextension excludes TWO simultaneous integrable
almost-everywhere majorants for the kinetic-anchored genuinely adverse
spectral cubic channels, on EVERY strict post-anchor terminal subtail. -/
theorem h3Path_kineticSignedChannels_no_joint_ae_integrable_majorants244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (rG rI : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hrG : IntegrableOn rG (Set.Ioo d T))
    (hrI : IntegrableOn rI (Set.Ioo d T)) :
    ¬ ((∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        h3PathKineticGradientAdverseRatio244 u T hH3 t ≤ rG t) ∧
       (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        h3PathKineticInterpolationAdverseRatio244 u T hH3 t ≤ rI t)) := by
  rintro ⟨hAeG, hAeI⟩
  have hdClass : d ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hd.1, hd.2⟩
  have hConst : IntegrableOn
      (fun _ : ℝ => |h3PathKineticAnchorSignedCost244 u b - 4422|)
      (Set.Ioo d T) := integrableOn_const measure_Ioo_lt_top.ne
  have hMajor : IntegrableOn
      (fun t : ℝ => |h3PathKineticAnchorSignedCost244 u b - 4422| +
        ‖rG t‖ + ‖rI t‖) (Set.Ioo d T) :=
    (hConst.add hrG.norm).add hrI.norm
  apply h3PathCanonical_unabsorbedRate_not_ae_le_integrable_on_subtail
    (r := fun t : ℝ => |h3PathKineticAnchorSignedCost244 u b - 4422| +
      ‖rG t‖ + ‖rI t‖)
    hH3 hNoExtension hClass hdClass hMajor
  filter_upwards [hAeG, hAeI, ae_restrict_mem measurableSet_Ioo]
    with t hBoundG hBoundI ht
  have htAnchor : t ∈ Set.Ioo b T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  have hPDE := h3Path_unabsorbed_le_kineticSignedChannelRemainder244
    hH3 hClass hb htAnchor
  have hG : rG t ≤ ‖rG t‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  have hI : rI t ≤ ‖rI t‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  have hC : h3PathKineticAnchorSignedCost244 u b - 4422 ≤
      |h3PathKineticAnchorSignedCost244 u b - 4422| :=
    le_abs_self _
  have hCeil :
      h3PathKineticAnchorSignedCost244 u b - 4422 +
        h3PathKineticGradientAdverseRatio244 u T hH3 t +
        h3PathKineticInterpolationAdverseRatio244 u T hH3 t ≤
      |h3PathKineticAnchorSignedCost244 u b - 4422| +
        ‖rG t‖ + ‖rI t‖ := by
    linarith only [hBoundG, hBoundI, hG, hI, hC]
  exact hPDE.trans (max_le
    (by positivity) hCeil)

/-- The same adverse cubic channel is selected BEFORE choosing either the
terminal subtail or the time-dependent integrable envelope. This upgrades
the previous pointwise kinetic-anchored cofinal negative-channel result to
a genuine essential physical-time obstruction. -/
theorem h3Path_kineticSignedChannels_fixed_ae_integrableMajorantBarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (∀ d : ℝ, d ∈ Set.Ioo b T → ∀ r : ℝ → ℝ,
      IntegrableOn r (Set.Ioo d T) →
      ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        h3PathKineticGradientAdverseRatio244 u T hH3 t ≤ r t)) ∨
    (∀ d : ℝ, d ∈ Set.Ioo b T → ∀ r : ℝ → ℝ,
      IntegrableOn r (Set.Ioo d T) →
      ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        h3PathKineticInterpolationAdverseRatio244 u T hH3 t ≤ r t)) := by
  classical
  by_cases hAllG : ∀ d : ℝ, d ∈ Set.Ioo b T → ∀ r : ℝ → ℝ,
      IntegrableOn r (Set.Ioo d T) →
      ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        h3PathKineticGradientAdverseRatio244 u T hH3 t ≤ r t)
  · exact Or.inl hAllG
  · right
    push Not at hAllG
    obtain ⟨d₀, hd₀, r₀, hr₀, hBoundG⟩ := hAllG
    intro d hd r hr hBoundI
    let e : ℝ := max d d₀
    have he : e ∈ Set.Ioo b T := by
      constructor
      · exact lt_of_lt_of_le hd.1 (le_max_left d d₀)
      · exact max_lt hd.2 hd₀.2
    have hSubsetG : Set.Ioo e T ⊆ Set.Ioo d₀ T := by
      intro t ht
      exact ⟨lt_of_le_of_lt (le_max_right d d₀) ht.1, ht.2⟩
    have hSubsetI : Set.Ioo e T ⊆ Set.Ioo d T := by
      intro t ht
      exact ⟨lt_of_le_of_lt (le_max_left d d₀) ht.1, ht.2⟩
    have hIntG : IntegrableOn r₀ (Set.Ioo e T) := hr₀.mono_set hSubsetG
    have hIntI : IntegrableOn r (Set.Ioo e T) := hr.mono_set hSubsetI
    have hAeG : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo e T)),
        h3PathKineticGradientAdverseRatio244 u T hH3 t ≤ r₀ t :=
      ae_restrict_of_ae_restrict_of_subset hSubsetG hBoundG
    have hAeI : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo e T)),
        h3PathKineticInterpolationAdverseRatio244 u T hH3 t ≤ r t :=
      ae_restrict_of_ae_restrict_of_subset hSubsetI hBoundI
    exact (h3Path_kineticSignedChannels_no_joint_ae_integrable_majorants244
      r₀ r hH3 hNoExtension hClass hb he hIntG hIntI) ⟨hAeG, hAeI⟩

/-- A concrete constant-threshold consequence: on every post-kinetic-anchor
terminal subtail, the SAME adverse physical cubic channel exceeds EVERY
finite normalized threshold outside the class of a.e.-bounded functions.
The threshold may be any real number, not merely a nonnegative one. -/
theorem h3Path_kineticSignedChannels_fixedEssentialHighRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (∀ d : ℝ, d ∈ Set.Ioo b T → ∀ M : ℝ,
      ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        h3PathKineticGradientAdverseRatio244 u T hH3 t ≤ M)) ∨
    (∀ d : ℝ, d ∈ Set.Ioo b T → ∀ M : ℝ,
      ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
        h3PathKineticInterpolationAdverseRatio244 u T hH3 t ≤ M)) := by
  rcases h3Path_kineticSignedChannels_fixed_ae_integrableMajorantBarrier244
      hH3 hNoExtension hClass hb with hG | hI
  · left
    intro d hd M
    have hConst : IntegrableOn (fun _ : ℝ => M) (Set.Ioo d T) :=
      integrableOn_const measure_Ioo_lt_top.ne
    exact hG d hd (fun _ : ℝ => M) hConst
  · right
    intro d hd M
    have hConst : IntegrableOn (fun _ : ℝ => M) (Set.Ioo d T) :=
      integrableOn_const measure_Ioo_lt_top.ne
    exact hI d hd (fun _ : ℝ => M) hConst

/-- Contrapositive: a.e. dissipation-adjusted lower bounds on both genuine
signed canonical cubics, modulo integrable time functions, suffice for
smooth continuation of the *actual* Navier-Stokes path. -/
theorem h3Path_extension_of_kineticSignedChannel_ae_integrableMajorants244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (rG rI : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hrG : IntegrableOn rG (Set.Ioo d T))
    (hrI : IntegrableOn rI (Set.Ioo d T))
    (hAeG : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      h3PathKineticGradientAdverseRatio244 u T hH3 t ≤ rG t)
    (hAeI : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      h3PathKineticInterpolationAdverseRatio244 u T hH3 t ≤ rI t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  exact (h3Path_kineticSignedChannels_no_joint_ae_integrable_majorants244
    rG rI hH3 hNoExtension hClass hb hd hrG hrI) ⟨hAeG, hAeI⟩

end
end PrimeTensor.FirstMonomialTriad
