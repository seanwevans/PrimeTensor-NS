import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalIntegratedSignedBudget244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalMeasurability
import Mathlib.Tactic

/-!
# Automatic compact-time canonical gradient budget for signed physical concentration

The actual H³ energy-class path has a continuous canonical square-root-energy
first-gradient envelope on every strict interval, without an additional
temporal-integrability assumption. Its compact-time integral is therefore
finite. The physical order-two commutator has previously been bounded by
36 times this envelope at each positive-mass time. Integrating that bound
eliminates the abstract order-two transport ceiling in the physical
three-channel budget:

  R(s)-R(t) <= integral(H + L) + 36 integral(h),
  h = C1 sqrt(E_H3).

Integrability of the actual normalized transport, global heat, Leray and
variance-derivative profiles is still explicitly assumed where splitting
or the fundamental theorem of calculus needs it. No time-integrability
of the gradient envelope is assumed; it follows from the strict H³ class.
No sign or ceiling for the heat/Leray action is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1600000

/-- The canonical sqrt-H³ gradient coefficient is automatically integrable
on every compact strict preterminal interval. There is no terminal-time
integrability claim. -/
theorem h3Path_canonicalGradientEnvelope_intervalIntegrable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t) :
    IntervalIntegrable (h3PathCanonicalSqrtEnergyGradientEnvelope u)
      volume s t := by
  have hEnergyCont : ContinuousOn (velocityH3EnergyAt u) (Set.Ioo a T) :=
    continuousOn_velocityH3EnergyAt_on_energyClassTail hH3 hClass
  have hSqrtCont : ContinuousOn
      (fun r : ℝ => Real.sqrt (velocityH3EnergyAt u r)) (Set.Ioo a T) :=
    Real.continuous_sqrt.comp_continuousOn hEnergyCont
  have hEnvelopeCont : ContinuousOn
      (h3PathCanonicalSqrtEnergyGradientEnvelope u) (Set.Ioo a T) := by
    unfold h3PathCanonicalSqrtEnergyGradientEnvelope
    exact continuousOn_const.mul hSqrtCont
  have hSubset : Set.Icc s t ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  exact (hEnvelopeCont.mono hSubset).intervalIntegrable_of_Icc hst

/-- Signed normalized order-two transport spends no more than the integral
of the canonical C1 sqrt-H³ envelope times the sharp proven factor 36.
The integrability of the transport source is kept explicit. -/
theorem h3Path_physicalOrderTwo_integral_le_gradientAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hTransportIntegrable : IntervalIntegrable
      (h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass)
      volume s t) :
    (∫ r in s..t, h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass r) ≤
      36 * (∫ r in s..t, h3PathCanonicalSqrtEnergyGradientEnvelope u r) := by
  have hEnvelopeIntegrable :=
    h3Path_canonicalGradientEnvelope_intervalIntegrable244
      hH3 hClass hs ht hst
  calc
    (∫ r in s..t, h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass r) ≤
        (∫ r in s..t, 36 * h3PathCanonicalSqrtEnergyGradientEnvelope u r) := by
      apply intervalIntegral.integral_mono_on hst
        hTransportIntegrable (hEnvelopeIntegrable.const_mul 36)
      intro r hr
      have hrClass : r ∈ Set.Ioo a T :=
        ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
      exact h3Path_globalOrderTwoNormalizedRate_le_gradientBudget244
        hH3 hClass hrClass (hMass r hr) (hD r hr)
    _ = 36 * (∫ r in s..t, h3PathCanonicalSqrtEnergyGradientEnvelope u r) := by
      rw [intervalIntegral.integral_const_mul]

/-- Physical concentration action obeys a strict-time integrated
heat-plus-Leray balance with an AUTOMATIC square-root-H³ order-two allowance.
Only separate integrability of the three actual source profiles and the
variance derivative is assumed, as required by the previous exact FTC. -/
theorem h3Path_physicalVariance_drop_le_heatLeray_gradientAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDerivativeIntegrable : IntervalIntegrable
      (deriv (h3PathTopFourierNormalizedVarianceOnClass244 hClass)) volume s t)
    (hHeatIntegrable : IntervalIntegrable
      (h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass) volume s t)
    (hTransportIntegrable : IntervalIntegrable
      (h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass) volume s t)
    (hLerayIntegrable : IntervalIntegrable
      (h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass) volume s t) :
    h3PathTopFourierNormalizedRadialVariance244 u s -
        h3PathTopFourierNormalizedRadialVariance244 u t -
        36 * (∫ r in s..t, h3PathCanonicalSqrtEnergyGradientEnvelope u r) ≤
      (∫ r in s..t,
        h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass r) +
      (∫ r in s..t,
        h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass r) := by
  have hExact := h3Path_physicalVariance_integratedHeat_transport_Leray_eq_drop244
    hH3 hClass hs ht hst hMass hD
    hDerivativeIntegrable hHeatIntegrable hTransportIntegrable hLerayIntegrable
  have hTransport := h3Path_physicalOrderTwo_integral_le_gradientAction244
    hH3 hClass hs ht hst.le hMass hD hTransportIntegrable
  linarith only [hExact, hTransport]

/-- Near-Young physical concentration requires the integrated heat/Leray
channels to overcome the earlier variance and the proved gradient action.
There is no abstract order-two budget constant. -/
theorem h3Path_nearYoung_forces_heatLeray_after_gradientAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDerivativeIntegrable : IntervalIntegrable
      (deriv (h3PathTopFourierNormalizedVarianceOnClass244 hClass)) volume s t)
    (hHeatIntegrable : IntervalIntegrable
      (h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass) volume s t)
    (hTransportIntegrable : IntervalIntegrable
      (h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass) volume s t)
    (hLerayIntegrable : IntervalIntegrable
      (h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass) volume s t)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    h3PathTopFourierNormalizedRadialVariance244 u s -
        (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t) -
        36 * (∫ r in s..t, h3PathCanonicalSqrtEnergyGradientEnvelope u r) ≤
      (∫ r in s..t,
        h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass r) +
      (∫ r in s..t,
        h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass r) := by
  have hDrop := h3Path_physicalVariance_drop_le_heatLeray_gradientAction244
    hH3 hClass hs ht hst hMass hD
    hDerivativeIntegrable hHeatIntegrable hTransportIntegrable hLerayIntegrable
  have hYoung := h3Path_topFourier_normalizedVariance_nearYoung_upper244
    hH3 hClass ht (hMass t ⟨hst.le, le_refl t⟩) hK
    (hD t ⟨hst.le, le_refl t⟩) hNear
  linarith only [hDrop, hYoung]

/-- The exact signed Leray action must pay the near-Young deficit after a
specified heat ceiling and the now-proved integrated order-two gradient
allowance. Unlike the earlier theorem, it assumes NO abstract transport G. -/
theorem h3Path_nearYoung_forces_Leray_after_heat_gradientAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t H K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDerivativeIntegrable : IntervalIntegrable
      (deriv (h3PathTopFourierNormalizedVarianceOnClass244 hClass)) volume s t)
    (hHeatIntegrable : IntervalIntegrable
      (h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass) volume s t)
    (hTransportIntegrable : IntervalIntegrable
      (h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass) volume s t)
    (hLerayIntegrable : IntervalIntegrable
      (h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass) volume s t)
    (hHeatCeiling :
      (∫ r in s..t,
        h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass r) ≤ H)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    h3PathTopFourierNormalizedRadialVariance244 u s -
        (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t) - H -
        36 * (∫ r in s..t, h3PathCanonicalSqrtEnergyGradientEnvelope u r) ≤
      ∫ r in s..t,
        h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass r := by
  have hBoth := h3Path_nearYoung_forces_heatLeray_after_gradientAction244
    hH3 hClass hs ht hst hMass hD
    hDerivativeIntegrable hHeatIntegrable hTransportIntegrable hLerayIntegrable
    hK hNear
  linarith only [hBoth, hHeatCeiling]

end
end PrimeTensor.FirstMonomialTriad
