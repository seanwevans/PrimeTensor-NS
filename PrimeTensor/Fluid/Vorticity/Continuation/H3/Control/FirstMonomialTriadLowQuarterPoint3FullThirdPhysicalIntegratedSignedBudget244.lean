import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdVariableBandHeatIntegratedAction244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGlobalLerayTransportBudget244
import Mathlib.Tactic

/-!
# Actual physical time-integrated normalized concentration budget

Unlike the finite two-band linear heat model, the physical Navier--Stokes
variance has three signed channels: heat, order-two transport, and the full
fourth-radial Leray transfer. On compact strict-time intervals where the
actual variance derivative is interval-integrable, its integral is exactly
the physical change of the normalized Fourier Cauchy defect.

The interval-integrability assumption is EXPLICIT: differentiability alone
is not enough for a fundamental theorem of calculus. Splitting the source
into three integrals additionally uses separate integrability assumptions.
No sign is assigned to physical heat or Leray transfer, and no unconditional
regularity is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- Global heat contribution on the physical class interval. The extension
outside that interval is zero and does not enter the strict-time integral. -/
noncomputable def h3PathTopFourierPhysicalIntegratedHeatProfile244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (r : ℝ) : ℝ :=
  if hr : r ∈ Set.Ioo a T then
    h3PathTopFourierGlobalDiffusionNormalizedRate244 hH3 hClass r hr
  else 0

/-- Global signed Leray contribution on the physical class interval. -/
noncomputable def h3PathTopFourierPhysicalIntegratedLerayProfile244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (r : ℝ) : ℝ :=
  if hr : r ∈ Set.Ioo a T then
    h3PathTopFourierGlobalLerayNormalizedRate244 hH3 hClass r hr
  else 0

/-- The signed physical derivative is exactly minus the sum of the three
PDE channels, at every strict time of positive kinetic and H3 masses. -/
theorem h3Path_physicalVariance_deriv_eq_neg_threeProfiles244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u r)
    (hD : 0 < velocityH3Dissipation3At u r) :
    deriv (h3PathTopFourierNormalizedVarianceOnClass244 hClass) r =
      -(h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass r +
        h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass r +
        h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass r) := by
  have hDerivative := h3Path_normalizedVariance_deriv_eq_neg_signedExcess244
    hH3 hClass hr hMass hD
  have hThree := h3Path_normalizedSignedExcess_eq_globalThreeChannels244
    hH3 hClass hr
  have hQuotient :
      -(h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass r) /
        (velocityH3Energy0At u r *
          h3TerminalPhysicalTopDissipation3Path hClass r) ^ 2 =
      -(h3PathTopFourierNormalizedSignedExcessRate244 hH3 hClass r) := by
    unfold h3PathTopFourierNormalizedSignedExcessRate244
    ring
  rw [hDerivative, hQuotient, hThree]
  simp only [h3PathTopFourierPhysicalIntegratedHeatProfile244,
    h3PathTopFourierPhysicalIntegratedLerayProfile244,
    dif_pos hr]

/-- An actual physical FTC on every strict preterminal interval. This
requires only integrability of the CLASS-LOCAL normalized variance derivative;
it does NOT postulate integrability of the three channels separately. -/
theorem h3Path_physicalVariance_integral_threeProfiles_eq_drop244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDerivativeIntegrable : IntervalIntegrable
      (deriv (h3PathTopFourierNormalizedVarianceOnClass244 hClass))
      volume s t) :
    (∫ r in s..t,
        h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass r +
        h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass r +
        h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass r) =
      h3PathTopFourierNormalizedRadialVariance244 u s -
        h3PathTopFourierNormalizedRadialVariance244 u t := by
  let F : ℝ → ℝ := h3PathTopFourierNormalizedVarianceOnClass244 hClass
  have hInside (r : ℝ) (hr : r ∈ Set.Icc s t) :
      r ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hDiff : ∀ r : ℝ, r ∈ Set.uIcc s t →
      DifferentiableAt ℝ F r := by
    intro r hr
    rw [Set.uIcc_of_le hst.le] at hr
    exact (h3Path_normalizedVarianceOnClass_hasDerivAt244
      hH3 hClass (hInside r hr) (hMass r hr) (hD r hr)).differentiableAt
  have hFTC : (∫ r in s..t, deriv F r) = F t - F s :=
    intervalIntegral.integral_deriv_eq_sub hDiff hDerivativeIntegrable
  have hEqualIntegral :
      (∫ r in s..t, deriv F r) =
        ∫ r in s..t,
          -(h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass r +
            h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass r +
            h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass r) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hst.le
    intro r hr
    have hrClosed : r ∈ Set.Icc s t := ⟨hr.1.le, hr.2.le⟩
    exact h3Path_physicalVariance_deriv_eq_neg_threeProfiles244
      hH3 hClass (hInside r hrClosed) (hMass r hrClosed) (hD r hrClosed)
  rw [hEqualIntegral, intervalIntegral.integral_neg] at hFTC
  have hAtS : F s = h3PathTopFourierNormalizedRadialVariance244 u s :=
    h3Path_normalizedVarianceOnClass_eq_physical244 hClass hs
      (hMass s ⟨le_refl s, hst.le⟩)
      (hD s ⟨le_refl s, hst.le⟩)
  have hAtT : F t = h3PathTopFourierNormalizedRadialVariance244 u t :=
    h3Path_normalizedVarianceOnClass_eq_physical244 hClass ht
      (hMass t ⟨hst.le, le_refl t⟩)
      (hD t ⟨hst.le, le_refl t⟩)
  rw [hAtS, hAtT] at hFTC
  linarith only [hFTC]

/-- The signed physical transport-versus-heat/Leray action is exactly the
finite-time variance drop, assuming separate integrability of the channels. -/
theorem h3Path_physicalVariance_integratedHeat_transport_Leray_eq_drop244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDerivativeIntegrable : IntervalIntegrable
      (deriv (h3PathTopFourierNormalizedVarianceOnClass244 hClass))
      volume s t)
    (hHeatIntegrable : IntervalIntegrable
      (h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass)
      volume s t)
    (hTransportIntegrable : IntervalIntegrable
      (h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass)
      volume s t)
    (hLerayIntegrable : IntervalIntegrable
      (h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass)
      volume s t) :
    (∫ r in s..t,
        h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass r) +
      (∫ r in s..t,
        h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass r) +
      (∫ r in s..t,
        h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass r) =
      h3PathTopFourierNormalizedRadialVariance244 u s -
        h3PathTopFourierNormalizedRadialVariance244 u t := by
  have hFTC := h3Path_physicalVariance_integral_threeProfiles_eq_drop244
    hH3 hClass hs ht hst hMass hD hDerivativeIntegrable
  have hSplit :
      (∫ r in s..t,
          h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass r +
          h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass r +
          h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass r) =
      (∫ r in s..t,
          h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass r) +
        (∫ r in s..t,
          h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass r) +
        (∫ r in s..t,
          h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass r) := by
    have hAll :
        (∫ r in s..t,
            (h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass r +
              h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass r) +
              h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass r) =
          (∫ r in s..t,
              h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass r +
                h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass r) +
          (∫ r in s..t,
              h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass r) := by
      exact intervalIntegral.integral_add
        (hHeatIntegrable.add hTransportIntegrable) hLerayIntegrable
    have hAB :
        (∫ r in s..t,
            h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass r +
              h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass r) =
          (∫ r in s..t,
              h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass r) +
          (∫ r in s..t,
              h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass r) := by
      exact intervalIntegral.integral_add hHeatIntegrable hTransportIntegrable
    calc
      _ = (∫ r in s..t,
            h3PathTopFourierPhysicalIntegratedHeatProfile244 hH3 hClass r +
              h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass r) +
            (∫ r in s..t,
              h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass r) := hAll
      _ = _ := by rw [hAB]
  rw [hSplit] at hFTC
  exact hFTC

/-- Under quantitative interval ceilings for the physical heat and order-two
transport channels, an actual variance drop REQUIRES at least the residual
integrated signed Leray transfer. This is a necessary condition, not a bound
or sign theorem for Leray forcing. -/
theorem h3Path_physicalVariance_drop_forces_integratedLeray244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t H G : ℝ}
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
    (hTransportCeiling :
      (∫ r in s..t,
        h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass r) ≤ G) :
    h3PathTopFourierNormalizedRadialVariance244 u s -
      h3PathTopFourierNormalizedRadialVariance244 u t - H - G ≤
      ∫ r in s..t,
        h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass r := by
  have hFTC := h3Path_physicalVariance_integratedHeat_transport_Leray_eq_drop244
    hH3 hClass hs ht hst hMass hD
    hDerivativeIntegrable hHeatIntegrable hTransportIntegrable hLerayIntegrable
  linarith only [hFTC, hHeatCeiling, hTransportCeiling]

/-- Near-Young saturation at the final time requires a SIGNED integrated
Leray contribution after the physical heat and order-two budgets, rather
than a merely large instantaneous source at some intermediate time. -/
theorem h3Path_nearYoung_forces_integratedLeray_after_budgets244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t H G K δ : ℝ}
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
    (hTransportCeiling :
      (∫ r in s..t,
        h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass r) ≤ G)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    h3PathTopFourierNormalizedRadialVariance244 u s -
      (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t) - H - G ≤
      ∫ r in s..t,
        h3PathTopFourierPhysicalIntegratedLerayProfile244 hH3 hClass r := by
  have hDrop := h3Path_physicalVariance_drop_forces_integratedLeray244
    hH3 hClass hs ht hst hMass hD
    hDerivativeIntegrable hHeatIntegrable hTransportIntegrable hLerayIntegrable
    hHeatCeiling hTransportCeiling
  have hYoung := h3Path_topFourier_normalizedVariance_nearYoung_upper244
    hH3 hClass ht (hMass t ⟨hst.le, le_refl t⟩) hK
    (hD t ⟨hst.le, le_refl t⟩) hNear
  linarith only [hDrop, hYoung]

end
end PrimeTensor.FirstMonomialTriad
