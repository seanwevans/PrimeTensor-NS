import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalIntegratedOrderTwoGradientBudget244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGlobalPhaseMiddleCoupling244
import Mathlib.Tactic

/-!
# Kinetic logarithmic action and signed fifth-phase transport budget

The genuine zeroth-order physical energy obeys E0' = L0 = -2 D0: both
order-zero transport and pressure cancel. Thus wherever E0 > 0,

    d/dt [-log E0] = -L0/E0 = 2 D0/E0.

On a compact strict interval, integrability of this derivative permits its
exact integration, producing the *endpoint logarithmic kinetic loss*.

The actual normalized concentration source is middle plus top-phase; the
middle contribution is at most the kinetic loss rate plus 36 times the
canonical sqrt-H3 gradient envelope. Integration therefore shows

  ∫ topPhase >= R(s)-R(t) - log(E0(s)/E0(t)) - 36 ∫ gradient.

Here topPhase is the EXACT signed fifth mass PLUS NONNEGATIVE PHASE DEFECT
MINUS cubic forcing, weighted by E2² E0/(E0 D3)². The positivity of the phase
defect contributes in the concentration direction, not a favorable
anti-concentration sign. Integrability of the actual source profiles is
EXPLICIT; no terminal-time integrability or NS continuation is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- Positive kinetic dissipation cost per unit of current kinetic energy. -/
noncomputable def h3PathPhysicalKineticLogLossRate244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : ℝ :=
  -(velocityH3DiffusionDerivative0At u t / velocityH3Energy0At u t)

/-- The logarithmic kinetic-loss primitive. -/
noncomputable def h3PathPhysicalKineticLogLossPrimitive244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : ℝ :=
  -Real.log (velocityH3Energy0At u t)

/-- The complete *physical*, unforced zeroth-order energy identity has no
order-zero transport or pressure contribution. -/
theorem h3Path_physicalKinetic_derivative_eq_diffusion0_244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3Energy0At u) t =
      velocityH3DiffusionDerivative0At u t := by
  let p : PrimeTensor.SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3EnergyClassSplitPressureAt hClass ht
  have hPDE : PreterminalNavierStokes3
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) p T := by
    dsimp only [p]
    exact h3EnergyClassSplitPressureAt_navierStokes hClass ht
  have hPair : H3PDEPairingIntegrableAt u p t := by
    dsimp only [p]
    exact h3PathEnergyClassProducesPDEPairingIntegrability_closed
      u T hH3 a hClass t ht
  have hPressure : velocityH3PressureDerivative0At u p t = 0 := by
    dsimp only [p]
    exact h3PathEnergyClassProducesPressure0Cancellation_closed
      u T hH3 a hClass t ht
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hH3At : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs
  have hGradient : VelocityGradientEnvelope u
      (h3PathCanonicalSqrtEnergyGradientEnvelope u) t :=
    h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass ht
  have hIBP : H3TransportEnergyIntegrationByPartsAt u t :=
    h3TransportEnergyIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradient
  have hFlux : H3TransportEnergyFluxVanishesAt u t :=
    h3TransportEnergyFluxVanishesAt_of_integrationByParts hIBP
  have hTransport : velocityH3TransportDerivative0At u t = 0 :=
    velocityH3TransportDerivative0At_eq_zero_of_energyClass
      hClass ht hFlux
  have hFormal := velocityH3FormalDerivative0At_eq_pde hPDE htAbs
  have hSplit := velocityH3PDEDerivative0At_eq_split hPair
  have hTime := h3PathEnergyClassProducesOrder0EnergyDerivativeIdentity_closed
    hH3 hClass ht
  calc
    deriv (velocityH3Energy0At u) t =
        velocityH3FormalDerivative0At u t := hTime.deriv
    _ = velocityH3PDEDerivative0At u p t := hFormal
    _ = velocityH3DiffusionDerivative0At u t -
          velocityH3TransportDerivative0At u t -
          velocityH3PressureDerivative0At u p t := hSplit
    _ = velocityH3DiffusionDerivative0At u t := by
      rw [hTransport, hPressure]
      ring

/-- The logarithmic kinetic-loss derivative is an actual PDE derivative,
not a surrogate scalar ODE assumed for the argument. -/
theorem h3Path_physicalKineticLogLoss_hasDerivAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t) :
    HasDerivAt (h3PathPhysicalKineticLogLossPrimitive244 u)
      (h3PathPhysicalKineticLogLossRate244 u t) t := by
  have hTime := h3PathEnergyClassProducesOrder0EnergyDerivativeIdentity_closed
    hH3 hClass ht
  have hEq := h3Path_physicalKinetic_derivative_eq_diffusion0_244
    hH3 hClass ht
  have hDerivative : HasDerivAt (velocityH3Energy0At u)
      (velocityH3DiffusionDerivative0At u t) t := by
    have hTime' := hTime.deriv
    exact hTime.congr_deriv (by
      rw [← hTime']
      exact hEq)
  have hLog := (hDerivative.log (ne_of_gt hMass)).neg
  have hPrimitive :
      h3PathPhysicalKineticLogLossPrimitive244 u =
        -(fun s : ℝ => Real.log (velocityH3Energy0At u s)) := by
    funext s
    rfl
  rw [hPrimitive]
  change HasDerivAt
    (-(fun s : ℝ => Real.log (velocityH3Energy0At u s)))
    (-(velocityH3DiffusionDerivative0At u t / velocityH3Energy0At u t)) t
  exact hLog

/-- Compact physical kinetic dissipation is exactly a logarithmic endpoint
ratio whenever its normalized rate is interval-integrable. -/
theorem h3Path_physicalKineticLogLoss_integral_eq_endpoint244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hLossIntegrable : IntervalIntegrable
      (h3PathPhysicalKineticLogLossRate244 u) volume s t) :
    (∫ r in s..t, h3PathPhysicalKineticLogLossRate244 u r) =
      Real.log (velocityH3Energy0At u s) -
        Real.log (velocityH3Energy0At u t) := by
  let F : ℝ → ℝ := h3PathPhysicalKineticLogLossPrimitive244 u
  have hInside (r : ℝ) (hr : r ∈ Set.Icc s t) : r ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hDerivative (r : ℝ) (hr : r ∈ Set.Icc s t) :
      HasDerivAt F (h3PathPhysicalKineticLogLossRate244 u r) r :=
    h3Path_physicalKineticLogLoss_hasDerivAt244
      hH3 hClass (hInside r hr) (hMass r hr)
  have hDiff : ∀ r : ℝ, r ∈ Set.uIcc s t → DifferentiableAt ℝ F r := by
    intro r hr
    rw [Set.uIcc_of_le hst] at hr
    exact (hDerivative r hr).differentiableAt
  have hEqualIntegral :
      (∫ r in s..t, deriv F r) =
        ∫ r in s..t, h3PathPhysicalKineticLogLossRate244 u r := by
    apply intervalIntegral.integral_congr_Ioo_of_le hst
    intro r hr
    exact (hDerivative r ⟨hr.1.le, hr.2.le⟩).deriv
  have hIntDeriv : IntervalIntegrable (deriv F) volume s t := by
    -- Interval integrability transfers across pointwise equality on [s,t].
    have hOn : Set.EqOn (h3PathPhysicalKineticLogLossRate244 u)
        (deriv F) (Set.uIoc s t) := by
      intro r hr
      rw [Set.uIoc_of_le hst] at hr
      exact (hDerivative r ⟨hr.1.le, hr.2⟩).deriv.symm
    exact hLossIntegrable.congr hOn
  have hFTC := intervalIntegral.integral_deriv_eq_sub hDiff hIntDeriv
  rw [hEqualIntegral] at hFTC
  dsimp only [F, h3PathPhysicalKineticLogLossPrimitive244] at hFTC
  linarith only [hFTC]

/-- Physical top fifth-mass/phase/cubic contribution on strict times. -/
noncomputable def h3PathPhysicalIntegratedTopPhaseProfile244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (r : ℝ) : ℝ :=
  if hr : r ∈ Set.Ioo a T then
    h3PathTopFourierGlobalTopPhaseNormalizedRate244 hH3 hClass r hr
  else 0

/-- Exact physical normalized variance derivative after keeping the
signed fifth-order phase defect and the middle-order coupling. -/
theorem h3Path_physicalVariance_deriv_eq_neg_middleTopPhase244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u r)
    (hD : 0 < velocityH3Dissipation3At u r) :
    deriv (h3PathTopFourierNormalizedVarianceOnClass244 hClass) r =
      -(h3PathTopFourierGlobalMiddleCouplingNormalizedRate244 hClass r +
        h3PathPhysicalIntegratedTopPhaseProfile244 hH3 hClass r) := by
  have hDerivative := h3Path_normalizedVariance_deriv_eq_neg_signedExcess244
    hH3 hClass hr hMass hD
  have hPhase := h3Path_normalizedExcessRate_eq_middleCoupling_add_topPhase244
    hH3 hClass hr
  have hQuot :
      -(h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass r) /
        (velocityH3Energy0At u r *
          h3TerminalPhysicalTopDissipation3Path hClass r) ^ 2 =
      -(h3PathTopFourierNormalizedSignedExcessRate244 hH3 hClass r) := by
    unfold h3PathTopFourierNormalizedSignedExcessRate244
    ring
  rw [hDerivative, hQuot, hPhase]
  simp only [h3PathPhysicalIntegratedTopPhaseProfile244, dif_pos hr]

/-- Exact middle-plus-signed-top temporal action: no phase is discarded. -/
theorem h3Path_physicalVariance_integral_middleTopPhase_eq_drop244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDerivativeIntegrable : IntervalIntegrable
      (deriv (h3PathTopFourierNormalizedVarianceOnClass244 hClass)) volume s t) :
    (∫ r in s..t,
      h3PathTopFourierGlobalMiddleCouplingNormalizedRate244 hClass r +
      h3PathPhysicalIntegratedTopPhaseProfile244 hH3 hClass r) =
      h3PathTopFourierNormalizedRadialVariance244 u s -
        h3PathTopFourierNormalizedRadialVariance244 u t := by
  let F : ℝ → ℝ := h3PathTopFourierNormalizedVarianceOnClass244 hClass
  have hInside (r : ℝ) (hr : r ∈ Set.Icc s t) : r ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hDiff : ∀ r : ℝ, r ∈ Set.uIcc s t → DifferentiableAt ℝ F r := by
    intro r hr
    rw [Set.uIcc_of_le hst.le] at hr
    exact (h3Path_normalizedVarianceOnClass_hasDerivAt244
      hH3 hClass (hInside r hr) (hMass r hr) (hD r hr)).differentiableAt
  have hFTC : (∫ r in s..t, deriv F r) = F t - F s :=
    intervalIntegral.integral_deriv_eq_sub hDiff hDerivativeIntegrable
  have hEqualIntegral :
      (∫ r in s..t, deriv F r) =
        ∫ r in s..t,
          -(h3PathTopFourierGlobalMiddleCouplingNormalizedRate244 hClass r +
            h3PathPhysicalIntegratedTopPhaseProfile244 hH3 hClass r) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hst.le
    intro r hr
    exact h3Path_physicalVariance_deriv_eq_neg_middleTopPhase244
      hH3 hClass (hInside r ⟨hr.1.le, hr.2.le⟩)
      (hMass r ⟨hr.1.le, hr.2.le⟩)
      (hD r ⟨hr.1.le, hr.2.le⟩)
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

/-- The *actual* signed middle coupling costs at most kinetic logarithmic
loss plus the canonical 36-sqrt-H³ gradient envelope. -/
theorem h3Path_physicalMiddle_le_kineticLog_gradient244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u r)
    (hD : 0 < velocityH3Dissipation3At u r) :
    h3PathTopFourierGlobalMiddleCouplingNormalizedRate244 hClass r ≤
      h3PathPhysicalKineticLogLossRate244 u r +
      36 * h3PathCanonicalSqrtEnergyGradientEnvelope u r := by
  have hMiddle := h3Path_globalMiddleCoupling_le_kineticGradientBudget244
    hH3 hClass hr hMass hD
  have hTop : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hr]
    exact hD
  have hCancel :
      -(velocityH3DiffusionDerivative0At u r *
          h3TerminalPhysicalTopDissipation3Path hClass r) /
        (velocityH3Energy0At u r *
          h3TerminalPhysicalTopDissipation3Path hClass r) =
      h3PathPhysicalKineticLogLossRate244 u r := by
    unfold h3PathPhysicalKineticLogLossRate244
    field_simp [ne_of_gt hMass, ne_of_gt hTop]
    <;> ring
  rw [hCancel] at hMiddle
  exact hMiddle

/-- Integrated middle budget: the kinetic logarithmic-loss action and
compact gradient action replace an arbitrary middle contribution ceiling. -/
theorem h3Path_physicalMiddle_integral_le_kineticLog_gradient244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hMiddleIntegrable : IntervalIntegrable
      (h3PathTopFourierGlobalMiddleCouplingNormalizedRate244 hClass) volume s t)
    (hLossIntegrable : IntervalIntegrable
      (h3PathPhysicalKineticLogLossRate244 u) volume s t) :
    (∫ r in s..t, h3PathTopFourierGlobalMiddleCouplingNormalizedRate244 hClass r) ≤
      (Real.log (velocityH3Energy0At u s) -
        Real.log (velocityH3Energy0At u t)) +
      36 * (∫ r in s..t, h3PathCanonicalSqrtEnergyGradientEnvelope u r) := by
  have hGradientIntegrable :=
    h3Path_canonicalGradientEnvelope_intervalIntegrable244
      hH3 hClass hs ht hst
  have hComparison :
      (∫ r in s..t, h3PathTopFourierGlobalMiddleCouplingNormalizedRate244 hClass r) ≤
      (∫ r in s..t,
        h3PathPhysicalKineticLogLossRate244 u r +
        36 * h3PathCanonicalSqrtEnergyGradientEnvelope u r) := by
    apply intervalIntegral.integral_mono_on hst hMiddleIntegrable
      (hLossIntegrable.add (hGradientIntegrable.const_mul 36))
    intro r hr
    have hrClass : r ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
    exact h3Path_physicalMiddle_le_kineticLog_gradient244
      hH3 hClass hrClass (hMass r hr) (hD r hr)
  have hSplit :
      (∫ r in s..t,
        h3PathPhysicalKineticLogLossRate244 u r +
        36 * h3PathCanonicalSqrtEnergyGradientEnvelope u r) =
      (∫ r in s..t, h3PathPhysicalKineticLogLossRate244 u r) +
        36 * (∫ r in s..t,
          h3PathCanonicalSqrtEnergyGradientEnvelope u r) := by
    rw [intervalIntegral.integral_add hLossIntegrable
      (hGradientIntegrable.const_mul 36), intervalIntegral.integral_const_mul]
  have hLog := h3Path_physicalKineticLogLoss_integral_eq_endpoint244
    hH3 hClass hs ht hst hMass hLossIntegrable
  rw [hSplit, hLog] at hComparison
  exact hComparison

/-- The integrated *signed fifth-plus-phase-minus-cubic* contribution must
pay the remaining concentration after kinetic logarithmic dissipation and
the proven compact square-root-energy gradient action. -/
theorem h3Path_physicalTopPhase_integral_ge_after_kineticLog_gradient244
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
    (hMiddleIntegrable : IntervalIntegrable
      (h3PathTopFourierGlobalMiddleCouplingNormalizedRate244 hClass) volume s t)
    (hTopIntegrable : IntervalIntegrable
      (h3PathPhysicalIntegratedTopPhaseProfile244 hH3 hClass) volume s t)
    (hLossIntegrable : IntervalIntegrable
      (h3PathPhysicalKineticLogLossRate244 u) volume s t) :
    h3PathTopFourierNormalizedRadialVariance244 u s -
      h3PathTopFourierNormalizedRadialVariance244 u t -
      (Real.log (velocityH3Energy0At u s) -
        Real.log (velocityH3Energy0At u t)) -
      36 * (∫ r in s..t,
        h3PathCanonicalSqrtEnergyGradientEnvelope u r) ≤
      ∫ r in s..t,
        h3PathPhysicalIntegratedTopPhaseProfile244 hH3 hClass r := by
  have hFTC := h3Path_physicalVariance_integral_middleTopPhase_eq_drop244
    hH3 hClass hs ht hst hMass hD hDerivativeIntegrable
  have hSplit := intervalIntegral.integral_add hMiddleIntegrable hTopIntegrable
  rw [hSplit] at hFTC
  have hMiddle := h3Path_physicalMiddle_integral_le_kineticLog_gradient244
    hH3 hClass hs ht hst.le hMass hD hMiddleIntegrable hLossIntegrable
  linarith only [hFTC, hMiddle]

/-- Sharp Young near-saturation forces the same integrated signed top-phase
action with no abstract middle or kinetic-loss constant. -/
theorem h3Path_nearYoung_forces_integratedTopPhase_after_kineticLog244
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
    (hMiddleIntegrable : IntervalIntegrable
      (h3PathTopFourierGlobalMiddleCouplingNormalizedRate244 hClass) volume s t)
    (hTopIntegrable : IntervalIntegrable
      (h3PathPhysicalIntegratedTopPhaseProfile244 hH3 hClass) volume s t)
    (hLossIntegrable : IntervalIntegrable
      (h3PathPhysicalKineticLogLossRate244 u) volume s t)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    h3PathTopFourierNormalizedRadialVariance244 u s -
      (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t) -
      (Real.log (velocityH3Energy0At u s) -
        Real.log (velocityH3Energy0At u t)) -
      36 * (∫ r in s..t,
        h3PathCanonicalSqrtEnergyGradientEnvelope u r) ≤
      ∫ r in s..t,
        h3PathPhysicalIntegratedTopPhaseProfile244 hH3 hClass r := by
  have hPhase := h3Path_physicalTopPhase_integral_ge_after_kineticLog_gradient244
    hH3 hClass hs ht hst hMass hD hDerivativeIntegrable
    hMiddleIntegrable hTopIntegrable hLossIntegrable
  have hYoung := h3Path_topFourier_normalizedVariance_nearYoung_upper244
    hH3 hClass ht (hMass t ⟨hst.le, le_refl t⟩) hK
    (hD t ⟨hst.le, le_refl t⟩) hNear
  linarith only [hPhase, hYoung]

end
end PrimeTensor.FirstMonomialTriad
