import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdPhysicalJetEnergyQuarticBridge
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedTopInterpolationFrontier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalLowerOrderSignedTransport
import Mathlib.Tactic

/-!
# Physical signed H³ growth and the exact quartic interpolation obstruction

The actual E₂/E₃ jet identifications and signed physical quartic inequality
now control the *positive part* of the residual in the old H³ PDE balance,
without discarding the full `2 D` viscosity term. The first and second
transport orders cost `h (6 E₁ + 18 E₂)`, and the easy third-gradient block
costs `24 h E₃`; what remains is supported by the signed 243-slot
interpolation, whose fourth power is bounded by `3^4 K^4 E₂ E₃^5`.

At a strictly adverse top-transport time, either the gradient cost already
accounts for the prescribed `M E + D`, or the *positive* excess over that
gradient cost satisfies the same fourth-power constraint. Nonextension
forces this necessary dichotomy arbitrarily near the terminal time. Under
the EXPLICIT additional assumption that dissipation absorbs the gradient
cost on a terminal tail, nonextension instead forces quartic source mass
large enough to pay `M^4 E^4` for arbitrarily large prescribed `M`.

These are necessary obstruction inequalities, NOT a proof that the adverse
branch is absent or that the quartic cost is integrable. In particular no
favorable sign is ascribed to the interpolation for a general solenoidal
velocity. The physical E₂ and E₃ coefficients are the original spatial
energies, not equivalent Sobolev substitutes.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Filter Topology PrimeTensor.Bridge.Euclidean Set
open scoped BigOperators ENNReal SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1200000

noncomputable local instance axisFintypePhysicalSignedQuarticGrowth244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The net PDE growth left after retaining the full physical `2D`, paying
only the real lower-order `6E₁+18E₂`, and subtracting the 24-fold easy
third-gradient contribution. There is no favorable-sign assumption. -/
noncomputable def thirdFullPhysicalSignedGrowthResidual244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : ℝ :=
  deriv (velocityH3EnergyAt u) t + 2 * velocityH3DissipationAt u t -
    ((h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        (6 * velocityH3Energy1At u t + 18 * velocityH3Energy2At u t) +
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        velocityH3Energy3At u t)

/-- The positive part of the exact OLD physical energy-growth residual
cannot exceed the magnitude of the genuinely signed interpolation block.
All full viscous dissipation is still present on the left. -/
theorem thirdFullPhysical_signedGrowthResidual_le_interpolationAbs244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    max 0 (thirdFullPhysicalSignedGrowthResidual244 u t) ≤
      |thirdOrderInterpolationTransportSum u t| := by
  have hBalance :=
    h3PathCanonical_deriv_add_dissipation_le_lowerOrderSignedTop
      hH3 hClass ht
  have hSplit :=
    h3PathCanonical_thirdTransport_eq_gradient_add_interpolation
      hH3 hClass ht
  have hGrad :=
    h3PathCanonical_abs_gradientTransport_le_topEnergy
      hH3 hClass ht
  have hNegGradient := neg_le_abs (thirdOrderGradientTransportSum u t)
  have hNegInterp := neg_le_abs (thirdOrderInterpolationTransportSum u t)
  rw [hSplit] at hBalance
  have hResidual : thirdFullPhysicalSignedGrowthResidual244 u t ≤
      |thirdOrderInterpolationTransportSum u t| := by
    unfold thirdFullPhysicalSignedGrowthResidual244
    linarith only [hBalance, hGrad, hNegGradient, hNegInterp]
  exact max_le (abs_nonneg _) hResidual

/-- A physical PDE inequality, rather than merely an abstract Schwartz
inequality: the fourth power of the positive, fully viscous H³ growth
residual is bounded by the original 27×81 physical E₂/E₃ mass. -/
theorem thirdFullPhysical_signedGrowthResidual_quarticBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    (max 0 (thirdFullPhysicalSignedGrowthResidual244 u t)) ^ 4 ≤
      (3 : ℝ) ^ 4 *
        (lowNormalRealSchwartz_holder244CriticalConstant ^ 4 *
          (velocityH3Energy2At u t * (velocityH3Energy3At u t) ^ 5)) := by
  have hMajor :=
    thirdFullPhysical_signedGrowthResidual_le_interpolationAbs244
      hH3 hClass ht
  have hFourth :
      (max 0 (thirdFullPhysicalSignedGrowthResidual244 u t)) ^ 4 ≤
        |thirdOrderInterpolationTransportSum u t| ^ 4 :=
    pow_le_pow_left₀ (le_max_left _ _) hMajor 4
  exact hFourth.trans
    (thirdFullPhysical_interpolationTransport_quarticEnergyBound244
      hH3 hClass ht hFourier)

/-- If an adverse third-order PDE transport pays more than the available
explicit gradient budget, the excess is forced into the physical signed
quartic budget. The first branch includes zero excess, so there is no
illicit division by the gradient coefficient or by E₂/E₃. -/
theorem thirdFullPhysical_signedAdversity_gradientOrQuartic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (M : ℝ)
    (hDeficit : M * velocityH3EnergyAt u t +
        velocityH3DissipationAt u t <
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
        thirdOrderInterpolationTransportSum u t) :
    M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t ∨
    (M * velocityH3EnergyAt u t + velocityH3DissipationAt u t -
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t) ^ 4 ≤
      (3 : ℝ) ^ 4 *
        (lowNormalRealSchwartz_holder244CriticalConstant ^ 4 *
          (velocityH3Energy2At u t * (velocityH3Energy3At u t) ^ 5)) := by
  let G : ℝ :=
    24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t
  let A : ℝ :=
    M * velocityH3EnergyAt u t + velocityH3DissipationAt u t
  change A < G - thirdOrderInterpolationTransportSum u t at hDeficit
  change A < G ∨ (A - G) ^ 4 ≤ _
  by_cases hSmall : A < G
  · exact Or.inl hSmall
  · right
    have hNonneg : 0 ≤ A - G := sub_nonneg.mpr (le_of_not_gt hSmall)
    have hSigned : A - G ≤ |thirdOrderInterpolationTransportSum u t| := by
      have hNeg := neg_le_abs (thirdOrderInterpolationTransportSum u t)
      linarith only [hDeficit, hNeg]
    have hPow : (A - G) ^ 4 ≤
        |thirdOrderInterpolationTransportSum u t| ^ 4 :=
      pow_le_pow_left₀ hNonneg hSigned 4
    exact hPow.trans
      (thirdFullPhysical_interpolationTransport_quarticEnergyBound244
        hH3 hClass ht hFourier)

/-- Conditional failure of continuation forces a physical gradient-versus-
quartic alternative on EVERY strict terminal subtail, without assuming
that the full dissipation absorbs the gradient. -/
theorem thirdFullPhysical_noExtension_cofinalGradientOrQuartic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hM : 0 ≤ M) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      (M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
          24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t ∨
        (M * velocityH3EnergyAt u t + velocityH3DissipationAt u t -
          24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t)) *
            velocityH3Energy3At u t) ^ 4 ≤
          (3 : ℝ) ^ 4 *
            (lowNormalRealSchwartz_holder244CriticalConstant ^ 4 *
              (velocityH3Energy2At u t * (velocityH3Energy3At u t) ^ 5))) := by
  obtain ⟨t, ht, hDeficit⟩ :=
    h3PathCanonical_interpolationDeficit_on_every_strict_subtail
      hH3 hNoExtension hClass hb hd hM
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  have htNS : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 htClass.1, htClass.2⟩
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htNS
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htNS
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htNS hInt
  exact ⟨t, ht,
    thirdFullPhysical_signedAdversity_gradientOrQuartic244
      hH3 hClass htClass hFourier M hDeficit⟩

/-- If actual viscosity absorbs the explicit 24-fold gradient block on
one terminal tail, hypothetical nonextension forces *unbounded prescribed*
normalized fourth-power interpolation cost there. This is a conditional
necessary obstruction, not a uniform gradient-absorption theorem. -/
theorem thirdFullPhysical_noExtension_gradientAbsorbed_quarticFloor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hM : 0 ≤ M)
    (hAbsorption : ∀ t : ℝ, t ∈ Set.Ioo d T →
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t ≤
          velocityH3DissipationAt u t) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      (M * velocityH3EnergyAt u t) ^ 4 ≤
        (3 : ℝ) ^ 4 *
          (lowNormalRealSchwartz_holder244CriticalConstant ^ 4 *
            (velocityH3Energy2At u t * (velocityH3Energy3At u t) ^ 5)) := by
  obtain ⟨t, ht, hAdverse⟩ :=
    h3PathCanonical_interpolationAdversity_on_every_strict_subtail_of_gradientAbsorption
      hH3 hNoExtension hClass hb hd hM hAbsorption
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  have htNS : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 htClass.1, htClass.2⟩
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htNS
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htNS
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htNS hInt
  have hNonneg : 0 ≤ M * velocityH3EnergyAt u t :=
    mul_nonneg hM (le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (one_le_velocityH3EnergyAt u t))
  have hBelow : M * velocityH3EnergyAt u t ≤
      |thirdOrderInterpolationTransportSum u t| :=
    (le_of_lt hAdverse).trans
      (neg_le_abs (thirdOrderInterpolationTransportSum u t))
  have hPow : (M * velocityH3EnergyAt u t) ^ 4 ≤
      |thirdOrderInterpolationTransportSum u t| ^ 4 :=
    pow_le_pow_left₀ hNonneg hBelow 4
  exact ⟨t, ht, hPow.trans
    (thirdFullPhysical_interpolationTransport_quarticEnergyBound244
      hH3 hClass htClass hFourier)⟩

end
end PrimeTensor.FirstMonomialTriad
