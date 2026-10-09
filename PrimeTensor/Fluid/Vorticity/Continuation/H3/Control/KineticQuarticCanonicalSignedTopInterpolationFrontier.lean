import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedTopFourthMomentCorridor

/-!
# Isolate the genuinely signed H³ third-order interpolation commutator

The preceding physical kinetic-Fourier absorption proves that hypothetical
nonextension forces arbitrarily late witnesses

    D(t) + M E(t) < -T₃(t),    M >= 0.

The *existing* order-three PDE transport closure splits the actual term as

    T₃ = G₃ + I₃,

where `G₃` is the gradient block and `I₃` is the second-derivative
interpolation commutator block. The already-closed gradient estimate gives

    |G₃| <= 24 C₁ sqrt(E) E₃.

Consequently every signed nonextension witness satisfies

    D + M E < 24 C₁ sqrt(E) E₃ - I₃.

If, at one such time, the full dissipation is at least the 24-gradient
allowance, the genuinely signed interpolation block is necessarily adverse:

    -I₃ > M E.

These are reductions to an actual physical nonlinear pairing. There is no
claim that the interpolation term has a favorable sign in general, that the
spectral gradient dominance holds automatically, or that continuation has
been proved without a stated additional condition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- Instantiate the established exact third-order PDE commutator split and
its independently proved `24 h E₃` gradient estimate on a genuine H³ slice.
This theorem introduces no new analytic estimates or assumptions. -/
theorem h3PathCanonical_signedThirdTransport_split_and_gradientBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3TransportDerivative3At u t =
        thirdOrderGradientTransportSum u t +
          thirdOrderInterpolationTransportSum u t ∧
      |thirdOrderGradientTransportSum u t| ≤
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t := by
  let h : ℝ → ℝ := h3PathCanonicalSqrtEnergyGradientEnvelope u
  have hGradient : VelocityGradientEnvelope u h t := by
    simpa only [h] using
      h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass ht
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hH3At : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs
  have hSobolev6 : WholeSpaceC1H1ToL6 :=
    wholeSpaceC1H1ToL6_of_fderiv wholeSpaceC1FDerivL2ToL6_cutoff
  have hSobolev : WholeSpaceC1H1ToL4 :=
    wholeSpaceC1H1ToL4_of_wholeSpaceC1H1ToL6 hSobolev6
  have hCore3 : H3OrderThreeInterpolationLandauCoreAnalyticDataAt u h t := by
    simpa [H3OrderThreeInterpolationLandauCoreAnalyticDataAt] using hGradient
  have hAnalytic3 : H3OrderThreeInterpolationLandauAnalyticDataAt u h t :=
    h3OrderThreeInterpolationLandauAnalyticDataAt_of_core
      hSobolev wholeSpaceQuarticDerivativeIntegrationByParts_cutoff
      hClass ht hH3At hCore3
  have hRegular3 : H3OrderThreeTransportRegularityAt u t :=
    h3OrderThreeTransportRegularityAt_of_energyClass hClass ht
  have hGradientPairing3 : H3OrderThreeGradientPairingIntegrableAt u t :=
    h3OrderThreeGradientPairingIntegrableAt_of_energyClass
      hClass ht hH3At hGradient
  have hMonomialPairing3 : H3OrderThreeInterpolationMonomialPairingIntegrableAt u t :=
    h3OrderThreeInterpolationMonomialPairingIntegrableAt_of_landauAnalyticData
      hAnalytic3
  have hInterpolationPairing3 : H3OrderThreeInterpolationPairingIntegrableAt u t :=
    h3OrderThreeInterpolationPairingIntegrableAt_of_monomials
      hMonomialPairing3
  have hPDEPairing : H3PDEPairingIntegrableAt u
      (h3EnergyClassSplitPressureAt hClass ht) t :=
    h3PathEnergyClassProducesPDEPairingIntegrability_closed
      u T hH3 a hClass t ht
  have hFlux3 : H3ThirdDerivativeTransportFluxVanishesAt u t :=
    h3ThirdDerivativeTransportFluxVanishesAt_of_pde
      hClass ht hH3At hPDEPairing hGradientPairing3 hInterpolationPairing3
  have hPairing3 : H3OrderThreeTransportPairingIntegrableAt u t :=
    h3OrderThreeTransportPairingIntegrableAt_of_pde
      hClass ht hPDEPairing hGradientPairing3 hInterpolationPairing3
  constructor
  · exact velocityH3TransportDerivative3At_eq_gradient_add_interpolation
      hClass ht hRegular3 hFlux3 hPairing3 hGradientPairing3 hInterpolationPairing3
  · have hBound := thirdOrderGradientTransportSum_named_le_gradientEnvelope
      hGradient hH3At hGradientPairing3
    simpa only [h, h3PathCanonicalSqrtEnergyGradientEnvelope] using hBound

/-- The exact third-order nonlinear pairing has the gradient/interpolation
split on every strict H³ energy-class slice. -/
theorem h3PathCanonical_thirdTransport_eq_gradient_add_interpolation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3TransportDerivative3At u t =
      thirdOrderGradientTransportSum u t +
        thirdOrderInterpolationTransportSum u t :=
  (h3PathCanonical_signedThirdTransport_split_and_gradientBound
    hH3 hClass ht).1

/-- The signed gradient part has a genuine physical 24-coefficient bound;
this is independent of the more expensive interpolation block. -/
theorem h3PathCanonical_abs_gradientTransport_le_topEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    |thirdOrderGradientTransportSum u t| ≤
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t :=
  (h3PathCanonical_signedThirdTransport_split_and_gradientBound
    hH3 hClass ht).2

/-- Every adverse top-order transport witness becomes a *signed interpolation*
witness after paying only the separately controlled gradient block. -/
theorem h3PathCanonical_signedAdversity_forces_interpolationDeficit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hAdverse :
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t) :
    M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
        thirdOrderInterpolationTransportSum u t := by
  have hSplit := h3PathCanonical_thirdTransport_eq_gradient_add_interpolation
    hH3 hClass ht
  have hGrad := h3PathCanonical_abs_gradientTransport_le_topEnergy
    hH3 hClass ht
  have hNegGrad := neg_le_abs (thirdOrderGradientTransportSum u t)
  rw [hSplit] at hAdverse
  linarith only [hAdverse, hGrad, hNegGrad]

/-- If full physical dissipation absorbs the complete gradient block at a
signed-adverse time, the interpolation block has a strictly negative
orientation of magnitude exceeding the prescribed growth allowance. -/
theorem h3PathCanonical_signedInterpolation_adverse_of_gradientAbsorption
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hAdverse :
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t)
    (hAbsorption :
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t ≤
        velocityH3DissipationAt u t) :
    M * velocityH3EnergyAt u t <
      -thirdOrderInterpolationTransportSum u t := by
  have hDeficit := h3PathCanonical_signedAdversity_forces_interpolationDeficit
    hH3 hClass ht hAdverse
  linarith only [hDeficit, hAbsorption]

/-- Hypothetical nonextension forces arbitrarily late concrete adverse
interpolation deficits, allowing for the exact controlled gradient cost. -/
theorem h3PathCanonical_interpolationDeficit_on_every_strict_subtail
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
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t -
          thirdOrderInterpolationTransportSum u t := by
  obtain ⟨t, ht, hAdverse⟩ :=
    h3PathCanonical_signedTopDominatesDissipation_on_every_subtail
      hH3 hNoExtension hClass hb hd hM
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  exact ⟨t, ht,
    h3PathCanonical_signedAdversity_forces_interpolationDeficit
      hH3 hClass htClass hAdverse⟩

/-- If full dissipation absorbs the explicit gradient block on a whole
terminal tail, nonextension demands arbitrarily adverse normalized
interpolation pairings on every later strict subtail. -/
theorem h3PathCanonical_interpolationAdversity_on_every_strict_subtail_of_gradientAbsorption
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
      M * velocityH3EnergyAt u t <
        -thirdOrderInterpolationTransportSum u t := by
  obtain ⟨t, ht, hAdverse⟩ :=
    h3PathCanonical_signedTopDominatesDissipation_on_every_subtail
      hH3 hNoExtension hClass hb hd hM
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  exact ⟨t, ht,
    h3PathCanonical_signedInterpolation_adverse_of_gradientAbsorption
      hH3 hClass htClass hAdverse (hAbsorption t ht)⟩

/-- A conditional *signed interpolation* continuation criterion: throughout
one strict terminal tail, the viscous dissipation and favorable interpolation
orientation cover the entire explicit gradient-block cost. -/
theorem h3PathCanonical_extension_of_eventual_gradientAbsorption_and_interpolationCompensation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hCompensation : ∀ t : ℝ, t ∈ Set.Ioo d T →
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t ≤
          velocityH3DissipationAt u t +
            thirdOrderInterpolationTransportSum u t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨t, ht, hAdverse⟩ :=
    h3PathCanonical_signedTopDominatesDissipation_on_every_subtail
      hH3 hNoExtension hClass hb hd (by norm_num : (0 : ℝ) ≤ 0)
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  have hDeficit := h3PathCanonical_signedAdversity_forces_interpolationDeficit
    hH3 hClass htClass hAdverse
  have hBound := hCompensation t ht
  simp only [zero_mul, zero_add] at hDeficit
  linarith only [hDeficit, hBound]

end Euclidean
end Bridge
end PrimeTensor
