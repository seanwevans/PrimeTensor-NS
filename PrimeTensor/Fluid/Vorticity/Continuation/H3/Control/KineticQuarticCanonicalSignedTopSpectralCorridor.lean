import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalAllLowerOrderAbsorption

/-!
# Signed top transport versus the physical top Fourier dissipation scale

Complete kinetic-Fourier absorption of the order-one and order-two transport
terms has isolated the necessary nonextension witness

    -T₃(t) > D(t) + M E(t)

at arbitrarily late strict times, for every M >= 0.  The already established
physical third-order Landau estimate simultaneously gives

    |T₃(t)| <= 4398 C₁ sqrt(E(t)) E₃(t).

Combining the *signed* witness with that bound and D₃ <= D produces

    D₃(t) + M E(t) < 4398 C₁ sqrt(E(t)) E₃(t).

In particular E₃(t)>0 at each such witness, and its genuine Fourier
frequency quotient D₃/E₃ must lie strictly below 4398 C₁ sqrt(E).

Conversely, if the actual top spectral dissipation satisfies

    4398 C₁ sqrt(E(t)) E₃(t) <= D₃(t)

throughout one strict terminal tail, the previously proved nonextension
witness cannot occur, so the H3 path continues. This is a *conditional*
high-frequency dissipation criterion, not a proof that the inequality holds
for arbitrary Navier--Stokes paths. No new spectral estimate or cancellation
is assumed or asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- The signed third-order transport witness bounds the actual top Fourier
viscous block plus any prescribed positive logarithmic-growth allowance. -/
theorem h3PathCanonical_topDissipation_add_growth_lt_LandauTopCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hAdverse :
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t) :
    velocityH3Dissipation3At u t + M * velocityH3EnergyAt u t <
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) * velocityH3Energy3At u t := by
  have hD3 : velocityH3Dissipation3At u t ≤
      velocityH3DissipationAt u t :=
    velocityH3Dissipation3At_le_dissipationAt u t
  have hSign : -velocityH3TransportDerivative3At u t ≤
      |velocityH3TransportDerivative3At u t| :=
    neg_le_abs _
  have hLandau :=
    h3PathCanonical_abs_thirdTransport_le_kineticGradientTopEnergy
      hH3 hClass ht
  linarith only [hAdverse, hD3, hSign, hLandau]

/-- Genuine signed dominance over D with a nonnegative growth excess
requires a strictly positive third-order Fourier energy block. -/
theorem h3PathCanonical_topEnergy_pos_of_signedTransportDominance
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hM : 0 ≤ M)
    (hAdverse :
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t) :
    0 < velocityH3Energy3At u t := by
  have hCorridor :=
    h3PathCanonical_topDissipation_add_growth_lt_LandauTopCeiling
      hH3 hClass ht hAdverse
  have hTopNonneg : 0 ≤ velocityH3Energy3At u t :=
    velocityH3Energy3At_nonneg u t
  have hD3Nonneg : 0 ≤ velocityH3Dissipation3At u t :=
    velocityH3Dissipation3At_nonneg u t
  have hEnergyNonneg : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  have hMNonneg : 0 ≤ M * velocityH3EnergyAt u t :=
    mul_nonneg hM hEnergyNonneg
  by_contra hNotPos
  have hZero : velocityH3Energy3At u t = 0 :=
    le_antisymm (le_of_not_gt hNotPos) hTopNonneg
  rw [hZero] at hCorridor
  nlinarith only [hCorridor, hD3Nonneg, hMNonneg]

/-- On a signed-adverse growth witness, the effective fourth-to-third
Fourier moment quotient is below the canonical square-root-energy
gradient scale, even after reserving the growth allowance M E. -/
theorem h3PathCanonical_topFourierFrequency_corridor_of_signedDominance
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hM : 0 ≤ M)
    (hAdverse :
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t) :
    velocityH3Dissipation3At u t / velocityH3Energy3At u t +
        (M * velocityH3EnergyAt u t) / velocityH3Energy3At u t <
      4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) := by
  have hE3 : 0 < velocityH3Energy3At u t :=
    h3PathCanonical_topEnergy_pos_of_signedTransportDominance
      hH3 hClass ht hM hAdverse
  have hCorridor :=
    h3PathCanonical_topDissipation_add_growth_lt_LandauTopCeiling
      hH3 hClass ht hAdverse
  have hDiv := (div_lt_iff₀ hE3).2 hCorridor
  simpa only [add_div] using hDiv

/-- Removing the nonnegative positive-growth quotient gives a simpler
strict upper bound on the physical top dissipation / top energy ratio. -/
theorem h3PathCanonical_topFourierFrequency_lt_gradientScale_of_signedDominance
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hM : 0 ≤ M)
    (hAdverse :
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t) :
    velocityH3Dissipation3At u t / velocityH3Energy3At u t <
      4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) := by
  have hE3 : 0 < velocityH3Energy3At u t :=
    h3PathCanonical_topEnergy_pos_of_signedTransportDominance
      hH3 hClass ht hM hAdverse
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  have hMscaled : 0 ≤ (M * velocityH3EnergyAt u t) /
      velocityH3Energy3At u t :=
    div_nonneg (mul_nonneg hM hE) hE3.le
  have hRatio :=
    h3PathCanonical_topFourierFrequency_corridor_of_signedDominance
      hH3 hClass ht hM hAdverse
  linarith only [hRatio, hMscaled]

/-- Hypothetical nonextension forces a positive third-order Fourier energy
and a subcritical effective top spectral frequency, arbitrarily late for
any prescribed nonnegative normalized-growth allowance. -/
theorem h3PathCanonical_topFourierFrequency_corridor_on_every_subtail
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
      0 < velocityH3Energy3At u t ∧
      velocityH3Dissipation3At u t / velocityH3Energy3At u t +
          (M * velocityH3EnergyAt u t) / velocityH3Energy3At u t <
        4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) := by
  obtain ⟨t, ht, hAdverse⟩ :=
    h3PathCanonical_signedTopDominatesDissipation_on_every_subtail
      hH3 hNoExtension hClass hb hd hM
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  exact ⟨t, ht,
    h3PathCanonical_topEnergy_pos_of_signedTransportDominance
      hH3 hClass htClass hM hAdverse,
    h3PathCanonical_topFourierFrequency_corridor_of_signedDominance
      hH3 hClass htClass hM hAdverse⟩

/-- A genuine terminal high-frequency dissipative dominance criterion.
If the top dissipation is at least the entire Landau allowance K E3 on
some strict terminal tail, then the signed top-adverse nonextension witness
cannot occur. This is CONDITIONAL; the criterion itself is not proved
for all H3 Navier--Stokes paths. -/
theorem h3PathCanonical_extension_of_eventual_topSpectralDissipationDominance
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hDominance : ∀ t : ℝ, t ∈ Set.Ioo d T →
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) * velocityH3Energy3At u t ≤
        velocityH3Dissipation3At u t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨t, ht, hAdverse⟩ :=
    h3PathCanonical_signedTopDominatesDissipation_on_every_subtail
      hH3 hNoExtension hClass hb hd (by norm_num : (0 : ℝ) ≤ 0)
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  have hCorridor :=
    h3PathCanonical_topDissipation_add_growth_lt_LandauTopCeiling
      hH3 hClass htClass hAdverse
  simp only [zero_mul, add_zero] at hCorridor
  exact (not_lt_of_ge (hDominance t ht)) hCorridor

end Euclidean
end Bridge
end PrimeTensor
