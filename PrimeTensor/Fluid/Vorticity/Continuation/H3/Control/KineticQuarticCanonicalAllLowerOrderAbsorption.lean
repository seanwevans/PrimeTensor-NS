import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSecondOrderKineticAbsorption
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Angular.Concentration

/-!
# Absorb all lower-order H3 transport with a fixed kinetic anchor

The pointwise Fourier polynomial `2q <= 1+q^2` implies the new, physical
order-one interpolation inequality `2E1 <= E0+E2` on H3 path slices.
Consequently, with `h=C1*sqrt(E)`,

    6h E1 + 18h E2 <= 3h E0 + 21h E2.

The previous module established `E2^2 <= E0(b) D` for every t>b. Applying
its elementary quadratic Young lemma to `21h E2` absorbs all remaining
lower-order transport into one unit of full physical dissipation:

    E' + D <= 3h E0(b) + (21h)^2 E0(b) - T3
           = 3C1 sqrt(E) E0(b) + 441 C1^2 E0(b) E - T3.

After normalization, the lower-order terms are bounded on the entire
kinetic-anchored tail: the first tends to zero at high H3 energy, while the
second is constant in time. This permits a qualitative strengthening: on
any hypothetical nonextendible path, arbitrarily late times satisfy

    M E(t) + D(t) < -T3(t)

for each M>=0. Thus the only possible arbitrarily high normalized growth
channel, after coercive lower-order absorption, is *genuinely adverse signed*
third-order transport, exceeding viscous dissipation by an arbitrary
multiple of full energy. No claim that this behavior is realized is made.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3AllLowerAbsorption
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3AllLowerAbsorption :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Interpolate the first radial Fourier moment against the zeroth and second
moments using `2q <= 1+q^2` pointwise, with no additional analytic axiom. -/
theorem h3PathCanonical_two_firstEnergy_le_zeroth_add_second
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    2 * velocityH3Energy1At u t ≤
      velocityH3Energy0At u t + velocityH3Energy2At u t := by
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs hInt
  let S : H3FourierPoint3 → ℝ :=
    velocityH3FourierMassDensityAt u t hInt hMeas
  let q : H3FourierPoint3 → ℝ := h3FourierGradientSquare
  have h0Int : Integrable S volume := by
    dsimp only [S]
    exact velocityH3FourierMassDensityAt_integrable u t hInt hMeas
  have h1Int : Integrable (fun ξ => q ξ * S ξ) volume := by
    dsimp only [q, S]
    exact velocityH3FourierFirstAggregateDensity_integrable hInt hMeas hFourier
  have h2Int : Integrable (fun ξ => q ξ ^ 2 * S ξ) volume := by
    dsimp only [q, S]
    exact velocityH3FourierSecondAggregateDensity_integrable hInt hMeas hFourier
  have hPointwise (ξ : H3FourierPoint3) :
      2 * (q ξ * S ξ) ≤ S ξ + q ξ ^ 2 * S ξ := by
    have hq : 2 * q ξ ≤ 1 + q ξ ^ 2 := by
      nlinarith only [sq_nonneg (q ξ - 1)]
    have hS : 0 ≤ S ξ := by
      dsimp only [S]
      exact velocityH3FourierMassDensityAt_nonneg u t hInt hMeas ξ
    have hMul := mul_le_mul_of_nonneg_right hq hS
    nlinarith only [hMul]
  have hIntegral :
      2 * (∫ ξ : H3FourierPoint3, q ξ * S ξ ∂volume) ≤
        (∫ ξ : H3FourierPoint3, S ξ ∂volume) +
          (∫ ξ : H3FourierPoint3, q ξ ^ 2 * S ξ ∂volume) := by
    have hBound := MeasureTheory.integral_mono
      (h1Int.const_mul 2) (h0Int.add h2Int) hPointwise
    have hSplit :
        (∫ ξ : H3FourierPoint3, S ξ + q ξ ^ 2 * S ξ ∂volume) =
          (∫ ξ : H3FourierPoint3, S ξ ∂volume) +
            (∫ ξ : H3FourierPoint3, q ξ ^ 2 * S ξ ∂volume) := by
      exact MeasureTheory.integral_add h0Int h2Int
    calc
      2 * (∫ ξ : H3FourierPoint3, q ξ * S ξ ∂volume) =
          ∫ ξ : H3FourierPoint3, 2 * (q ξ * S ξ) ∂volume := by
        rw [integral_const_mul]
      _ ≤ ∫ ξ : H3FourierPoint3, S ξ + q ξ ^ 2 * S ξ ∂volume := hBound
      _ = (∫ ξ : H3FourierPoint3, S ξ ∂volume) +
            (∫ ξ : H3FourierPoint3, q ξ ^ 2 * S ξ ∂volume) := hSplit
  have h0 := velocityH3Energy0At_eq_fourierZerothRadialMoment hInt hMeas
  have h1 := velocityH3Energy1At_eq_fourierFirstRadialMoment hInt hMeas hFourier
  have h2 := velocityH3Energy2At_eq_fourierSecondRadialMoment hInt hMeas hFourier
  rw [h0, h1, h2]
  rw [velocityH3FourierFirstRadialMomentAt_eq_integral_massDensity
    hInt hMeas hFourier,
    velocityH3FourierZerothRadialMomentAt_eq_integral_massDensity
    hInt hMeas,
    velocityH3FourierSecondRadialMomentAt_eq_integral_massDensity
    hInt hMeas hFourier]
  exact hIntegral

/-- The genuine first- and second-order commutator costs can be reduced to
one kinetic term and one second-order energy term, both with sharp explicit
coefficients from the polynomial Fourier interpolation. -/
theorem h3PathCanonical_bothLowerCosts_le_kinetic_add_secondCost
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) *
        (6 * velocityH3Energy1At u t + 18 * velocityH3Energy2At u t) ≤
      (3 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) * velocityH3Energy0At u b +
      (21 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) * velocityH3Energy2At u t := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hFirst := h3PathCanonical_two_firstEnergy_le_zeroth_add_second
    hH3 hClass htClass
  have hAnti : AntitoneOn (velocityH3Energy0At u) (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed hH3 hClass
  have hKinetic : velocityH3Energy0At u t ≤ velocityH3Energy0At u b :=
    hAnti hb htClass (le_of_lt ht.1)
  let h : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
    Real.sqrt (velocityH3EnergyAt u t)
  have hh : 0 ≤ h := by
    dsimp only [h]
    exact mul_nonneg
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)
  have hScale := mul_le_mul_of_nonneg_left hFirst
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hh)
  have hMass := mul_le_mul_of_nonneg_left hKinetic
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hh)
  dsimp only [h] at hScale hMass ⊢
  nlinarith only [hScale, hMass]

/-- The second-order Fourier moment bound absorbs the remaining 21h E2,
spending εD and paying only a quadratic kinetic-energy remainder. -/
theorem h3PathCanonical_twentyOneSecondCost_le_viscousShare
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T)
    (hε : 0 < ε) :
    (21 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t))) * velocityH3Energy2At u t ≤
      ε * velocityH3DissipationAt u t +
        (21 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) ^ 2 *
          velocityH3Energy0At u b / ε := by
  let K : ℝ := 21 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
    Real.sqrt (velocityH3EnergyAt u t))
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by norm_num)
      (mul_nonneg
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
        (Real.sqrt_nonneg _))
  have hInterp := h3PathCanonical_secondEnergy_sq_le_anchorKinetic_mul_fullDissipation
    hH3 hClass hb ht
  have hScaled : (K * velocityH3Energy2At u t) ^ 2 ≤
      (K ^ 2 * velocityH3Energy0At u b) *
        velocityH3DissipationAt u t := by
    simpa only [mul_pow, mul_assoc] using
      mul_le_mul_of_nonneg_left hInterp (pow_nonneg hK 2)
  have hAbsorb := h3PathCanonical_absorb_of_square_le
    (mul_nonneg (pow_nonneg hK 2) (velocityH3Energy0At_nonneg u b))
    (velocityH3DissipationAt_nonneg u t) hε hScaled
  simpa only [K] using hAbsorb

/-- Both lower-order transport commutators are absorbed with only a fixed
kinetic anchor, leaving the *signed* third-order nonlinear pairing untouched. -/
theorem h3PathCanonical_deriv_retainedDissipation_le_signedTop_only
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T)
    (hε : 0 < ε) :
    deriv (velocityH3EnergyAt u) t +
        (2 - ε) * velocityH3DissipationAt u t ≤
      3 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy0At u b +
      (21 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) ^ 2 *
        velocityH3Energy0At u b / ε -
      velocityH3TransportDerivative3At u t := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hSigned := h3PathCanonical_deriv_add_dissipation_le_lowerOrderSignedTop
    hH3 hClass htClass
  have hLower := h3PathCanonical_bothLowerCosts_le_kinetic_add_secondCost
    hH3 hClass hb ht
  have hYoung := h3PathCanonical_twentyOneSecondCost_le_viscousShare
    hH3 hClass hb ht hε
  nlinarith only [hSigned, hLower, hYoung]

/-- Spend one full unit of dissipation to eliminate both low-order costs. -/
theorem h3PathCanonical_deriv_add_oneDissipation_le_signedTop_only
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    deriv (velocityH3EnergyAt u) t + velocityH3DissipationAt u t ≤
      3 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy0At u b +
      (21 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) ^ 2 *
        velocityH3Energy0At u b -
      velocityH3TransportDerivative3At u t := by
  have h := h3PathCanonical_deriv_retainedDissipation_le_signedTop_only
    hH3 hClass hb ht (show (0 : ℝ) < 1 by norm_num)
  convert h using 1 <;> norm_num

/-- The absorbed E2 remainder has precisely *linear* full H3 energy growth,
with a fixed kinetic-anchor prefactor. -/
theorem h3PathCanonical_twentyOneYoungAnchor_eq_linearEnergy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b t : ℝ) :
    (21 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) ^ 2 *
        velocityH3Energy0At u b =
      (441 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient ^ 2 *
        velocityH3Energy0At u b) * velocityH3EnergyAt u t := by
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  rw [mul_pow, mul_pow, Real.sq_sqrt hE]
  ring

/-- Every high unabsorbed H3 growth instant must pay the retained viscous
cost and an explicitly bounded kinetic remainder through adverse signed T3. -/
theorem h3PathCanonical_highUnabsorbed_forces_signedTopBeyondLowOrders
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T)
    (hM : 0 ≤ M)
    (hHigh : M < h3PathCanonicalUnabsorbedRiccatiRate u t) :
    (4422 + M -
      441 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient ^ 2 *
        velocityH3Energy0At u b) * velocityH3EnergyAt u t +
        velocityH3DissipationAt u t <
      3 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy0At u b -
      velocityH3TransportDerivative3At u t := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hSlope :=
    (h3PathCanonical_unabsorbedAbove_iff_normalizedEnergySlopeAbove
      hH3 hClass htClass hM).1 hHigh
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hPhysical := (lt_div_iff₀ hEPos).1 hSlope
  have hBound := h3PathCanonical_deriv_add_oneDissipation_le_signedTop_only
    hH3 hClass hb ht
  rw [h3PathCanonical_twentyOneYoungAnchor_eq_linearEnergy u b t] at hBound
  linarith only [hPhysical, hBound]

/-- The complete lower-order absorption converts *arbitrarily large*
actual H3 growth into arbitrarily large signed third-order transport adversity
above one unit of full physical dissipation, on every strict terminal tail.
No smallness or first-order ceiling hypothesis remains. -/
theorem h3PathCanonical_signedTopDominatesDissipation_on_every_subtail
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
        -velocityH3TransportDerivative3At u t := by
  let C : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  let K : ℝ := velocityH3Energy0At u b
  let B : ℝ := 441 * C ^ 2 * K + 3 * C * K + M + 1
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact velocityH3Energy0At_nonneg u b
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hdClass : d ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hd.1, hd.2⟩
  obtain ⟨t, ht, hHigh⟩ :=
    h3PathCanonical_unabsorbedRiccatiRate_unbounded_on_tail
      B hH3 hNoExtension hClass hdClass
  have htAnchor : t ∈ Set.Ioo b T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  have hAdverse := h3PathCanonical_highUnabsorbed_forces_signedTopBeyondLowOrders
    hH3 hClass hb htAnchor hB hHigh
  have hEOne : 1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t
  have hRootOne : 1 ≤ Real.sqrt (velocityH3EnergyAt u t) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hEOne
  have hRootBound : Real.sqrt (velocityH3EnergyAt u t) ≤
      velocityH3EnergyAt u t := by
    calc
      Real.sqrt (velocityH3EnergyAt u t) =
          1 * Real.sqrt (velocityH3EnergyAt u t) := by ring
      _ ≤ Real.sqrt (velocityH3EnergyAt u t) *
          Real.sqrt (velocityH3EnergyAt u t) :=
        mul_le_mul_of_nonneg_right hRootOne (Real.sqrt_nonneg _)
      _ = velocityH3EnergyAt u t := by
        nlinarith only [Real.sq_sqrt (le_trans zero_le_one hEOne)]
  have hRootScaled : 3 * C * K * Real.sqrt (velocityH3EnergyAt u t) ≤
      3 * C * K * velocityH3EnergyAt u t :=
    mul_le_mul_of_nonneg_left hRootBound (by positivity)
  dsimp only [B, C, K] at hAdverse hRootScaled
  refine ⟨t, ht, ?_⟩
  nlinarith only [hAdverse, hRootScaled, hEOne]

end

end Euclidean
end Bridge
end PrimeTensor
