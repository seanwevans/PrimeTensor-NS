import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalLowerOrderSignedTransport
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Fourier.Identification

/-!
# Kinetic-mass Fourier absorption of second-order H3 transport

The existing physical Fourier identifications and Cauchy--Schwarz theorem give

  E₂(t)^2 ≤ E₀(t) D₃(t).

Kinetic antitonicity E₀(t) ≤ E₀(b), and D₃ ≤ D, imply at every later strict
energy-class time

  E₂(t)^2 ≤ E₀(b) D(t).

A quadratic Young estimate then absorbs the *entire* order-two transport
allowance 18 C₁ sqrt(E) E₂ into an arbitrary positive viscous share:

  18 h E₂ ≤ ε D + (18 h)^2 E₀(b)/ε,  h = C₁ sqrt(E).

The exact signed PDE budget from `LowerOrderSignedTransport` therefore refines to

  E' + (2-ε)D ≤ 6 h E₁ + (18 h)^2 E₀(b)/ε - T₃.

With ε=1, the normalized quadratic remainder is the *fixed kinetic-anchor*
coefficient 324 C₁² E₀(b). This leaves only E₁ and the actual signed T₃ as
potential unabsorbed growth sources, rather than E₁ plus E₂ plus T₃.

These inequalities are genuine consequences of established Fourier/PDE facts,
not a bound on the remaining E₁ or favorable sign for T₃; no unconditional
continuation or existence of singularities is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- The *physical* second derivative energy is a Fourier middle moment:
`E₂² ≤ E₀ D₃`. This is a new physical-space repackaging of the already
proved exact radial moments and their Cauchy--Schwarz inequality. -/
theorem h3PathCanonical_secondEnergy_sq_le_kinetic_mul_topDissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3Energy2At u t ^ 2 ≤
      velocityH3Energy0At u t * velocityH3Dissipation3At u t := by
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
  have hMoment :=
    velocityH3FourierSecondRadialMomentAt_sq_le_zero_mul_fourth
      hH3 hClass ht hInt hMeas hFourier
  have h0 := velocityH3Energy0At_eq_fourierZerothRadialMoment
    hInt hMeas
  have h2 := velocityH3Energy2At_eq_fourierSecondRadialMoment
    hInt hMeas hFourier
  have h4 := velocityH3Dissipation3At_eq_fourierFourthRadialMoment
    hH3 hClass ht hInt hMeas hFourier
  rw [h2, h0, h4]
  exact hMoment

/-- Kinetic monotonicity and `D₃ ≤ D` make the moment inequality uniform
on every strict tail later than a fixed physical kinetic-energy anchor. -/
theorem h3PathCanonical_secondEnergy_sq_le_anchorKinetic_mul_fullDissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    velocityH3Energy2At u t ^ 2 ≤
      velocityH3Energy0At u b * velocityH3DissipationAt u t := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hMoment := h3PathCanonical_secondEnergy_sq_le_kinetic_mul_topDissipation
    hH3 hClass htClass
  have hAnti : AntitoneOn (velocityH3Energy0At u) (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3 hClass
  have hE0 : velocityH3Energy0At u t ≤ velocityH3Energy0At u b :=
    hAnti hb htClass (le_of_lt ht.1)
  have hD3 : velocityH3Dissipation3At u t ≤
      velocityH3DissipationAt u t :=
    velocityH3Dissipation3At_le_dissipationAt u t
  have hD3Nonneg : 0 ≤ velocityH3Dissipation3At u t :=
    velocityH3Dissipation3At_nonneg u t
  have hE0Nonneg : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  calc
    velocityH3Energy2At u t ^ 2 ≤
        velocityH3Energy0At u t * velocityH3Dissipation3At u t := hMoment
    _ ≤ velocityH3Energy0At u b * velocityH3Dissipation3At u t :=
      mul_le_mul_of_nonneg_right hE0 hD3Nonneg
    _ ≤ velocityH3Energy0At u b * velocityH3DissipationAt u t :=
      mul_le_mul_of_nonneg_left hD3 hE0Nonneg

/-- Division-free quadratic Young inequality with an explicit (nonoptimal)
constant: if `x² ≤ b d` then `x ≤ εd+b/ε` for every ε>0. -/
theorem h3PathCanonical_absorb_of_square_le
    {x b d ε : ℝ}
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hε : 0 < ε)
    (hPower : x ^ 2 ≤ b * d) :
    x ≤ ε * d + b / ε := by
  apply le_of_not_gt
  intro hLarge
  have hQuot : 0 ≤ b / ε := div_nonneg hb hε.le
  have hProduct : 0 ≤ ε * d := mul_nonneg hε.le hd
  have hxd : ε * d < x := by linarith only [hLarge, hQuot]
  have hx : 0 < x := lt_of_le_of_lt hProduct hxd
  have hxb : b / ε < x := by linarith only [hLarge, hProduct]
  have hbUpper : b < x * ε := (div_lt_iff₀ hε).1 hxb
  have hdUpper : d ≤ x / ε := by
    apply (le_div_iff₀ hε).2
    nlinarith only [hxd]
  have hImpossible : x ^ 2 < x ^ 2 := calc
    x ^ 2 ≤ b * d := hPower
    _ ≤ b * (x / ε) := mul_le_mul_of_nonneg_left hdUpper hb
    _ < (x * ε) * (x / ε) :=
      mul_lt_mul_of_pos_right hbUpper (div_pos hx hε)
    _ = x ^ 2 := by
      field_simp [ne_of_gt hε]
      <;> ring
  exact (lt_irrefl (x ^ 2)) hImpossible

/-- The second-order nonlinear transport allowance is absorbed using only
kinetic mass and full dissipation. The remainder scales like `h² E₀` rather
than the quartic `h⁴ E₀` required to absorb the top `E₃` block. -/
theorem h3PathCanonical_secondOrderCost_le_viscousShare_add_kineticRemainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T)
    (hε : 0 < ε) :
    (18 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t))) * velocityH3Energy2At u t ≤
      ε * velocityH3DissipationAt u t +
        (18 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) ^ 2 *
          velocityH3Energy0At u b / ε := by
  let K : ℝ := 18 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
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

/-- Keep the signed third-order PDE channel and absorb just the entire
second-order commutator through full physical viscous dissipation. -/
theorem h3PathCanonical_deriv_retainedDissipation_le_firstOrder_signedTop_quadraticKinetic
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T)
    (hε : 0 < ε) :
    deriv (velocityH3EnergyAt u) t +
        (2 - ε) * velocityH3DissipationAt u t ≤
      6 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy1At u t +
      (18 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) ^ 2 *
        velocityH3Energy0At u b / ε -
      velocityH3TransportDerivative3At u t := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hSigned := h3PathCanonical_deriv_add_dissipation_le_lowerOrderSignedTop
    hH3 hClass htClass
  have hYoung := h3PathCanonical_secondOrderCost_le_viscousShare_add_kineticRemainder
    hH3 hClass hb ht hε
  linarith only [hSigned, hYoung]

/-- With one complete unit of viscous dissipation reserved for absorption,
there is still a full positive `D` on the left. The remaining kinetic
remainder is `324 C₁² E E₀(b)` and its normalized coefficient is constant. -/
theorem h3PathCanonical_deriv_add_oneDissipation_le_firstOrder_signedTop_anchored
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    deriv (velocityH3EnergyAt u) t + velocityH3DissipationAt u t ≤
      6 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy1At u t +
      (18 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) ^ 2 *
        velocityH3Energy0At u b - velocityH3TransportDerivative3At u t := by
  have h := h3PathCanonical_deriv_retainedDissipation_le_firstOrder_signedTop_quadraticKinetic
    hH3 hClass hb ht (show (0 : ℝ) < 1 by norm_num)
  convert h using 1 <;> norm_num

/-- After kinetic anchoring, the entire second-order Young remainder is
*linear* in the full H³ energy. The normalization costs only the fixed
physical kinetic energy at the anchor. -/
theorem h3PathCanonical_secondOrderYoungAnchor_eq_linearEnergy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b t : ℝ) :
    (18 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) ^ 2 *
        velocityH3Energy0At u b =
      (324 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient ^ 2 *
        velocityH3Energy0At u b) * velocityH3EnergyAt u t := by
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  rw [mul_pow, mul_pow, Real.sq_sqrt hE]
  ring

/-- A high unabsorbed H³ growth instant forces the actual signed T₃ pairing
plus one unit of viscous dissipation to compensate all but the first-order
commutator and a fixed kinetic-anchor coefficient. -/
theorem h3PathCanonical_highUnabsorbed_forces_firstOrder_or_signedTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T)
    (hM : 0 ≤ M)
    (hHigh : M < h3PathCanonicalUnabsorbedRiccatiRate u t) :
    (4422 + M -
      324 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient ^ 2 *
        velocityH3Energy0At u b) * velocityH3EnergyAt u t +
        velocityH3DissipationAt u t <
      6 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy1At u t -
      velocityH3TransportDerivative3At u t := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hSlope :=
    (h3PathCanonical_unabsorbedAbove_iff_normalizedEnergySlopeAbove
      hH3 hClass htClass hM).1 hHigh
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hPhysical := (lt_div_iff₀ hEPos).1 hSlope
  have hBound := h3PathCanonical_deriv_add_oneDissipation_le_firstOrder_signedTop_anchored
    hH3 hClass hb ht
  rw [h3PathCanonical_secondOrderYoungAnchor_eq_linearEnergy u b t] at hBound
  linarith only [hPhysical, hBound]

/-- If the surviving first-order commutator is itself below the explicit
anchor-dependent threshold at a high-growth time, the third-order signed
transport pairing must be genuinely adverse and exceed a full unit of D. -/
theorem h3PathCanonical_highUnabsorbed_forces_topAdversity_of_firstOrderCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T)
    (hM : 0 ≤ M)
    (hHigh : M < h3PathCanonicalUnabsorbedRiccatiRate u t)
    (hFirst :
      6 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy1At u t ≤
        (4422 + M -
          324 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient ^ 2 *
            velocityH3Energy0At u b) * velocityH3EnergyAt u t) :
    velocityH3DissipationAt u t <
      -velocityH3TransportDerivative3At u t := by
  have hAdverse := h3PathCanonical_highUnabsorbed_forces_firstOrder_or_signedTop
    hH3 hClass hb ht hM hHigh
  linarith only [hAdverse, hFirst]

end Euclidean
end Bridge
end PrimeTensor
