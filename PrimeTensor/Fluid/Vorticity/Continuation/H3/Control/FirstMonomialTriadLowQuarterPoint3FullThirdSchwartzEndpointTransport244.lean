import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzReservedEnergy244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzSharpAdjacentCauchy
import Mathlib.Tactic

/-!
# Endpoint-only control of the lower H3 transport on actual Schwartz slices

The sharp adjacent Cauchy inequalities E1^2 <= E0 E2 and E2^2 <= E1 E3
imply 2 E1 <= E0+E2 and 2 E2 <= E1+E3. Eliminating the intermediate
moments gives the genuine discrete order-convexity bounds

    3 E1 <= 2 E0 + E3,   3 E2 <= E0 + 2 E3.

Consequently the actual orderwise nonlinear transport is controlled by

    |T1+T2| <= C1 sqrt(E) (10 E0 + 14 E3).

Unlike the prior uniform 18 E bound, this controls the two commutators using
only the kinetic and order-three masses, with no additional analytic premise.
The coefficient-one Cauchy estimates use all physical derivative slots.

The corresponding exact physical energy inequality and unabsorbed-growth
alternative are conditional on actual Schwartz realization. A final theorem
makes the extra endpoint-ceiling assumption explicit on a nonextension tail:
it does not identify arbitrary static packets with Navier--Stokes slices.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdEndpointTransport244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Division-free, real-number arithmetic-geometric comparison.
The lower bound on z is not required: the Cauchy bound already forces
2z <= x+y if x,y are nonnegative. -/
private theorem two_mul_le_add_of_sq_le_mul_endpoint244
    {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hCS : z ^ 2 ≤ x * y) :
    2 * z ≤ x + y := by
  have hSq : (2 * z) ^ 2 ≤ (x + y) ^ 2 := by
    nlinarith only [hCS, sq_nonneg (x - y)]
  by_contra hNot
  have hStrict : x + y < 2 * z := lt_of_not_ge hNot
  have hNonneg : 0 ≤ x + y := add_nonneg hx hy
  have hPower : (x + y) ^ 2 < (2 * z) ^ 2 :=
    pow_lt_pow_left₀ hStrict hNonneg (by norm_num : (2 : ℕ) ≠ 0)
  exact (not_lt_of_ge hSq) hPower

/-- The full physical Schwartz H3 energies are discretely convex between
orders zero and three, with sharp linear interpolation coefficients. -/
theorem thirdFullSchwartz_energyOrder_arithmeticConvexity244
    (f : A3 → SchwartzMap V3 ℝ) :
    3 * lowNormalRealSchwartzH3Energy1 f ≤
      2 * lowNormalRealSchwartzH3Energy0 f +
        lowNormalRealSchwartzH3Energy3 f ∧
    3 * lowNormalRealSchwartzH3Energy2 f ≤
      lowNormalRealSchwartzH3Energy0 f +
        2 * lowNormalRealSchwartzH3Energy3 f := by
  have h01 :
      2 * lowNormalRealSchwartzH3Energy1 f ≤
        lowNormalRealSchwartzH3Energy0 f +
          lowNormalRealSchwartzH3Energy2 f :=
    two_mul_le_add_of_sq_le_mul_endpoint244
      (lowNormalRealSchwartzH3Energy0_nonneg f)
      (lowNormalRealSchwartzH3Energy2_nonneg f)
      (lowNormalRealSchwartzH3Energy1_sq_le_E0_mul_E2 f)
  have h12 :
      2 * lowNormalRealSchwartzH3Energy2 f ≤
        lowNormalRealSchwartzH3Energy1 f +
          lowNormalRealSchwartzH3Energy3 f :=
    two_mul_le_add_of_sq_le_mul_endpoint244
      (lowNormalRealSchwartzH3Energy1_nonneg f)
      (lowNormalRealSchwartzH3Energy3_nonneg f)
      (lowNormalRealSchwartzH3Energy2_sq_le_E1_mul_E3 f)
  constructor
  · linarith only [h01, h12]
  · linarith only [h01, h12]

/-- The entire first- and second-order transport allocation is bounded by
kinetic and third-order masses only. The constants are 10 and 14, without
a finite-axis loss or a hidden interpolation assumption. -/
theorem thirdFullSchwartz_orderwiseBudget_le_endpointMass244
    (f : A3 → SchwartzMap V3 ℝ) :
    6 * lowNormalRealSchwartzH3Energy1 f +
      18 * lowNormalRealSchwartzH3Energy2 f ≤
    10 * lowNormalRealSchwartzH3Energy0 f +
      14 * lowNormalRealSchwartzH3Energy3 f := by
  obtain ⟨hFirst, hSecond⟩ :=
    thirdFullSchwartz_energyOrder_arithmeticConvexity244 f
  linarith only [hFirst, hSecond]

/-- A realized H3 Navier--Stokes Schwartz slice satisfies the lower-order
transport estimate charged solely to its physical kinetic and top jets. -/
theorem h3Path_lowerTransport_abs_le_realSchwartzEndpointMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    |velocityH3TransportDerivative1At u t +
      velocityH3TransportDerivative2At u t| ≤
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
        (10 * lowNormalRealSchwartzH3Energy0 f +
          14 * lowNormalRealSchwartzH3Energy3 f) := by
  have hOld := h3Path_lowerTransport_abs_le_realSchwartzOrderwise244
    hH3 hClass ht f hRealization
  have hMass := thirdFullSchwartz_orderwiseBudget_le_endpointMass244 f
  have hCoeff :
      0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f) :=
    mul_nonneg
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)
  exact le_trans hOld (mul_le_mul_of_nonneg_left hMass hCoeff)

/-- Signed H3 energy balance with complete viscous dissipation and an
endpoint-only lower-order commutator budget. -/
theorem h3Path_deriv_add_completeSchwartzDissipation_le_endpointMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    deriv (velocityH3EnergyAt u) t +
      2 * lowNormalRealSchwartzH3FullDissipation244 f ≤
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
        (10 * lowNormalRealSchwartzH3Energy0 f +
          14 * lowNormalRealSchwartzH3Energy3 f) -
      fullSchwartzThirdCommutator244 f := by
  have hOld := h3Path_deriv_add_completeSchwartzDissipation_le_orderwise244
    hH3 hClass ht f hRealization
  have hMass := thirdFullSchwartz_orderwiseBudget_le_endpointMass244 f
  have hCoeff :
      0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f) :=
    mul_nonneg
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)
  exact le_trans hOld
    (sub_le_sub_right (mul_le_mul_of_nonneg_left hMass hCoeff)
      (fullSchwartzThirdCommutator244 f))

/-- A genuinely sufficient positive energy-slope criterion, obtained from
the exact signed balance rather than by reversing an upper estimate. -/
theorem h3Path_energySlope_pos_of_realSchwartzEndpointBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hAdverse :
      2 * lowNormalRealSchwartzH3FullDissipation244 f +
        (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
          (10 * lowNormalRealSchwartzH3Energy0 f +
            14 * lowNormalRealSchwartzH3Energy3 f) <
      -fullSchwartzThirdCommutator244 f) :
    0 < deriv (velocityH3EnergyAt u) t := by
  have hExact :=
    h3Path_exactEnergyBalance_fullThirdSchwartz_noFluxAssumption244
      hH3 hClass ht f hRealization
  have hLower :=
    h3Path_lowerTransport_abs_le_realSchwartzEndpointMass244
      hH3 hClass ht f hRealization
  have hUpper :
      velocityH3TransportDerivative1At u t +
        velocityH3TransportDerivative2At u t ≤
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
          (10 * lowNormalRealSchwartzH3Energy0 f +
            14 * lowNormalRealSchwartzH3Energy3 f) :=
    le_trans (le_abs_self _) hLower
  linarith only [hExact, hUpper, hAdverse]

/-- At a realized slice of very high unabsorbed growth, either the lower
commutator threshold can be paid for using endpoint masses, or the signed
third-order transport defeats the COMPLETE viscous dissipation. -/
theorem h3Path_highUnabsorbed_realSchwartzEndpointAlternative244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hM : 0 ≤ M)
    (hHigh : M < h3PathCanonicalUnabsorbedRiccatiRate u t) :
    (4422 + M) * lowNormalRealSchwartzH3Energy f <
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
          (10 * lowNormalRealSchwartzH3Energy0 f +
            14 * lowNormalRealSchwartzH3Energy3 f) ∨
      2 * lowNormalRealSchwartzH3FullDissipation244 f <
        -fullSchwartzThirdCommutator244 f := by
  have hOld := h3Path_highUnabsorbed_realSchwartzOrderwiseAlternative244
    hH3 hClass ht f hRealization hM hHigh
  rcases hOld with hLow | hTop
  · left
    have hMass := thirdFullSchwartz_orderwiseBudget_le_endpointMass244 f
    have hCoeff :
        0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (lowNormalRealSchwartzH3Energy f) :=
      mul_nonneg
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
        (Real.sqrt_nonneg _)
    exact lt_of_lt_of_le hLow
      (mul_le_mul_of_nonneg_left hMass hCoeff)
  · exact Or.inr hTop

/-- An explicit endpoint-energy ceiling rules out the lower-commutator
branch at a high-growth realized slice and forces genuinely adverse top
transport. This ceiling is NOT asserted automatically for every solution. -/
theorem h3Path_highUnabsorbed_topAdverse_of_endpointMassCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hM : 0 ≤ M)
    (hHigh : M < h3PathCanonicalUnabsorbedRiccatiRate u t)
    (hCeiling :
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
          (10 * lowNormalRealSchwartzH3Energy0 f +
            14 * lowNormalRealSchwartzH3Energy3 f) ≤
      (4422 + M) * lowNormalRealSchwartzH3Energy f) :
    2 * lowNormalRealSchwartzH3FullDissipation244 f <
      -fullSchwartzThirdCommutator244 f := by
  rcases h3Path_highUnabsorbed_realSchwartzEndpointAlternative244
      hH3 hClass ht f hRealization hM hHigh with hLow | hTop
  · exact False.elim ((not_lt_of_ge hCeiling) hLow)
  · exact hTop

/-- On the hypothetical nonextension branch, if every strict tail slice
admits a Schwartz representative satisfying the explicit endpoint ceiling,
then arbitrarily far along the tail there is a realized field whose signed
top nonlinear transport exceeds twice the complete viscosity. This DOES
NOT deduce the ceiling or Schwartz realization from admissibility. -/
theorem h3Path_noExtension_topAdverseWitness_of_endpointCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hM : 0 ≤ M)
    (hRealizedCeilingTail : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∃ f : A3 → SchwartzMap V3 ℝ,
        (∀ j : A3,
          loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) ∧
        (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
            (10 * lowNormalRealSchwartzH3Energy0 f +
              14 * lowNormalRealSchwartzH3Energy3 f) ≤
          (4422 + M) * lowNormalRealSchwartzH3Energy f) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      ∃ f : A3 → SchwartzMap V3 ℝ,
        (∀ j : A3,
          loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) ∧
        2 * lowNormalRealSchwartzH3FullDissipation244 f <
          -fullSchwartzThirdCommutator244 f := by
  obtain ⟨t, ht, hHigh⟩ :=
    h3PathCanonical_unabsorbedRiccatiRate_unbounded_on_tail
      M hH3 hNoExtension hClass hd
  obtain ⟨f, hRealization, hCeiling⟩ := hRealizedCeilingTail t ht
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  have hTop := h3Path_highUnabsorbed_topAdverse_of_endpointMassCeiling244
    hH3 hClass htClass f hRealization hM hHigh hCeiling
  exact ⟨t, ht, f, hRealization, hTop⟩

end
end PrimeTensor.FirstMonomialTriad
