import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzCanonicalOrderwise244
import Mathlib.Tactic

/-!
# Reserved kinetic and top-order energy in the physical Schwartz budget

The canonical first/second transport estimate costs 6 E1 + 18 E2, not
24 times the full energy. Since E = 1 + E0 + E1 + E2 + E3,

  6 E1 + 18 E2 + 18 (1 + E0 + E3) <= 18 E.

This retains the kinetic and top-order H3 masses without charging either
against the lower commutators. It improves the coarse universal factor 24
to 18, while the exact 6/18 weights remain available separately.

The resulting high-unabsorbed-growth alternative says either the actual
normalized square-root H3 gradient scale clears a quantitative threshold,
or the exact signed third-order Schwartz transport defeats twice the full
viscosity. No static Schwarz witness is identified with an NS time slice.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdReservedEnergy244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact unused normalized kinetic/top-third mass is reserved from
lower commutators. Only nonnegativity of E1 is required. -/
theorem thirdFullSchwartz_orderwiseBudget_add_reservedMass_le_18_energy244
    (f : A3 → SchwartzMap V3 ℝ) :
    (6 * lowNormalRealSchwartzH3Energy1 f +
      18 * lowNormalRealSchwartzH3Energy2 f) +
      18 * (1 + lowNormalRealSchwartzH3Energy0 f +
        lowNormalRealSchwartzH3Energy3 f) ≤
      18 * lowNormalRealSchwartzH3Energy f := by
  rw [lowNormalRealSchwartzH3Energy_eq_one_add_quadratic,
    lowNormalRealSchwartzH3EnergyQuadratic_eq_sum]
  have h1 := lowNormalRealSchwartzH3Energy1_nonneg f
  linarith only [h1]

/-- The orderwise cost has coefficient 18, NOT 24, when expressed as a
uniform multiple of the complete normalized energy. -/
theorem thirdFullSchwartz_orderwiseBudget_le_18_energy244
    (f : A3 → SchwartzMap V3 ℝ) :
    6 * lowNormalRealSchwartzH3Energy1 f +
      18 * lowNormalRealSchwartzH3Energy2 f ≤
      18 * lowNormalRealSchwartzH3Energy f := by
  have hReserved :=
    thirdFullSchwartz_orderwiseBudget_add_reservedMass_le_18_energy244 f
  have h0 := lowNormalRealSchwartzH3Energy0_nonneg f
  have h3 := lowNormalRealSchwartzH3Energy3_nonneg f
  linarith only [hReserved, h0, h3]

/-- On an actually realized Schwartz slice, the absolute lower commutator
plus a separately reserved kinetic/top-third mass fits in 18 h E. -/
theorem h3Path_lowerTransport_abs_add_reservedMass_le_18_energy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    |velocityH3TransportDerivative1At u t +
      velocityH3TransportDerivative2At u t| +
      18 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
        (1 + lowNormalRealSchwartzH3Energy0 f +
          lowNormalRealSchwartzH3Energy3 f) ≤
      18 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
        lowNormalRealSchwartzH3Energy f := by
  let H : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
    Real.sqrt (lowNormalRealSchwartzH3Energy f)
  have hH : 0 ≤ H := by
    dsimp only [H]
    exact mul_nonneg
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)
  have hTransport := h3Path_lowerTransport_abs_le_realSchwartzOrderwise244
    hH3 hClass ht f hRealization
  change |velocityH3TransportDerivative1At u t +
    velocityH3TransportDerivative2At u t| ≤ H *
    (6 * lowNormalRealSchwartzH3Energy1 f +
      18 * lowNormalRealSchwartzH3Energy2 f) at hTransport
  have hMass := thirdFullSchwartz_orderwiseBudget_add_reservedMass_le_18_energy244 f
  have hScale := mul_le_mul_of_nonneg_left hMass hH
  change H * ((6 * lowNormalRealSchwartzH3Energy1 f +
    18 * lowNormalRealSchwartzH3Energy2 f) +
    18 * (1 + lowNormalRealSchwartzH3Energy0 f +
      lowNormalRealSchwartzH3Energy3 f)) ≤
    H * (18 * lowNormalRealSchwartzH3Energy f) at hScale
  change |velocityH3TransportDerivative1At u t +
    velocityH3TransportDerivative2At u t| +
      18 * H * (1 + lowNormalRealSchwartzH3Energy0 f +
        lowNormalRealSchwartzH3Energy3 f) ≤
      18 * H * lowNormalRealSchwartzH3Energy f
  nlinarith only [hTransport, hScale]

/-- A closed physical signed energy inequality with a *positive* kinetic/
third-jet reserve remaining on the left side. -/
theorem h3Path_deriv_add_fullViscosity_add_reservedMass_le_18_energy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    deriv (velocityH3EnergyAt u) t +
      2 * lowNormalRealSchwartzH3FullDissipation244 f +
      18 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
        (1 + lowNormalRealSchwartzH3Energy0 f +
          lowNormalRealSchwartzH3Energy3 f) ≤
      18 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
        lowNormalRealSchwartzH3Energy f -
        fullSchwartzThirdCommutator244 f := by
  let H : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
    Real.sqrt (lowNormalRealSchwartzH3Energy f)
  have hH : 0 ≤ H := by
    dsimp only [H]
    exact mul_nonneg
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)
  have hBase := h3Path_deriv_add_completeSchwartzDissipation_le_orderwise244
    hH3 hClass ht f hRealization
  have hMass := thirdFullSchwartz_orderwiseBudget_add_reservedMass_le_18_energy244 f
  have hScaled := mul_le_mul_of_nonneg_left hMass hH
  change H * ((6 * lowNormalRealSchwartzH3Energy1 f +
      18 * lowNormalRealSchwartzH3Energy2 f) +
      18 * (1 + lowNormalRealSchwartzH3Energy0 f +
        lowNormalRealSchwartzH3Energy3 f)) ≤
    H * (18 * lowNormalRealSchwartzH3Energy f) at hScaled
  change deriv (velocityH3EnergyAt u) t +
      2 * lowNormalRealSchwartzH3FullDissipation244 f ≤
      H * (6 * lowNormalRealSchwartzH3Energy1 f +
        18 * lowNormalRealSchwartzH3Energy2 f) -
        fullSchwartzThirdCommutator244 f at hBase
  change deriv (velocityH3EnergyAt u) t +
    2 * lowNormalRealSchwartzH3FullDissipation244 f +
    18 * H * (1 + lowNormalRealSchwartzH3Energy0 f +
      lowNormalRealSchwartzH3Energy3 f) ≤
    18 * H * lowNormalRealSchwartzH3Energy f -
      fullSchwartzThirdCommutator244 f
  nlinarith only [hBase, hScaled]

/-- A threshold in genuine normalized H3 energy, with its kinetic and
highest-order mass subtracted from the lower commutator allocation. -/
theorem h3Path_energySlope_pos_of_realSchwartzReservedBudget244
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
        18 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
          (lowNormalRealSchwartzH3Energy f - 1 -
            lowNormalRealSchwartzH3Energy0 f -
            lowNormalRealSchwartzH3Energy3 f) <
      -fullSchwartzThirdCommutator244 f) :
    0 < deriv (velocityH3EnergyAt u) t := by
  let H : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
    Real.sqrt (lowNormalRealSchwartzH3Energy f)
  have hH : 0 ≤ H := by
    dsimp only [H]
    exact mul_nonneg
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)
  have hEnergy : lowNormalRealSchwartzH3Energy f - 1 -
      lowNormalRealSchwartzH3Energy0 f -
      lowNormalRealSchwartzH3Energy3 f =
        lowNormalRealSchwartzH3Energy1 f +
        lowNormalRealSchwartzH3Energy2 f := by
    rw [lowNormalRealSchwartzH3Energy_eq_one_add_quadratic,
      lowNormalRealSchwartzH3EnergyQuadratic_eq_sum]
    ring
  have hE1 := lowNormalRealSchwartzH3Energy1_nonneg f
  have hWeights : 6 * lowNormalRealSchwartzH3Energy1 f +
      18 * lowNormalRealSchwartzH3Energy2 f ≤
    18 * (lowNormalRealSchwartzH3Energy1 f +
      lowNormalRealSchwartzH3Energy2 f) := by
    linarith only [hE1]
  have hScaled := mul_le_mul_of_nonneg_left hWeights hH
  have hExact := h3Path_exactEnergyBalance_fullThirdSchwartz_noFluxAssumption244
    hH3 hClass ht f hRealization
  have hLower := h3Path_lowerTransport_abs_le_realSchwartzOrderwise244
    hH3 hClass ht f hRealization
  have hUpper :
      velocityH3TransportDerivative1At u t +
        velocityH3TransportDerivative2At u t ≤
      H * (6 * lowNormalRealSchwartzH3Energy1 f +
        18 * lowNormalRealSchwartzH3Energy2 f) := by
    exact le_trans (le_abs_self _ ) hLower
  rw [hEnergy] at hAdverse
  change 2 * lowNormalRealSchwartzH3FullDissipation244 f +
      18 * H * (lowNormalRealSchwartzH3Energy1 f +
        lowNormalRealSchwartzH3Energy2 f) <
    -fullSchwartzThirdCommutator244 f at hAdverse
  nlinarith only [hExact, hUpper, hScaled, hAdverse]

/-- High unabsorbed growth forces either the sharpened lower-budget branch
(with the kinetic/third-order reserve explicit) or exact top adversity. -/
theorem h3Path_highUnabsorbed_realSchwartzReservedAlternative244
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
    (4422 + M) * lowNormalRealSchwartzH3Energy f +
      18 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
        (1 + lowNormalRealSchwartzH3Energy0 f +
          lowNormalRealSchwartzH3Energy3 f) <
      18 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
        lowNormalRealSchwartzH3Energy f ∨
      2 * lowNormalRealSchwartzH3FullDissipation244 f <
        -fullSchwartzThirdCommutator244 f := by
  have hOld := h3Path_highUnabsorbed_realSchwartzOrderwiseAlternative244
    hH3 hClass ht f hRealization hM hHigh
  rcases hOld with hLow | hTop
  · left
    let H : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (lowNormalRealSchwartzH3Energy f)
    have hH : 0 ≤ H := by
      dsimp only [H]
      exact mul_nonneg
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
        (Real.sqrt_nonneg _)
    have hMass := thirdFullSchwartz_orderwiseBudget_add_reservedMass_le_18_energy244 f
    have hScaled := mul_le_mul_of_nonneg_left hMass hH
    change H * ((6 * lowNormalRealSchwartzH3Energy1 f +
        18 * lowNormalRealSchwartzH3Energy2 f) +
        18 * (1 + lowNormalRealSchwartzH3Energy0 f +
          lowNormalRealSchwartzH3Energy3 f)) ≤
      H * (18 * lowNormalRealSchwartzH3Energy f) at hScaled
    change (4422 + M) * lowNormalRealSchwartzH3Energy f <
      H * (6 * lowNormalRealSchwartzH3Energy1 f +
        18 * lowNormalRealSchwartzH3Energy2 f) at hLow
    change (4422 + M) * lowNormalRealSchwartzH3Energy f +
        18 * H * (1 + lowNormalRealSchwartzH3Energy0 f +
          lowNormalRealSchwartzH3Energy3 f) <
        18 * H * lowNormalRealSchwartzH3Energy f
    nlinarith only [hLow, hScaled]
  · exact Or.inr hTop

/-- The spectral alternative eliminates E0/E3 bookkeeping completely:
if the top block does not dominate, high Riccati growth requires the
normalized square-root H3 scale to cross (4422+M)/18. -/
theorem h3Path_highUnabsorbed_realSchwartzGradientThreshold244
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
    4422 + M <
      18 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) ∨
      2 * lowNormalRealSchwartzH3FullDissipation244 f <
        -fullSchwartzThirdCommutator244 f := by
  have hOld := h3Path_highUnabsorbed_realSchwartzOrderwiseAlternative244
    hH3 hClass ht f hRealization hM hHigh
  rcases hOld with hLow | hTop
  · left
    let H : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (lowNormalRealSchwartzH3Energy f)
    have hH : 0 ≤ H := by
      dsimp only [H]
      exact mul_nonneg
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
        (Real.sqrt_nonneg _)
    have hMass := thirdFullSchwartz_orderwiseBudget_le_18_energy244 f
    have hScaled := mul_le_mul_of_nonneg_left hMass hH
    have hOne : 1 ≤ lowNormalRealSchwartzH3Energy f := by
      rw [lowNormalRealSchwartzH3Energy_eq_one_add_quadratic]
      have hQ := lowNormalRealSchwartzH3EnergyQuadratic_nonneg f
      linarith only [hQ]
    have hPos : 0 < lowNormalRealSchwartzH3Energy f :=
      lt_of_lt_of_le zero_lt_one hOne
    change (4422 + M) * lowNormalRealSchwartzH3Energy f <
      H * (6 * lowNormalRealSchwartzH3Energy1 f +
        18 * lowNormalRealSchwartzH3Energy2 f) at hLow
    have hRaw : (4422 + M) * lowNormalRealSchwartzH3Energy f <
        (18 * H) * lowNormalRealSchwartzH3Energy f := by
      nlinarith only [hLow, hScaled]
    change 4422 + M < 18 * H
    by_contra hNot
    have hGe : 18 * H ≤ 4422 + M := le_of_not_gt hNot
    have hScaledBack := mul_le_mul_of_nonneg_right hGe (le_of_lt hPos)
    exact (not_lt_of_ge hScaledBack) hRaw
  · exact Or.inr hTop

/-- Below the precise sqrt-energy lower-transport threshold, high actual
growth cannot be explained by the first two commutators: signed top
transport must defeat twice the *complete* viscosity. -/
theorem h3Path_highUnabsorbed_topAdverse_of_realSchwartzGradientCeiling244
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
      18 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) ≤ 4422 + M) :
    2 * lowNormalRealSchwartzH3FullDissipation244 f <
      -fullSchwartzThirdCommutator244 f := by
  rcases h3Path_highUnabsorbed_realSchwartzGradientThreshold244
      hH3 hClass ht f hRealization hM hHigh with hCross | hTop
  · exact False.elim ((not_lt_of_ge hCeiling) hCross)
  · exact hTop

end
end PrimeTensor.FirstMonomialTriad
