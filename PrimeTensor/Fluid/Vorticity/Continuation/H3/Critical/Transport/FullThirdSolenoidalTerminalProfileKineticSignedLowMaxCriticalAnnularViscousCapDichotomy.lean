import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalOuterTailKineticViscousBudget
import Mathlib.Tactic

/-!
# Actual critical H3 annular compensation: a linear-viscous charge or a spike

The previous actual physical annular compensation budget contains an outer
source term quadratic in the instantaneous full H3 viscous dissipation D(t).
A finite L1 viscous clock does not pay D(t)^2, even at selected times.

This module proves the precise *truncated* alternative, with NO additional
PDE assumption. For an arbitrary cap H, either D(t) > H or D(t) <= H.
In the latter case the exact algebraic identity

  (k (B+3D))^2 <= (k B)^2 + (6 k^2 B+9 k^2 H) D

replaces the squared source ceiling by a linear charge. The true annular
Young-gap and frequency-width costs are retained with their precise
coefficients, as is the physical kinetic excess.

This is a SAME-TIME dichotomy. It does not give persistence of either
branch over a positive-width physical time interval; the latter is the
missing ingredient for charging the already constructed disjoint L1 clocks.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeAnnularViscousCap244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceAnnularViscousCap244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- An exact linearization of the squared affine dissipation source budget
on the sublevel set D <= H. No positivity of the affine constant is needed. -/
theorem thirdFullKinetic_affineViscousSquare_linearBelowCap244
    (k B D H : ℝ) (hD : 0 ≤ D) (hCap : D ≤ H) :
    (k * (B + 3 * D)) ^ 2 ≤
      (k * B) ^ 2 + (6 * k ^ 2 * B + 9 * k ^ 2 * H) * D := by
  have hNonneg : 0 ≤ 9 * k ^ 2 * D * (H - D) := by
    apply mul_nonneg
    · exact mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) (sq_nonneg k)) hD
    · exact sub_nonneg.mpr hCap
  nlinarith only [hNonneg]

/-- The genuine physical outer-tail budget at zero full H3 dissipation. -/
noncomputable def thirdFullPhysicalOuterViscousCapBase244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b rate : ℝ) : ℝ :=
  2 * ((3 + h3AuditInitialLerayEnergyCoefficient) *
    (1 + 6 * velocityH3Energy0At u b)) ^ 2 +
    2 * rate ^ 2 * velocityH3Energy0At u b

/-- The exact slope obtained by replacing D(t)^2 with H*D(t) on D <= H.
It depends on the chosen cap, not on a presumed terminal H3 bound. -/
noncomputable def thirdFullPhysicalOuterViscousCapSlope244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b H : ℝ) : ℝ :=
  12 * (3 + h3AuditInitialLerayEnergyCoefficient) ^ 2 *
      (1 + 6 * velocityH3Energy0At u b) +
    18 * (3 + h3AuditInitialLerayEnergyCoefficient) ^ 2 * H

/-- The actual physical Fourier outer ceiling is LINEAR in full H3
dissipation on every specified sublevel set D(t) <= H. This is an algebraic
consequence of the already proved physical source estimate, not an L2_t
integrability statement. -/
theorem thirdFullPhysical_outerKineticViscousBudget_linearBelowCap244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b t rate H : ℝ)
    (hCap : velocityH3DissipationAt u t ≤ H) :
    thirdFullPhysicalOuterKineticViscousBudget244 u b t rate ≤
      thirdFullPhysicalOuterViscousCapBase244 u b rate +
        thirdFullPhysicalOuterViscousCapSlope244 u b H *
          velocityH3DissipationAt u t := by
  let k : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let B : ℝ := 1 + 6 * velocityH3Energy0At u b
  let D : ℝ := velocityH3DissipationAt u t
  have hD : 0 ≤ D := velocityH3DissipationAt_nonneg u t
  have hSq := thirdFullKinetic_affineViscousSquare_linearBelowCap244
    k B D H hD hCap
  change 2 * (k * (B + 3 * D)) ^ 2 +
      2 * rate ^ 2 * velocityH3Energy0At u b ≤
    2 * (k * B) ^ 2 + 2 * rate ^ 2 * velocityH3Energy0At u b +
      (12 * k ^ 2 * B + 18 * k ^ 2 * H) * D
  nlinarith only [hSq]

/-- The EXACT two local costs, with neither the original outer tail nor its
full physical viscous ceiling. Their Fourier integrals remain unaltered. -/
noncomputable def thirdFullPhysicalActualAnnularYoungWidthCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t rho sigma : ℝ) : ℝ :=
  let ann : Set H3FourierPoint3 :=
    ((h3TerminalRadialFrequencyBelow rho)ᶜ) ∩
      h3TerminalRadialFrequencyBelow sigma
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  2 * (∑ j : Fin 3, ∫ ξ in ann,
    h3FourierGradientSquare ξ ^ 3 *
      ‖h3RawFinLerayOuterProductDivergence U U j ξ +
        2 * ((h3FourierGradientSquare ξ : ℂ) *
          h3SpectralScalarRawFourierL2 (U j) ξ)‖ ^ 2 ∂volume) +
  (2 * (sigma ^ 2) ^ 3 * ((sigma ^ 2 - rho ^ 2) / 2) ^ 2) *
    (∑ j : Fin 3, ∫ ξ in ann,
      ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume)

/-- The accepted full physical cost is EXACTLY Young gap + width + its
outer kinetic/viscous ceiling, with no hidden additional terms. -/
theorem thirdFullPhysical_actualAnnularViscousCost_split244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b t rho sigma : ℝ) :
    thirdFullPhysicalActualAnnularViscousCost244 hH3 b t rho sigma =
      thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 t rho sigma +
        (rho ^ 2) ^ 3 * thirdFullPhysicalOuterKineticViscousBudget244
          u b t ((rho ^ 2 + sigma ^ 2) / 2) := by
  rfl

/-- Localized Young-gap and width remain exact. Only the quadratic outer
physical source budget is linearized, and only when D(t) <= H. -/
theorem thirdFullPhysical_actualAnnularViscousCost_linearBelowCap244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b t rho sigma H : ℝ)
    (hCap : velocityH3DissipationAt u t ≤ H) :
    thirdFullPhysicalActualAnnularViscousCost244 hH3 b t rho sigma ≤
      thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 t rho sigma +
        (rho ^ 2) ^ 3 *
          (thirdFullPhysicalOuterViscousCapBase244 u b
            ((rho ^ 2 + sigma ^ 2) / 2) +
           thirdFullPhysicalOuterViscousCapSlope244 u b H *
             velocityH3DissipationAt u t) := by
  have hOld := thirdFullPhysical_actualAnnularViscousCost_split244
    hH3 b t rho sigma
  have hBound := thirdFullPhysical_outerKineticViscousBudget_linearBelowCap244
    u b t ((rho ^ 2 + sigma ^ 2) / 2) H hCap
  rw [hOld]
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left hBound
      (pow_nonneg (sq_nonneg rho) 3)) _

/-- Actual highpass kinetic mass. This remains a real physical L2 mass, not
an independently specified Fourier carrier. -/
noncomputable def thirdFullPhysicalActualSharpKineticHighMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t rho : ℝ) : ℝ :=
  ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
    thirdFullPhysicalSharpLowCutoffHilbert244 rho
      (h3AuditInitialOldPhysicalHilbertTotal hH3 t)‖ ^ 2

/-- The prior nonnegative kinetic excess squared, with the exact radial
weight rho^6 and genuine initial kinetic-only lowpass budget. -/
noncomputable def thirdFullPhysicalActualSharpKineticExcessSquare244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b t rho sigma : ℝ) : ℝ :=
  (rho ^ 2) ^ 3 *
    (((rho ^ 2 + sigma ^ 2) / 2) *
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho -
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b))) ^ 2

/-- The amount of physical kinetic excess that cannot be covered by the
annular gap, width, or the baseline (zero-viscosity) outer source cost. -/
noncomputable def thirdFullPhysicalActualAnnularKineticDeficit244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b t rho sigma : ℝ) : ℝ :=
  thirdFullPhysicalActualSharpKineticExcessSquare244 hH3 b t rho sigma -
    thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho *
      (thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 t rho sigma +
        (rho ^ 2) ^ 3 * thirdFullPhysicalOuterViscousCapBase244 u b
          ((rho ^ 2 + sigma ^ 2) / 2))

/-- Under an arbitrary cap, the *unfunded* kinetic excess is bounded by a
LINEAR real physical viscous charge. All annular integrals are actual PDE
objects, and no D(t)^2 appears on the right. -/
theorem thirdFullPhysical_kineticDeficit_linearViscousChargeBelowCap244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (rho sigma : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) (H : ℝ)
    (hCap : velocityH3DissipationAt u t ≤ H)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho) :
    thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b t rho sigma ≤
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho *
        (rho ^ 2) ^ 3 *
        thirdFullPhysicalOuterViscousCapSlope244 u b H *
          velocityH3DissipationAt u t := by
  have hPrev := thirdFullPhysical_kineticExcess_forces_annularViscousCost244
    hH3 hClass b hb rho sigma hRho hOrder t ht hExcess
  have hCost := thirdFullPhysical_actualAnnularViscousCost_linearBelowCap244
    hH3 b t rho sigma H hCap
  have hM : 0 ≤ thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho :=
    sq_nonneg _
  have hTotal := hPrev.trans (mul_le_mul_of_nonneg_left hCost hM)
  let M : ℝ := thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho
  let W : ℝ := (rho ^ 2) ^ 3
  let S : ℝ := thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 t rho sigma
  let B : ℝ := thirdFullPhysicalOuterViscousCapBase244 u b
    ((rho ^ 2 + sigma ^ 2) / 2)
  let L : ℝ := thirdFullPhysicalOuterViscousCapSlope244 u b H
  let D : ℝ := velocityH3DissipationAt u t
  let X : ℝ := thirdFullPhysicalActualSharpKineticExcessSquare244
    hH3 b t rho sigma
  change X ≤ M * (S + W * (B + L * D)) at hTotal
  change X - M * (S + W * B) ≤ M * W * L * D
  nlinarith only [hTotal]

/-- The endpoint-relevant alternative holds at EVERY genuine physical time:
for ANY cap H, either its full H3 dissipation breaches H, or the remaining
kinetic excess must pay the sharp LINEAR viscous charge at that time.
This is NOT a uniform-in-time bound or a disjoint-clock summability theorem. -/
theorem thirdFullPhysical_kineticDeficit_highViscousOrLinearCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (rho sigma : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) (H : ℝ)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho) :
    H < velocityH3DissipationAt u t ∨
      thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b t rho sigma ≤
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho *
          (rho ^ 2) ^ 3 *
          thirdFullPhysicalOuterViscousCapSlope244 u b H *
            velocityH3DissipationAt u t := by
  by_cases hHigh : H < velocityH3DissipationAt u t
  · exact Or.inl hHigh
  · exact Or.inr
      (thirdFullPhysical_kineticDeficit_linearViscousChargeBelowCap244
        hH3 hClass b hb rho sigma hRho hOrder t ht H
        (le_of_not_gt hHigh) hExcess)

/-- If the unfunded physical kinetic excess STRICTLY exceeds the entire
cap-H linear charge at this same time, the real H3 dissipation must exceed H.
This is the contrapositive used to select genuine high-viscous peak times. -/
theorem thirdFullPhysical_kineticDeficit_forces_highViscous244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (rho sigma : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) (H : ℝ)
    (hExcess :
      Real.sqrt (velocityH3Energy0At u b) *
        (3 * thirdFullPhysicalKineticLowBandSourceCeiling244
          rho (velocityH3Energy0At u b)) ≤
      ((rho ^ 2 + sigma ^ 2) / 2) *
        thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho)
    (hUnfunded :
      thirdFullPhysicalActualSharpKineticHighMass244 hH3 t rho *
          (rho ^ 2) ^ 3 *
          thirdFullPhysicalOuterViscousCapSlope244 u b H *
            velocityH3DissipationAt u t <
        thirdFullPhysicalActualAnnularKineticDeficit244 hH3 b t rho sigma) :
    H < velocityH3DissipationAt u t := by
  rcases thirdFullPhysical_kineticDeficit_highViscousOrLinearCharge244
      hH3 hClass b hb rho sigma hRho hOrder t ht H hExcess with
    hSpike | hPaid
  · exact hSpike
  · exact False.elim ((not_lt_of_ge hPaid) hUnfunded)

end
end PrimeTensor.FirstMonomialTriad
