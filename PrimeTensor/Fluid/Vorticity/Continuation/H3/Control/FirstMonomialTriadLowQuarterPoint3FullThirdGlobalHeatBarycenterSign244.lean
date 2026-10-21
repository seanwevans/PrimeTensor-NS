import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGlobalPhaseMiddleCoupling244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Dissipation
import Mathlib.Tactic

/-!
# Signed Fourier heat production as a radial barycenter imbalance

The exact physical normalized concentration source contains a HEAT component
  B_heat = [2 E2 L2 (E0 D3) - E2^2 (L0 D3 + E0 H5)]/(E0 D3)^2.
Write the genuine Fourier moments m0 = E0, m1 = dissipation0, m2 = E2,
m3 = dissipation2, m4 = D3, m5 = fifth velocity mass. The diffusion
identities are L0=-2m1, L2=-2m3, H5=-2m5. Then the numerator factors as

  2m2 [m2(m1 m4 + m0 m5) - 2m0 m3 m4].

Thus the HEAT contribution has no universal sign. A two-band spectral model
with masses x,y at q=1 and q=2 has the signed numerator

  18 x y (x-4y)(x+4y).

It changes sign across x=4y, despite every heat dissipation moment being
nonnegative. These are algebraic two-band test data, NOT an assertion that
Dirac frequency shells themselves are smooth Navier-Stokes solutions. The
physical factorization uses the actual H3 energy-class diffusion pairing.
This rules out a universal monotonicity argument for normalized variance
based on heat dissipation signs alone. It does not rule out a stronger
nonlinear coupled argument or unconditional regularity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1200000

noncomputable local instance axisFintypeH3GlobalHeatBarycenter244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Cubic-polynomial imbalance of the three radial-frequency barycenters.
It controls the SIGN of pure heat production in normalized H3 variance. -/
noncomputable def h3GlobalRadialHeatBarycenterImbalance244
    (m0 m1 m2 m3 m4 m5 : ℝ) : ℝ :=
  m2 * (m1 * m4 + m0 * m5) - 2 * m0 * m3 * m4

/-- Exact six-moment factorization of signed normalized heat production. -/
theorem h3_radialHeat_numerator_eq_barycenterImbalance244
    (m0 m1 m2 m3 m4 m5 : ℝ) :
    2 * m2 * (-2 * m3) * (m0 * m4) -
      m2 ^ 2 * ((-2 * m1) * m4 + m0 * (-2 * m5)) =
      2 * m2 *
        h3GlobalRadialHeatBarycenterImbalance244 m0 m1 m2 m3 m4 m5 := by
  unfold h3GlobalRadialHeatBarycenterImbalance244
  ring

/-- The physical heat contribution is exactly the radial-moment barycenter
imbalance. In particular, its sign cannot be inferred merely from L0,L2,H5
being nonpositive: the three different frequency weights interact. -/
theorem h3Path_globalDiffusionNormalizedRate_eq_barycenterImbalance244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierGlobalDiffusionNormalizedRate244 hH3 hClass t ht =
      (2 * velocityH3Energy2At u t *
        h3GlobalRadialHeatBarycenterImbalance244
          (velocityH3Energy0At u t)
          (velocityH3Dissipation0At u t)
          (velocityH3Energy2At u t)
          (velocityH3Dissipation2At u t)
          (h3TerminalPhysicalTopDissipation3Path hClass t)
          (h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht)) /
        (velocityH3Energy0At u t *
          h3TerminalPhysicalTopDissipation3Path hClass t) ^ 2 := by
  have hIBP : H3DiffusionIntegrationByPartsAt u t :=
    h3PathEnergyClassProducesDiffusionIntegrationByParts_closed
      u T hH3 a hClass t ht
  have hL0 :=
    velocityH3DiffusionDerivative0At_eq_neg_two_mul_dissipation0 hIBP
  have hL2 :=
    velocityH3DiffusionDerivative2At_eq_neg_two_mul_dissipation2 hIBP
  have hHeat := h3Path_globalHeatRate_eq_negTwoFifthMass244
    hH3 hClass ht
  unfold h3PathTopFourierGlobalDiffusionNormalizedRate244
    h3PathTopFourierGlobalDiffusionExcess244
    h3GlobalRadialHeatBarycenterImbalance244
  dsimp only
  rw [hL0, hL2, hHeat]
  ring

/-- For the genuine physical PDE heat term, a nonnegative barycenter
imbalance produces nonnegative normalized spectral concentration. -/
theorem h3Path_globalDiffusionNormalizedRate_nonneg_of_barycenter244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hImbalance : 0 ≤ h3GlobalRadialHeatBarycenterImbalance244
      (velocityH3Energy0At u t) (velocityH3Dissipation0At u t)
      (velocityH3Energy2At u t) (velocityH3Dissipation2At u t)
      (h3TerminalPhysicalTopDissipation3Path hClass t)
      (h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht)) :
    0 ≤ h3PathTopFourierGlobalDiffusionNormalizedRate244
      hH3 hClass t ht := by
  rw [h3Path_globalDiffusionNormalizedRate_eq_barycenterImbalance244
    hH3 hClass ht]
  have hE2 := velocityH3Energy2At_nonneg u t
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hE2) hImbalance)
    (sq_nonneg _)

/-- The opposite barycenter sign forces nonpositive normalized HEAT
production. Neither sign is automatic for a general physical spectral state. -/
theorem h3Path_globalDiffusionNormalizedRate_nonpos_of_barycenter244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hImbalance : h3GlobalRadialHeatBarycenterImbalance244
      (velocityH3Energy0At u t) (velocityH3Dissipation0At u t)
      (velocityH3Energy2At u t) (velocityH3Dissipation2At u t)
      (h3TerminalPhysicalTopDissipation3Path hClass t)
      (h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht) ≤ 0) :
    h3PathTopFourierGlobalDiffusionNormalizedRate244
      hH3 hClass t ht ≤ 0 := by
  rw [h3Path_globalDiffusionNormalizedRate_eq_barycenterImbalance244
    hH3 hClass ht]
  have hE2 := velocityH3Energy2At_nonneg u t
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by norm_num) hE2) hImbalance)
    (sq_nonneg _)

/-- Algebraic two-band spectral heat model, at radial weights q=1 and q=2,
with nonnegative masses x and y. These are moment values, not Dirac-state
claims about an actual physical H3 solution. -/
noncomputable def h3TwoBandHeatNormalizedRate244 (x y : ℝ) : ℝ :=
  (2 * (x + 4 * y) * (-2 * (x + 8 * y)) *
      ((x + y) * (x + 16 * y)) -
    (x + 4 * y) ^ 2 *
      ((-2 * (x + 2 * y)) * (x + 16 * y) +
        (x + y) * (-2 * (x + 32 * y)))) /
    ((x + y) * (x + 16 * y)) ^ 2

/-- The two-band radial barycenter imbalance changes sign exactly at x=4y. -/
theorem h3_twoBandHeat_barycenterImbalance_factor244 (x y : ℝ) :
    h3GlobalRadialHeatBarycenterImbalance244
        (x + y) (x + 2 * y) (x + 4 * y)
        (x + 8 * y) (x + 16 * y) (x + 32 * y) =
      9 * x * y * (x - 4 * y) := by
  unfold h3GlobalRadialHeatBarycenterImbalance244
  ring

/-- Closed-form signed normalized heat production for two spectral bands. -/
theorem h3_twoBandHeat_normalizedRate_eq_factor244 (x y : ℝ) :
    h3TwoBandHeatNormalizedRate244 x y =
      18 * x * y * (x - 4 * y) * (x + 4 * y) /
        ((x + y) * (x + 16 * y)) ^ 2 := by
  unfold h3TwoBandHeatNormalizedRate244
  ring

/-- Heat can produce POSITIVE normalized concentration: q=1 has mass 8,
q=2 has mass 1. The exact signed source is 4/27. -/
theorem h3_twoBandHeat_normalizedRate_positive_example244 :
    h3TwoBandHeatNormalizedRate244 (8 : ℝ) (1 : ℝ) = 4 / 27 := by
  norm_num [h3TwoBandHeatNormalizedRate244]

/-- Heat can produce NEGATIVE normalized concentration: equal band masses
at q=1 and q=2. The exact signed source is -135/578. -/
theorem h3_twoBandHeat_normalizedRate_negative_example244 :
    h3TwoBandHeatNormalizedRate244 (1 : ℝ) (1 : ℝ) = -135 / 578 := by
  norm_num [h3TwoBandHeatNormalizedRate244]

/-- The normalized heat production crosses zero at x=4y. -/
theorem h3_twoBandHeat_normalizedRate_zero_example244 :
    h3TwoBandHeatNormalizedRate244 (4 : ℝ) (1 : ℝ) = 0 := by
  norm_num [h3TwoBandHeatNormalizedRate244]

end
end PrimeTensor.FirstMonomialTriad
