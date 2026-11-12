import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularYoungWidthTemporalContinuity
import Mathlib.Tactic

/-!
# Cutoff-uniform nonlinear Young-residual modulus on a bounded frequency band

For all 0 <= rho <= sigma <= R, the sharp annulus and the exact
sqrt(q^3) multiplier act on the *same* quotient Fourier L² space with
operator norm <= 2 R^3. Combining this with the actual quadratic Leray
forcing difference estimate gives a single modulus independent of the
chosen annular radii. Squared Young masses inherit a corresponding
cutoff-uniform variation estimate.

This is the nonlinear contribution to a common temporal modulus for bounded
annular families. It does not assert cutoff-uniformity as R tends to infinity,
or control of the velocity-width part of the exact Young functional.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeAnnularUniformYoung244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceAnnularUniformYoung244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- No frequency support hypothesis is required for the two-projection
annular estimate; the factor two is independent of both radii. -/
theorem thirdFullKinetic_sharpAnnulus_norm_le_two244
    (rho sigma : ℝ) (F : H3FourierComplexL2) :
    ‖h3CriticalFourierSharpLowCutoffCLM sigma F -
      h3CriticalFourierSharpLowCutoffCLM rho F‖ ≤ 2 * ‖F‖ := by
  calc
    ‖h3CriticalFourierSharpLowCutoffCLM sigma F -
      h3CriticalFourierSharpLowCutoffCLM rho F‖ ≤
        ‖h3CriticalFourierSharpLowCutoffCLM sigma F‖ +
          ‖h3CriticalFourierSharpLowCutoffCLM rho F‖ := norm_sub_le _ _
    _ ≤ ‖F‖ + ‖F‖ := add_le_add
      (h3Critical_fourierSharpLowCutoffApply_norm_le sigma F)
      (h3Critical_fourierSharpLowCutoffApply_norm_le rho F)
    _ = 2 * ‖F‖ := by ring

/-- Frequency projection of a difference is the difference of projections,
for the actual Fourier L² equivalence classes. -/
theorem thirdFullKinetic_sharpAnnulus_sub244
    (rho sigma : ℝ) (F G : H3FourierComplexL2) :
    (h3CriticalFourierSharpLowCutoffCLM sigma F -
      h3CriticalFourierSharpLowCutoffCLM rho F) -
      (h3CriticalFourierSharpLowCutoffCLM sigma G -
        h3CriticalFourierSharpLowCutoffCLM rho G) =
    h3CriticalFourierSharpLowCutoffCLM sigma (F - G) -
      h3CriticalFourierSharpLowCutoffCLM rho (F - G) := by
  rw [map_sub, map_sub]
  abel

/-- The same annular Fourier cutoff is 2-Lipschitz, uniformly in radii. -/
theorem thirdFullKinetic_sharpAnnulus_sub_norm_le_two244
    (rho sigma : ℝ) (F G : H3FourierComplexL2) :
    ‖(h3CriticalFourierSharpLowCutoffCLM sigma F -
        h3CriticalFourierSharpLowCutoffCLM rho F) -
      (h3CriticalFourierSharpLowCutoffCLM sigma G -
        h3CriticalFourierSharpLowCutoffCLM rho G)‖ ≤
      2 * ‖F - G‖ := by
  rw [thirdFullKinetic_sharpAnnulus_sub244]
  exact thirdFullKinetic_sharpAnnulus_norm_le_two244 rho sigma (F - G)

/-- The *actual* finite-band cubic Young multiplier composed with a sharp
annulus: a quotient-L² operator, not a pointwise substitute. -/
noncomputable def thirdFullKineticCubicAnnulusApply244
    (rho sigma : ℝ) (hSigma : 0 ≤ sigma)
    (F : H3FourierComplexL2) : H3FourierComplexL2 :=
  thirdFullKineticFiniteCubicRootMultiplierCLM244 sigma hSigma
    (h3CriticalFourierSharpLowCutoffCLM sigma F -
      h3CriticalFourierSharpLowCutoffCLM rho F)

/-- All annuli inside a single finite ball have the *same* cubic multiplier
operator bound. No bound on the lower radius appears in the estimate. -/
theorem thirdFullKinetic_cubicAnnulusApply_norm_le_uniform244
    (rho sigma R : ℝ) (hSigma : 0 ≤ sigma) (hR : sigma ≤ R)
    (F : H3FourierComplexL2) :
    ‖thirdFullKineticCubicAnnulusApply244 rho sigma hSigma F‖ ≤
      (2 * R ^ 3) * ‖F‖ := by
  have hPow : sigma ^ 3 ≤ R ^ 3 :=
    pow_le_pow_left₀ hSigma hR 3
  have hRoot :
      ‖thirdFullKineticCubicAnnulusApply244 rho sigma hSigma F‖ ≤
        sigma ^ 3 *
          ‖h3CriticalFourierSharpLowCutoffCLM sigma F -
            h3CriticalFourierSharpLowCutoffCLM rho F‖ := by
    change ‖thirdFullKineticFiniteCubicRootMultiplierCLM244 sigma hSigma
      (h3CriticalFourierSharpLowCutoffCLM sigma F -
        h3CriticalFourierSharpLowCutoffCLM rho F)‖ ≤ _
    rw [thirdFullKinetic_finiteCubicRootMultiplierCLM_apply244]
    exact thirdFullKinetic_finiteCubicRootMultiplier_norm_le244 sigma hSigma _
  calc
    ‖thirdFullKineticCubicAnnulusApply244 rho sigma hSigma F‖ ≤
      sigma ^ 3 *
        ‖h3CriticalFourierSharpLowCutoffCLM sigma F -
          h3CriticalFourierSharpLowCutoffCLM rho F‖ := hRoot
    _ ≤ sigma ^ 3 * (2 * ‖F‖) :=
      mul_le_mul_of_nonneg_left
        (thirdFullKinetic_sharpAnnulus_norm_le_two244 rho sigma F)
        (pow_nonneg hSigma 3)
    _ = (2 * sigma ^ 3) * ‖F‖ := by ring
    _ ≤ (2 * R ^ 3) * ‖F‖ := by
      exact mul_le_mul_of_nonneg_right
        (by linarith only [hPow] : 2 * sigma ^ 3 ≤ 2 * R ^ 3)
        (norm_nonneg _)

/-- Exact linearity under differences; this prevents a spurious extra
nonlinear term when comparing two times. -/
theorem thirdFullKinetic_cubicAnnulusApply_sub244
    (rho sigma : ℝ) (hSigma : 0 ≤ sigma)
    (F G : H3FourierComplexL2) :
    thirdFullKineticCubicAnnulusApply244 rho sigma hSigma F -
      thirdFullKineticCubicAnnulusApply244 rho sigma hSigma G =
    thirdFullKineticCubicAnnulusApply244 rho sigma hSigma (F - G) := by
  unfold thirdFullKineticCubicAnnulusApply244
  rw [← map_sub]
  rw [thirdFullKinetic_sharpAnnulus_sub244]

/-- Fixed finite upper frequency gives a cutoff-uniform L² modulus in
both the input and the lower-frequency annular radius. -/
theorem thirdFullKinetic_cubicAnnulusApply_sub_norm_le_uniform244
    (rho sigma R : ℝ) (hSigma : 0 ≤ sigma) (hR : sigma ≤ R)
    (F G : H3FourierComplexL2) :
    ‖thirdFullKineticCubicAnnulusApply244 rho sigma hSigma F -
      thirdFullKineticCubicAnnulusApply244 rho sigma hSigma G‖ ≤
      (2 * R ^ 3) * ‖F - G‖ := by
  rw [thirdFullKinetic_cubicAnnulusApply_sub244]
  exact thirdFullKinetic_cubicAnnulusApply_norm_le_uniform244
    rho sigma R hSigma hR (F - G)

/-- Quantitative cutoff-uniform estimate for the TRUE quadratic Leray
residual and anti-heat Laplacian, not an arbitrary continuous surrogate.
This is a single bound for every rho <= sigma <= R. -/
theorem thirdFullPhysical_annularYoungResidual_uniformBandDifference244
    (rho sigma R : ℝ) (hSigma : 0 ≤ sigma) (hR : sigma ≤ R)
    (U V : H3SpectralVelocityState) (j : Fin 3) :
    ‖thirdFullKineticCubicAnnulusApply244 rho sigma hSigma
        (thirdFullPhysicalAnnularYoungResidualFourierL2244 U j) -
      thirdFullKineticCubicAnnulusApply244 rho sigma hSigma
        (thirdFullPhysicalAnnularYoungResidualFourierL2244 V j)‖ ≤
      ((2 * R ^ 3) *
        ((576 * Real.pi * h3SobolevDeweightingConstant) *
          (‖U‖ + ‖V‖) + 2)) * ‖U - V‖ := by
  have hTwo : 0 ≤ 2 * R ^ 3 := by
    have hRNonneg : 0 ≤ R := hSigma.trans hR
    positivity
  calc
    ‖thirdFullKineticCubicAnnulusApply244 rho sigma hSigma
        (thirdFullPhysicalAnnularYoungResidualFourierL2244 U j) -
      thirdFullKineticCubicAnnulusApply244 rho sigma hSigma
        (thirdFullPhysicalAnnularYoungResidualFourierL2244 V j)‖ ≤
      (2 * R ^ 3) *
        ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j -
          thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖ :=
            thirdFullKinetic_cubicAnnulusApply_sub_norm_le_uniform244
              rho sigma R hSigma hR _ _
    _ ≤ (2 * R ^ 3) *
        (((576 * Real.pi * h3SobolevDeweightingConstant) *
          (‖U‖ + ‖V‖) + 2) * ‖U - V‖) :=
            mul_le_mul_of_nonneg_left
              (thirdFullPhysical_annularYoungResidualFourier_sub_norm_le244 U V j)
              hTwo
    _ = ((2 * R ^ 3) *
          ((576 * Real.pi * h3SobolevDeweightingConstant) *
            (‖U‖ + ‖V‖) + 2)) * ‖U - V‖ := by ring

/-- The norm-square estimate used to transport cubic Young charge between
actual spectral states. -/
theorem thirdFullKinetic_fourierNormSquare_difference_le244
    (F G : H3FourierComplexL2) :
    |‖F‖ ^ 2 - ‖G‖ ^ 2| ≤
      ‖F - G‖ * (‖F‖ + ‖G‖) := by
  have hPositive : 0 ≤ ‖F‖ + ‖G‖ :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    |‖F‖ ^ 2 - ‖G‖ ^ 2| =
        |‖F‖ - ‖G‖| * (‖F‖ + ‖G‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg hPositive]
      ac_rfl
    _ ≤ ‖F - G‖ * (‖F‖ + ‖G‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le F G) hPositive

/-- The *squared* cubic Young residual is cutoff-uniformly locally
Lipschitz in the actual H³ spectral state on every bounded frequency ball.
No separate time measurability assumption, viscosity term, or H⁶ bound. -/
theorem thirdFullPhysical_annularYoungResidual_uniformSquareDifference244
    (rho sigma R : ℝ) (hSigma : 0 ≤ sigma) (hR : sigma ≤ R)
    (U V : H3SpectralVelocityState) (j : Fin 3) :
    |‖thirdFullKineticCubicAnnulusApply244 rho sigma hSigma
         (thirdFullPhysicalAnnularYoungResidualFourierL2244 U j)‖ ^ 2 -
      ‖thirdFullKineticCubicAnnulusApply244 rho sigma hSigma
         (thirdFullPhysicalAnnularYoungResidualFourierL2244 V j)‖ ^ 2| ≤
      ((4 * R ^ 6) *
          (‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖ +
           ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖) *
          ((576 * Real.pi * h3SobolevDeweightingConstant) *
            (‖U‖ + ‖V‖) + 2)) * ‖U - V‖ := by
  let F := thirdFullPhysicalAnnularYoungResidualFourierL2244 U j
  let G := thirdFullPhysicalAnnularYoungResidualFourierL2244 V j
  let A := thirdFullKineticCubicAnnulusApply244 rho sigma hSigma
  let C : ℝ :=
    (576 * Real.pi * h3SobolevDeweightingConstant) *
      (‖U‖ + ‖V‖) + 2
  have hRnonneg : 0 ≤ R := hSigma.trans hR
  have hF := thirdFullKinetic_cubicAnnulusApply_norm_le_uniform244
    rho sigma R hSigma hR F
  have hG := thirdFullKinetic_cubicAnnulusApply_norm_le_uniform244
    rho sigma R hSigma hR G
  have hDiff := thirdFullPhysical_annularYoungResidual_uniformBandDifference244
    rho sigma R hSigma hR U V j
  change ‖A F‖ ≤ (2 * R ^ 3) * ‖F‖ at hF
  change ‖A G‖ ≤ (2 * R ^ 3) * ‖G‖ at hG
  change ‖A F - A G‖ ≤ ((2 * R ^ 3) * C) * ‖U - V‖ at hDiff
  have hSum : ‖A F‖ + ‖A G‖ ≤
      (2 * R ^ 3) * (‖F‖ + ‖G‖) := by
    nlinarith only [hF, hG]
  have hSumNonneg : 0 ≤ (2 * R ^ 3) * (‖F‖ + ‖G‖) := by
    positivity
  change |‖A F‖ ^ 2 - ‖A G‖ ^ 2| ≤
    ((4 * R ^ 6) * (‖F‖ + ‖G‖) * C) * ‖U - V‖
  calc
    |‖A F‖ ^ 2 - ‖A G‖ ^ 2| ≤
        ‖A F - A G‖ * (‖A F‖ + ‖A G‖) :=
      thirdFullKinetic_fourierNormSquare_difference_le244 _ _
    _ ≤ ‖A F - A G‖ *
        ((2 * R ^ 3) * (‖F‖ + ‖G‖)) :=
      mul_le_mul_of_nonneg_left hSum (norm_nonneg _)
    _ ≤ (((2 * R ^ 3) * C) * ‖U - V‖) *
        ((2 * R ^ 3) * (‖F‖ + ‖G‖)) :=
      mul_le_mul_of_nonneg_right hDiff hSumNonneg
    _ = ((4 * R ^ 6) * (‖F‖ + ‖G‖) * C) * ‖U - V‖ := by ring

/-- The same radius-independent stability bound applies *directly* to the
actual preterminal physical times; the underlying state is the genuine
spectral velocity path. -/
theorem thirdFullPhysical_actualAnnularYoung_uniformSquareTwoTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (rho sigma R s t : ℝ) (hSigma : 0 ≤ sigma) (hR : sigma ≤ R)
    (j : Fin 3) :
    let U := h3AuditActualSpectralVelocityTotal hH3 s
    let V := h3AuditActualSpectralVelocityTotal hH3 t
    |‖thirdFullKineticCubicAnnulusApply244 rho sigma hSigma
         (thirdFullPhysicalAnnularYoungResidualFourierL2244 U j)‖ ^ 2 -
      ‖thirdFullKineticCubicAnnulusApply244 rho sigma hSigma
         (thirdFullPhysicalAnnularYoungResidualFourierL2244 V j)‖ ^ 2| ≤
      ((4 * R ^ 6) *
          (‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖ +
           ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖) *
          ((576 * Real.pi * h3SobolevDeweightingConstant) *
            (‖U‖ + ‖V‖) + 2)) * ‖U - V‖ := by
  exact thirdFullPhysical_annularYoungResidual_uniformSquareDifference244
    rho sigma R hSigma hR _ _ j

end
end PrimeTensor.FirstMonomialTriad
