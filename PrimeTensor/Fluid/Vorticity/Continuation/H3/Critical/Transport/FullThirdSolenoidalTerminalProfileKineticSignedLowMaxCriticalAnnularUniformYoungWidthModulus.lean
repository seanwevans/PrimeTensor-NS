import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularUniformYoungModulus
import Mathlib.Tactic

/-!
# Common finite-radius modulus for the complete actual annular Young-width cost

The preceding result bounded the cubic-weighted nonlinear Leray residual,
uniformly over all annuli inside one fixed frequency ball. Here the other
piece of the ORIGINAL Young-width functional is included: its radial-width
coefficient and three squared raw-velocity Fourier band masses.

For 0 <= rho <= sigma <= R, the width coefficient is at most 2 R^10.
The raw velocity annular difference has norm at most twice the H3 spectral
increment. Combining squared-norm variation, the existing cubic Young
modulus, and a finite coordinate sum yields a single explicit modulus for
the complete original functional, with no radius-dependent constants apart
from R. The same bound holds between arbitrary two actual physical times.

This does NOT furnish a modulus uniform as R tends to infinity or by itself
force positive cofinal annular window lengths.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeAnnularUniformWidth244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceAnnularUniformWidth244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The exact annular raw-velocity Fourier class appearing in the width
cost. This is the quotient L2 class, not a choice of representatives. -/
noncomputable def thirdFullPhysicalAnnularRawVelocityBand244
    (rho sigma : ℝ) (U : H3SpectralVelocityState) (j : Fin 3) :
    H3FourierComplexL2 :=
  h3CriticalFourierSharpLowCutoffCLM sigma
      (h3SpectralScalarRawFourierL2 (U j)) -
    h3CriticalFourierSharpLowCutoffCLM rho
      (h3SpectralScalarRawFourierL2 (U j))

/-- The native H3 state bounds the raw annular Fourier L2 mass, uniformly
in both radius parameters. -/
theorem thirdFullPhysical_annularRawVelocityBand_norm_le_two244
    (rho sigma : ℝ) (U : H3SpectralVelocityState) (j : Fin 3) :
    ‖thirdFullPhysicalAnnularRawVelocityBand244 rho sigma U j‖ ≤
      2 * ‖U‖ := by
  calc
    ‖thirdFullPhysicalAnnularRawVelocityBand244 rho sigma U j‖ ≤
        2 * ‖h3SpectralScalarRawFourierL2 (U j)‖ :=
      thirdFullKinetic_sharpAnnulus_norm_le_two244 rho sigma _
    _ ≤ 2 * ‖U j‖ :=
      mul_le_mul_of_nonneg_left
        (norm_h3SpectralScalarRawFourierL2_le (U j)) (by norm_num)
    _ ≤ 2 * ‖U‖ :=
      mul_le_mul_of_nonneg_left
        (h3SpectralVelocity_coordinate_norm_le U j) (by norm_num)

/-- Difference of real velocity spectra is represented by the exact
annular projection of the Fourier difference. -/
theorem thirdFullPhysical_annularRawVelocityBand_sub244
    (rho sigma : ℝ) (U V : H3SpectralVelocityState) (j : Fin 3) :
    thirdFullPhysicalAnnularRawVelocityBand244 rho sigma U j -
      thirdFullPhysicalAnnularRawVelocityBand244 rho sigma V j =
    h3CriticalFourierSharpLowCutoffCLM sigma
      (h3SpectralScalarRawFourierL2 (U j - V j)) -
    h3CriticalFourierSharpLowCutoffCLM rho
      (h3SpectralScalarRawFourierL2 (U j - V j)) := by
  unfold thirdFullPhysicalAnnularRawVelocityBand244
  rw [thirdFullKinetic_sharpAnnulus_sub244]
  rw [h3SpectralScalarRawFourierL2_sub]

/-- The raw-velocity annular state is uniformly two-Lipschitz in the
weighted H3 velocity, regardless of the annular radii. -/
theorem thirdFullPhysical_annularRawVelocityBand_sub_norm_le_two244
    (rho sigma : ℝ) (U V : H3SpectralVelocityState) (j : Fin 3) :
    ‖thirdFullPhysicalAnnularRawVelocityBand244 rho sigma U j -
      thirdFullPhysicalAnnularRawVelocityBand244 rho sigma V j‖ ≤
      2 * ‖U - V‖ := by
  rw [thirdFullPhysical_annularRawVelocityBand_sub244]
  calc
    ‖h3CriticalFourierSharpLowCutoffCLM sigma
        (h3SpectralScalarRawFourierL2 (U j - V j)) -
      h3CriticalFourierSharpLowCutoffCLM rho
        (h3SpectralScalarRawFourierL2 (U j - V j))‖ ≤
      2 * ‖h3SpectralScalarRawFourierL2 (U j - V j)‖ :=
        thirdFullKinetic_sharpAnnulus_norm_le_two244 rho sigma _
    _ ≤ 2 * ‖U j - V j‖ :=
      mul_le_mul_of_nonneg_left
        (norm_h3SpectralScalarRawFourierL2_le (U j - V j)) (by norm_num)
    _ ≤ 2 * ‖U - V‖ := by
      have hCoord : ‖U j - V j‖ ≤ ‖U - V‖ := by
        simpa only [Pi.sub_apply] using (norm_le_pi_norm (U - V) j)
      exact mul_le_mul_of_nonneg_left hCoord (by norm_num)

/-- The actual squared raw-velocity annular Fourier mass has a sharp
radius-independent quadratic variation bound (with factor four from two
cutoffs). -/
theorem thirdFullPhysical_annularRawVelocityBandSquare_sub_le244
    (rho sigma : ℝ) (U V : H3SpectralVelocityState) (j : Fin 3) :
    |‖thirdFullPhysicalAnnularRawVelocityBand244 rho sigma U j‖ ^ 2 -
      ‖thirdFullPhysicalAnnularRawVelocityBand244 rho sigma V j‖ ^ 2| ≤
      (4 * (‖U‖ + ‖V‖)) * ‖U - V‖ := by
  let A : H3FourierComplexL2 :=
    thirdFullPhysicalAnnularRawVelocityBand244 rho sigma U j
  let B : H3FourierComplexL2 :=
    thirdFullPhysicalAnnularRawVelocityBand244 rho sigma V j
  have hA : ‖A‖ ≤ 2 * ‖U‖ :=
    thirdFullPhysical_annularRawVelocityBand_norm_le_two244 rho sigma U j
  have hB : ‖B‖ ≤ 2 * ‖V‖ :=
    thirdFullPhysical_annularRawVelocityBand_norm_le_two244 rho sigma V j
  have hDiff : ‖A - B‖ ≤ 2 * ‖U - V‖ :=
    thirdFullPhysical_annularRawVelocityBand_sub_norm_le_two244 rho sigma U V j
  have hSum : ‖A‖ + ‖B‖ ≤ 2 * (‖U‖ + ‖V‖) := by
    linarith only [hA, hB]
  have hBoundNonneg : 0 ≤ 2 * (‖U‖ + ‖V‖) := by positivity
  calc
    |‖A‖ ^ 2 - ‖B‖ ^ 2| ≤
        ‖A - B‖ * (‖A‖ + ‖B‖) :=
          thirdFullKinetic_fourierNormSquare_difference_le244 A B
    _ ≤ ‖A - B‖ * (2 * (‖U‖ + ‖V‖)) :=
      mul_le_mul_of_nonneg_left hSum (norm_nonneg _)
    _ ≤ (2 * ‖U - V‖) * (2 * (‖U‖ + ‖V‖)) :=
      mul_le_mul_of_nonneg_right hDiff hBoundNonneg
    _ = (4 * (‖U‖ + ‖V‖)) * ‖U - V‖ := by ring

/-- The ORIGINAL velocity-width multiplier, with unchanged PDE constants. -/
noncomputable def thirdFullPhysicalAnnularWidthFactor244
    (rho sigma : ℝ) : ℝ :=
  2 * (sigma ^ 2) ^ 3 * ((sigma ^ 2 - rho ^ 2) / 2) ^ 2

/-- One finite upper frequency controls the exact width multiplier on
EVERY annulus inside the ball: 0 <= width <= 2 R^10. -/
theorem thirdFullPhysical_annularWidthFactor_bound244
    (rho sigma R : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma)
    (hUpper : sigma ≤ R) :
    0 ≤ thirdFullPhysicalAnnularWidthFactor244 rho sigma ∧
      thirdFullPhysicalAnnularWidthFactor244 rho sigma ≤ 2 * R ^ 10 := by
  have hSigma : 0 ≤ sigma := hRho.trans hOrder
  have hSigmaSq : rho ^ 2 ≤ sigma ^ 2 :=
    pow_le_pow_left₀ hRho hOrder 2
  have hUpperSq : sigma ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ hSigma hUpper 2
  have hGapNonneg : 0 ≤ (sigma ^ 2 - rho ^ 2) / 2 := by
    linarith only [hSigmaSq]
  have hGapUpper : (sigma ^ 2 - rho ^ 2) / 2 ≤ R ^ 2 := by
    linarith only [hUpperSq, sq_nonneg rho, sq_nonneg R]
  have hCube : (sigma ^ 2) ^ 3 ≤ (R ^ 2) ^ 3 :=
    pow_le_pow_left₀ (sq_nonneg sigma) hUpperSq 3
  have hSquare : ((sigma ^ 2 - rho ^ 2) / 2) ^ 2 ≤
      (R ^ 2) ^ 2 :=
    pow_le_pow_left₀ hGapNonneg hGapUpper 2
  constructor
  · change 0 ≤ 2 * (sigma ^ 2) ^ 3 *
      ((sigma ^ 2 - rho ^ 2) / 2) ^ 2
    positivity
  · change 2 * (sigma ^ 2) ^ 3 *
      ((sigma ^ 2 - rho ^ 2) / 2) ^ 2 ≤ 2 * R ^ 10
    calc
      2 * (sigma ^ 2) ^ 3 * ((sigma ^ 2 - rho ^ 2) / 2) ^ 2 ≤
        2 * (R ^ 2) ^ 3 * ((sigma ^ 2 - rho ^ 2) / 2) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hCube (by norm_num))
            (sq_nonneg _)
      _ ≤ 2 * (R ^ 2) ^ 3 * (R ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hSquare (by positivity)
      _ = 2 * R ^ 10 := by ring

/-- Single coefficient for the COMPLETE Young-gap plus width functional.
It is independent of rho and sigma as long as they stay below R. -/
noncomputable def thirdFullPhysicalAnnularFullYoungWidthModulus244
    (R : ℝ) (U V : H3SpectralVelocityState) : ℝ :=
  ∑ j : Fin 3,
    ((8 * R ^ 6) *
      (‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖ +
       ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖) *
      ((576 * Real.pi * h3SobolevDeweightingConstant) *
        (‖U‖ + ‖V‖) + 2) +
      (8 * R ^ 10) * (‖U‖ + ‖V‖))

/-- The common coefficient is nonnegative on nonnegative finite radii. -/
theorem thirdFullPhysical_annularFullYoungWidthModulus_nonneg244
    (R : ℝ) (hR : 0 ≤ R) (U V : H3SpectralVelocityState) :
    0 ≤ thirdFullPhysicalAnnularFullYoungWidthModulus244 R U V := by
  unfold thirdFullPhysicalAnnularFullYoungWidthModulus244
  apply Finset.sum_nonneg
  intro j _
  have hC : 0 ≤
      (576 * Real.pi * h3SobolevDeweightingConstant) *
        (‖U‖ + ‖V‖) + 2 := by
    positivity [h3SobolevDeweightingConstant_nonneg]
  positivity

/-- A UNIFORM difference estimate for the COMPLETE original Hilbert Young
functional. Both the genuine cubic Leray term and the physical width term
are included, with no dependence on the annular radii beyond R. -/
theorem thirdFullPhysical_annularYoungWidthHilbert_uniformDifference244
    (rho sigma R : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma)
    (hUpper : sigma ≤ R) (U V : H3SpectralVelocityState) :
    |thirdFullPhysicalAnnularYoungWidthHilbertCost244 rho sigma
        (hRho.trans hOrder) U -
      thirdFullPhysicalAnnularYoungWidthHilbertCost244 rho sigma
        (hRho.trans hOrder) V| ≤
      thirdFullPhysicalAnnularFullYoungWidthModulus244 R U V * ‖U - V‖ := by
  let hSigma : 0 ≤ sigma := hRho.trans hOrder
  let K : ℝ := thirdFullPhysicalAnnularWidthFactor244 rho sigma
  let A : H3SpectralVelocityState → Fin 3 → H3FourierComplexL2 :=
    fun Z j => thirdFullKineticCubicAnnulusApply244 rho sigma hSigma
      (thirdFullPhysicalAnnularYoungResidualFourierL2244 Z j)
  let B : H3SpectralVelocityState → Fin 3 → H3FourierComplexL2 :=
    fun Z j => thirdFullPhysicalAnnularRawVelocityBand244 rho sigma Z j
  let C : ℝ :=
    (576 * Real.pi * h3SobolevDeweightingConstant) *
      (‖U‖ + ‖V‖) + 2
  let d : ℝ := ‖U - V‖
  have hK : 0 ≤ K ∧ K ≤ 2 * R ^ 10 :=
    thirdFullPhysical_annularWidthFactor_bound244
      rho sigma R hRho hOrder hUpper
  have hDecomp (Z : H3SpectralVelocityState) :
      thirdFullPhysicalAnnularYoungWidthHilbertCost244 rho sigma hSigma Z =
        ∑ j : Fin 3, (2 * ‖A Z j‖ ^ 2 + K * ‖B Z j‖ ^ 2) := by
    change 2 * (∑ j : Fin 3, ‖A Z j‖ ^ 2) +
        K * (∑ j : Fin 3, ‖B Z j‖ ^ 2) =
      ∑ j : Fin 3, (2 * ‖A Z j‖ ^ 2 + K * ‖B Z j‖ ^ 2)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hSingle (j : Fin 3) :
      |(2 * ‖A U j‖ ^ 2 + K * ‖B U j‖ ^ 2) -
        (2 * ‖A V j‖ ^ 2 + K * ‖B V j‖ ^ 2)| ≤
      (((8 * R ^ 6) *
        (‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖ +
         ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖) * C) +
        (8 * R ^ 10) * (‖U‖ + ‖V‖)) * d := by
    have hYoung :=
      thirdFullPhysical_annularYoungResidual_uniformSquareDifference244
        rho sigma R hSigma hUpper U V j
    change |‖A U j‖ ^ 2 - ‖A V j‖ ^ 2| ≤
      ((4 * R ^ 6) *
        (‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖ +
         ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖) * C) * d
      at hYoung
    have hWidth :=
      thirdFullPhysical_annularRawVelocityBandSquare_sub_le244 rho sigma U V j
    change |‖B U j‖ ^ 2 - ‖B V j‖ ^ 2| ≤
      (4 * (‖U‖ + ‖V‖)) * d at hWidth
    have hYoung2 :
        2 * |‖A U j‖ ^ 2 - ‖A V j‖ ^ 2| ≤
        ((8 * R ^ 6) *
          (‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖ +
           ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖) * C) * d := by
      calc
        2 * |‖A U j‖ ^ 2 - ‖A V j‖ ^ 2| ≤
            2 * (((4 * R ^ 6) *
              (‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖ +
               ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖) * C) * d) :=
          mul_le_mul_of_nonneg_left hYoung (by norm_num)
        _ = _ := by ring
    have hWidthK :
        K * |‖B U j‖ ^ 2 - ‖B V j‖ ^ 2| ≤
        ((8 * R ^ 10) * (‖U‖ + ‖V‖)) * d := by
      calc
        K * |‖B U j‖ ^ 2 - ‖B V j‖ ^ 2| ≤
            K * ((4 * (‖U‖ + ‖V‖)) * d) :=
          mul_le_mul_of_nonneg_left hWidth hK.1
        _ ≤ (2 * R ^ 10) * ((4 * (‖U‖ + ‖V‖)) * d) :=
          mul_le_mul_of_nonneg_right hK.2 (by positivity)
        _ = _ := by ring
    have hRewrite :
        (2 * ‖A U j‖ ^ 2 + K * ‖B U j‖ ^ 2) -
          (2 * ‖A V j‖ ^ 2 + K * ‖B V j‖ ^ 2) =
        2 * (‖A U j‖ ^ 2 - ‖A V j‖ ^ 2) +
          K * (‖B U j‖ ^ 2 - ‖B V j‖ ^ 2) := by ring
    rw [hRewrite]
    calc
      |2 * (‖A U j‖ ^ 2 - ‖A V j‖ ^ 2) +
          K * (‖B U j‖ ^ 2 - ‖B V j‖ ^ 2)| ≤
        |2 * (‖A U j‖ ^ 2 - ‖A V j‖ ^ 2)| +
          |K * (‖B U j‖ ^ 2 - ‖B V j‖ ^ 2)| := abs_add_le _ _
      _ = 2 * |‖A U j‖ ^ 2 - ‖A V j‖ ^ 2| +
          K * |‖B U j‖ ^ 2 - ‖B V j‖ ^ 2| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg hK.1]
      _ ≤ ((8 * R ^ 6) *
            (‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖ +
             ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖) * C) * d +
          ((8 * R ^ 10) * (‖U‖ + ‖V‖)) * d :=
        add_le_add hYoung2 hWidthK
      _ = _ := by ring
  rw [hDecomp U, hDecomp V]
  change |(∑ j : Fin 3, (2 * ‖A U j‖ ^ 2 + K * ‖B U j‖ ^ 2)) -
      (∑ j : Fin 3, (2 * ‖A V j‖ ^ 2 + K * ‖B V j‖ ^ 2))| ≤
    (∑ j : Fin 3,
      ((8 * R ^ 6) *
        (‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖ +
         ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖) * C +
       (8 * R ^ 10) * (‖U‖ + ‖V‖))) * d
  calc
    |(∑ j : Fin 3, (2 * ‖A U j‖ ^ 2 + K * ‖B U j‖ ^ 2)) -
        (∑ j : Fin 3, (2 * ‖A V j‖ ^ 2 + K * ‖B V j‖ ^ 2))| =
      |(∑ j : Fin 3,
        ((2 * ‖A U j‖ ^ 2 + K * ‖B U j‖ ^ 2) -
         (2 * ‖A V j‖ ^ 2 + K * ‖B V j‖ ^ 2)))| := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ j : Fin 3,
        |(2 * ‖A U j‖ ^ 2 + K * ‖B U j‖ ^ 2) -
          (2 * ‖A V j‖ ^ 2 + K * ‖B V j‖ ^ 2)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3,
        (((8 * R ^ 6) *
          (‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖ +
           ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖) * C) +
          (8 * R ^ 10) * (‖U‖ + ‖V‖)) * d := by
            apply Finset.sum_le_sum
            intro j _
            exact hSingle j
    _ = (∑ j : Fin 3,
          ((8 * R ^ 6) *
            (‖thirdFullPhysicalAnnularYoungResidualFourierL2244 U j‖ +
             ‖thirdFullPhysicalAnnularYoungResidualFourierL2244 V j‖) * C +
            (8 * R ^ 10) * (‖U‖ + ‖V‖))) * d := by
            rw [Finset.sum_mul]

/-- The same radius-uniform modulus controls the exact ORIGINAL weighted
Young/width integral at ANY two physical times of the real H3 path. -/
theorem thirdFullPhysical_actualAnnularYoungWidth_uniformTwoTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (rho sigma R s t : ℝ) (hRho : 0 ≤ rho) (hOrder : rho ≤ sigma)
    (hUpper : sigma ≤ R) :
    let U := h3AuditActualSpectralVelocityTotal hH3 s
    let V := h3AuditActualSpectralVelocityTotal hH3 t
    |thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 s rho sigma -
      thirdFullPhysicalActualAnnularYoungWidthCost244 hH3 t rho sigma| ≤
    thirdFullPhysicalAnnularFullYoungWidthModulus244 R U V * ‖U - V‖ := by
  rw [thirdFullPhysical_actualYoungWidthCost_eq_hilbert244
        hH3 s rho sigma hOrder (hRho.trans hOrder),
      thirdFullPhysical_actualYoungWidthCost_eq_hilbert244
        hH3 t rho sigma hOrder (hRho.trans hOrder)]
  exact thirdFullPhysical_annularYoungWidthHilbert_uniformDifference244
    rho sigma R hRho hOrder hUpper _ _

end
end PrimeTensor.FirstMonomialTriad
