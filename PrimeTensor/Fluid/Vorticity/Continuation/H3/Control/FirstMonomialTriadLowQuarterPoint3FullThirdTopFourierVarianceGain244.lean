import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdTwoCauchySpectralDefect244
import Mathlib.Tactic

/-!
# Retain the first Fourier Cauchy defect in sharp top-order Young absorption

The existing second Fourier Cauchy estimate is E₃² ≤ E₂ D₃. Squaring
and spending one unit of top viscosity with the *sharp* fourth-power Young
inequality gives, whenever D₃>0,

    K E₃ ≤ D₃ + (27/256) K⁴ E₂²/D₃.

Since the first Cauchy defect F₁ = E₀ D₃ - E₂² is nonnegative,
this is an unconditional improvement of the earlier K⁴ E₀ ceiling:

    K E₃ + (27/256) K⁴ F₁/D₃ ≤ D₃ + (27/256) K⁴ E₀.

The displayed gain is an actual physical Fourier variance, not an
assumed spectral gap. It may become arbitrarily small for narrow shells;
no unconditional regularity or quantitative lower bound is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

/-- Square the genuinely physical second Fourier Cauchy bound without
eliminating its middle E₂ moment. -/
theorem h3Path_topFourier_secondCauchy_fourthPower244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3Energy3At u t ^ 4 ≤
      velocityH3Energy2At u t ^ 2 * velocityH3Dissipation3At u t ^ 2 := by
  have hCS := h3Path_topFourier_secondCauchy_le244 hH3 hClass ht
  have hSquare := mul_self_le_mul_self
    (sq_nonneg (velocityH3Energy3At u t)) hCS
  nlinarith only [hSquare]

/-- The sharp one-unit Young bound can retain E₂²/D₃ instead of paying
all of E₀. The only additional requirement is nonzero physical D₃. -/
theorem h3Path_topFourier_reducedSharpYoung244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hK : 0 ≤ K)
    (hD : 0 < velocityH3Dissipation3At u t) :
    K * velocityH3Energy3At u t ≤
      velocityH3Dissipation3At u t +
        (27 / 256 : ℝ) *
          ((K ^ 4 * velocityH3Energy2At u t ^ 2) /
            velocityH3Dissipation3At u t) := by
  have hFourth := h3Path_topFourier_secondCauchy_fourthPower244
    hH3 hClass ht
  have hScaled :
      (K * velocityH3Energy3At u t) ^ 4 ≤
        ((K ^ 4 * velocityH3Energy2At u t ^ 2) /
          velocityH3Dissipation3At u t) *
          velocityH3Dissipation3At u t ^ 3 := by
    have hMul := mul_le_mul_of_nonneg_left hFourth (pow_nonneg hK 4)
    calc
      _ = K ^ 4 * velocityH3Energy3At u t ^ 4 := by ring
      _ ≤ K ^ 4 *
          (velocityH3Energy2At u t ^ 2 * velocityH3Dissipation3At u t ^ 2) :=
        hMul
      _ = ((K ^ 4 * velocityH3Energy2At u t ^ 2) /
            velocityH3Dissipation3At u t) *
          velocityH3Dissipation3At u t ^ 3 := by
        field_simp [ne_of_gt hD] <;> ring
  exact h3_sharpTopYoung_of_fourthPower244
    (div_nonneg
      (mul_nonneg (pow_nonneg hK 4)
        (sq_nonneg (velocityH3Energy2At u t))) hD.le)
    hD.le hScaled

/-- The first physical Fourier Cauchy defect yields an EXPLICIT positive
correction to sharp Young absorption, without an additional dispersion
hypothesis: it is the precise difference between E₀ and E₂²/D₃. -/
theorem h3Path_topFourier_firstVarianceGain244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hK : 0 ≤ K)
    (hD : 0 < velocityH3Dissipation3At u t) :
    K * velocityH3Energy3At u t +
      (27 / 256 : ℝ) *
        ((K ^ 4 * h3PathTopFourierFirstCauchyDefect244 u t) /
          velocityH3Dissipation3At u t) ≤
      velocityH3Dissipation3At u t +
        (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t := by
  have hReduced := h3Path_topFourier_reducedSharpYoung244
    hH3 hClass ht hK hD
  have hSplit : velocityH3Energy2At u t ^ 2 +
      h3PathTopFourierFirstCauchyDefect244 u t =
      velocityH3Energy0At u t * velocityH3Dissipation3At u t := by
    unfold h3PathTopFourierFirstCauchyDefect244
    ring
  have hRatio :
      (velocityH3Energy2At u t ^ 2 +
        h3PathTopFourierFirstCauchyDefect244 u t) /
        velocityH3Dissipation3At u t = velocityH3Energy0At u t := by
    apply (div_eq_iff (ne_of_gt hD)).2
    exact hSplit
  have hCost :
      (27 / 256 : ℝ) *
          ((K ^ 4 * velocityH3Energy2At u t ^ 2) /
            velocityH3Dissipation3At u t) +
        (27 / 256 : ℝ) *
          ((K ^ 4 * h3PathTopFourierFirstCauchyDefect244 u t) /
            velocityH3Dissipation3At u t) =
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t := by
    calc
      _ = (27 / 256 : ℝ) * K ^ 4 *
          ((velocityH3Energy2At u t ^ 2 +
            h3PathTopFourierFirstCauchyDefect244 u t) /
            velocityH3Dissipation3At u t) := by ring
      _ = (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t := by
        rw [hRatio]
  linarith only [hReduced, hCost]

/-- The variance correction is nonnegative on actual H³ solutions and
positive if the first Cauchy inequality is strict and K>0. -/
theorem h3Path_topFourier_firstVarianceGain_nonneg244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hK : 0 ≤ K)
    (hD : 0 < velocityH3Dissipation3At u t) :
    0 ≤ (27 / 256 : ℝ) *
      ((K ^ 4 * h3PathTopFourierFirstCauchyDefect244 u t) /
        velocityH3Dissipation3At u t) := by
  have hCS := (h3Path_topFourier_twoCauchyDefects_nonneg244
    hH3 hClass ht).1
  exact mul_nonneg (by norm_num)
    (div_nonneg (mul_nonneg (pow_nonneg hK 4) hCS) hD.le)

/-- A positive first-Cauchy defect makes the corrected Young ceiling
strictly lower than the formerly optimal (but spectrally oblivious) bound. -/
theorem h3Path_topFourier_strictYoung_of_firstVariance244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hK : 0 < K)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hSpread : 0 < h3PathTopFourierFirstCauchyDefect244 u t) :
    K * velocityH3Energy3At u t <
      velocityH3Dissipation3At u t +
        (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t := by
  have hCorrected := h3Path_topFourier_firstVarianceGain244
    hH3 hClass ht hK.le hD
  have hGain : 0 < (27 / 256 : ℝ) *
      ((K ^ 4 * h3PathTopFourierFirstCauchyDefect244 u t) /
        velocityH3Dissipation3At u t) := by
    exact mul_pos (by norm_num)
      (div_pos (mul_pos (pow_pos hK 4) hSpread) hD)
  linarith only [hCorrected, hGain]

/-- The genuine Landau top-order coefficient inherits the first-variance
correction. This is a physical Fourier inequality, with NO dispersion floor
or shell-separation assumption. -/
theorem h3Path_topLandau_firstVarianceGain244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hD : 0 < velocityH3Dissipation3At u t) :
    (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) * velocityH3Energy3At u t +
      (27 / 256 : ℝ) *
        (((4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) ^ 4 *
          h3PathTopFourierFirstCauchyDefect244 u t) /
          velocityH3Dissipation3At u t) ≤
      velocityH3Dissipation3At u t +
        (27 / 256 : ℝ) *
          (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t))) ^ 4 *
            velocityH3Energy0At u t := by
  have hK : 0 ≤ 4398 *
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) :=
    mul_nonneg (by norm_num)
      (mul_nonneg h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
        (Real.sqrt_nonneg _))
  exact h3Path_topFourier_firstVarianceGain244 hH3 hClass ht hK hD

end
end PrimeTensor.FirstMonomialTriad
