import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdKineticEssentialSpectralCorridor244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.ThirdOrderAbsorption
import Mathlib.Tactic

/-!
# Sharp top-Fourier Young absorption for the kinetic H³ spectral corridor

The established Fourier moment inequality E₃⁴ ≤ E₀ D₃³ has a sharper
one-unit-viscosity Young consequence than the earlier coefficient-one bound:

  K E₃ - D₃ ≤ (27/256) K⁴ E₀.

The coefficient is optimal for the abstract moment cone: equality occurs at
K = E₀ = 1, E₃ = 27/64, D₃ = 81/256. The proof uses the exact nonnegative
sum-of-squares factorization

  27 x⁴ - 256 (x-d) d³ = (3x-4d)² (3x²+8xd+16d²).

This improves the actual Landau-minus-top-dissipation margin, and therefore
the kinetic-anchored physical logarithmic-growth bound, with no new path
hypotheses. The resulting quartic term remains energy-superlinear and is
NOT thereby time-integrable; this is a quantitative PDE estimate, not an
unconditional continuation theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1000000

/-- Exact polynomial certificate for the optimal fourth-power Young constant. -/
theorem h3_sharpTopYoung_factorization244 (x d : ℝ) :
    27 * x ^ 4 - 256 * (x - d) * d ^ 3 =
      (3 * x - 4 * d) ^ 2 *
        (3 * x ^ 2 + 8 * x * d + 16 * d ^ 2) := by
  ring

/-- Sharp fourth-power Young inequality, with the full `d` dissipation
spent exactly once. The constant 27/256 is attained on the moment cone. -/
theorem h3_sharpTopYoung_of_fourthPower244
    {x b d : ℝ}
    (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hPower : x ^ 4 ≤ b * d ^ 3) :
    x ≤ d + (27 / 256 : ℝ) * b := by
  by_contra hNot
  have hLarge : d + (27 / 256 : ℝ) * b < x := lt_of_not_ge hNot
  have hx : 0 < x := by
    have hCoeff : 0 ≤ (27 / 256 : ℝ) * b :=
      mul_nonneg (by norm_num) hb
    linarith only [hLarge, hd, hCoeff]
  have hdPos : 0 < d := by
    by_contra hNotPos
    have hdZero : d = 0 := le_antisymm (le_of_not_gt hNotPos) hd
    rw [hdZero] at hPower
    norm_num at hPower
    have hx4 : 0 < x ^ 4 := pow_pos hx 4
    linarith only [hPower, hx4]
  have hGap : (27 : ℝ) * b < 256 * (x - d) := by
    nlinarith only [hLarge]
  have hd3 : 0 < d ^ 3 := pow_pos hdPos 3
  have hScaled := mul_lt_mul_of_pos_right hGap hd3
  have hMoment := mul_le_mul_of_nonneg_left hPower
    (show (0 : ℝ) ≤ 27 by norm_num)
  have hSOS : 0 ≤
      (3 * x - 4 * d) ^ 2 *
        (3 * x ^ 2 + 8 * x * d + 16 * d ^ 2) := by
    apply mul_nonneg (sq_nonneg _)
    positivity
  have hUpper : 256 * (x - d) * d ^ 3 ≤ 27 * x ^ 4 := by
    nlinarith only [hSOS]
  have hStrict : 27 * x ^ 4 < 256 * (x - d) * d ^ 3 := by
    nlinarith only [hMoment, hScaled]
  exact (not_lt_of_ge hUpper) hStrict

/-- Rational equality witness: the coefficient 27/256 cannot be reduced
for the abstract Fourier-moment interpolation cone. -/
theorem h3_sharpTopYoung_equalityWitness244 :
    (27 / 64 : ℝ) ^ 4 = (1 : ℝ) * (81 / 256 : ℝ) ^ 3 ∧
    (27 / 64 : ℝ) = (81 / 256 : ℝ) + (27 / 256 : ℝ) * 1 := by
  constructor <;> norm_num

/-- Actual H³ Fourier moment interpolation, with the OPTIMAL one-unit
viscous absorption coefficient 27/256 instead of the older coefficient 1. -/
theorem h3Path_sharpTopFourierYoung244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hK : 0 ≤ K) :
    K * velocityH3Energy3At u t ≤
      velocityH3Dissipation3At u t +
        (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t := by
  have hMoment :=
    velocityH3Energy3At_pow_four_le_energy0_mul_dissipation3_pow_three
      hH3 hClass ht
  have hScaled :
      (K * velocityH3Energy3At u t) ^ 4 ≤
        (K ^ 4 * velocityH3Energy0At u t) *
          velocityH3Dissipation3At u t ^ 3 := by
    calc
      _ = K ^ 4 * velocityH3Energy3At u t ^ 4 := by ring
      _ ≤ K ^ 4 * (velocityH3Energy0At u t *
          velocityH3Dissipation3At u t ^ 3) :=
        mul_le_mul_of_nonneg_left hMoment (pow_nonneg hK 4)
      _ = _ := by ring
  have hSharp := h3_sharpTopYoung_of_fourthPower244
    (mul_nonneg (pow_nonneg hK 4) (velocityH3Energy0At_nonneg u t))
    (velocityH3Dissipation3At_nonneg u t) hScaled
  nlinarith only [hSharp]

/-- The actual normalized physical top Landau-minus-dissipation margin
has the sharp Fourier Young quartic coefficient. -/
theorem h3Path_kineticTopLandauMargin_le_sharpYoung244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathKineticTopLandauMargin244 u t ≤
      ((27 / 256 : ℝ) *
        (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) ^ 4 *
        velocityH3Energy0At u t) / velocityH3EnergyAt u t := by
  let K : ℝ := 4398 *
    (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t))
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by norm_num)
      (mul_nonneg
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
        (Real.sqrt_nonneg _))
  have hSharp := h3Path_sharpTopFourierYoung244 hH3 hClass ht hK
  have hEpos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  unfold h3PathKineticTopLandauMargin244
  apply (div_le_div_iff_of_pos_right hEpos).2
  dsimp only [K] at hSharp
  linarith only [hSharp]

/-- An unconditional quantitative improvement of the ACTUAL kinetic-anchored
physical logarithmic growth inequality. No integrability is inferred. -/
theorem h3Path_kineticAnchor_growth_le_sharpTopYoung244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t ≤
      h3PathKineticAnchorSignedCost244 u b +
        ((27 / 256 : ℝ) *
          (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t))) ^ 4 *
          velocityH3Energy0At u t) / velocityH3EnergyAt u t := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hGrowth := h3Path_kineticAnchor_normalizedGrowth_le_topLandauMargin244
    hH3 hClass hb ht
  have hTop := h3Path_kineticTopLandauMargin_le_sharpYoung244
    hH3 hClass htClass
  linarith only [hGrowth, hTop]


/-- A fixed physical kinetic anchor freezes the sharp fourth-power Young
remainder into a quadratic Riccati coefficient: its normalized size is at
most (27/256) (4398 C₁)^4 E₀(b) E(t). -/
theorem h3Path_kineticTopLandauMargin_le_sharpAnchoredEnergy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    h3PathKineticTopLandauMargin244 u t ≤
      ((27 / 256 : ℝ) *
        (4398 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 4 *
        velocityH3Energy0At u b) * velocityH3EnergyAt u t := by
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hAnti := antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed hH3 hClass
  have hMass : velocityH3Energy0At u t ≤ velocityH3Energy0At u b :=
    hAnti hb htClass (le_of_lt ht.1)
  have hEone : 1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t
  have hEpos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one hEone
  have hEne : velocityH3EnergyAt u t ≠ 0 := ne_of_gt hEpos
  have hEnonneg : 0 ≤ velocityH3EnergyAt u t := hEpos.le
  have hRoot4 : Real.sqrt (velocityH3EnergyAt u t) ^ 4 =
      velocityH3EnergyAt u t ^ 2 := by
    calc
      _ = (Real.sqrt (velocityH3EnergyAt u t) ^ 2) ^ 2 := by ring
      _ = velocityH3EnergyAt u t ^ 2 := by
        rw [Real.sq_sqrt hEnonneg]
  have hExpression :
      ((27 / 256 : ℝ) *
        (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) ^ 4 *
        velocityH3Energy0At u t) / velocityH3EnergyAt u t =
      ((27 / 256 : ℝ) *
        (4398 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 4 *
        velocityH3Energy0At u t) * velocityH3EnergyAt u t := by
    have hPower :
        (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) ^ 4 =
        (4398 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 4 *
          velocityH3EnergyAt u t ^ 2 := by
      rw [show (4398 : ℝ) *
          (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t)) =
          (4398 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
            Real.sqrt (velocityH3EnergyAt u t) by ring, mul_pow, hRoot4]
    rw [hPower]
    field_simp [hEne]
  have hC : 0 ≤ (27 / 256 : ℝ) *
      (4398 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 4 := by
    positivity
  have hScaled :
      ((27 / 256 : ℝ) *
        (4398 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 4 *
        velocityH3Energy0At u t) * velocityH3EnergyAt u t ≤
      ((27 / 256 : ℝ) *
        (4398 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 4 *
        velocityH3Energy0At u b) * velocityH3EnergyAt u t :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hMass hC) hEnonneg
  exact (h3Path_kineticTopLandauMargin_le_sharpYoung244
    hH3 hClass htClass).trans ((le_of_eq hExpression).trans hScaled)

/-- The already-established kinetic anchor and exact Fourier interpolation
yield a quantitative Riccati upper bound with the sharp 27/256 Young
coefficient. The E² contribution remains and is not controlled here. -/
theorem h3Path_kineticAnchor_growth_le_sharpAnchoredRiccati244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    deriv (velocityH3EnergyAt u) t ≤
      h3PathKineticAnchorSignedCost244 u b * velocityH3EnergyAt u t +
      ((27 / 256 : ℝ) *
        (4398 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 4 *
        velocityH3Energy0At u b) * velocityH3EnergyAt u t ^ 2 := by
  have hGrowth := h3Path_kineticAnchor_normalizedGrowth_le_topLandauMargin244
    hH3 hClass hb ht
  have hMargin := h3Path_kineticTopLandauMargin_le_sharpAnchoredEnergy244
    hH3 hClass hb ht
  have hEpos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hRatio : deriv (velocityH3EnergyAt u) t /
        velocityH3EnergyAt u t ≤
      h3PathKineticAnchorSignedCost244 u b +
        ((27 / 256 : ℝ) *
          (4398 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 4 *
          velocityH3Energy0At u b) * velocityH3EnergyAt u t := by
    linarith only [hGrowth, hMargin]
  have hMult := (div_le_iff₀ hEpos).1 hRatio
  nlinarith only [hMult]

end
end PrimeTensor.FirstMonomialTriad
