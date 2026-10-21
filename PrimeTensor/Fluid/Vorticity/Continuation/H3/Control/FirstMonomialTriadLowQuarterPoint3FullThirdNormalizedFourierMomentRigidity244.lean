import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRelativeFourierCorridor244
import Mathlib.Tactic

/-!
# Normalized physical Fourier moment rigidity at sharp H³ Young saturation

The first physical Cauchy defect is F₁ = E₀ D₃ - E₂².
On the positive-kinetic, positive-dissipation branch, define

  R = F₁ / (E₀ D₃),    C = E₂² / (E₀ D₃).

Then R + C = 1, 0 < R ≤ 1, and 0 ≤ C < 1. In particular, exact
spectral Cauchy saturation C = 1 is impossible for the actual physical
Fourier density at positive kinetic mass.

The already established first-Cauchy sharp Young deficit budget gives

  27 K⁴ F₁ ≤ 256 D₃ Δ_Y,

so whenever Δ_Y ≤ δ and K,E₀,D₃>0,

  R ≤ 256 δ / (27 K⁴ E₀),
  C ≥ 1 - 256 δ / (27 K⁴ E₀).

Thus normalized near-Young saturation forces the physical *middle Fourier
moment ratio* toward equality in Cauchy. This is a necessary spectral
rigidity condition, NOT a proof that such near-saturation occurs along
Navier--Stokes evolution, and NOT a uniform positive variance gap.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

/-- The dimensionless first physical Fourier Cauchy defect, normalized
by the actual kinetic/top-dissipation product. -/
noncomputable def h3PathTopFourierNormalizedRadialVariance244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : ℝ :=
  h3PathTopFourierFirstCauchyDefect244 u t /
    (velocityH3Energy0At u t * velocityH3Dissipation3At u t)

/-- Dimensionless saturation ratio of the middle Fourier moment. -/
noncomputable def h3PathTopFourierNormalizedMiddleMoment244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : ℝ :=
  velocityH3Energy2At u t ^ 2 /
    (velocityH3Energy0At u t * velocityH3Dissipation3At u t)

/-- Exact dimensionless decomposition: variance ratio plus middle-moment
Cauchy saturation ratio is identically one on the positive branch. -/
theorem h3Path_topFourier_normalizedVariance_add_middle_eq_one244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t) :
    h3PathTopFourierNormalizedRadialVariance244 u t +
      h3PathTopFourierNormalizedMiddleMoment244 u t = 1 := by
  have hDen : 0 < velocityH3Energy0At u t *
      velocityH3Dissipation3At u t := mul_pos hMass hD
  unfold h3PathTopFourierNormalizedRadialVariance244
    h3PathTopFourierNormalizedMiddleMoment244
  calc
    h3PathTopFourierFirstCauchyDefect244 u t /
        (velocityH3Energy0At u t * velocityH3Dissipation3At u t) +
        velocityH3Energy2At u t ^ 2 /
        (velocityH3Energy0At u t * velocityH3Dissipation3At u t) =
      (h3PathTopFourierFirstCauchyDefect244 u t +
        velocityH3Energy2At u t ^ 2) /
        (velocityH3Energy0At u t * velocityH3Dissipation3At u t) := by
      rw [add_div]
    _ = (velocityH3Energy0At u t * velocityH3Dissipation3At u t) /
        (velocityH3Energy0At u t * velocityH3Dissipation3At u t) := by
      unfold h3PathTopFourierFirstCauchyDefect244
      ring
    _ = 1 := div_self (ne_of_gt hDen)

/-- Actual positive physical kinetic mass rules out normalized zero
radial variance. The normalization does not change the sign. -/
theorem h3Path_topFourier_normalizedVariance_pos244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t) :
    0 < h3PathTopFourierNormalizedRadialVariance244 u t := by
  unfold h3PathTopFourierNormalizedRadialVariance244
  exact div_pos
    (h3Path_topFourier_firstCauchyDefect_pos_of_kineticMass244
      hH3 hClass ht hMass) (mul_pos hMass hD)

/-- The dimensionless variance belongs to (0,1], and the middle-moment
ratio belongs to [0,1). Equality at the upper Cauchy endpoint is excluded
by nullity of the corresponding physical Fourier sphere. -/
theorem h3Path_topFourier_normalizedMoment_strictRange244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t) :
    (0 < h3PathTopFourierNormalizedRadialVariance244 u t ∧
      h3PathTopFourierNormalizedRadialVariance244 u t ≤ 1) ∧
    (0 ≤ h3PathTopFourierNormalizedMiddleMoment244 u t ∧
      h3PathTopFourierNormalizedMiddleMoment244 u t < 1) := by
  have hPositive := h3Path_topFourier_normalizedVariance_pos244
    hH3 hClass ht hMass hD
  have hMiddleNonneg :
      0 ≤ h3PathTopFourierNormalizedMiddleMoment244 u t := by
    unfold h3PathTopFourierNormalizedMiddleMoment244
    exact div_nonneg (sq_nonneg _)
      (mul_pos hMass hD).le
  have hSum := h3Path_topFourier_normalizedVariance_add_middle_eq_one244
    hMass hD
  constructor
  · constructor
    · exact hPositive
    · linarith only [hMiddleNonneg, hSum]
  · constructor
    · exact hMiddleNonneg
    · linarith only [hPositive, hSum]

/-- Quantitative normalized first-Cauchy deficit from a near-sharp Young
budget. The positive D₃ factor cancels; the remaining scale is K⁴ E₀. -/
theorem h3Path_topFourier_normalizedVariance_nearYoung_upper244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hK : 0 < K)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    h3PathTopFourierNormalizedRadialVariance244 u t ≤
      (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t) := by
  have hFirst := h3Path_topFourier_firstCauchy_le_sharpGapScaled244
    hH3 hClass ht hK.le hD hNear
  have hDen : 0 < velocityH3Energy0At u t *
      velocityH3Dissipation3At u t := mul_pos hMass hD
  have hWeight : 0 < 27 * K ^ 4 * velocityH3Energy0At u t := by
    positivity
  unfold h3PathTopFourierNormalizedRadialVariance244
  apply (div_le_div_iff₀ hDen hWeight).2
  calc
    h3PathTopFourierFirstCauchyDefect244 u t *
        (27 * K ^ 4 * velocityH3Energy0At u t) =
      (27 * K ^ 4 * h3PathTopFourierFirstCauchyDefect244 u t) *
        velocityH3Energy0At u t := by ring
    _ ≤ (256 * velocityH3Dissipation3At u t * δ) *
        velocityH3Energy0At u t :=
      mul_le_mul_of_nonneg_right hFirst hMass.le
    _ = (256 * δ) *
        (velocityH3Energy0At u t * velocityH3Dissipation3At u t) := by
      ring

/-- Near-saturation of the physical sharp Young inequality forces the
normalized middle Fourier moment Cauchy ratio close to one from below.
This states spectral *rigidity*, not dynamical near-saturation. -/
theorem h3Path_topFourier_normalizedMiddle_nearYoung_floor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hK : 0 < K)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    1 - (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t) ≤
      h3PathTopFourierNormalizedMiddleMoment244 u t := by
  have hSum := h3Path_topFourier_normalizedVariance_add_middle_eq_one244
    hMass hD
  have hBound := h3Path_topFourier_normalizedVariance_nearYoung_upper244
    hH3 hClass ht hMass hK hD hNear
  linarith only [hSum, hBound]

/-- The normalized physical middle-moment ratio is *strictly* less than
one, yet it must exceed the displayed threshold at any near-Young time. -/
theorem h3Path_topFourier_normalizedMiddle_nearYoung_corridor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hK : 0 < K)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    1 - (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t) ≤
        h3PathTopFourierNormalizedMiddleMoment244 u t ∧
      h3PathTopFourierNormalizedMiddleMoment244 u t < 1 := by
  exact ⟨h3Path_topFourier_normalizedMiddle_nearYoung_floor244
    hH3 hClass ht hMass hK hD hNear,
    (h3Path_topFourier_normalizedMoment_strictRange244
      hH3 hClass ht hMass hD).2.2⟩

/-- The same dimensionless moment rigidity with the concrete physical
Landau coefficient `K = 4398 C₁ sqrt(E)`. This preserves the exact signed
H³ Young gap and does not assert that the gap vanishes. -/
theorem h3Path_topLandau_normalizedMiddle_nearYoung_floor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) *
        (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) ^ 4 *
        velocityH3Energy0At u t -
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) *
        velocityH3Energy3At u t ≤ δ) :
    1 - (256 * δ) /
      (27 *
        (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) ^ 4 *
        velocityH3Energy0At u t) ≤
      h3PathTopFourierNormalizedMiddleMoment244 u t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hK : 0 < 4398 *
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) := by
    exact mul_pos (by norm_num)
      (mul_pos h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos
        (Real.sqrt_pos.2 hEPos))
  exact h3Path_topFourier_normalizedMiddle_nearYoung_floor244
    hH3 hClass ht hMass hK hD hNear

end
end PrimeTensor.FirstMonomialTriad
