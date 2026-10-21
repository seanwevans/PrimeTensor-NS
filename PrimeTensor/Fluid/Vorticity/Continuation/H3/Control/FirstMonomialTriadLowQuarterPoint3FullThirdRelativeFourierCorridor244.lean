import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdMovingFourierCorridor244
import Mathlib.Tactic

/-!
# Scale-relative physical Fourier concentration under sharp Young near-saturation

The previous moving-corridor theorem estimates Fourier mass outside
  |E₀ q(ξ)² - E₂| ≥ ρ
by the sharp Young gap. Choosing the *intrinsic* half-width
  ρ = ε sqrt(E₀ D₃)
produces the normalization-invariant squared-frequency event
  |q(ξ)² - E₂/E₀| ≥ ε sqrt(D₃/E₀)
when E₀,D₃>0. Its Young budget cancels the product E₀ D₃ exactly:
  27 K⁴ ε² M_far ≤ 256 Δ_Y.
Consequently the fraction M_far/E₀ is controlled by
  256 Δ_Y / (27 K⁴ ε² E₀).

This is a NECESSARY spectral concentration criterion for sharp Young
near-saturation, not a dynamical anti-concentration theorem or global
Navier--Stokes regularity result.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

noncomputable local instance axisFintypeRelativeFourierCorridor244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceRelativeFourierCorridor244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The physical mass outside a moving corridor at the intrinsic Fourier
frequency scale `sqrt(E₀ D₃)`, with dimensionless relative width `ε`. -/
noncomputable def h3PathTopFourierRelativeOffCorridorMass244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t ε : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) : ℝ :=
  h3PathTopFourierMovingOffCorridorMass244 u t
    (ε * Real.sqrt (velocityH3Energy0At u t *
      velocityH3Dissipation3At u t)) hInt hMeas

/-- Exact cancellation of the kinetic-dissipation scale in a squared
moving-corridor Young budget. The proof is algebraic and division-free
in the conclusion; only positive scale is required for cancellation. -/
theorem h3_relativeFourierCorridor_cancelScale244
    {E0 D K ε M δ : ℝ}
    (hScale : 0 < E0 * D)
    (hBudget :
      27 * K ^ 4 * (ε * Real.sqrt (E0 * D)) ^ 2 * M ≤
        256 * E0 * D * δ) :
    27 * K ^ 4 * ε ^ 2 * M ≤ 256 * δ := by
  have hRootSq :
      (ε * Real.sqrt (E0 * D)) ^ 2 = ε ^ 2 * (E0 * D) := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hScale)]
  have hScaled :
      (E0 * D) * (27 * K ^ 4 * ε ^ 2 * M) ≤
        (E0 * D) * (256 * δ) := by
    calc
      (E0 * D) * (27 * K ^ 4 * ε ^ 2 * M) =
          27 * K ^ 4 * (ε * Real.sqrt (E0 * D)) ^ 2 * M := by
        rw [hRootSq]
        ring
      _ ≤ 256 * E0 * D * δ := hBudget
      _ = (E0 * D) * (256 * δ) := by ring
  exact (mul_le_mul_iff_of_pos_left hScale).mp hScaled

/-- At positive kinetic mass and top dissipation, sharp Young
near-saturation forces an unnormalized but scale-relative mass budget.
The factor E₀ D₃ from the earlier corridor theorem disappears. -/
theorem h3Path_topFourier_nearYoung_relativeCorridorBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K δ ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hK : 0 ≤ K)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hε : 0 ≤ ε)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    27 * K ^ 4 * ε ^ 2 *
      h3PathTopFourierRelativeOffCorridorMass244 u t ε hInt hMeas ≤
        256 * δ := by
  have hScale : 0 < velocityH3Energy0At u t *
      velocityH3Dissipation3At u t := mul_pos hMass hD
  have hρ : 0 ≤ ε * Real.sqrt
      (velocityH3Energy0At u t * velocityH3Dissipation3At u t) :=
    mul_nonneg hε (Real.sqrt_nonneg _)
  have hBudget := h3Path_topFourier_nearYoung_movingCorridorBudget244
    hH3 hClass ht hK hD hρ hInt hMeas hNear
  exact h3_relativeFourierCorridor_cancelScale244 hScale
    (by simpa only [h3PathTopFourierRelativeOffCorridorMass244] using hBudget)

/-- Relative Fourier mass outside the scale-relative frequency corridor
is bounded by the sharp Young gap divided by the natural K⁴E₀ scale.
Thus Δ_Y/(K⁴ E₀) → 0 forces concentration in each fixed positive
relative-width corridor, provided the pointwise positivity assumptions hold. -/
theorem h3Path_topFourier_nearYoung_relativeCorridorFraction_upper244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K δ ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hK : 0 < K)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hε : 0 < ε)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    h3PathTopFourierRelativeOffCorridorMass244 u t ε hInt hMeas /
        velocityH3Energy0At u t ≤
      (256 * δ) /
        (27 * K ^ 4 * ε ^ 2 * velocityH3Energy0At u t) := by
  have hBudget := h3Path_topFourier_nearYoung_relativeCorridorBudget244
    hH3 hClass ht hMass hK.le hD hε.le hInt hMeas hNear
  have hDen : 0 < 27 * K ^ 4 * ε ^ 2 *
      velocityH3Energy0At u t := by positivity
  apply (div_le_div_iff₀ hMass hDen).2
  calc
    h3PathTopFourierRelativeOffCorridorMass244 u t ε hInt hMeas *
        (27 * K ^ 4 * ε ^ 2 * velocityH3Energy0At u t) =
      (27 * K ^ 4 * ε ^ 2 *
        h3PathTopFourierRelativeOffCorridorMass244 u t ε hInt hMeas) *
        velocityH3Energy0At u t := by ring
    _ ≤ (256 * δ) * velocityH3Energy0At u t :=
      mul_le_mul_of_nonneg_right hBudget hMass.le

/-- Specialize scale-relative near-Young concentration to the actual
Landau top-order coefficient `4398 C₁ sqrt(E)`. -/
theorem h3Path_topLandau_nearYoung_relativeCorridorFraction_upper244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t δ ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hε : 0 < ε)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) *
        (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t))) ^ 4 *
        velocityH3Energy0At u t -
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) *
        velocityH3Energy3At u t ≤ δ) :
    h3PathTopFourierRelativeOffCorridorMass244 u t ε hInt hMeas /
        velocityH3Energy0At u t ≤
      (256 * δ) /
        (27 *
          (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t))) ^ 4 *
          ε ^ 2 * velocityH3Energy0At u t) := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hK : 0 < 4398 *
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) := by
    exact mul_pos (by norm_num)
      (mul_pos h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos
        (Real.sqrt_pos.2 hEPos))
  exact h3Path_topFourier_nearYoung_relativeCorridorFraction_upper244
    hH3 hClass ht hMass hK hD hε hInt hMeas hNear

end
end PrimeTensor.FirstMonomialTriad
