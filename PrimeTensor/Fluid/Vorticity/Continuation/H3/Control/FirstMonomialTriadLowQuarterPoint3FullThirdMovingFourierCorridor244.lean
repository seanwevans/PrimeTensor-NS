import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdTwoBandYoungSaturation244
import Mathlib.Tactic

/-!
# Moving Fourier-frequency corridor forced by sharp H³ Young near-saturation

The first physical Cauchy defect has the EXACT centered Fourier identity

  E₀ F₁ = ∫ (E₀ q(ξ)² - E₂)² S(ξ) dξ,

where S is physical velocity Fourier mass. The already-registered general
centered-sector lower bound controls the mass on ANY measurable set on
which the centered deviation is large, not merely two fixed radial bands.

For ρ≥0, write M_far(ρ) for the actual spectral mass on

  {ξ : ρ ≤ |E₀ q(ξ)² - E₂|}.

The resulting division-free Chebyshev estimate is

  ρ² M_far(ρ) ≤ E₀ F₁.

Combine with the exact first-Cauchy contribution to the sharp Young gap
  Δ = D₃ + (27/256) K⁴ E₀ - K E₃.

When D₃>0 and Δ≤δ this forces

  27 K⁴ ρ² M_far(ρ) ≤ 256 E₀ D₃ δ.

For K,ρ>0, this gives an explicit upper bound for the off-corridor mass.
The corridor moves with E₂/E₀; this is only a necessary condition on
near-saturation and does NOT establish that actual solutions saturate Young,
that their spectral mass has a uniform concentration rate, or continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

noncomputable local instance axisFintypeMovingFourierCorridor244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMovingFourierCorridor244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Physical Fourier mass outside the moving frequency corridor of width ρ
in the *unnormalized* centered variable `E₀ q² - E₂`.
The integral is over the actual spectral velocity mass density. -/
noncomputable def h3PathTopFourierMovingOffCorridorMass244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t ρ : ℝ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) : ℝ :=
  ∫ ξ in {ξ : H3FourierPoint3 |
      ρ ≤ |velocityH3Energy0At u t * h3FourierGradientSquare ξ ^ 2 -
        velocityH3Energy2At u t|},
    velocityH3FourierMassDensityAt u t hInt hMeas ξ ∂volume

/-- The physical Fourier variance dominates squared corridor width times
mass outside the corridor. It is entirely division-free and follows from
actual Fourier moment integrability, without assuming a spectral gap. -/
theorem h3Path_topFourier_movingOffCorridor_varianceBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t ρ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hρ : 0 ≤ ρ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    ρ ^ 2 * h3PathTopFourierMovingOffCorridorMass244 u t ρ hInt hMeas ≤
      velocityH3Energy0At u t *
        h3PathTopFourierFirstCauchyDefect244 u t := by
  let S : H3FourierPoint3 → ℝ :=
    velocityH3FourierMassDensityAt u t hInt hMeas
  let z : H3FourierPoint3 → ℝ := fun ξ =>
    velocityH3Energy0At u t * h3FourierGradientSquare ξ ^ 2 -
      velocityH3Energy2At u t
  let A : Set H3FourierPoint3 := {ξ | ρ ≤ |z ξ|}
  have hS : ∀ ξ, 0 ≤ S ξ := by
    intro ξ
    exact velocityH3FourierMassDensityAt_nonneg u t hInt hMeas ξ
  have hSInt : Integrable S volume := by
    dsimp only [S]
    exact velocityH3FourierMassDensityAt_integrable u t hInt hMeas
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs hInt
  have h2Int : Integrable
      (fun ξ : H3FourierPoint3 => h3FourierGradientSquare ξ ^ 2 * S ξ)
      volume := by
    dsimp only [S]
    exact velocityH3FourierSecondAggregateDensity_integrable
      hInt hMeas hFourier
  have h4Int : Integrable
      (fun ξ : H3FourierPoint3 => h3FourierGradientSquare ξ ^ 4 * S ξ)
      volume := by
    dsimp only [S]
    exact h3Path_velocityH3FourierFourthAggregateDensity_integrable
      hH3 hClass ht hInt hMeas hFourier
  have hExpand :
      (fun ξ : H3FourierPoint3 => z ξ ^ 2 * S ξ) =
      (fun ξ => velocityH3Energy0At u t ^ 2 *
          (h3FourierGradientSquare ξ ^ 4 * S ξ) -
        (2 * velocityH3Energy0At u t * velocityH3Energy2At u t) *
          (h3FourierGradientSquare ξ ^ 2 * S ξ) +
        velocityH3Energy2At u t ^ 2 * S ξ) := by
    funext ξ
    dsimp only [z]
    ring
  have hZInt : Integrable (fun ξ => z ξ ^ 2 * S ξ) volume := by
    rw [hExpand]
    exact ((h4Int.const_mul _).sub (h2Int.const_mul _)).add
      (hSInt.const_mul _)
  have hzMeas : Measurable z := by
    dsimp only [z, h3FourierGradientSquare]
    fun_prop
  have hA : MeasurableSet A := by
    dsimp only [A]
    exact measurableSet_le measurable_const hzMeas.abs
  have hSq (ξ : H3FourierPoint3) (hξ : ξ ∈ A) :
      ρ ^ 2 ≤ z ξ ^ 2 := by
    change ρ ≤ |z ξ| at hξ
    have hAbs : 0 ≤ |z ξ| := abs_nonneg _
    have hSquare := (sq_le_sq₀ hρ hAbs).2 hξ
    simpa only [sq_abs] using hSquare
  have hSector :
      ρ ^ 2 * (∫ ξ in A, S ξ ∂volume) ≤
        ∫ ξ, z ξ ^ 2 * S ξ ∂volume := by
    exact h3_twoBand_centered_sector_lower244
      (volume : Measure H3FourierPoint3) S z A ρ
      (∫ ξ in A, S ξ ∂volume)
      hA hS hSInt hZInt (le_refl _) hSq
  have hVar := h3Path_topFourier_firstCauchyDefect_radialVariance244
    hH3 hClass ht
  have hVarEq :
      (∫ ξ, z ξ ^ 2 * S ξ ∂volume) =
      velocityH3Energy0At u t *
        h3PathTopFourierFirstCauchyDefect244 u t := by
    simpa only [z, S, hInt, hMeas] using hVar
  calc
    ρ ^ 2 * h3PathTopFourierMovingOffCorridorMass244 u t ρ hInt hMeas =
        ρ ^ 2 * (∫ ξ in A, S ξ ∂volume) := by rfl
    _ ≤ ∫ ξ, z ξ ^ 2 * S ξ ∂volume := hSector
    _ = velocityH3Energy0At u t *
        h3PathTopFourierFirstCauchyDefect244 u t := hVarEq

/-- The actual first-Cauchy sharp Young budget, with its positive power
of D₃ cancelled. This is a reusable deficit estimate in physical variables. -/
theorem h3Path_topFourier_firstCauchy_le_sharpGapScaled244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hK : 0 ≤ K)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    27 * K ^ 4 * h3PathTopFourierFirstCauchyDefect244 u t ≤
      256 * velocityH3Dissipation3At u t * δ := by
  have hFirst := h3Path_sharpTopYoung_firstCauchy_le_gap244
    hH3 hClass ht hK
  have hGapNonneg : 0 ≤ (256 : ℝ) * velocityH3Dissipation3At u t ^ 3 :=
    mul_nonneg (by norm_num) (pow_nonneg hD.le 3)
  have hScaled := mul_le_mul_of_nonneg_left hNear hGapNonneg
  have hCombined :
      (27 * K ^ 4 * h3PathTopFourierFirstCauchyDefect244 u t) *
        velocityH3Dissipation3At u t ^ 2 ≤
      (256 * velocityH3Dissipation3At u t * δ) *
        velocityH3Dissipation3At u t ^ 2 := by
    calc
      _ = 27 * K ^ 4 * h3PathTopFourierFirstCauchyDefect244 u t *
          velocityH3Dissipation3At u t ^ 2 := by ring
      _ ≤ 256 * velocityH3Dissipation3At u t ^ 3 *
          (velocityH3Dissipation3At u t +
            (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
            K * velocityH3Energy3At u t) := by
        simpa only [mul_assoc] using hFirst
      _ ≤ 256 * velocityH3Dissipation3At u t ^ 3 * δ := hScaled
      _ = (256 * velocityH3Dissipation3At u t * δ) *
          velocityH3Dissipation3At u t ^ 2 := by ring
  exact (mul_le_mul_iff_of_pos_right (pow_pos hD 2)).mp hCombined

/-- Small Young gap forces the actual Fourier spectrum into a moving
single-frequency corridor. All mass outside a centered width ρ obeys
this explicit division-free budget. -/
theorem h3Path_topFourier_nearYoung_movingCorridorBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K δ ρ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hK : 0 ≤ K)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hρ : 0 ≤ ρ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    27 * K ^ 4 * ρ ^ 2 *
      h3PathTopFourierMovingOffCorridorMass244 u t ρ hInt hMeas ≤
      256 * velocityH3Energy0At u t *
        velocityH3Dissipation3At u t * δ := by
  have hVariance := h3Path_topFourier_movingOffCorridor_varianceBudget244
    hH3 hClass ht hρ hInt hMeas
  have hYoung := h3Path_topFourier_firstCauchy_le_sharpGapScaled244
    hH3 hClass ht hK hD hNear
  have hE0 : 0 ≤ velocityH3Energy0At u t :=
    velocityH3Energy0At_nonneg u t
  have hScale27 :
      27 * K ^ 4 * (ρ ^ 2 *
        h3PathTopFourierMovingOffCorridorMass244 u t ρ hInt hMeas) ≤
      27 * K ^ 4 * (velocityH3Energy0At u t *
        h3PathTopFourierFirstCauchyDefect244 u t) := by
    exact mul_le_mul_of_nonneg_left hVariance
      (mul_nonneg (by norm_num) (pow_nonneg hK 4))
  have hMassScaled := mul_le_mul_of_nonneg_left hYoung hE0
  calc
    27 * K ^ 4 * ρ ^ 2 *
        h3PathTopFourierMovingOffCorridorMass244 u t ρ hInt hMeas =
      27 * K ^ 4 * (ρ ^ 2 *
        h3PathTopFourierMovingOffCorridorMass244 u t ρ hInt hMeas) := by ring
    _ ≤ 27 * K ^ 4 * (velocityH3Energy0At u t *
        h3PathTopFourierFirstCauchyDefect244 u t) := hScale27
    _ = velocityH3Energy0At u t *
        (27 * K ^ 4 * h3PathTopFourierFirstCauchyDefect244 u t) := by ring
    _ ≤ velocityH3Energy0At u t *
        (256 * velocityH3Dissipation3At u t * δ) := hMassScaled
    _ = 256 * velocityH3Energy0At u t *
        velocityH3Dissipation3At u t * δ := by ring

/-- Quantitative Chebyshev upper bound on the mass outside the moving
spectral corridor. Here K and ρ are strictly positive, so dividing by
the explicit weight is mathematically justified. -/
theorem h3Path_topFourier_nearYoung_movingOffCorridorMass_upper244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K δ ρ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hK : 0 < K)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hρ : 0 < ρ)
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    h3PathTopFourierMovingOffCorridorMass244 u t ρ hInt hMeas ≤
      (256 * velocityH3Energy0At u t *
        velocityH3Dissipation3At u t * δ) / (27 * K ^ 4 * ρ ^ 2) := by
  have hBound := h3Path_topFourier_nearYoung_movingCorridorBudget244
    hH3 hClass ht hK.le hD hρ.le hInt hMeas hNear
  have hWeight : 0 < 27 * K ^ 4 * ρ ^ 2 := by positivity
  apply (le_div_iff₀ hWeight).2
  calc
    h3PathTopFourierMovingOffCorridorMass244 u t ρ hInt hMeas *
        (27 * K ^ 4 * ρ ^ 2) =
      27 * K ^ 4 * ρ ^ 2 *
        h3PathTopFourierMovingOffCorridorMass244 u t ρ hInt hMeas := by ring
    _ ≤ 256 * velocityH3Energy0At u t *
        velocityH3Dissipation3At u t * δ := hBound

/-- Specialization to the genuine physical H³ Landau top coefficient.
It supplies an explicit necessary narrow-corridor mass restriction at
any time of small actual sharp Young gap. -/
theorem h3Path_topLandau_nearYoung_movingOffCorridorMass_upper244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t δ ρ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hρ : 0 < ρ)
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
    h3PathTopFourierMovingOffCorridorMass244 u t ρ hInt hMeas ≤
      (256 * velocityH3Energy0At u t *
        velocityH3Dissipation3At u t * δ) /
        (27 *
          (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t))) ^ 4 * ρ ^ 2) := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hK : 0 < 4398 *
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) := by
    exact mul_pos (by norm_num)
      (mul_pos h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos
        (Real.sqrt_pos.2 hEPos))
  exact h3Path_topFourier_nearYoung_movingOffCorridorMass_upper244
    hH3 hClass ht hK hD hρ hInt hMeas hNear

end
end PrimeTensor.FirstMonomialTriad
