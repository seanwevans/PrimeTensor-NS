import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialH3EnergyMajorizedProjectedRHS
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialAutomaticOldTimeMeasurability
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.RHS.Bound

/-!
# Canonical initial physical diffusion and Leray source bounds from actual H³ data

The preceding initial-energy criterion assumed two source-to-energy inequalities.
Here concrete physical real L² diffusion and Leray source candidates are
constructed from the ACTUAL strict-time weighted H³ spectral state, using the
already-proved raw Fourier Laplacian and quadratic Leray-forcing estimates.

At positive times their physical Hilbert norms obey

  ‖D(t)‖ ≤ 3 * E₃(t),
  ‖N(t)‖ ≤ (3 * 576 * π * C₃) * E₃(t),

where `E₃(t) = velocityH3EnergyAt u t ≥ 1` and
`C₃ = h3SobolevDeweightingConstant`.

Zero extensions ensure the same inequalities at the left endpoint of an
initial interval. Thus neither pointwise estimate need remain in the
initial-energy-majorized comparison data.

IMPORTANT: This file constructs physical Fourier-reconstructed candidates.
Its PDE-facing comparison interface still explicitly assumes strong time
measurability and the positive-time weak momentum derivative for precisely
these candidates. Their literal identification with the spatial Laplacian
and the Leray projection of the actual PDE is a distinct remaining task.
Initial H³-energy integrability and the vanishing old/selected comparison
residual also remain independent conditions.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- The exact coefficient in the physical `L²` Leray forcing bound. -/
noncomputable def h3AuditInitialLerayEnergyCoefficient : ℝ :=
  3 * (576 * Real.pi * h3SobolevDeweightingConstant)

theorem h3AuditInitialLerayEnergyCoefficient_nonneg :
    0 ≤ h3AuditInitialLerayEnergyCoefficient := by
  unfold h3AuditInitialLerayEnergyCoefficient
  positivity [h3SobolevDeweightingConstant_nonneg]

/-- Real physical Hilbert reconstruction of the raw Fourier Laplacian of
an arbitrary weighted H³ spectral velocity state. -/
noncomputable def h3AuditSpectralPhysicalLaplacian
    (U : H3SpectralVelocityState) :
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2 (fun j : Fin 3 =>
    h3FromFourierRealL2
      (h3RealPartFourierL2
        (h3SpectralScalarLaplacianRawFourierL2 (U j))))

/-- Real physical Hilbert reconstruction of the quadratic Leray forcing
of the same weighted H³ spectral velocity state. -/
noncomputable def h3AuditSpectralPhysicalLerayForcing
    (U : H3SpectralVelocityState) :
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2 (fun j : Fin 3 =>
    h3FromFourierRealL2
      (h3RealPartFourierL2
        (h3RawFinLerayOuterProductDivergenceFourierL2 U U j)))

/-- The physical Laplacian norm is bounded by three times the spectral H³
norm. The only inputs are Plancherel-carrier norm preservation, real-part
contraction, and the already-proved Laplacian multiplier estimate. -/
theorem h3AuditSpectralPhysicalLaplacian_norm_le
    (U : H3SpectralVelocityState) :
    ‖h3AuditSpectralPhysicalLaplacian U‖ ≤ 3 * ‖U‖ := by
  apply norm_h3PhysicalRealFinVectorL2Hilbert_le_three_mul_of_coordinate_norm_le
    _ (norm_nonneg U)
  intro j
  change
    ‖h3FromFourierRealL2
      (h3RealPartFourierL2
        (h3SpectralScalarLaplacianRawFourierL2 (U j)))‖ ≤ ‖U‖
  calc
    ‖h3FromFourierRealL2
        (h3RealPartFourierL2
          (h3SpectralScalarLaplacianRawFourierL2 (U j)))‖ =
      ‖h3RealPartFourierL2
        (h3SpectralScalarLaplacianRawFourierL2 (U j))‖ :=
        norm_h3FromFourierRealL2 _
    _ ≤ ‖h3SpectralScalarLaplacianRawFourierL2 (U j)‖ :=
      norm_h3RealPartFourierL2_le _
    _ ≤ ‖U j‖ := norm_h3SpectralScalarLaplacianRawFourierL2_le _
    _ ≤ ‖U‖ := h3SpectralVelocity_coordinate_norm_le U j

/-- The physical nonlinear Leray source is quadratic in the genuine H³
spectral norm. The coefficient is the existing raw Fourier convolution
constant multiplied by the three-component Hilbert comparison. -/
theorem h3AuditSpectralPhysicalLerayForcing_norm_le
    (U : H3SpectralVelocityState) :
    ‖h3AuditSpectralPhysicalLerayForcing U‖ ≤
      h3AuditInitialLerayEnergyCoefficient * (‖U‖ * ‖U‖) := by
  let C : ℝ := 576 * Real.pi * h3SobolevDeweightingConstant
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity [h3SobolevDeweightingConstant_nonneg]
  have hRaw : ‖h3AuditSpectralPhysicalLerayForcing U‖ ≤
      3 * (C * ‖U‖ * ‖U‖) := by
    apply norm_h3PhysicalRealFinVectorL2Hilbert_le_three_mul_of_coordinate_norm_le
      _ (by positivity)
    intro j
    change
      ‖h3FromFourierRealL2
        (h3RealPartFourierL2
          (h3RawFinLerayOuterProductDivergenceFourierL2 U U j))‖ ≤
        C * ‖U‖ * ‖U‖
    calc
      ‖h3FromFourierRealL2
          (h3RealPartFourierL2
            (h3RawFinLerayOuterProductDivergenceFourierL2 U U j))‖ =
        ‖h3RealPartFourierL2
          (h3RawFinLerayOuterProductDivergenceFourierL2 U U j)‖ :=
          norm_h3FromFourierRealL2 _
      _ ≤ ‖h3RawFinLerayOuterProductDivergenceFourierL2 U U j‖ :=
        norm_h3RealPartFourierL2_le _
      _ ≤ C * ‖U‖ * ‖U‖ := by
        dsimp only [C]
        exact norm_h3RawFinLerayOuterProductDivergenceFourierL2_le U U j
  calc
    ‖h3AuditSpectralPhysicalLerayForcing U‖ ≤
        3 * (C * ‖U‖ * ‖U‖) := hRaw
    _ = h3AuditInitialLerayEnergyCoefficient * (‖U‖ * ‖U‖) := by
      unfold h3AuditInitialLerayEnergyCoefficient
      dsimp only [C]
      ring

/-- The actual strict-time old spectral velocity, Fourier reconstructed
as a physical Laplacian. Nonphysical times are extended by zero. -/
noncomputable def h3AuditInitialActualSpectralLaplacianTotal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : H3PhysicalRealFinVectorL2Hilbert :=
  if ht : t ∈ Set.Ioo (0 : ℝ) T then
    h3AuditSpectralPhysicalLaplacian
      (h3AuditActualSpectralVelocityTotal hH3 t)
  else 0

/-- The actual strict-time old spectral velocity, Fourier reconstructed
as a physical Leray transport. Nonphysical times are extended by zero. -/
noncomputable def h3AuditInitialActualSpectralLerayTotal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : H3PhysicalRealFinVectorL2Hilbert :=
  if ht : t ∈ Set.Ioo (0 : ℝ) T then
    h3AuditSpectralPhysicalLerayForcing
      (h3AuditActualSpectralVelocityTotal hH3 t)
  else 0

/-- The actual old H³ encoder has a squared norm no greater than its
normalized physical energy. -/
theorem h3Audit_initialActualSpectralState_norm_sq_le_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2 ≤
      velocityH3EnergyAt u t := by
  let U := h3AuditActualSpectralVelocityTotal hH3 t
  have hEnergy : 0 ≤ velocityH3EnergyAt u t :=
    (zero_le_one).trans (one_le_velocityH3EnergyAt u t)
  have hU : ‖U‖ ≤ Real.sqrt (velocityH3EnergyAt u t) := by
    dsimp only [U]
    rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t ht]
    exact h3AuditActualSpectralVelocityAt_norm_le_sqrt_energy hH3 t ht
  have hPower := pow_le_pow_left₀ (norm_nonneg U) hU 2
  rw [Real.sq_sqrt hEnergy] at hPower
  exact hPower

/-- The original normalized H³ energy exceeds its square root, because it
includes a positive unit term. -/
theorem h3Audit_initialActualEnergy_sqrt_le
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    Real.sqrt (velocityH3EnergyAt u t) ≤ velocityH3EnergyAt u t := by
  have hOne : 1 ≤ velocityH3EnergyAt u t := one_le_velocityH3EnergyAt u t
  have hEnergy : 0 ≤ velocityH3EnergyAt u t := (zero_le_one).trans hOne
  have hSqrtOne : 1 ≤ Real.sqrt (velocityH3EnergyAt u t) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hOne
  nlinarith [Real.sq_sqrt hEnergy]

/-- Exact physical diffusion candidate is pointwise controlled by three
times the actual H³ energy, including the left zero-extension endpoint. -/
theorem h3Audit_initialActualSpectralLaplacian_norm_le_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hbT : b < T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b) :
    ‖h3AuditInitialActualSpectralLaplacianTotal hH3 t‖ ≤
      3 * velocityH3EnergyAt u t := by
  by_cases hZero : t = 0
  · subst t
    have hEnergy : 0 ≤ velocityH3EnergyAt u 0 :=
      (zero_le_one).trans (one_le_velocityH3EnergyAt u 0)
    have hOutside : ¬ (0 : ℝ) ∈ Set.Ioo (0 : ℝ) T := by simp
    simp only [h3AuditInitialActualSpectralLaplacianTotal,
      dif_neg hOutside, norm_zero]
    positivity
  · have hPos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hZero)
    have htT : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨hPos, lt_of_le_of_lt ht.2 hbT⟩
    have hNormU :
        ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ≤
          Real.sqrt (velocityH3EnergyAt u t) := by
      rw [h3AuditActualSpectralVelocityTotal_eq_at hH3 t htT]
      exact h3AuditActualSpectralVelocityAt_norm_le_sqrt_energy hH3 t htT
    calc
      ‖h3AuditInitialActualSpectralLaplacianTotal hH3 t‖ =
          ‖h3AuditSpectralPhysicalLaplacian
            (h3AuditActualSpectralVelocityTotal hH3 t)‖ := by
        simp only [h3AuditInitialActualSpectralLaplacianTotal, dite_eq_left htT]
      _ ≤ 3 * ‖h3AuditActualSpectralVelocityTotal hH3 t‖ :=
        h3AuditSpectralPhysicalLaplacian_norm_le _
      _ ≤ 3 * Real.sqrt (velocityH3EnergyAt u t) :=
        mul_le_mul_of_nonneg_left hNormU (by norm_num)
      _ ≤ 3 * velocityH3EnergyAt u t :=
        mul_le_mul_of_nonneg_left
          (h3Audit_initialActualEnergy_sqrt_le u t) (by norm_num)

/-- Exact physical Leray candidate has a linear normalized-H³-energy
ceiling, since the underlying forcing is quadratic in spectral norm. -/
theorem h3Audit_initialActualSpectralLeray_norm_le_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hbT : b < T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b) :
    ‖h3AuditInitialActualSpectralLerayTotal hH3 t‖ ≤
      h3AuditInitialLerayEnergyCoefficient * velocityH3EnergyAt u t := by
  by_cases hZero : t = 0
  · subst t
    have hEnergy : 0 ≤ velocityH3EnergyAt u 0 :=
      (zero_le_one).trans (one_le_velocityH3EnergyAt u 0)
    have hOutside : ¬ (0 : ℝ) ∈ Set.Ioo (0 : ℝ) T := by simp
    simp only [h3AuditInitialActualSpectralLerayTotal,
      dif_neg hOutside, norm_zero]
    exact mul_nonneg h3AuditInitialLerayEnergyCoefficient_nonneg hEnergy
  · have hPos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hZero)
    have htT : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨hPos, lt_of_le_of_lt ht.2 hbT⟩
    have hSq := h3Audit_initialActualSpectralState_norm_sq_le_energy
      hH3 t htT
    calc
      ‖h3AuditInitialActualSpectralLerayTotal hH3 t‖ =
          ‖h3AuditSpectralPhysicalLerayForcing
            (h3AuditActualSpectralVelocityTotal hH3 t)‖ := by
        simp only [h3AuditInitialActualSpectralLerayTotal, dite_eq_left htT]
      _ ≤ h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 t‖ *
            ‖h3AuditActualSpectralVelocityTotal hH3 t‖) :=
        h3AuditSpectralPhysicalLerayForcing_norm_le _
      _ ≤ h3AuditInitialLerayEnergyCoefficient * velocityH3EnergyAt u t := by
        have hProduct :
            ‖h3AuditActualSpectralVelocityTotal hH3 t‖ *
              ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ≤
                velocityH3EnergyAt u t := by
          simpa only [pow_two] using hSq
        exact mul_le_mul_of_nonneg_left hProduct
          h3AuditInitialLerayEnergyCoefficient_nonneg

/-- Once the actual physical spectral reconstructions are time measurable,
only scalar initial-H³-energy integrability is needed for their separate
Bochner integrability and an explicit projected RHS budget. -/
theorem h3Audit_initialActualSpectralSources_integrable_and_budget
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b : ℝ) (hb : 0 < b) (hbT : b < T)
    (hE : IntervalIntegrable (velocityH3EnergyAt u) volume 0 b)
    (hDMeas : AEStronglyMeasurable
      (h3AuditInitialActualSpectralLaplacianTotal hH3)
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) b)))
    (hNMeas : AEStronglyMeasurable
      (h3AuditInitialActualSpectralLerayTotal hH3)
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) b))) :
    IntervalIntegrable (h3AuditInitialActualSpectralLaplacianTotal hH3)
      volume 0 b ∧
    IntervalIntegrable (h3AuditInitialActualSpectralLerayTotal hH3)
      volume 0 b ∧
    IntervalIntegrable
      (fun t => h3AuditInitialActualSpectralLaplacianTotal hH3 t -
        h3AuditInitialActualSpectralLerayTotal hH3 t) volume 0 b ∧
    (∫ t in (0 : ℝ)..b,
        ‖h3AuditInitialActualSpectralLaplacianTotal hH3 t -
          h3AuditInitialActualSpectralLerayTotal hH3 t‖) ≤
        (3 + h3AuditInitialLerayEnergyCoefficient) *
          ∫ t in (0 : ℝ)..b, velocityH3EnergyAt u t := by
  exact h3Audit_initialEnergyMajorant_diffusionLeray_integrable_and_budget
    (velocityH3EnergyAt u)
    (h3AuditInitialActualSpectralLaplacianTotal hH3)
    (h3AuditInitialActualSpectralLerayTotal hH3)
    b 3 h3AuditInitialLerayEnergyCoefficient hb.le hE
    hDMeas hNMeas
    (h3Audit_initialActualSpectralLaplacian_norm_le_energy hH3 b hbT)
    (h3Audit_initialActualSpectralLeray_norm_le_energy hH3 b hbT)

end
end Euclidean
end Bridge
end PrimeTensor
