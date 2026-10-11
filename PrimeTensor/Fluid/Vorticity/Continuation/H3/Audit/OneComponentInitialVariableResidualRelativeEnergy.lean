import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialVanishingDefectRelativeEnergy

/-!
# Initial uniqueness from variable coefficients and controlled residual profiles

The previous initial comparison uses one fixed Gronwall coefficient `K` and
one approximation defect `δ n` independent of physical time. Actual PDE
cutoff/pressure/commutator estimates can instead have coefficients `κ n`
and time-dependent residuals `ρ n t`.

This module allows any coefficients bounded above by one finite `K`, and any
residual profile bounded above on the initial interval by a sequence `δ`
converging to zero. Nonnegativity of the *physical scalar relative energy*
ensures nonnegativity of its forward integral, so the variable-coefficient
estimate implies the earlier uniform approximate estimate. The existing
Gronwall/physical-decoder chain then yields canonical overlap.

Uniform coefficient bounds, vanishing residual budgets, scalar-energy
continuity at the actual zero endpoint, and the approximate PDE inequality
remain independent analytic obligations. No assertion of unconditional
Navier--Stokes initial uniqueness or terminal endpoint regularity is made.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- Collapse variable comparison coefficients and time-dependent residuals
into one exact integral relative-energy inequality. The integral is
nonnegative because the energy is nonnegative and `t ≥ 0`. -/
theorem h3Audit_initialRelativeEnergy_exact_of_variableResidualBudget
    (e : ℝ → ℝ) (b K : ℝ)
    (κ δ : ℕ → ℝ) (ρ : ℕ → ℝ → ℝ)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (hκ : ∀ n : ℕ, κ n ≤ K)
    (hδ : Tendsto δ atTop (𝓝 (0 : ℝ)))
    (hBudget : ∀ (n : ℕ) (t : ℝ),
      t ∈ Set.Icc (0 : ℝ) b → ρ n t ≤ δ n)
    (hApprox : ∀ (n : ℕ) (t : ℝ),
      t ∈ Set.Icc (0 : ℝ) b →
        e t ≤ (κ n * ∫ s in (0 : ℝ)..t, e s) + ρ n t) :
    ∀ t ∈ Set.Icc (0 : ℝ) b,
      e t ≤ K * ∫ s in (0 : ℝ)..t, e s := by
  have hUniform : ∀ (n : ℕ) (t : ℝ),
      t ∈ Set.Icc (0 : ℝ) b →
        e t ≤ (K * ∫ s in (0 : ℝ)..t, e s) + δ n := by
    intro n t ht
    have hIntegralNonneg :
        0 ≤ ∫ s in (0 : ℝ)..t, e s := by
      exact intervalIntegral.integral_nonneg ht.1
        (fun s _hs => heNonneg s)
    have hCoefficient :
        κ n * (∫ s in (0 : ℝ)..t, e s) ≤
          K * (∫ s in (0 : ℝ)..t, e s) := by
      exact mul_le_mul_of_nonneg_right (hκ n) hIntegralNonneg
    calc
      e t ≤ (κ n * ∫ s in (0 : ℝ)..t, e s) + ρ n t :=
        hApprox n t ht
      _ ≤ (K * ∫ s in (0 : ℝ)..t, e s) + ρ n t :=
        add_le_add_left hCoefficient (ρ n t)
      _ ≤ (K * ∫ s in (0 : ℝ)..t, e s) + δ n :=
        add_le_add_right (hBudget n t ht) _
  exact h3Audit_initialRelativeEnergy_exact_of_vanishingDefects
    e b K δ hδ hUniform

/-- Scalar Gronwall under variable coefficient/residual profiles. -/
theorem h3Audit_initialScalarEnergy_integralGronwall_of_variableResidualBudget
    (e : ℝ → ℝ) (b K : ℝ)
    (κ δ : ℕ → ℝ) (ρ : ℕ → ℝ → ℝ)
    (hb : 0 < b)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (heCont : ContinuousOn e (Set.Icc (0 : ℝ) b))
    (hκ : ∀ n : ℕ, κ n ≤ K)
    (hδ : Tendsto δ atTop (𝓝 (0 : ℝ)))
    (hBudget : ∀ (n : ℕ) (t : ℝ),
      t ∈ Set.Icc (0 : ℝ) b → ρ n t ≤ δ n)
    (hApprox : ∀ (n : ℕ) (t : ℝ),
      t ∈ Set.Icc (0 : ℝ) b →
        e t ≤ (κ n * ∫ s in (0 : ℝ)..t, e s) + ρ n t)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b) :
    e t = 0 := by
  exact h3Audit_initialScalarEnergy_integralGronwall
    e b K hb heNonneg heCont
    (h3Audit_initialRelativeEnergy_exact_of_variableResidualBudget
      e b K κ δ ρ heNonneg hκ hδ hBudget hApprox) t ht

/-- PDE-facing initial relative-energy data with approximation-dependent
coefficients and time-dependent residual errors. The only residual
condition is a uniform *upper* budget converging to zero. -/
def H3AuditInitialCanonicalVariableResidualRelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b : ℝ),
    0 < b ∧ b < T ∧
    b ≤ h3FinHeatLerayRestartRadius 1 A ∧
    ∃ (K : ℝ) (κ δ : ℕ → ℝ) (ρ : ℕ → ℝ → ℝ),
      (∀ n : ℕ, κ n ≤ K) ∧
      Tendsto δ atTop (𝓝 (0 : ℝ)) ∧
      (∀ (n : ℕ) (t : ℝ),
        t ∈ Set.Icc (0 : ℝ) b → ρ n t ≤ δ n) ∧
      ContinuousOn
        (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2)
        (Set.Icc (0 : ℝ) b) ∧
      ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) b →
        ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
        (κ n * ∫ s in (0 : ℝ)..t,
          ‖h3AuditInitialCanonicalPhysicalDifference
            hH3 hFourier0 A hA hU₀ s‖ ^ 2) + ρ n t

/-- Variable coefficients and controlled residual profiles recover the
previous exact scalar relative-energy data, hence physical uniqueness. -/
theorem h3Audit_initialVariableResidual_implies_scalarRelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalVariableResidualRelativeEnergyData hH3) :
    H3AuditInitialCanonicalScalarRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, κ, δ, ρ,
    hκ, hδ, hBudget, hScalar, hApprox⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hScalar, ?_⟩
  exact h3Audit_initialRelativeEnergy_exact_of_variableResidualBudget
    (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
      hH3 hFourier0 A hA hU₀ t‖ ^ 2)
    b K κ δ ρ
    (fun s => sq_nonneg _)
    hκ hδ hBudget hApprox

/-- The earlier fixed-coefficient, uniform-defect data is a special case
of the new contract (constant coefficient and residual profile). -/
theorem h3Audit_initialVanishingDefect_implies_variableResidualData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalVanishingDefectRelativeEnergyData hH3) :
    H3AuditInitialCanonicalVariableResidualRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, δ, hδ, hScalar, hApprox⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, (fun _ : ℕ => K), δ,
    (fun n _t => δ n), ?_, hδ, ?_, hScalar, ?_⟩
  · intro n
    exact le_refl K
  · intro n t ht
    exact le_refl (δ n)
  · intro n t ht
    exact hApprox n t ht

/-- Canonical initial compact-test agreement from controlled PDE residuals. -/
theorem h3Audit_initialVariableResidual_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalVariableResidualRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialScalarRelativeEnergy_implies_compactWeakComparisonData
    hH3 (h3Audit_initialVariableResidual_implies_scalarRelativeEnergyData
      hH3 hData)

/-- Physical initial L² and H³ energy right traces from variable residuals. -/
theorem h3Audit_initialVariableResidual_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalVariableResidualRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialScalarRelativeEnergy_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialVariableResidual_implies_scalarRelativeEnergyData
      hH3 hData)

/-- The transverse physical-space conclusion continues to require the
independent terminal strong-H³ vorticity endpoint. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialVariableResidual
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalVariableResidualRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialScalarRelativeEnergy
    hH3 hClass i hPhysical
    (h3Audit_initialVariableResidual_implies_scalarRelativeEnergyData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
