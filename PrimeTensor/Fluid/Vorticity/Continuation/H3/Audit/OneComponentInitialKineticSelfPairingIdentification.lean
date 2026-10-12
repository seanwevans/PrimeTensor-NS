import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialDefectDirectionObstruction

/-!
# Identify the initial velocity from kinetic control and one fixed self-pairing

The subcritical projected physical source and old temporal joint continuity
supply an actual physical L² strong right limit L with a quantitative rate.
But that limit may differ from the stipulated initial velocity U₀ unless
initial-time compatibility is separately proved.

The earlier module tested an adaptive, unknown direction L - U₀ along one
initial sequence. This module instead uses only the *known initial vector U₀*:

1. the actual kinetic energy eventually stays below its initial value; and
2. the ONE scalar correlation ⟪F(t),U₀⟫ converges to ‖U₀‖².

The elementary polarization identity then gives

    ‖L-U₀‖² = ‖L‖² + ‖U₀‖² - 2⟪L,U₀⟫ = 0.

There is no all-Hilbert weak trace, no unknown defect test, and no new
nonlinear relative-energy residual. The two initial energy/correlation
inputs are independent requirements; they are *not* proved here from
positive-time Navier--Stokes H³ admissibility. Nor are the subcritical H³
rate or old-temporal joint continuity removed. In particular this module
does not establish unconditional Navier--Stokes regularity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- An approximate Hilbert energy ceiling and initial-vector correlation
floor control the squared defect, without requiring a full family of
weak tests or the unknown defect direction as a test vector. -/
theorem h3Audit_initialHilbert_energyCorrelation_defectBudget
    (L U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (e c : ℝ)
    (hEnergy : ‖L‖ ^ 2 ≤ ‖U₀‖ ^ 2 + e)
    (hCross : ‖U₀‖ ^ 2 ≤ inner ℝ L U₀ + c) :
    ‖L - U₀‖ ^ 2 ≤ e + 2 * c := by
  calc
    ‖L - U₀‖ ^ 2 =
        ‖L‖ ^ 2 - 2 * inner ℝ L U₀ + ‖U₀‖ ^ 2 :=
      norm_sub_sq_real L U₀
    _ ≤ e + 2 * c := by
      linarith only [hEnergy, hCross]

/-- Exact kinetic ceiling and lower initial self-correlation identify the
right limit with U₀. A single fixed vector suffices because the kinetic
ceiling rules out a perpendicular hidden component. -/
theorem h3Audit_initialHilbert_identify_of_kineticCeiling_and_selfPairing
    (L U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (hEnergy : ‖L‖ ^ 2 ≤ ‖U₀‖ ^ 2)
    (hCross : ‖U₀‖ ^ 2 ≤ inner ℝ L U₀) :
    L = U₀ := by
  have hBound : ‖L - U₀‖ ^ 2 ≤ (0 : ℝ) := by
    have h := h3Audit_initialHilbert_energyCorrelation_defectBudget
      L U₀ 0 0 (by simpa only [add_zero] using hEnergy)
        (by simpa only [add_zero] using hCross)
    simpa only [mul_zero, add_zero, zero_add] using h
  have hSquare : ‖L - U₀‖ ^ 2 = 0 :=
    le_antisymm hBound (sq_nonneg _)
  have hNormZero : ‖L - U₀‖ = 0 := by
    nlinarith only [hSquare, norm_nonneg (L - U₀)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hNormZero)

/-- A one-vector physical initial compatibility criterion: kinetic energy
is bounded by its *actual* initial value on a right-zero neighborhood,
and the pairing against the *known initial physical velocity* has its
prescribed initial right limit. These are independent analytic inputs. -/
def H3AuditInitialKineticCeilingSelfPairingTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ)) : Prop :=
  (∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
    velocityH3Energy0At u t ≤ velocityH3Energy0At u 0) ∧
  Tendsto
    (fun t : ℝ =>
      inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
        (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0))
    (𝓝[>] (0 : ℝ))
    (𝓝 (‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2))

/-- The actual kinetic upper bound and a single fixed initial-velocity
correlation test replace the previous adaptive defect-direction weak
sequence in the quantitative subcritical physical momentum/kinetic
convergence theorem. -/
theorem h3Audit_initialSubcriticalSelfPairing_identifies_physicalAndKineticRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b α M : ℝ) (hb : 0 < b) (hbT : b < T)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hM : 0 ≤ M)
    (hRate : ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) b →
      velocityH3EnergyAt u s ≤ M * s ^ (-α))
    (hInitial : H3AuditInitialKineticCeilingSelfPairingTrace
      hH3 hInt0 hMeas0) :
    (Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[>] (0 : ℝ))
        (𝓝 (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ≤
          ((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
            (t ^ (-α + 1) / (-α + 1))) ∧
    (Tendsto (velocityH3Energy0At u)
        (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3Energy0At u 0)) ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        |velocityH3Energy0At u t - velocityH3Energy0At u 0| ≤
          (((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
            (t ^ (-α + 1) / (-α + 1))) *
          (2 * ‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ +
            ((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
              (t ^ (-α + 1) / (-α + 1)))) := by
  let F : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let U₀ : H3PhysicalRealFinVectorL2Hilbert :=
    h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0
  obtain ⟨hCeiling, hSelfPairing⟩ := hInitial
  obtain ⟨L, hL, hKinetic, _hModulus⟩ :=
    h3Audit_initialSubcriticalEnergyRate_kinetic_rightLimitRate
      hH3 hOldJoint b α M hb hbT hα0 hα1 hM hRate
  have hZero : ‖U₀‖ ^ 2 = velocityH3Energy0At u 0 :=
    h3Audit_initialActualPhysicalHilbertAtZero_norm_sq_eq_kineticEnergy
      hInt0 hMeas0
  have hKineticBound : ‖L‖ ^ 2 ≤ ‖U₀‖ ^ 2 := by
    rw [hZero]
    exact le_of_tendsto_of_tendsto hKinetic
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => velocityH3Energy0At u 0)
          (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3Energy0At u 0)))
      hCeiling
  have hInnerContinuous :
      Continuous (fun z : H3PhysicalRealFinVectorL2Hilbert =>
        inner ℝ z U₀) :=
    continuous_id.inner continuous_const
  have hSelfLimit :
      Tendsto (fun t : ℝ => inner ℝ (F t) U₀)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ L U₀)) :=
    hInnerContinuous.continuousAt.tendsto.comp hL
  have hSelfEq : inner ℝ L U₀ = ‖U₀‖ ^ 2 :=
    tendsto_nhds_unique hSelfLimit hSelfPairing
  have hIdentify : L = U₀ :=
    h3Audit_initialHilbert_identify_of_kineticCeiling_and_selfPairing
      L U₀ hKineticBound hSelfEq.ge
  have hStrong : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
    simpa only [hIdentify] using hL
  have hWeak : ∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto
        (fun t : ℝ => inner ℝ (F t) ψ)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ U₀ ψ)) := by
    intro ψ
    have hPairContinuous :
        Continuous (fun z : H3PhysicalRealFinVectorL2Hilbert =>
          inner ℝ z ψ) :=
      continuous_id.inner continuous_const
    exact hPairContinuous.continuousAt.tendsto.comp hStrong
  exact ⟨
    h3Audit_initialSubcriticalEnergyRate_weakIdentifies_physicalMomentumRate
      hH3 hOldJoint hInt0 hMeas0 b α M hb hbT hα0 hα1 hM
      hRate hWeak,
    h3Audit_initialSubcriticalEnergyRate_weakIdentifies_kineticRate
      hH3 hOldJoint hInt0 hMeas0 b α M hb hbT hα0 hα1 hM
      hRate hWeak⟩

end
end Euclidean
end Bridge
end PrimeTensor
