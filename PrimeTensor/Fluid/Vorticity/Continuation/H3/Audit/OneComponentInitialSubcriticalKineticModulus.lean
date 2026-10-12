import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialSubcriticalMomentumModulus

/-!
# Quantitative initial kinetic-energy modulus from physical L² momentum

The previous theorem gives the actual old physical L² Hilbert momentum's
initial right limit L and a subcritical growth-based rate of convergence.
The exact physical zeroth-order kinetic identity says

    velocityH3Energy0At u t = ‖old(t)‖²

at every strict positive time. We now transfer the physical momentum
estimate to the kinetic energy, using an elementary norm-square stability
bound in the real three-component L² Hilbert space.

The resulting kinetic limit is ‖L‖², with the explicit modulus

    |E₀(t) - ‖L‖²| ≤ δ(t) * (2 * ‖L‖ + δ(t)),
    δ(t) = (3 + C_L) * M * t^(1-α) / (1-α).

When L = 0 the estimate is quadratic in δ. No equality between L and
the stipulated physical initial velocity is asserted.

The subcritical H³ growth premise and the old-velocity temporal
joint-continuity premise remain independent. This is a conditional
initial-time estimate, not unconditional Navier–Stokes regularity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- Stability of the squared physical L² Hilbert norm under an L²
momentum increment. No initial-data or PDE hypotheses enter this lemma. -/
private theorem h3Audit_initialPhysicalHilbert_normSq_stability
    (x y : H3PhysicalRealFinVectorL2Hilbert) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤
      ‖x - y‖ * (‖x‖ + ‖y‖) := by
  have hPositive : 0 ≤ ‖x‖ + ‖y‖ :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    |‖x‖ ^ 2 - ‖y‖ ^ 2| =
        |‖x‖ - ‖y‖| * (‖x‖ + ‖y‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg hPositive]
      ac_rfl
    _ ≤ ‖x - y‖ * (‖x‖ + ‖y‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le x y) hPositive

/-- The physical kinetic energy has an explicit two-time modulus
involving only the actual old momentum norms and the subcritical H³
envelope. It does not require a separately chosen initial trace. -/
theorem h3Audit_initialSubcriticalEnergyRate_kinetic_twoTimeModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (b α M : ℝ) (hb : 0 < b) (hbT : b < T)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hM : 0 ≤ M)
    (hRate : ∀ r : ℝ, r ∈ Set.Ioc (0 : ℝ) b →
      velocityH3EnergyAt u r ≤ M * r ^ (-α))
    (s t : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) b)
    (ht : t ∈ Set.Ioo (0 : ℝ) b) (hst : s ≤ t) :
    |velocityH3Energy0At u t - velocityH3Energy0At u s| ≤
      (((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
        ((t ^ (-α + 1) - s ^ (-α + 1)) / (-α + 1))) *
      (‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ +
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s‖) := by
  let F : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  have hsT : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨hs.1, lt_trans hs.2 hbT⟩
  have htT : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨ht.1, lt_trans ht.2 hbT⟩
  have hEnergyS : velocityH3Energy0At u s = ‖F s‖ ^ 2 :=
    (h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
      hH3 s hsT).symm
  have hEnergyT : velocityH3Energy0At u t = ‖F t‖ ^ 2 :=
    (h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
      hH3 t htT).symm
  have hIncrement :=
    h3Audit_initialSubcriticalEnergyRate_physicalMomentum_twoTimeModulus
      hH3 hOldJoint b α M hb hbT hα0 hα1 hM hRate
      s t hs ht hst
  calc
    |velocityH3Energy0At u t - velocityH3Energy0At u s| =
        |‖F t‖ ^ 2 - ‖F s‖ ^ 2| := by
      rw [hEnergyT, hEnergyS]
    _ ≤ ‖F t - F s‖ * (‖F t‖ + ‖F s‖) :=
      h3Audit_initialPhysicalHilbert_normSq_stability (F t) (F s)
    _ ≤
        (((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
          ((t ^ (-α + 1) - s ^ (-α + 1)) / (-α + 1))) *
          (‖F t‖ + ‖F s‖) :=
      mul_le_mul_of_nonneg_right hIncrement
        (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Quantitative right convergence of actual kinetic energy, with the
limit identified exactly as the squared norm of the *derived* physical
L² momentum limit. No equation with the separately declared time-zero
kinetic datum is used. -/
theorem h3Audit_initialSubcriticalEnergyRate_kinetic_rightLimitRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (b α M : ℝ) (hb : 0 < b) (hbT : b < T)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hM : 0 ≤ M)
    (hRate : ∀ r : ℝ, r ∈ Set.Ioc (0 : ℝ) b →
      velocityH3EnergyAt u r ≤ M * r ^ (-α)) :
    ∃ L : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      Tendsto (velocityH3Energy0At u)
        (𝓝[>] (0 : ℝ)) (𝓝 (‖L‖ ^ 2)) ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        |velocityH3Energy0At u t - ‖L‖ ^ 2| ≤
          (((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
            (t ^ (-α + 1) / (-α + 1))) *
          (2 * ‖L‖ +
            ((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
              (t ^ (-α + 1) / (-α + 1))) := by
  obtain ⟨L, hL, hMomentumRate⟩ :=
    h3Audit_initialSubcriticalEnergyRate_physicalMomentum_rightLimitRate
      hH3 hOldJoint b α M hb hbT hα0 hα1 hM hRate
  let F : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  have hNormLimit : Tendsto (fun t : ℝ => ‖F t‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (‖L‖ ^ 2)) :=
    (continuous_norm.pow 2).continuousAt.tendsto.comp hL
  have hStrict : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with t ht0 htb
    exact ⟨ht0, htb⟩
  have hEnergyEventually :
      (velocityH3Energy0At u) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t : ℝ => ‖F t‖ ^ 2) := by
    filter_upwards [hStrict] with t ht
    have htT : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨ht.1, lt_trans ht.2 hbT⟩
    exact (h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
      hH3 t htT).symm
  refine ⟨L, hL, hNormLimit.congr' hEnergyEventually.symm, ?_⟩
  intro t ht
  let K : ℝ := (3 + h3AuditInitialLerayEnergyCoefficient) * M
  let β : ℝ := -α + 1
  let δ : ℝ := K * (t ^ β / β)
  have hβ : 0 < β := by
    dsimp only [β]
    linarith only [hα1]
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg
      (by linarith only [h3AuditInitialLerayEnergyCoefficient_nonneg]) hM
  have hδ : 0 ≤ δ := by
    dsimp only [δ]
    exact mul_nonneg hK
      (div_nonneg (Real.rpow_nonneg ht.1.le β) hβ.le)
  have hMomentum : ‖F t - L‖ ≤ δ := by
    simpa only [F, δ, K, β] using hMomentumRate t ht
  have hUpper : ‖F t‖ ≤ δ + ‖L‖ := by
    calc
      ‖F t‖ = ‖(F t - L) + L‖ := by rw [sub_add_cancel]
      _ ≤ ‖F t - L‖ + ‖L‖ := norm_add_le _ _
      _ ≤ δ + ‖L‖ := add_le_add hMomentum (le_refl ‖L‖)
  have hFactor : ‖F t‖ + ‖L‖ ≤ 2 * ‖L‖ + δ := by
    linarith only [hUpper]
  have htT : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨ht.1, lt_trans ht.2 hbT⟩
  have hEnergy : velocityH3Energy0At u t = ‖F t‖ ^ 2 :=
    (h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
      hH3 t htT).symm
  change |velocityH3Energy0At u t - ‖L‖ ^ 2| ≤
    δ * (2 * ‖L‖ + δ)
  calc
    |velocityH3Energy0At u t - ‖L‖ ^ 2| =
        |‖F t‖ ^ 2 - ‖L‖ ^ 2| := by rw [hEnergy]
    _ ≤ ‖F t - L‖ * (‖F t‖ + ‖L‖) :=
      h3Audit_initialPhysicalHilbert_normSq_stability (F t) L
    _ ≤ δ * (‖F t‖ + ‖L‖) :=
      mul_le_mul_of_nonneg_right hMomentum
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ δ * (2 * ‖L‖ + δ) :=
      mul_le_mul_of_nonneg_left hFactor hδ

end
end Euclidean
end Bridge
end PrimeTensor
