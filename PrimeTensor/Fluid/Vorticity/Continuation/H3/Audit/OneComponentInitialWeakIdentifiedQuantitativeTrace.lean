import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialSubcriticalKineticModulus
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialWeakL2CofinalKineticControl

/-!
# Identify quantitative initial momentum and kinetic limits by weak physical data

The subcritical projected-source condition establishes an actual old physical
L² right limit L, with a quantitative physical momentum rate, and the precise
kinetic limit ‖L‖². These statements did not identify L with u(0).

Here only the genuine initial weak L² pairing condition is added. Strong
convergence to L implies scalar convergence against every Hilbert test; the
weak initial-value limit against the *same* tests forces L to equal the
actual time-zero three-component physical L² jet. Thus the previously proved
moduli hold for the true zero-time datum, without postulating a strong initial
trace or using the old/selected relative-energy residual.

The actual initial kinetic energy is identified exactly with the squared norm
of the initial real physical L² Hilbert jet, using the already-proved
zeroth-order jet energy identity.

The weak initial pairing, subcritical H³ envelope, and old temporal joint
continuity are independent premises, not consequences of H³ admissibility.
No unconditional global regularity result follows.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- A strong right physical Hilbert limit is necessarily the stipulated
weak initial Hilbert limit. This is a general uniqueness principle and uses
no PDE or energy inequalities. -/
theorem h3Audit_initialStrongPhysicalHilbertLimit_eq_of_weakInitialPairings
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (L U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (hStrong : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hWeak : ∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (fun t : ℝ => inner ℝ (F t) ψ)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ U₀ ψ))) :
    L = U₀ := by
  have hInnerContinuous (ψ : H3PhysicalRealFinVectorL2Hilbert) :
      Continuous (fun z : H3PhysicalRealFinVectorL2Hilbert =>
        inner ℝ z ψ) :=
    continuous_id.inner continuous_const
  have hPair (ψ : H3PhysicalRealFinVectorL2Hilbert) :
      inner ℝ L ψ = inner ℝ U₀ ψ :=
    tendsto_nhds_unique
      ((hInnerContinuous ψ).continuousAt.tendsto.comp hStrong)
      (hWeak ψ)
  have hZeroInner : inner ℝ (L - U₀) (L - U₀) = 0 := by
    rw [inner_sub_left]
    exact sub_eq_zero.mpr (hPair (L - U₀))
  have hNormSq : ‖L - U₀‖ ^ 2 = 0 := by
    simpa only [real_inner_self_eq_norm_sq] using hZeroInner
  have hNormZero : ‖L - U₀‖ = 0 := by
    nlinarith [norm_nonneg (L - U₀)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hNormZero)

/-- The physical kinetic energy of the *actual initial velocity* is the
squared norm of its three-component real physical L² Hilbert realization.
Unlike a positive-time identity, this needs only the explicit integrability
and measurability of the time-zero snapshot. -/
theorem h3Audit_initialActualPhysicalHilbertAtZero_norm_sq_eq_kineticEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ)) :
    ‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2 =
      velocityH3Energy0At u 0 := by
  let U₀ : H3PhysicalRealFinVectorL2Hilbert :=
    h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0
  have hCoord (j : Fin 3) :
      U₀ j = velocityH3L2JetAt u 0 hInt0 hMeas0 (Sum.inl j) := by
    change velocityH3L2JetAt u 0 hInt0 hMeas0 (h3JetSlot0 j) =
      velocityH3L2JetAt u 0 hInt0 hMeas0 (Sum.inl j)
    rfl
  calc
    ‖U₀‖ ^ 2 = ∑ j : Fin 3, ‖U₀ j‖ ^ 2 :=
      PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => H3ScalarL2) U₀
    _ = ∑ j : H3JetIndex0,
          ‖velocityH3L2JetAt u 0 hInt0 hMeas0 (Sum.inl j)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hCoord j]
    _ = velocityH3Energy0At u 0 :=
      velocityH3L2JetAt_squareEnergy0_eq hInt0 hMeas0

/-- A genuine weak initial L² velocity trace identifies the subcritical
strong physical momentum right limit with the actual u(0), preserving its
quantitative `t^(1-α)` convergence rate. Neither a strong trace nor the
nonlinear relative-energy comparison is an input. -/
theorem h3Audit_initialSubcriticalEnergyRate_weakIdentifies_physicalMomentumRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b α M : ℝ) (hb : 0 < b) (hbT : b < T)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hM : 0 ≤ M)
    (hRate : ∀ r : ℝ, r ∈ Set.Ioc (0 : ℝ) b →
      velocityH3EnergyAt u r ≤ M * r ^ (-α))
    (hWeak : ∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto
        (fun t : ℝ =>
          inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 t) ψ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ
          (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0) ψ))) :
    Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) ∧
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
        h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ≤
      ((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
        (t ^ (-α + 1) / (-α + 1)) := by
  obtain ⟨L, hL, hModulus⟩ :=
    h3Audit_initialSubcriticalEnergyRate_physicalMomentum_rightLimitRate
      hH3 hOldJoint b α M hb hbT hα0 hα1 hM hRate
  have hIdentify : L =
      h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0 :=
    h3Audit_initialStrongPhysicalHilbertLimit_eq_of_weakInitialPairings
      (h3AuditInitialOldPhysicalHilbertTotal hH3) L
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
      hL hWeak
  constructor
  · simpa only [← hIdentify] using hL
  · intro t ht
    simpa only [← hIdentify] using hModulus t ht

/-- With the same weak initial-value condition, the quantitative physical
kinetic trace is now identified with the exact stipulated time-zero kinetic
energy, not merely an unknown squared Hilbert norm. -/
theorem h3Audit_initialSubcriticalEnergyRate_weakIdentifies_kineticRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b α M : ℝ) (hb : 0 < b) (hbT : b < T)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hM : 0 ≤ M)
    (hRate : ∀ r : ℝ, r ∈ Set.Ioc (0 : ℝ) b →
      velocityH3EnergyAt u r ≤ M * r ^ (-α))
    (hWeak : ∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto
        (fun t : ℝ =>
          inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 t) ψ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ
          (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0) ψ))) :
    Tendsto (velocityH3Energy0At u)
      (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3Energy0At u 0)) ∧
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      |velocityH3Energy0At u t - velocityH3Energy0At u 0| ≤
        (((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
          (t ^ (-α + 1) / (-α + 1))) *
        (2 * ‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ +
          ((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
            (t ^ (-α + 1) / (-α + 1))) := by
  obtain ⟨L, hL, hKinetic, hModulus⟩ :=
    h3Audit_initialSubcriticalEnergyRate_kinetic_rightLimitRate
      hH3 hOldJoint b α M hb hbT hα0 hα1 hM hRate
  have hIdentify : L =
      h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0 :=
    h3Audit_initialStrongPhysicalHilbertLimit_eq_of_weakInitialPairings
      (h3AuditInitialOldPhysicalHilbertTotal hH3) L
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
      hL hWeak
  have hEnergyZero : ‖L‖ ^ 2 = velocityH3Energy0At u 0 := by
    rw [hIdentify]
    exact h3Audit_initialActualPhysicalHilbertAtZero_norm_sq_eq_kineticEnergy
      hInt0 hMeas0
  constructor
  · simpa only [hEnergyZero] using hKinetic
  · intro t ht
    have hRateAt := hModulus t ht
    rw [hEnergyZero] at hRateAt
    simpa only [hIdentify] using hRateAt

end
end Euclidean
end Bridge
end PrimeTensor
