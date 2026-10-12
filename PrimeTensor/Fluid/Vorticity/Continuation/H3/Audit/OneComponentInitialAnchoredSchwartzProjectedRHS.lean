import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialWeakIdentifiedQuantitativeTrace
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialProjectedRHSWeakFTCControl
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialCompactWeakFTC

/-!
# Identify the initial physical momentum trace through anchored Schwartz momentum

The existing subcritical H³ energy rate controls the genuine reconstructed
physical source G = Δu - Leray in Bochner L¹ and yields a strong right limit
L of the physical velocity together with a quantitative momentum modulus.

The preceding weak-identification audit imposed convergence against ALL
physical Hilbert tests to the prescribed u(0). Here that independent
all-test weak-limit premise is replaced by a PDE-facing, initial-anchored
weak momentum equation ONLY against real Schwartz vector tests:

  ⟪F(t), ψ⟫ - ⟪u(0), ψ⟫ = ∫₀ᵗ ⟪G(s), ψ⟫ ds.

Bochner L¹ makes the scalar primitive tend to zero; density of Schwartz
vectors forces L = u(0). The previously proved physical momentum and kinetic
right-limit moduli then hold for the *actual* initial velocity.

The anchored equation is an independent initial-data compatibility
requirement. The existing positive-time Hilbert FTC only proves increments
between strictly positive times, not the anchored equation at time zero.
This file does not derive that anchored identity from positive-time H³
admissibility, nor does it establish unconditional regularity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- Weak momentum evolution from the prescribed initial Hilbert datum,
tested only against physical three-component real Schwartz vectors. -/
def H3AuditInitialAnchoredSchwartzPhysicalMomentum
    (F G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) : Prop :=
  ∀ (Φ : H3PhysicalRealFinVectorSchwartz) (t : ℝ),
    t ∈ Set.Ioo (0 : ℝ) b →
      inner ℝ (F t)
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) -
        inner ℝ U₀
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) =
      ∫ s in (0 : ℝ)..t,
        inner ℝ (G s)
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)

/-- Initial-anchored Schwartz momentum evolution with a single Bochner
integrable physical source forces right convergence of each Schwartz
pairing to the stipulated initial value. -/
theorem h3Audit_initialAnchoredSchwartzSource_weakPairing
    (F G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 < b)
    (hG : IntervalIntegrable G volume 0 b)
    (hAnchor : H3AuditInitialAnchoredSchwartzPhysicalMomentum F G U₀ b) :
    ∀ Φ : H3PhysicalRealFinVectorSchwartz,
      Tendsto
        (fun t : ℝ =>
          inner ℝ (F t)
            (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ U₀
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))) := by
  intro Φ
  let ψ : H3PhysicalRealFinVectorL2Hilbert :=
    h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ
  let g : ℝ → ℝ := fun s => inner ℝ (G s) ψ
  have hScalar : IntervalIntegrable g volume 0 b := by
    dsimp only [g]
    simpa only [innerSL_apply_apply] using
      (h3Audit_initialProjectedRHS_scalarPairing_intervalIntegrable
        G b hb.le hG ψ)
  have hPrimitive : Tendsto
      (fun t : ℝ => ∫ s in (0 : ℝ)..t, g s)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    h3Audit_initialScalarWeakPrimitive_tendsto_zero g b hb hScalar
  have hStrict : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with t ht0 htb
    exact ⟨ht0, htb⟩
  have hEq :
      (fun t : ℝ =>
        inner ℝ (F t) ψ - inner ℝ U₀ ψ)
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ∫ s in (0 : ℝ)..t, g s) := by
    filter_upwards [hStrict] with t ht
    exact hAnchor Φ t ht
  have hDiff : Tendsto
      (fun t : ℝ => inner ℝ (F t) ψ - inner ℝ U₀ ψ)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    hPrimitive.congr' hEq.symm
  have hSum := hDiff.add
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => inner ℝ U₀ ψ)
      (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ U₀ ψ)))
  simpa only [ψ, sub_add_cancel, zero_add] using hSum

/-- Since Schwartz test vectors are dense in the exact physical Hilbert
carrier, the strong right limit and the anchored weak initial value
must coincide. No strong initial-time trace was assumed. -/
theorem h3Audit_initialStrongPhysicalLimit_eq_of_anchoredSchwartzSource
    (F G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (L U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 < b)
    (hG : IntervalIntegrable G volume 0 b)
    (hAnchor : H3AuditInitialAnchoredSchwartzPhysicalMomentum F G U₀ b)
    (hL : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    L = U₀ := by
  have hWeak :=
    h3Audit_initialAnchoredSchwartzSource_weakPairing
      F G U₀ b hb hG hAnchor
  apply DenseRange.eq_of_inner_left ℝ
    denseRange_h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert
  intro Φ
  let ψ : H3PhysicalRealFinVectorL2Hilbert :=
    h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ
  have hInnerContinuous :
      Continuous (fun z : H3PhysicalRealFinVectorL2Hilbert =>
        inner ℝ z ψ) :=
    continuous_id.inner continuous_const
  exact tendsto_nhds_unique
    (hInnerContinuous.continuousAt.tendsto.comp hL)
    (hWeak Φ)

/-- The reconstructed physical projected RHS, a subcritical H³ energy
envelope, and ONE initial-anchored Schwartz momentum contract identify
the quantitative right limit with the original physical initial velocity.
No full-Hilbert weak convergence is postulated. -/
theorem h3Audit_initialSubcriticalAnchoredSchwartz_physicalMomentumRate
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
    (hAnchor : H3AuditInitialAnchoredSchwartzPhysicalMomentum
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (fun s : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0) b) :
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
  have hG :
      IntervalIntegrable
        (fun s : ℝ =>
          h3AuditInitialActualSpectralLaplacianTotal hH3 s -
            h3AuditInitialActualSpectralLerayTotal hH3 s)
        volume 0 b :=
    (h3Audit_initialSubcriticalEnergyRate_projectedRHS_integrable_and_mass
      hH3 b α M hb hbT hα0 hα1 hM hRate).1
  have hIdentify :
      L = h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0 :=
    h3Audit_initialStrongPhysicalLimit_eq_of_anchoredSchwartzSource
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (fun s : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s)
      L (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
      b hb hG hAnchor hL
  constructor
  · simpa only [← hIdentify] using hL
  · intro t ht
    simpa only [← hIdentify] using hModulus t ht

/-- The same anchored Schwartz physical momentum contract identifies the
quantitative kinetic right trace with the exact kinetic energy of the
prescribed physical u(0), using no independent weak-L² right-limit premise. -/
theorem h3Audit_initialSubcriticalAnchoredSchwartz_kineticRate
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
    (hAnchor : H3AuditInitialAnchoredSchwartzPhysicalMomentum
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (fun s : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0) b) :
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
  have hG :
      IntervalIntegrable
        (fun s : ℝ =>
          h3AuditInitialActualSpectralLaplacianTotal hH3 s -
            h3AuditInitialActualSpectralLerayTotal hH3 s)
        volume 0 b :=
    (h3Audit_initialSubcriticalEnergyRate_projectedRHS_integrable_and_mass
      hH3 b α M hb hbT hα0 hα1 hM hRate).1
  have hIdentify :
      L = h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0 :=
    h3Audit_initialStrongPhysicalLimit_eq_of_anchoredSchwartzSource
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (fun s : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s)
      L (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
      b hb hG hAnchor hL
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
