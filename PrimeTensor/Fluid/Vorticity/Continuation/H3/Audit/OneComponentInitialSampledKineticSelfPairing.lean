import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialKineticSelfPairingIdentification

/-!
# A single initial sequence suffices for physical kinetic/self-pairing identification

The prior physical trace criterion asked for a kinetic ceiling eventually
at every small time and convergence of the initial-vector self-pairing
along the full right-neighborhood filter.

The projected-source H³ rate already supplies a strong right Hilbert
momentum limit L and a kinetic right limit ‖L‖². Therefore both initial
compatibility tests can be weakened to ONE common sequence τₙ → 0+:

  E₀(τₙ) ≤ E₀(0) eventually,
  ⟪old(τₙ),U₀⟫ → ‖U₀‖².

Taking limits gives ‖L‖² ≤ ‖U₀‖² and
⟪L,U₀⟫ = ‖U₀‖², so the previously established polarization identity
proves L = U₀. It then transfers the exact quantitative physical
momentum and kinetic estimates to the actual initial velocity.

Neither sampled kinetic compatibility nor the one scalar sampled weak
pairing is derived from the open-time PDE by this module. Subcritical
H³ growth and old temporal joint-continuity also remain explicit.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- A scalar energy observable with a known strong-limit energy and
eventually bounded samples, together with ONE sampled initial-vector
correlation, identifies the strong Hilbert limit. No pointwise initial
energy inequality or all-time weak trace is needed. -/
theorem h3Audit_initialStrongHilbertLimit_eq_of_sampledKineticSelfPairing
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (E : ℝ → ℝ)
    (L U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)))
    (hStrong : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hKinetic : Tendsto E (𝓝[>] (0 : ℝ)) (𝓝 (‖L‖ ^ 2)))
    (hEnergySamples : ∀ᶠ n : ℕ in atTop, E (τ n) ≤ ‖U₀‖ ^ 2)
    (hSelfSample : Tendsto
      (fun n : ℕ => inner ℝ (F (τ n)) U₀)
      atTop (𝓝 (‖U₀‖ ^ 2))) :
    L = U₀ := by
  have hEnergySequence : Tendsto (fun n : ℕ => E (τ n))
      atTop (𝓝 (‖L‖ ^ 2)) := by
    simpa only [Function.comp_def] using hKinetic.comp hτ
  have hLimitEnergy : ‖L‖ ^ 2 ≤ ‖U₀‖ ^ 2 :=
    le_of_tendsto_of_tendsto hEnergySequence
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => ‖U₀‖ ^ 2)
        atTop (𝓝 (‖U₀‖ ^ 2))) hEnergySamples
  have hPhysicalSequence : Tendsto (fun n : ℕ => F (τ n))
      atTop (𝓝 L) := by
    simpa only [Function.comp_def] using hStrong.comp hτ
  have hInnerContinuous :
      Continuous (fun V : H3PhysicalRealFinVectorL2Hilbert =>
        inner ℝ V U₀) :=
    continuous_id.inner continuous_const
  have hPairLimit :
      Tendsto (fun n : ℕ => inner ℝ (F (τ n)) U₀)
        atTop (𝓝 (inner ℝ L U₀)) :=
    hInnerContinuous.continuousAt.tendsto.comp hPhysicalSequence
  have hPairEquality : inner ℝ L U₀ = ‖U₀‖ ^ 2 :=
    tendsto_nhds_unique hPairLimit hSelfSample
  exact h3Audit_initialHilbert_identify_of_kineticCeiling_and_selfPairing
    L U₀ hLimitEnergy hPairEquality.ge

/-- Sampled physical initial compatibility is required along only one
right-zero time sequence. The energy upper bound is merely eventual on
the sequence, not on a whole initial time interval. The self-pairing
uses the known actual time-zero physical velocity. -/
def H3AuditInitialSampledKineticSelfPairingTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ)) : Prop :=
  ∃ τ : ℕ → ℝ,
    Tendsto τ atTop (𝓝[>] (0 : ℝ)) ∧
    (∀ᶠ n : ℕ in atTop,
      velocityH3Energy0At u (τ n) ≤ velocityH3Energy0At u 0) ∧
    Tendsto
      (fun n : ℕ =>
        inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n))
          (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0))
      atTop
      (𝓝 (‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2))

/-- The subcritical initial projected RHS creates both a strong
physical momentum right limit and a kinetic right limit. One sampled
kinetic inequality and one sampled self-pairing then identify both with
the actual physical time-zero data, preserving the explicit moduli. -/
theorem h3Audit_initialSubcriticalSampledKineticSelfPairing_identifies_physicalAndKineticRate
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
    (hInitial : H3AuditInitialSampledKineticSelfPairingTrace
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
  obtain ⟨τ, hτ, hKineticSamples, hSelfSample⟩ := hInitial
  obtain ⟨L, hL, hKinetic, _hRateKinetic⟩ :=
    h3Audit_initialSubcriticalEnergyRate_kinetic_rightLimitRate
      hH3 hOldJoint b α M hb hbT hα0 hα1 hM hRate
  have hZero : ‖U₀‖ ^ 2 = velocityH3Energy0At u 0 :=
    h3Audit_initialActualPhysicalHilbertAtZero_norm_sq_eq_kineticEnergy
      hInt0 hMeas0
  have hSamples : ∀ᶠ n : ℕ in atTop,
      velocityH3Energy0At u (τ n) ≤ ‖U₀‖ ^ 2 := by
    simpa only [hZero] using hKineticSamples
  have hIdentify : L = U₀ :=
    h3Audit_initialStrongHilbertLimit_eq_of_sampledKineticSelfPairing
      F (velocityH3Energy0At u) L U₀ τ
      hτ hL hKinetic hSamples hSelfSample
  have hStrong : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
    simpa only [hIdentify] using hL
  have hWeak : ∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto
        (fun t : ℝ => inner ℝ (F t) ψ)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ U₀ ψ)) := by
    intro ψ
    have hInnerContinuous :
        Continuous (fun z : H3PhysicalRealFinVectorL2Hilbert =>
          inner ℝ z ψ) :=
      continuous_id.inner continuous_const
    exact hInnerContinuous.continuousAt.tendsto.comp hStrong
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
