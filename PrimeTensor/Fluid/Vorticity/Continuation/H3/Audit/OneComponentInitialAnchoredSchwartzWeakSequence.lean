import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialAnchoredSchwartzProjectedRHS
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialScalarWeakSequenceDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialCanonicalWeakFTCAbsoluteTransfer

/-!
# Initial anchored Schwartz momentum from positive-time evolution and weak sequences

On each strict positive-time interval the actual physical projected source
controls the Schwartz momentum derivative. Under a subcritical near-zero H³
energy rate that source is Bochner L¹. The remaining integration constant is
identified from one weak right-approaching sequence for each Schwartz test.

The existing scalar initial-FTC-from-sequence theorem then derives the
initial-anchored equation. Combined with the previously proved anchored
Schwartz bridge, the quantitative physical momentum and kinetic-energy rates
are identified with the actual initial velocity/energy.

This does NOT derive the weak initial-value sequences from the bare
positive-time H³ path. Their existence remains a separate datum; the strong
right limit and the anchored initial FTC are not assumed. No terminal
regularity assertion is made.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- Weak initial data along one positive-time sequence for each Schwartz
probe. The sequence may depend on the test and must approach zero from the
right. No continuous-time weak trace is assumed. -/
def H3AuditInitialSchwartzWeakCofinalSequence
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (U₀ : H3PhysicalRealFinVectorL2Hilbert) : Prop :=
  ∀ Φ : H3PhysicalRealFinVectorSchwartz,
    ∃ τ : ℕ → ℝ,
      Tendsto τ atTop (𝓝[>] (0 : ℝ)) ∧
      Tendsto
        (fun n : ℕ => inner ℝ (F (τ n))
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
        atTop
        (𝓝 (inner ℝ U₀
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)))

/-- Bochner-integrable positive-time evolution plus a weak initial sequence
for each Schwartz test implies the exact initial-anchored momentum equation.
This is a direct specialization of the previously proved scalar FTC theorem. -/
theorem h3Audit_initialAnchoredSchwartzSource_of_positiveDerivative_and_weakSequence
    (F G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 < b)
    (hG : IntervalIntegrable G volume 0 b)
    (hDerivative : ∀ (Φ : H3PhysicalRealFinVectorSchwartz) (s : ℝ),
      s ∈ Set.Ioo (0 : ℝ) b →
        HasDerivAt
          (fun t : ℝ => inner ℝ (F t)
            (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
          (inner ℝ (G s)
            (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)) s)
    (hSequence : H3AuditInitialSchwartzWeakCofinalSequence F U₀) :
    H3AuditInitialAnchoredSchwartzPhysicalMomentum F G U₀ b := by
  intro Φ t ht
  let ψ : H3PhysicalRealFinVectorL2Hilbert :=
    h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ
  let f : ℝ → ℝ := fun s => inner ℝ (F s) ψ
  let g : ℝ → ℝ := fun s => inner ℝ (G s) ψ
  have hg : IntervalIntegrable g volume 0 b := by
    dsimp only [g]
    simpa only [innerSL_apply_apply] using
      (h3Audit_initialProjectedRHS_scalarPairing_intervalIntegrable
        G b hb.le hG ψ)
  obtain ⟨τ, hτ, hWeak⟩ := hSequence Φ
  have hDeriv : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b →
      HasDerivAt f (g s) s := by
    intro s hs
    exact hDerivative Φ s hs
  change f t - inner ℝ U₀ ψ = ∫ s in (0 : ℝ)..t, g s
  exact h3Audit_initialScalarWeakFTC_of_interiorDerivative_and_sequence
    f g (inner ℝ U₀ ψ) b hb hg hDeriv τ hτ hWeak t ht

/-- The actual projected diffusion-minus-Leray source has an anchored
Schwartz momentum equation when its positive-time derivative is known and
the original initial data are reached along weak Schwartz-test sequences.
No initial-anchored equation is posited separately. -/
theorem h3Audit_initialSubcriticalEnergyRate_anchoredSchwartz_of_weakSequence
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
    (hSequence : H3AuditInitialSchwartzWeakCofinalSequence
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) :
    H3AuditInitialAnchoredSchwartzPhysicalMomentum
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (fun s : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0) b := by
  have hSource : IntervalIntegrable
      (fun s : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s)
      volume 0 b :=
    (h3Audit_initialSubcriticalEnergyRate_projectedRHS_integrable_and_mass
      hH3 b α M hb hbT hα0 hα1 hM hRate).1
  apply h3Audit_initialAnchoredSchwartzSource_of_positiveDerivative_and_weakSequence
    (h3AuditInitialOldPhysicalHilbertTotal hH3)
    (fun s : ℝ =>
      h3AuditInitialActualSpectralLaplacianTotal hH3 s -
        h3AuditInitialActualSpectralLerayTotal hH3 s)
    (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
    b hb hSource ?_ hSequence
  intro Φ s hs
  have hsT : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨hs.1, lt_trans hs.2 hbT⟩
  simpa only [innerSL_apply_apply] using
    (h3Audit_initialOldJoint_implies_SchwartzHasDerivAt_at_positiveTime
      hH3 hOldJoint Φ s hsT)

/-- With only per-test weak sequences at zero, subcritical H³ source growth
and the actual positive-time momentum evolution produce the identified
physical and kinetic right traces and their explicit quantitative moduli. -/
theorem h3Audit_initialSubcriticalWeakSequence_identifies_physicalAndKineticRate
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
    (hSequence : H3AuditInitialSchwartzWeakCofinalSequence
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) :
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
  have hAnchor :=
    h3Audit_initialSubcriticalEnergyRate_anchoredSchwartz_of_weakSequence
      hH3 hOldJoint hInt0 hMeas0 b α M hb hbT hα0 hα1 hM
      hRate hSequence
  exact ⟨
    h3Audit_initialSubcriticalAnchoredSchwartz_physicalMomentumRate
      hH3 hOldJoint hInt0 hMeas0 b α M hb hbT hα0 hα1 hM
      hRate hAnchor,
    h3Audit_initialSubcriticalAnchoredSchwartz_kineticRate
      hH3 hOldJoint hInt0 hMeas0 b α M hb hbT hα0 hα1 hM
      hRate hAnchor⟩

end
end Euclidean
end Bridge
end PrimeTensor
