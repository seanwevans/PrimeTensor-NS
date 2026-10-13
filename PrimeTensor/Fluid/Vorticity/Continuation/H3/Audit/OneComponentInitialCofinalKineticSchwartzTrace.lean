import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialSchwartzScalarFTCStrongTrace
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialCofinalKineticAnchorsRelativeEnergy

/-!
# Strong physical initial L² trace from one approximate kinetic sequence

The prior initial Schwartz scalar FTC + physical kinetic-budget theorem
assumed an initial-anchored kinetic inequality with an L¹ temporal defect.
That is sufficient, but it is stronger than the *energy* information used
by the positive-time Navier--Stokes kinetic antitonicity theorem.

Here we assume ONE right-zero sequence τₙ → 0+ on which the actual old
kinetic energy is asymptotically no greater than the prescribed initial
kinetic energy:

  ∀ ε > 0, eventually E₀(τₙ) ≤ E₀(0) + ε.

For any positive t, choose an earlier sample with energy within ε of
the initial energy. The existing positive-time antitonicity eliminates
ε and yields E₀(t) ≤ E₀(0) on all of (0,T). Paired with the already
proved dense Schwartz weak initial-trace theorem, this gives strong
physical L² and kinetic right continuity WITHOUT an L¹ kinetic budget.

A variant derives the required initial Schwartz weak trace from per-test
anchored real scalar L¹ FTC equations. Another variant derives those
scalar equations from positive-time scalar derivatives and per-test
initial weak sequences. Neither scalar source has to be Hilbert-valued,
nor must the sources share a uniform testwise temporal majorant.

The one kinetic sample sequence and the scalar initial matching data
remain independent initial-value conditions. They are not inferred from
strictly positive-time H³ admissibility. This module does not imply
unconditional 3D Navier--Stokes regularity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- Approximate upper energy bounds along one sequence approaching the
initial right filter give arbitrarily early approximate energy anchors.
No energy right limit, global energy bound, or integral budget is assumed. -/
theorem h3Audit_initialScalarCofinalApproximateAnchors_of_sequence
    (E : ℝ → ℝ) (C : ℝ)
    (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)))
    (hSamples : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, E (τ n) ≤ C + ε)
    (t : ℝ) (ht : 0 < t)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t ∧ E s ≤ C + ε := by
  have hNear : ∀ᶠ s : ℝ in (𝓝[>] (0 : ℝ)),
      s ∈ Set.Ioo (0 : ℝ) t := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds ht)] with s hs0 hst
    exact ⟨hs0, hst⟩
  have hNearSequence : ∀ᶠ n : ℕ in atTop,
      τ n ∈ Set.Ioo (0 : ℝ) t :=
    hτ.eventually hNear
  obtain ⟨n, hnTime, hnEnergy⟩ :=
    (hNearSequence.and (hSamples ε hε)).exists
  exact ⟨τ n, hnTime, hnEnergy⟩

/-- One asymptotically initial-energy-bounded right-zero sequence
suffices for the *exact* kinetic energy ceiling for every positive
preterminal time, using the existing Navier--Stokes H³ kinetic
antitonicity theorem. No initial L¹ kinetic defect is needed. -/
theorem h3Audit_initialCofinalApproximateKineticSequence_exactCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)))
    (hSamples : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        velocityH3Energy0At u (τ n) ≤ velocityH3Energy0At u 0 + ε) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      velocityH3Energy0At u t ≤ velocityH3Energy0At u 0 := by
  apply h3Audit_initialKineticEnergy_le_initial_of_cofinalApproximateAnchors hH3
  intro t ht ε hε
  exact h3Audit_initialScalarCofinalApproximateAnchors_of_sequence
    (velocityH3Energy0At u) (velocityH3Energy0At u 0)
    τ hτ hSamples t ht.1 ε hε

/-- The sampled approximate kinetic bound and Schwartz distributional
right trace imply STRONG physical L² right continuity and correct kinetic
energy at time zero. Unlike the earlier proof, this needs NO initial
kinetic L¹ budget, no subcritical H³ rate and no physical temporal
derivative joint continuity. -/
theorem h3Audit_initialCofinalKinetic_SchwartzWeak_physicalAndKineticTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)))
    (hSamples : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        velocityH3Energy0At u (τ n) ≤ velocityH3Energy0At u 0 + ε)
    (hWeak : H3AuditInitialSchwartzRightWeakTrace hH3 hInt0 hMeas0) :
    Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) ∧
    Tendsto (velocityH3Energy0At u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (velocityH3Energy0At u 0)) := by
  let F : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let U₀ : H3PhysicalRealFinVectorL2Hilbert :=
    h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0
  have hCeiling :=
    h3Audit_initialCofinalApproximateKineticSequence_exactCeiling
      hH3 τ hτ hSamples
  have hZero : ‖U₀‖ ^ 2 = velocityH3Energy0At u 0 :=
    h3Audit_initialActualPhysicalHilbertAtZero_norm_sq_eq_kineticEnergy
      hInt0 hMeas0
  have hNear : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) T := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hT)] with t ht0 htT
    exact ⟨ht0, htT⟩
  have hNormCeiling : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      ‖F t‖ ^ 2 ≤ ‖U₀‖ ^ 2 := by
    filter_upwards [hNear] with t ht
    calc
      ‖F t‖ ^ 2 = velocityH3Energy0At u t :=
        h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
          hH3 t ht
      _ ≤ velocityH3Energy0At u 0 := hCeiling t ht
      _ = ‖U₀‖ ^ 2 := hZero.symm
  have hStrong : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 U₀) :=
    h3Audit_initialHilbert_strong_of_denseWeak_energyCeiling
      (𝓝[>] (0 : ℝ))
      h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert
      denseRange_h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert
      F U₀ hNormCeiling hWeak
  have hSquared : Tendsto
      (fun t : ℝ => ‖F t‖ ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (‖U₀‖ ^ 2)) := by
    have hNorm := (continuous_norm.tendsto U₀).comp hStrong
    simpa only [Function.comp_def] using hNorm.pow 2
  have hEq : (velocityH3Energy0At u) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ‖F t‖ ^ 2) := by
    filter_upwards [hNear] with t ht
    exact (h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
      hH3 t ht).symm
  have hKinetic : Tendsto (velocityH3Energy0At u)
      (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3Energy0At u 0)) := by
    rw [← hZero]
    exact hSquared.congr' hEq.symm
  exact ⟨hStrong, hKinetic⟩

/-- Anchored scalar Schwartz FTC with test-dependent L¹ sources
manufactures the entire weak Schwartz initial trace, then the single
asymptotically bounded kinetic sequence gives the strong physical
initial and kinetic right traces. -/
theorem h3Audit_initialCofinalKinetic_SchwartzScalarFTC_physicalAndKineticTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)))
    (hSamples : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        velocityH3Energy0At u (τ n) ≤ velocityH3Energy0At u 0 + ε)
    (b : ℝ) (hb : 0 < b) (hbT : b < T)
    (hFTC : H3AuditInitialSchwartzAnchoredScalarFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0) b) :
    Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) ∧
    Tendsto (velocityH3Energy0At u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (velocityH3Energy0At u 0)) := by
  have hWeak : H3AuditInitialSchwartzRightWeakTrace
      hH3 hInt0 hMeas0 :=
    h3Audit_initialSchwartzAnchoredScalarFTC_weakRightTrace
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
      b hb hFTC
  exact h3Audit_initialCofinalKinetic_SchwartzWeak_physicalAndKineticTrace
    hH3 (lt_trans hb hbT) hInt0 hMeas0 τ hτ hSamples hWeak

/-- Optional lower-level initial-value route: scalar interior derivatives
and separate right-zero weak sequences per Schwartz test derive the
anchored scalar equations. The energy compatibility needs only ONE
asymptotically initial-energy-bounded kinetic sequence. Neither the
energy sequence nor the matching weak sequences need be identical. -/
theorem h3Audit_initialCofinalKinetic_SchwartzDerivativeSequence_physicalAndKineticTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)))
    (hSamples : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        velocityH3Energy0At u (τ n) ≤ velocityH3Energy0At u 0 + ε)
    (b : ℝ) (hb : 0 < b) (hbT : b < T)
    (hDerivativeSequence :
      ∀ Φ : H3PhysicalRealFinVectorSchwartz,
        ∃ (g : ℝ → ℝ) (σ : ℕ → ℝ),
          IntervalIntegrable g volume 0 b ∧
          (∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b →
            HasDerivAt
              (fun t : ℝ =>
                inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
                  (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
              (g s) s) ∧
          Tendsto σ atTop (𝓝[>] (0 : ℝ)) ∧
          Tendsto
            (fun n : ℕ =>
              inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 (σ n))
                (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
            atTop
            (𝓝 (inner ℝ
              (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)))) :
    Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) ∧
    Tendsto (velocityH3Energy0At u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (velocityH3Energy0At u 0)) := by
  have hFTC : H3AuditInitialSchwartzAnchoredScalarFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0) b :=
    h3Audit_initialSchwartzAnchoredScalarFTC_of_derivativeAndSequence
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
      b hb hDerivativeSequence
  exact h3Audit_initialCofinalKinetic_SchwartzScalarFTC_physicalAndKineticTrace
    hH3 hInt0 hMeas0 τ hτ hSamples b hb hbT hFTC

end
end Euclidean
end Bridge
end PrimeTensor
