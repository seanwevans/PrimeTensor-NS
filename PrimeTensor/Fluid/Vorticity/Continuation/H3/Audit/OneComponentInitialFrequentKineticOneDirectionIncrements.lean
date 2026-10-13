import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialFrequentKineticTestwiseSchwartzIncrements

/-!
# One initial-data scalar direction replaces the Schwartz test family

Earlier initial physical L² criteria imposed a weak initial sequence and
integrable positive-time momentum increments separately for EVERY
three-component Schwartz probe. Here we instead test only against ONE
fixed vector: the actual initial physical velocity U₀ in the L² Hilbert
carrier, which need not itself be a Schwartz function.

A real L¹ scalar source g for ⟪F(t),U₀⟫, exact scalar increments only
at strictly positive times, and ONE right-approaching weak sample
⟪F(σ n),U₀⟫ → ‖U₀‖² identify the scalar right limit, using the existing
scalar integrable-increments theorem. The full Schwartz test family and
pointwise HasDerivAt premises are removed.

Independently, FREQUENT approximate initial-energy samples along a
possibly different right-zero sequence τ give the exact global
positive-time kinetic ceiling by the previous theorem. Radon--Riesz
with the ONE scalar self-pairing gives STRONG physical L² continuity
at time zero and exact order-zero kinetic energy continuity.

The anchored scalar FTC also supplies the SHARP squared-error bound
    ‖F(t)-U₀‖² ≤ 2 |∫₀ᵗ g(s) ds|,
for 0 < t < b, without postulating a strong time-zero trace.

This reduction weakens the NUMBER of test directions, but requires an
L¹ scalar increment identity specifically against U₀, an arbitrary
physical L² vector. That identity is not automatically implied by
distributional Schwartz-test momentum equations. Frequent kinetic
samples and the one-vector initial pairing sequence likewise remain
independent PDE-facing initial-value obligations; neither terminal
strong-H³ continuation nor unconditional Navier--Stokes regularity
is claimed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- Integrable positive-time increments of ONE physical scalar
correlation admit a right limit. ONE right-zero sequence identifies
that limit with the prescribed initial kinetic self-pairing. -/
theorem h3Audit_initialOneDirectionPositiveIncrements_selfPairRightTrace
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (g : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hg : IntervalIntegrable g volume 0 b)
    (hIncrements : ∀ (s t : ℝ),
      s ∈ Set.Ioo (0 : ℝ) b →
      t ∈ Set.Ioo (0 : ℝ) b →
        inner ℝ (F t) U₀ - inner ℝ (F s) U₀ =
          ∫ r in s..t, g r)
    (σ : ℕ → ℝ)
    (hσ : Tendsto σ atTop (𝓝[>] (0 : ℝ)))
    (hSample : Tendsto
      (fun n : ℕ => inner ℝ (F (σ n)) U₀)
      atTop (𝓝 (‖U₀‖ ^ 2))) :
    Tendsto (fun t : ℝ => inner ℝ (F t) U₀)
      (𝓝[>] (0 : ℝ)) (𝓝 (‖U₀‖ ^ 2)) := by
  obtain ⟨L, hRight⟩ :=
    h3Audit_initialScalarIntegrableIncrements_exists_rightLimit
      (fun t : ℝ => inner ℝ (F t) U₀) g b hb hg hIncrements
  have hAlong : Tendsto
      (fun n : ℕ => inner ℝ (F (σ n)) U₀)
      atTop (𝓝 L) := by
    simpa only [Function.comp_def] using hRight.comp hσ
  have hIdentify : L = ‖U₀‖ ^ 2 :=
    tendsto_nhds_unique hAlong hSample
  simpa only [hIdentify] using hRight

/-- Abstract physical L² and kinetic right continuity from
the EXACT positive-time kinetic ceiling and convergence of the
single initial-data self-pairing. This separates the two essential
assumptions from how each is supplied. -/
theorem h3Audit_initialPhysicalCeilingAndSelfPair_rightTraces
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hCeiling : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      velocityH3Energy0At u t ≤ velocityH3Energy0At u 0)
    (hPair : Tendsto
      (fun t : ℝ =>
        inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
          (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0))
      (𝓝[>] (0 : ℝ))
      (𝓝 (‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2))) :
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
    h3Audit_initialHilbert_strong_of_energyCeiling_selfPairing
      (𝓝[>] (0 : ℝ)) F U₀ hNormCeiling hPair
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

/-- Independently sampled positive-time kinetic control and ONE
initial datum scalar increment/weak sequence contract. The energy
and scalar witness sequences need not coincide. -/
def H3AuditInitialFrequentKineticOneDirectionIncrementData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) : Prop :=
  ∃ (τ : ℕ → ℝ) (g : ℝ → ℝ) (σ : ℕ → ℝ),
    Tendsto τ atTop (𝓝[>] (0 : ℝ)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        velocityH3Energy0At u (τ n) ≤ velocityH3Energy0At u 0 + ε) ∧
    IntervalIntegrable g volume 0 b ∧
    (∀ (s t : ℝ),
      s ∈ Set.Ioo (0 : ℝ) b →
      t ∈ Set.Ioo (0 : ℝ) b →
        inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
            (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0) -
          inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 s)
            (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0) =
          ∫ x in s..t, g x) ∧
    Tendsto σ atTop (𝓝[>] (0 : ℝ)) ∧
    Tendsto
      (fun n : ℕ =>
        inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 (σ n))
          (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0))
      atTop
      (𝓝 (‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2))

/-- The one-direction initial scalar source gives a quantitative
finite-positive-time squared error modulus. It needs no Schwartz
approximation and does not require the scalar temporal source to
be a physical Hilbert-valued Bochner derivative. -/
theorem h3Audit_initialOneDirectionIncrements_physicalSquaredError
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (g : ℝ → ℝ) (b : ℝ) (hb : 0 < b) (hbT : b < T)
    (hg : IntervalIntegrable g volume 0 b)
    (hCeiling : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      velocityH3Energy0At u t ≤ velocityH3Energy0At u 0)
    (hIncrements : ∀ (s t : ℝ),
      s ∈ Set.Ioo (0 : ℝ) b →
      t ∈ Set.Ioo (0 : ℝ) b →
        inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
            (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0) -
          inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 s)
            (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0) =
          ∫ x in s..t, g x)
    (σ : ℕ → ℝ)
    (hσ : Tendsto σ atTop (𝓝[>] (0 : ℝ)))
    (hSample : Tendsto
      (fun n : ℕ =>
        inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 (σ n))
          (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0))
      atTop
      (𝓝 (‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2))) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
        h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2 ≤
        2 * |∫ x in (0 : ℝ)..t, g x| := by
  let F : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let U₀ : H3PhysicalRealFinVectorL2Hilbert :=
    h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0
  have hAnchored :=
    h3Audit_initialScalarPositiveIncrements_anchoredFTC_of_sequence
      (fun t : ℝ => inner ℝ (F t) U₀) g (‖U₀‖ ^ 2)
      b hb hg hIncrements σ hσ hSample
  have hZero : ‖U₀‖ ^ 2 = velocityH3Energy0At u 0 :=
    h3Audit_initialActualPhysicalHilbertAtZero_norm_sq_eq_kineticEnergy
      hInt0 hMeas0
  intro t ht
  have htT : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨ht.1, lt_trans ht.2 hbT⟩
  have hEnergy : ‖F t‖ ^ 2 ≤ ‖U₀‖ ^ 2 := by
    rw [h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy hH3 t htT,
      hZero]
    exact hCeiling t htT
  have hAbs := neg_le_abs (∫ x in (0 : ℝ)..t, g x)
  have hCross : ‖U₀‖ ^ 2 ≤
      inner ℝ (F t) U₀ + |∫ x in (0 : ℝ)..t, g x| := by
    have hAt := hAnchored t ht
    linarith only [hAt, hAbs]
  exact h3Audit_initialEnergySelfPairing_squaredDefect_le
    (F t) U₀ _ hEnergy hCross

/-- Full actual strong physical initial L² and kinetic right traces
using FREQUENT kinetic anchors plus ONE scalar U₀-direction positive
increment equation and one independently sampled self-pairing.
No Schwartz-test family, common sequence, initial kinetic L¹
budget, H³ subcritical rate, or temporal joint-continuity premise. -/
theorem h3Audit_initialFrequentKineticOneDirection_physicalAndKineticRightTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) (hb : 0 < b) (hbT : b < T)
    (hData : H3AuditInitialFrequentKineticOneDirectionIncrementData
      hH3 hInt0 hMeas0 b) :
    (Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) ∧
    Tendsto (velocityH3Energy0At u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (velocityH3Energy0At u 0))) ∧
    ∃ g : ℝ → ℝ,
      IntervalIntegrable g volume 0 b ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2 ≤
          2 * |∫ x in (0 : ℝ)..t, g x| := by
  obtain ⟨τ, g, σ, hτ, hFrequent, hg, hIncrements, hσ, hSample⟩ := hData
  have hCeiling :=
    h3Audit_initialFrequentKineticSequence_exactPositiveCeiling
      hH3 τ hτ hFrequent
  have hPair :=
    h3Audit_initialOneDirectionPositiveIncrements_selfPairRightTrace
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
      g b hb hg hIncrements σ hσ hSample
  have hTrace :=
    h3Audit_initialPhysicalCeilingAndSelfPair_rightTraces
      hH3 (lt_trans hb hbT) hInt0 hMeas0 hCeiling hPair
  have hRate :=
    h3Audit_initialOneDirectionIncrements_physicalSquaredError
      hH3 hInt0 hMeas0 g b hb hbT hg hCeiling
      hIncrements σ hσ hSample
  exact ⟨hTrace, g, hg, hRate⟩

end
end Euclidean
end Bridge
end PrimeTensor
