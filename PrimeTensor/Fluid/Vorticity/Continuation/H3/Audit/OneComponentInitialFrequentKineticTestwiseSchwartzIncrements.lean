import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialJointKineticSchwartzIncrements

/-!
# Frequent kinetic energy anchors and independently sampled Schwartz tests

The previous theorem uses ONE common right-zero sequence τ for both:
  (i) eventually E₀(τ n) ≤ E₀(0) + ε, for every ε > 0;
  (ii) weak initial matching against every physical Schwartz test.

Neither synchronization nor an eventual upper bound is needed when
positive-time scalar L¹ increments are available.

First, approximate energy samples need only occur ARBITRARILY LATE:
  ∀ ε > 0, ∀ N, ∃ n ≥ N, E₀(τ n) ≤ E₀(0) + ε.
The energy antitonicity of the actual old H³ path turns these
arbitrarily late, arbitrarily early energy anchors into the exact
positive-time kinetic ceiling and hence an eventual energy bound.

Second, for EACH Schwartz probe Φ, permit a DIFFERENT sequence σΦ
approaching zero from the right along which the scalar pairing
converges to the prescribed initial datum. The already-proved
scalar positive-increment theorem identifies the constant of
integration for that individual Φ. The resulting full weak
Schwartz right trace, composed with τ, supplies the joint weak
matching on τ without postulating it.

We thereby construct the previous audited joint-sequence contract and
derive the true strong physical L² and kinetic right traces from
separately sampled initial data.

Remaining hypotheses: existence of frequent kinetic anchors, matching
weak sequences for each test, and test-specific positive-time scalar
L¹ increment equations. These are NOT consequences of strictly
positive-time H³ admissibility alone. There is no unconditional
Navier--Stokes smoothness or terminal H³ regularity conclusion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- Infinitely recurring approximate initial energy samples on a
right-zero sequence give an arbitrarily early approximate anchor.
Unlike the earlier sampled lemma, the energy inequality need not
hold eventually: there need only be an acceptable index beyond
every index N. -/
theorem h3Audit_initialFrequentScalarSequence_cofinalApproximateAnchors
    (E : ℝ → ℝ) (C : ℝ) (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)))
    (hFrequent : ∀ ε : ℝ, 0 < ε →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ E (τ n) ≤ C + ε)
    (t : ℝ) (ht : 0 < t)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t ∧ E s ≤ C + ε := by
  have hNear : ∀ᶠ s : ℝ in (𝓝[>] (0 : ℝ)),
      s ∈ Set.Ioo (0 : ℝ) t := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds ht)] with s hs0 hst
    exact ⟨hs0, hst⟩
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (hτ.eventually hNear))
  obtain ⟨n, hnN, hnEnergy⟩ := hFrequent ε hε N
  exact ⟨τ n, hN n hnN, hnEnergy⟩

/-- Navier--Stokes positive-time energy antitonicity upgrades only
FREQUENT approximate samples into the exact initial kinetic ceiling.
No initial kinetic budget, uniform kinetic control on τ, or sampled
kinetic limit is assumed. -/
theorem h3Audit_initialFrequentKineticSequence_exactPositiveCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)))
    (hFrequent : ∀ ε : ℝ, 0 < ε →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        velocityH3Energy0At u (τ n) ≤ velocityH3Energy0At u 0 + ε) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      velocityH3Energy0At u t ≤ velocityH3Energy0At u 0 := by
  apply h3Audit_initialKineticEnergy_le_initial_of_cofinalApproximateAnchors hH3
  intro t ht ε hε
  exact h3Audit_initialFrequentScalarSequence_cofinalApproximateAnchors
    (velocityH3Energy0At u) (velocityH3Energy0At u 0)
    τ hτ hFrequent t ht.1 ε hε

/-- After the exact ceiling has been established on positive times,
the same frequent kinetic witness sequence actually satisfies the
earlier EVENTUAL sample bound. This is a consequence of PDE
positive-time monotonicity, not a strengthening of the initial data. -/
theorem h3Audit_initialFrequentKineticSequence_eventualUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hT : 0 < T)
    (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)))
    (hFrequent : ∀ ε : ℝ, 0 < ε →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        velocityH3Energy0At u (τ n) ≤ velocityH3Energy0At u 0 + ε) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        velocityH3Energy0At u (τ n) ≤ velocityH3Energy0At u 0 + ε := by
  have hCeiling :=
    h3Audit_initialFrequentKineticSequence_exactPositiveCeiling
      hH3 τ hτ hFrequent
  have hNear : ∀ᶠ s : ℝ in (𝓝[>] (0 : ℝ)),
      s ∈ Set.Ioo (0 : ℝ) T := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hT)] with s hs0 hst
    exact ⟨hs0, hst⟩
  intro ε hε
  filter_upwards [hτ.eventually hNear] with n hn
  have hBound := hCeiling (τ n) hn
  linarith only [hBound, hε]

/-- Schwartz scalar positive-time increments and INDIVIDUAL weak initial
matching sequences already determine the anchored momentum FTC.
Unlike the previous theorem, no single sequence must work for every
Schwartz test. -/
theorem h3Audit_initialSchwartzPositiveIncrements_anchoredFTC_of_testwiseSequences
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 < b)
    (hIncrements : H3AuditInitialSchwartzScalarPositiveIncrementsOn F b)
    (hPerTest : ∀ Φ : H3PhysicalRealFinVectorSchwartz,
      ∃ σ : ℕ → ℝ,
        Tendsto σ atTop (𝓝[>] (0 : ℝ)) ∧
        Tendsto
          (fun n : ℕ => inner ℝ (F (σ n))
            (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
          atTop
          (𝓝 (inner ℝ U₀
            (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)))) :
    H3AuditInitialSchwartzAnchoredScalarFTCOn F U₀ b := by
  intro Φ
  obtain ⟨g, hg, hIncrement⟩ := hIncrements Φ
  obtain ⟨σ, hσ, hWeak⟩ := hPerTest Φ
  refine ⟨g, hg, ?_⟩
  exact h3Audit_initialScalarPositiveIncrements_anchoredFTC_of_sequence
    (fun t : ℝ => inner ℝ (F t)
      (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
    g
    (inner ℝ U₀ (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
    b hb hg hIncrement σ hσ hWeak

/-- Once test-specific right limits are identified by scalar
increments, they are automatically reached ALONG ANY OTHER
right-zero sequence. This is the missing synchronization between
the independent kinetic and weak initial sequences. -/
theorem h3Audit_initialSchwartzPositiveIncrements_syncTestwiseWeakToSequence
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 < b)
    (hIncrements : H3AuditInitialSchwartzScalarPositiveIncrementsOn F b)
    (hPerTest : ∀ Φ : H3PhysicalRealFinVectorSchwartz,
      ∃ σ : ℕ → ℝ,
        Tendsto σ atTop (𝓝[>] (0 : ℝ)) ∧
        Tendsto
          (fun n : ℕ => inner ℝ (F (σ n))
            (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
          atTop
          (𝓝 (inner ℝ U₀
            (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))))
    (τ : ℕ → ℝ) (hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ))) :
    ∀ Φ : H3PhysicalRealFinVectorSchwartz,
      Tendsto (fun n : ℕ => inner ℝ (F (τ n))
        (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
        atTop
        (𝓝 (inner ℝ U₀
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))) := by
  have hAnchor : H3AuditInitialSchwartzAnchoredScalarFTCOn F U₀ b :=
    h3Audit_initialSchwartzPositiveIncrements_anchoredFTC_of_testwiseSequences
      F U₀ b hb hIncrements hPerTest
  have hFull :=
    h3Audit_initialSchwartzAnchoredScalarFTC_weakRightTrace
      F U₀ b hb hAnchor
  intro Φ
  simpa only [Function.comp_def] using (hFull Φ).comp hτ

/-- Weaker initial-value data than the previous joint-sequence contract:
the kinetic sequence has only FREQUENT near-initial upper-energy
samples, while each Schwartz probe may have a DIFFERENT weak-matching
sequence. Testwise positive-time scalar L¹ increments synchronize them. -/
def H3AuditInitialFrequentKineticTestwiseSchwartzIncrementData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) : Prop :=
  ∃ τ : ℕ → ℝ,
    Tendsto τ atTop (𝓝[>] (0 : ℝ)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        velocityH3Energy0At u (τ n) ≤ velocityH3Energy0At u 0 + ε) ∧
    (∀ Φ : H3PhysicalRealFinVectorSchwartz,
      ∃ σ : ℕ → ℝ,
        Tendsto σ atTop (𝓝[>] (0 : ℝ)) ∧
        Tendsto
          (fun n : ℕ =>
            inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 (σ n))
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
          atTop
          (𝓝 (inner ℝ
            (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
            (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)))) ∧
    H3AuditInitialSchwartzScalarPositiveIncrementsOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3) b

/-- An arbitrary frequently suitable kinetic sequence can be
synchronized with separate weak initial Schwartz sequences to
manufacture the STRONGER pre-existing joint-sequence initial contract.
This does NOT postulate or assume joint weak and kinetic matching. -/
theorem h3Audit_initialFrequentTestwiseData_implies_jointKineticSchwartzData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) (hb : 0 < b) (hbT : b < T)
    (hData : H3AuditInitialFrequentKineticTestwiseSchwartzIncrementData
      hH3 hInt0 hMeas0 b) :
    H3AuditInitialJointKineticSchwartzIncrementData
      hH3 hInt0 hMeas0 b := by
  obtain ⟨τ, hτ, hFrequent, hPerTest, hIncrements⟩ := hData
  have hEventual :=
    h3Audit_initialFrequentKineticSequence_eventualUpper
      hH3 (lt_trans hb hbT) τ hτ hFrequent
  have hJointWeak :=
    h3Audit_initialSchwartzPositiveIncrements_syncTestwiseWeakToSequence
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
      b hb hIncrements hPerTest τ hτ
  exact ⟨τ, hτ, hEventual, hJointWeak, hIncrements⟩

/-- Full physical strong L² and order-zero kinetic right continuity
from only FREQUENT sampled approximate kinetic control, independently
sampled weak Schwartz initial compatibility, and test-dependent
positive-time scalar L¹ increments. No subcritical H³ rate, initial
kinetic L¹ budget, or common weak/kinetic matching sequence is needed. -/
theorem h3Audit_initialFrequentKineticTestwiseIncrements_physicalAndKineticRightTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) (hb : 0 < b) (hbT : b < T)
    (hData : H3AuditInitialFrequentKineticTestwiseSchwartzIncrementData
      hH3 hInt0 hMeas0 b) :
    Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) ∧
    Tendsto (velocityH3Energy0At u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (velocityH3Energy0At u 0)) := by
  have hJoint : H3AuditInitialJointKineticSchwartzIncrementData
      hH3 hInt0 hMeas0 b :=
    h3Audit_initialFrequentTestwiseData_implies_jointKineticSchwartzData
      hH3 hInt0 hMeas0 b hb hbT hData
  exact h3Audit_initialJointKineticSchwartzIncrements_physicalAndKineticRightTrace
    hH3 hInt0 hMeas0 b hb hbT hJoint

end
end Euclidean
end Bridge
end PrimeTensor
