import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialCofinalKineticSchwartzTrace
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialScalarWeakFTCControl

/-!
# One joint initial weak--kinetic sequence and positive-time scalar increments

The previous module assumes one right-zero sequence with asymptotically
bounded kinetic energy and an entire Schwartz weak right trace, or derives
that right trace from scalar anchored FTC / ordinary pointwise derivatives.

Here the initial matching is instead required ALONG THE SAME right-zero
sequence for ALL Schwartz tests, while the scalar momentum evolution is
assumed ONLY as exact L¹ increments between strictly positive times:

  ⟪F(t),Φ⟫ - ⟪F(s),Φ⟫ = ∫_s^t gΦ(r) dr, 0 < s,t < b.

This is weaker than a HasDerivAt hypothesis and does not assume the
initial-anchored equation or full Schwartz weak trace. The existing
scalar positive-increment limit theorem gives a right limit for each
Schwartz probe. Composition with the ONE sampled weak limit identifies
the integration constant, and the anchored weak FTC follows.

Independently, approximate kinetic control along that same sequence and
positive-time kinetic antitonicity yield E₀(t) ≤ E₀(0). Dense Schwartz
weak convergence then produces the actual physical strong L² and kinetic
right traces. Without ANY scalar increments, the same joint sequence
already forces a strong L² trace ALONG THAT SEQUENCE, though not at all
times. The latter distinction is kept explicit.

The joint initial matching sequence and testwise scalar increments remain
independent PDE initial-value premises. Strictly positive-time H³
admissibility alone does not identify the initial integration constant.
No unconditional Navier--Stokes regularity claim is made.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- Scalar L¹ increments strictly inside the positive-time interval,
combined with one right-approaching sequence that identifies the initial
value, yield the exact initial-anchored FTC. No ordinary derivative at
any positive time is required. -/
theorem h3Audit_initialScalarPositiveIncrements_anchoredFTC_of_sequence
    (f g : ℝ → ℝ) (C b : ℝ) (hb : 0 < b)
    (hg : IntervalIntegrable g volume 0 b)
    (hIncrements : ∀ (s t : ℝ),
      s ∈ Set.Ioo (0 : ℝ) b →
      t ∈ Set.Ioo (0 : ℝ) b →
      f t - f s = ∫ r in s..t, g r)
    (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)))
    (hSample : Tendsto (fun n : ℕ => f (τ n)) atTop (𝓝 C)) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      f t - C = ∫ r in (0 : ℝ)..t, g r := by
  let q : ℝ := b / 2
  have hq : q ∈ Set.Ioo (0 : ℝ) b := by
    dsimp only [q]
    constructor <;> linarith
  let L : ℝ := f q - ∫ r in (0 : ℝ)..q, g r
  have hLocal : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      IntervalIntegrable g volume 0 t := by
    intro t ht
    exact h3Audit_initialScalarIntervalIntegrable_of_global g b hb hg t ht
  have hRepresentation : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      f t = L + ∫ r in (0 : ℝ)..t, g r := by
    intro t ht
    have hIncrement := hIncrements q t hq ht
    have hSplit : (∫ r in q..t, g r) =
        (∫ r in (0 : ℝ)..t, g r) -
          (∫ r in (0 : ℝ)..q, g r) :=
      (intervalIntegral.integral_interval_sub_left
        (hLocal t ht) (hLocal q hq)).symm
    rw [hSplit] at hIncrement
    dsimp only [L]
    linarith only [hIncrement]
  have hPrimitive :
      Tendsto (fun t : ℝ => ∫ r in (0 : ℝ)..t, g r)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    h3Audit_initialScalarWeakPrimitive_tendsto_zero g b hb hg
  have hPlus :
      Tendsto (fun t : ℝ => L + ∫ r in (0 : ℝ)..t, g r)
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    have h :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => L)
        (𝓝[>] (0 : ℝ)) (𝓝 L)).add hPrimitive
    simpa only [add_zero] using h
  have hNear : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with t ht0 htb
    exact ⟨ht0, htb⟩
  have hEventually : f =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => L + ∫ r in (0 : ℝ)..t, g r) := by
    filter_upwards [hNear] with t ht
    exact hRepresentation t ht
  have hRight : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    hPlus.congr' hEventually.symm
  have hAlong : Tendsto (fun n : ℕ => f (τ n)) atTop (𝓝 L) := by
    simpa only [Function.comp_def] using hRight.comp hτ
  have hIdentify : L = C := tendsto_nhds_unique hAlong hSample
  intro t ht
  have hAt := hRepresentation t ht
  rw [hIdentify] at hAt
  linarith only [hAt]

/-- Positive-time scalar L¹ increment data ONLY on vector Schwartz
probes, each with its own integrable real source. No uniform-in-probe
source bound or spatial Hilbert-valued time derivative is assumed. -/
def H3AuditInitialSchwartzScalarPositiveIncrementsOn
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) : Prop :=
  ∀ Φ : H3PhysicalRealFinVectorSchwartz,
    ∃ g : ℝ → ℝ,
      IntervalIntegrable g volume 0 b ∧
      ∀ (s t : ℝ),
        s ∈ Set.Ioo (0 : ℝ) b →
        t ∈ Set.Ioo (0 : ℝ) b →
          inner ℝ (F t)
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) -
            inner ℝ (F s)
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) =
            ∫ r in s..t, g r

/-- One shared right-zero sequence of weak Schwartz initial values,
plus independent scalar L¹ positive-time increments for each probe,
produces all initially anchored Schwartz scalar FTC identities.
The sequence does NOT have to depend on the test. -/
theorem h3Audit_initialSchwartzPositiveIncrements_anchoredFTC_of_jointSequence
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 < b)
    (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)))
    (hWeak : ∀ Φ : H3PhysicalRealFinVectorSchwartz,
      Tendsto
        (fun n : ℕ => inner ℝ (F (τ n))
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
        atTop
        (𝓝 (inner ℝ U₀
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))))
    (hIncrements : H3AuditInitialSchwartzScalarPositiveIncrementsOn F b) :
    H3AuditInitialSchwartzAnchoredScalarFTCOn F U₀ b := by
  intro Φ
  obtain ⟨g, hg, hIncrement⟩ := hIncrements Φ
  refine ⟨g, hg, ?_⟩
  exact h3Audit_initialScalarPositiveIncrements_anchoredFTC_of_sequence
    (fun t : ℝ => inner ℝ (F t)
      (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
    g
    (inner ℝ U₀ (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
    b hb hg hIncrement τ hτ (hWeak Φ)

/-- With no temporal increment premise at all, one joint sequence of
Schwartz weak initial data and asymptotically bounded kinetic energy
already converges STRONGLY in physical L² ALONG THAT SEQUENCE.
This deliberately does NOT claim all-positive-time convergence. -/
theorem h3Audit_initialJointKineticSchwartzSequence_sampledStrongTrace
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
    (hWeak : ∀ Φ : H3PhysicalRealFinVectorSchwartz,
      Tendsto
        (fun n : ℕ => inner ℝ
          (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n))
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
        atTop
        (𝓝 (inner ℝ
          (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)))) :
    Tendsto
      (fun n : ℕ => h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n))
      atTop
      (𝓝 (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) := by
  let U₀ : H3PhysicalRealFinVectorL2Hilbert :=
    h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0
  let F : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  have hCeiling :=
    h3Audit_initialCofinalApproximateKineticSequence_exactCeiling
      hH3 τ hτ hSamples
  have hInitial : ‖U₀‖ ^ 2 = velocityH3Energy0At u 0 :=
    h3Audit_initialActualPhysicalHilbertAtZero_norm_sq_eq_kineticEnergy
      hInt0 hMeas0
  have hNear : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) T := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hT)] with t ht0 htT
    exact ⟨ht0, htT⟩
  have hNearSeq : ∀ᶠ n : ℕ in atTop,
      τ n ∈ Set.Ioo (0 : ℝ) T :=
    hτ.eventually hNear
  have hNormCeiling : ∀ᶠ n : ℕ in atTop,
      ‖F (τ n)‖ ^ 2 ≤ ‖U₀‖ ^ 2 := by
    filter_upwards [hNearSeq] with n hn
    calc
      ‖F (τ n)‖ ^ 2 = velocityH3Energy0At u (τ n) :=
        h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
          hH3 (τ n) hn
      _ ≤ velocityH3Energy0At u 0 := hCeiling (τ n) hn
      _ = ‖U₀‖ ^ 2 := hInitial.symm
  exact h3Audit_initialHilbert_strong_of_denseWeak_energyCeiling
    atTop
    h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert
    denseRange_h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert
    (fun n : ℕ => F (τ n)) U₀ hNormCeiling hWeak

/-- One joint kinetic-and-Schwartz initial matching sequence plus
positive-time scalar L¹ increments against Schwartz vector tests.
Crucially, neither a full weak right filter trace nor an anchored
initial-time scalar FTC is included in this data structure. -/
def H3AuditInitialJointKineticSchwartzIncrementData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) : Prop :=
  ∃ τ : ℕ → ℝ,
    Tendsto τ atTop (𝓝[>] (0 : ℝ)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        velocityH3Energy0At u (τ n) ≤ velocityH3Energy0At u 0 + ε) ∧
    (∀ Φ : H3PhysicalRealFinVectorSchwartz,
      Tendsto
        (fun n : ℕ => inner ℝ
          (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n))
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
        atTop
        (𝓝 (inner ℝ
          (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)))) ∧
    H3AuditInitialSchwartzScalarPositiveIncrementsOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3) b

/-- Physical initial matching is reduced to ONE common right-approaching
joint weak-and-kinetic sequence and test-dependent L¹ increments only
between positive times. The previous cofinal-energy and anchored-FTC
results give strong physical L² and kinetic right-time continuity.

No initial L¹ kinetic budget, subcritical H³ rate, full weak right trace,
pointwise scalar temporal derivative, or common Hilbert-valued source
is assumed. The joint initial sequence and increments are still true
independent PDE-facing initial-value conditions. -/
theorem h3Audit_initialJointKineticSchwartzIncrements_physicalAndKineticRightTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) (hb : 0 < b) (hbT : b < T)
    (hData : H3AuditInitialJointKineticSchwartzIncrementData
      hH3 hInt0 hMeas0 b) :
    Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) ∧
    Tendsto (velocityH3Energy0At u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (velocityH3Energy0At u 0)) := by
  obtain ⟨τ, hτ, hSamples, hWeak, hIncrements⟩ := hData
  have hAnchor : H3AuditInitialSchwartzAnchoredScalarFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0) b :=
    h3Audit_initialSchwartzPositiveIncrements_anchoredFTC_of_jointSequence
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
      b hb τ hτ hWeak hIncrements
  exact h3Audit_initialCofinalKinetic_SchwartzScalarFTC_physicalAndKineticTrace
    hH3 hInt0 hMeas0 τ hτ hSamples b hb hbT hAnchor

end
end Euclidean
end Bridge
end PrimeTensor
