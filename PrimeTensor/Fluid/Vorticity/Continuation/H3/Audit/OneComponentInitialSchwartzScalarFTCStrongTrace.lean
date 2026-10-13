import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialSchwartzWeakEnergyStrongTrace
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialScalarWeakSequenceDerivative

/-!
# Actual physical initial L² trace from test-dependent Schwartz scalar FTC

The preceding audited theorem upgrades right weak convergence against every
three-component Schwartz test, together with the initial-anchored kinetic
L¹ budget, to the actual physical strong L² trace and kinetic right trace.

Here the whole right Schwartz weak trace is derived from a familiar
initial-value formulation: for each Schwartz Φ, there is an independently
chosen real scalar L¹ source gΦ such that

    ⟪old(t),Φ⟫ - ⟪u(0),Φ⟫ = ∫₀ᵗ gΦ(s) ds.

Every real L¹ primitive tends to zero at t = 0+, so no Schwartz weak
right trace is additionally assumed. This does NOT demand a single
Hilbert-valued Bochner source or a common dual temporal source bound.

Moreover the anchored scalar identity itself can be DERIVED from a
test-specific interior derivative and only one weak sequence approaching
the prescribed initial pairing for each test, using the already-proved
scalar initial FTC theorem. The sequences and sources may depend on Φ.

In both routes the initial-anchored L¹ kinetic budget remains separate.
The initial scalar equations or their derivative-plus-sequence data are
also independent initial-value premises; the open-time PDE by itself
does not choose the time-zero integration constant. No unconditional
3D Navier--Stokes regularity or terminal H³ statement is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- Scalar initial momentum equations against real physical Schwartz
vector tests, with one separately integrable real source for each test.
No Bochner-valued or uniform-in-test source is assumed. -/
def H3AuditInitialSchwartzAnchoredScalarFTCOn
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) : Prop :=
  ∀ Φ : H3PhysicalRealFinVectorSchwartz,
    ∃ g : ℝ → ℝ,
      IntervalIntegrable g volume 0 b ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        inner ℝ (F t)
            (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) -
          inner ℝ U₀
            (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) =
          ∫ s in (0 : ℝ)..t, g s

/-- The test-dependent anchored L¹ scalar FTC implies the entire
right weak Schwartz initial trace. No strong momentum limit,
L² source, or kinetic assumption is used in this step. -/
theorem h3Audit_initialSchwartzAnchoredScalarFTC_weakRightTrace
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 < b)
    (hFTC : H3AuditInitialSchwartzAnchoredScalarFTCOn F U₀ b) :
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
  obtain ⟨g, hg, hIdentity⟩ := hFTC Φ
  have hPrimitive :
      Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..t, g s)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    h3Audit_initialScalarWeakPrimitive_tendsto_zero g b hb hg
  have hStrict : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with t ht0 htb
    exact ⟨ht0, htb⟩
  have hEq :
      (fun t : ℝ => inner ℝ (F t) ψ - inner ℝ U₀ ψ)
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ∫ s in (0 : ℝ)..t, g s) := by
    filter_upwards [hStrict] with t ht
    exact hIdentity t ht
  have hDifference :
      Tendsto (fun t : ℝ => inner ℝ (F t) ψ - inner ℝ U₀ ψ)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    hPrimitive.congr' hEq.symm
  have hSum := hDifference.add
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => inner ℝ U₀ ψ)
      (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ U₀ ψ)))
  simpa only [ψ, sub_add_cancel, zero_add] using hSum

/-- For each Schwartz test separately, a scalar L¹ interior temporal
derivative and one weak initial sequence identify the constant in the
scalar FTC. The initial-anchored scalar equations are conclusions,
not premises, of this theorem. -/
theorem h3Audit_initialSchwartzAnchoredScalarFTC_of_derivativeAndSequence
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 < b)
    (hDerivativeSequence :
      ∀ Φ : H3PhysicalRealFinVectorSchwartz,
        ∃ (g : ℝ → ℝ) (τ : ℕ → ℝ),
          IntervalIntegrable g volume 0 b ∧
          (∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b →
            HasDerivAt
              (fun t : ℝ =>
                inner ℝ (F t)
                  (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
              (g s) s) ∧
          Tendsto τ atTop (𝓝[>] (0 : ℝ)) ∧
          Tendsto
            (fun n : ℕ =>
              inner ℝ (F (τ n))
                (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
            atTop
            (𝓝 (inner ℝ U₀
              (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)))) :
    H3AuditInitialSchwartzAnchoredScalarFTCOn F U₀ b := by
  intro Φ
  obtain ⟨g, τ, hg, hDeriv, hτ, hWeak⟩ := hDerivativeSequence Φ
  refine ⟨g, hg, ?_⟩
  exact h3Audit_initialScalarWeakFTC_of_interiorDerivative_and_sequence
    (fun t : ℝ =>
      inner ℝ (F t)
        (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
    g
    (inner ℝ U₀
      (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
    b hb hg hDeriv τ hτ hWeak

/-- An initial-anchored kinetic L¹ budget and test-dependent initial
scalar weak integral equations imply strong physical L² and kinetic
right-time continuity. No H³ subcritical rate, temporal-derivative
joint continuity, common Bochner source, or assumed strong initial
trace is required. -/
theorem h3Audit_initialBudget_SchwartzScalarFTC_strongPhysicalAndKineticTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (r : ℝ → ℝ) (b : ℝ) (hb : 0 < b) (hbT : b < T)
    (hR : IntervalIntegrable (fun s : ℝ => |r s|) volume 0 b)
    (hBudget : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b →
      velocityH3Energy0At u s ≤
        velocityH3Energy0At u 0 +
          ∫ x in (0 : ℝ)..s, |r x|)
    (hFTC : H3AuditInitialSchwartzAnchoredScalarFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
      b) :
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
  exact h3Audit_initialBudget_SchwartzWeak_implies_physicalAndKineticRightTrace
    hH3 hInt0 hMeas0 r b hb hbT hR hBudget hWeak

/-- Discharge the initial-anchored scalar weak FTC via actual
positive-time Schwartz scalar derivatives, testwise integrability,
and one per-test initial weak sequence, then derive the strong physical
L² and kinetic right traces from the independent initial kinetic
budget. No full weak right trace or initial scalar FTC is assumed. -/
theorem h3Audit_initialBudget_SchwartzDerivativeSequence_strongPhysicalAndKineticTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (r : ℝ → ℝ) (b : ℝ) (hb : 0 < b) (hbT : b < T)
    (hR : IntervalIntegrable (fun s : ℝ => |r s|) volume 0 b)
    (hBudget : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b →
      velocityH3Energy0At u s ≤
        velocityH3Energy0At u 0 +
          ∫ x in (0 : ℝ)..s, |r x|)
    (hDerivativeSequence :
      ∀ Φ : H3PhysicalRealFinVectorSchwartz,
        ∃ (g : ℝ → ℝ) (τ : ℕ → ℝ),
          IntervalIntegrable g volume 0 b ∧
          (∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b →
            HasDerivAt
              (fun t : ℝ =>
                inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
                  (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
              (g s) s) ∧
          Tendsto τ atTop (𝓝[>] (0 : ℝ)) ∧
          Tendsto
            (fun n : ℕ =>
              inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n))
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
  exact h3Audit_initialBudget_SchwartzScalarFTC_strongPhysicalAndKineticTrace
    hH3 hInt0 hMeas0 r b hb hbT hR hBudget hFTC

end
end Euclidean
end Bridge
end PrimeTensor
