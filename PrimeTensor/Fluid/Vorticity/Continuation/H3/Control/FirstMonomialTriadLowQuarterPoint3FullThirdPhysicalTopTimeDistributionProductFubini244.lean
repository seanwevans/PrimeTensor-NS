import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionLocalL2Envelope244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.FTC.Lipschitz
import Mathlib.Tactic

/-!
# Physical momentum time distributions from actual old-branch space-time Fubini

The existing old-branch endpoint-independent weak-Fubini theorem derives scalar
weak FTC from coordinatewise integrability of the compact-tested classical
physical temporal derivative over time × space. Unlike the local L²-envelope
criterion, it does NOT assume a single spatial majorant uniform in time.

We carry that precisely identified PDE-side hypothesis through a shortened
canonical restart that strictly straddles an arbitrary observation time,
then apply the established Hilbert weak-to-strong derivative theorem and the
connected-time distributional momentum equivalence.

Product-space integrability is a separately stated analytic premise: it is
not inferred here from merely separate continuity, pointwise H³ bounds, or
continuity of the already identified projected physical L² source.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter TopologicalSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

/-- An actual short physical restart *straddling* `s`, on which each compact
solenoidal test has the old temporal-derivative product-space integrability
needed for time-space Fubini on every elapsed prefix. This is not an
assumption of weak FTC, Hilbert differentiability, or time-distributional
momentum. Nor does it posit a common pointwise spatial envelope. -/
def h3PathInteriorTimeOldTemporalProductIntegrabilityAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (_hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s : ℝ) : Prop :=
  ∃ (t₀ S E τ : ℝ)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) S)
    (_hST : S < T)
    (_hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ S E)
    (_hτ : 0 < τ)
    (hEnd : t₀ + τ < S)
    (hNSShort : LoggedPreterminalNavierStokesAdmissible u S),
      s ∈ Set.Ioo t₀ (t₀ + τ) ∧
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
        hNSShort ht₀ hEnd hTail

/-- Old pointwise classical Navier--Stokes plus the genuine space-time
integrability of its compactly tested temporal derivative gives actual
physical Hilbert L² differentiation at the interior observation time.
This uses the already proved Fubini-to-weak-FTC theorem, not a common
spatial envelope or the spatial-equicontinuity corridor. -/
theorem h3Path_physicalHilbertHasDerivAt_of_oldTemporalProductFubini244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hProduct : h3PathInteriorTimeOldTemporalProductIntegrabilityAt244 hH3 s) :
    HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3 s) s := by
  rcases hProduct with
    ⟨t₀, S, E, τ, ht₀, hST, _hE, hTail, hτ, hEnd,
      hNSShort, hs, hProd⟩
  have hWeakFTC :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hNSShort ht₀ hτ hEnd hTail :=
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed_of_allTemporalProductIntegrable
      hNSShort ht₀ hτ hEnd hTail hProd
  have hSpos : 0 < S := lt_trans ht₀.1 ht₀.2
  let hShort : LoggedPreterminalH3PathAdmissible u S :=
    h3Audit_h3PathAdmissible_restrict_terminal hH3 hSpos hST.le
  change HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
    (h3AuditInitialActualSpectralLaplacianTotal hH3 s -
      h3AuditInitialActualSpectralLerayTotal hH3 s) s
  exact h3Audit_initialCanonicalWeakFTC_implies_physicalHilbertHasDerivAt_onElapsed
    hH3 hShort hST.le ht₀ hτ hEnd hTail hWeakFTC s hs

/-- The actual physical momentum time distribution follows on each strict
interval from local old-branch space-time Fubini around every interior time.
No time-uniform pointwise spatial bound is present in the premise. -/
theorem h3Path_distributionalMomentum_of_oldTemporalProductFubini244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hProduct : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimeOldTemporalProductIntegrabilityAt244 hH3 s) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b := by
  apply (h3Path_distributionalMomentum_iff_physicalHilbertHasDerivAt_onStrict244
    hH3 ha hab hb).2
  intro s hs
  exact h3Path_physicalHilbertHasDerivAt_of_oldTemporalProductFubini244
    hH3 (hProduct s hs)

/-- The Fubini criterion also supplies the literal smooth compact temporal
test momentum equation, including the distributional integration-by-parts
sign, against every compact solenoidal spatial test. -/
theorem h3Path_timeTestMomentum_of_oldTemporalProductFubini244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hProduct : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimeOldTemporalProductIntegrabilityAt244 hH3 s) :
    h3PathSolenoidalTimeTestMomentumOn244 hH3 a b := by
  exact (h3Path_distributionalMomentum_iff_timeTestMomentum244
    hH3 ha hab hb).mp
    (h3Path_distributionalMomentum_of_oldTemporalProductFubini244
      hH3 ha hab hb hProduct)

/-- An actual nonzero Hilbert momentum FTC defect forces at least one
interior time to lack the old temporal-derivative Fubini integrability
on every admissible straddling restart. -/
theorem h3Path_nonzeroPhysicalFTCDefect_forces_oldTemporalProductFubiniFailure244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hNonzero : h3PathActualProjectedMomentumFTCDefect244 hH3 a b ≠ 0) :
    ∃ s : ℝ, s ∈ Set.Ioo a b ∧
      ¬ h3PathInteriorTimeOldTemporalProductIntegrabilityAt244 hH3 s := by
  classical
  by_contra hNo
  have hAll : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimeOldTemporalProductIntegrabilityAt244 hH3 s := by
    intro s hs
    by_contra hFail
    exact hNo ⟨s, hs, hFail⟩
  have hDist : h3PathSolenoidalDistributionalMomentumOn244 hH3 a b :=
    h3Path_distributionalMomentum_of_oldTemporalProductFubini244
      hH3 ha hab hb hAll
  have hStrong :=
    (h3Path_distributionalMomentum_iff_physicalHilbertHasDerivAt_onStrict244
      hH3 ha hab hb).1 hDist
  have hScalar : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∀ s : ℝ, s ∈ Set.Ioo a b →
        HasDerivAt
          (fun r : ℝ => inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3AuditInitialOldPhysicalHilbertTotal hH3 r))
          (inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PathActualProjectedMomentumSource244 hH3 s)) s := by
    intro φ _hφ s hs
    let ψ : H3PhysicalRealFinVectorL2Hilbert :=
      h3WeakTestVectorPhysicalL2Hilbert φ
    exact (((innerSL ℝ) ψ).hasFDerivAt).comp_hasDerivAt s (hStrong s hs)
  have hWeak := h3Path_solenoidalWeakFTC_of_pointwiseWeakMomentum244
    hH3 ha hab hb hScalar
  have hZero := (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
    hH3 ha hab hb).2 hWeak
  exact hNonzero (hZero b ⟨hab.le, le_rfl⟩)

end
end PrimeTensor.FirstMonomialTriad
