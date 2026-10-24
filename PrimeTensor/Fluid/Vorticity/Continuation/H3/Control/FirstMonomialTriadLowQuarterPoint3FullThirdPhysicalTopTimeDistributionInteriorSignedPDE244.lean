import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionFromJointPDE244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopSignedMomentumCorridor244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalHilbertTimeEvolution
import Mathlib.Tactic

/-!
# Interior compact momentum domination yields genuine time distributions

A local weak-FTC interval must extend to BOTH sides of an observation time
if it is to determine a genuine two-sided Hilbert time derivative there.
The earlier short-window condition stopped exactly at the observation time,
which suffices for eighth moments but not this derivative assertion.

We introduce the correct strict-interior local condition and derive its
strong physical L2 time derivative through the already-formalized compact-
test parametric-integral argument, projected-RHS identification, and physical
Hilbert weak-to-strong theorem. We then transfer this derivative to the
actual scalar time distributional momentum equation.

The signed PDE-side condition uses the FULL signed diffusion/advection/pressure
sum. This retains Navier--Stokes cancellations and is strictly weaker than
bounding the three terms separately. Neither signed local domination nor
joint time-space continuity is inferred from bare H3 path admissibility.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set TopologicalSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

/-- A local canonical H3 window *straddling* the observation time, on which
all solenoidal compact spatial tests have the old temporal-derivative
integrable majorants. The old PDE is available on the shortened terminal `S`.
No weak FTC or time-distribution equation is part of this definition. -/
def h3PathInteriorTimeTemporalDominationAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (_hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s : ℝ) : Prop :=
  ∃ (t₀ S E τ : ℝ)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) S)
    (_hST : S < T)
    (_hE : 1 ≤ E)
    (_hTail : CanonicalH3TailDataFrom u t₀ S E)
    (_hτ : 0 < τ)
    (_hEnd : t₀ + τ < S)
    (hNSShort : LoggedPreterminalNavierStokesAdmissible u S),
      s ∈ Set.Ioo t₀ (t₀ + τ) ∧
      ∀ φ : H3WeakTestVector,
        H3WeakTestVectorDivergenceFree φ →
        H3PreterminalLoggedVelocityWeakTemporalLocallyDominatedOnElapsed
          hNSShort t₀ τ φ

/-- Genuine physical L2 time differentiation from old compact-test temporal
domination on an interval with the observation time strictly in its interior.
The proof uses no classical differentiation-under-an-integral assertion as an
unproved premise; that implication is the already proved local-domination
weak-evolution theorem. -/
theorem h3Path_physicalHilbertHasDerivAt_of_interiorTemporalDomination244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hDom : h3PathInteriorTimeTemporalDominationAt244 hH3 s) :
    HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3 s) s := by
  rcases hDom with
    ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
      hNSShort, hs, hDom⟩
  have hEvolution :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakEvolutionOnElapsed
        hNSShort ht₀ hτ hEnd hTail :=
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakEvolutionOnElapsed_of_allLocalDomination
      hNSShort ht₀ hτ hEnd hE hTail hDom
  have hWeakFTC :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hNSShort ht₀ hτ hEnd hTail :=
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed_of_allProjectedRHSWeakEvolution
      hNSShort ht₀ hτ hEnd hE hTail hEvolution
  have hSPos : 0 < S := lt_trans ht₀.1 ht₀.2
  let hShort : LoggedPreterminalH3PathAdmissible u S :=
    h3Audit_h3PathAdmissible_restrict_terminal hH3 hSPos hST.le
  change HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
    (h3AuditInitialActualSpectralLaplacianTotal hH3 s -
      h3AuditInitialActualSpectralLerayTotal hH3 s) s
  exact h3Audit_initialCanonicalWeakFTC_implies_physicalHilbertHasDerivAt_onElapsed
    hH3 hShort hST.le ht₀ hτ hEnd hTail hWeakFTC s hs

/-- For every interior physical time, compact test temporal domination on a
straddling short restart suffices to prove the actual distributional momentum
identity on the whole strict time interval. No joint time-space continuity is
assumed. -/
theorem h3Path_distributionalMomentum_of_interiorTemporalDomination244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hDom : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimeTemporalDominationAt244 hH3 s) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b := by
  apply (h3Path_distributionalMomentum_iff_physicalHilbertHasDerivAt_onStrict244
    hH3 ha hab hb).2
  intro s hs
  exact h3Path_physicalHilbertHasDerivAt_of_interiorTemporalDomination244
    hH3 (hDom s hs)

/-- The PDE-side criterion bounds only the *signed sum* of Laplacian,
advection and pressure on test supports, locally in time. The interval must
straddle `s`. This is not the earlier endpoint-only moment condition. -/
def h3PathInteriorTimeSignedMomentumBoundAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (_hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s : ℝ) : Prop :=
  ∃ (t₀ S E τ : ℝ)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) S)
    (_hST : S < T)
    (_hE : 1 ≤ E)
    (_hTail : CanonicalH3TailDataFrom u t₀ S E)
    (_hτ : 0 < τ)
    (_hEnd : t₀ + τ < S)
    (hNSShort : LoggedPreterminalNavierStokesAdmissible u S),
      s ∈ Set.Ioo t₀ (t₀ + τ) ∧
      h3PreterminalSignedMomentumCompactBoundOnElapsed244 hNSShort t₀ τ

/-- The full signed Navier--Stokes momentum bound implies the compact
parametric-integral domination needed on the same straddling interval. -/
theorem h3Path_interiorTemporalDomination_of_signedMomentumBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hSigned : h3PathInteriorTimeSignedMomentumBoundAt244 hH3 s) :
    h3PathInteriorTimeTemporalDominationAt244 hH3 s := by
  rcases hSigned with
    ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
      hNSShort, hs, hBound⟩
  refine ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
    hNSShort, hs, ?_⟩
  exact h3Preterminal_compactTemporalDomination_of_signedMomentumBound244
    hNSShort t₀ τ hBound

/-- Signed compact momentum control around an individual observation time
produces its actual strong L2 physical momentum derivative. -/
theorem h3Path_physicalHilbertHasDerivAt_of_interiorSignedMomentumBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hSigned : h3PathInteriorTimeSignedMomentumBoundAt244 hH3 s) :
    HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3 s) s := by
  exact h3Path_physicalHilbertHasDerivAt_of_interiorTemporalDomination244
    hH3 (h3Path_interiorTemporalDomination_of_signedMomentumBound244 hH3 hSigned)

/-- A genuine classical-PDE-to-time-distribution theorem with only
cancellation-preserving compact-support domination, rather than joint
continuity of the whole physical temporal derivative. -/
theorem h3Path_distributionalMomentum_of_interiorSignedMomentumBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hSigned : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimeSignedMomentumBoundAt244 hH3 s) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b := by
  apply h3Path_distributionalMomentum_of_interiorTemporalDomination244
    hH3 ha hab hb
  intro s hs
  exact h3Path_interiorTemporalDomination_of_signedMomentumBound244
    hH3 (hSigned s hs)

/-- The same signed bound yields the literal compact smooth temporal test
momentum equation, with the negative sign dictated by time integration by
parts. -/
theorem h3Path_timeTestMomentum_of_interiorSignedMomentumBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hSigned : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimeSignedMomentumBoundAt244 hH3 s) :
    h3PathSolenoidalTimeTestMomentumOn244 hH3 a b := by
  exact (h3Path_distributionalMomentum_iff_timeTestMomentum244
    hH3 ha hab hb).mp
    (h3Path_distributionalMomentum_of_interiorSignedMomentumBound244
      hH3 ha hab hb hSigned)

/-- Failure of actual physical Hilbert FTC on `[a,b]` forces failure of the
signed straddling-neighborhood estimate at SOME strict interior time.
This identifies a precise remaining PDE-side compactness obstruction. -/
theorem h3Path_nonzeroPhysicalFTCDefect_forces_interiorSignedFailure244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hNonzero : h3PathActualProjectedMomentumFTCDefect244 hH3 a b ≠ 0) :
    ∃ s : ℝ, s ∈ Set.Ioo a b ∧
      ¬ h3PathInteriorTimeSignedMomentumBoundAt244 hH3 s := by
  classical
  by_contra hNo
  have hAll : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimeSignedMomentumBoundAt244 hH3 s := by
    intro s hs
    by_contra hFail
    exact hNo ⟨s, hs, hFail⟩
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
    exact (((innerSL ℝ) ψ).hasFDerivAt).comp_hasDerivAt s
      (h3Path_physicalHilbertHasDerivAt_of_interiorSignedMomentumBound244
        hH3 (hAll s hs))
  have hWeak := h3Path_solenoidalWeakFTC_of_pointwiseWeakMomentum244
    hH3 ha hab hb hScalar
  have hZero := (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
    hH3 ha hab hb).2 hWeak
  exact hNonzero (hZero b ⟨hab.le, le_rfl⟩)

end
end PrimeTensor.FirstMonomialTriad
