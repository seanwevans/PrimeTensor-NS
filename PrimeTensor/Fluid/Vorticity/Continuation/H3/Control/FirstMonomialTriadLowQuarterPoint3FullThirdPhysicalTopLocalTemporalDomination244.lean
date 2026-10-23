import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopLocalShortRestartEighthMoments244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Projected.RHS.Weak.Evolution.Local.Domination
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Projected.RHS.Weak.Evolution.Reduction
import Mathlib.Tactic

/-!
# Physical eighth moments from local compact-test temporal domination

The preceding local-short-restart theorem transfers all eighth raw Fourier
velocity moments if the OLD projected RHS satisfies a scalar weak FTC on one
shortened positive-time restart interval. Here that analytic assumption is
reduced to a spatially integrable bound on compactly tested OLD temporal
derivatives, locally in elapsed time. The existing parametric-integral
argument proves weak evolution from this domination; the existing scalar
integrability lemma upgrades evolution to weak FTC. Gronwall then identifies
the selected and old physical velocities, transferring the selected high
Fourier moments to the actual H3 velocity.

Unlike joint continuity of (time,space) -> dt u, compact-test domination need
only hold separately for each test and each local elapsed-time neighborhood.
Separate continuity by itself does not establish domination; this is still an
explicit analytic hypothesis, not a proof of unconditional continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- The actual physical time has a shortened canonical restart window on which
all compact divergence-free tests have a locally integrable spatial majorant
for their pairing with the actual OLD temporal derivative. No weak FTC is
assumed in this definition. -/
def h3PathVelocityShortWindowTemporalDominationAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (_hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : Prop :=
  ∃ (t₀ S E : ℝ)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) S)
    (_hST : S < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ S E)
    (hq : 0 < t - t₀)
    (_hqR : t - t₀ < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hEnd : t₀ + (t - t₀) < S)
    (hNSShort : LoggedPreterminalNavierStokesAdmissible u S),
    ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      H3PreterminalLoggedVelocityWeakTemporalLocallyDominatedOnElapsed
        hNSShort t₀ (t - t₀) φ

/-- The old compact-test parametric-integral differentiation theorem gives
weak evolution from local temporal domination. The separately proved scalar
projected-RHS integrability theorem completes the old weak FTC on precisely
the shortened interval, with no old endpoint-continuity assumption. -/
theorem h3Path_shortWindowWeakFTC_of_temporalDomination244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hDom : h3PathVelocityShortWindowTemporalDominationAt244 hH3 t) :
    h3PathVelocityShortWindowWeakFTCAt244 hH3 t := by
  rcases hDom with
    ⟨t₀, S, E, ht₀, hST, hE, hTail, hq, hqR, hEnd,
      hNSShort, hDom⟩
  have hEvolution :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakEvolutionOnElapsed
        hNSShort ht₀ hq hEnd hTail :=
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakEvolutionOnElapsed_of_allLocalDomination
      hNSShort ht₀ hq hEnd hE hTail hDom
  have hWeakFTC :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hNSShort ht₀ hq hEnd hTail :=
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed_of_allProjectedRHSWeakEvolution
      hNSShort ht₀ hq hEnd hE hTail hEvolution
  exact ⟨t₀, S, E, ht₀, hST, hE, hTail, hq, hqR,
    hEnd, hNSShort, hWeakFTC⟩

/-- Local compact-test temporal domination yields actual raw eighth Fourier
moments at any interior H3 slice. The truncated restart geometry and
selected/old spectral equality are both supplied by earlier results. -/
theorem h3Path_physicalEighthMoments_of_localTemporalDomination244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hDom : h3PathVelocityShortWindowTemporalDominationAt244 hH3 t) :
    h3PathVelocityRawEightMomentsAt244 hH3 hClass ht := by
  exact h3Path_physicalEighthMoments_of_localShortWeakFTC244
    hH3 hClass ht
    (h3Path_shortWindowWeakFTC_of_temporalDomination244 hH3 hDom)

/-- Under local domination at each strict time, top dissipation escape
requires either lower-order dissipation escape or cofinal raw velocity
eighth-moment escape, with no independent high-moment assumption. -/
theorem h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_localTemporalDomination244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hDom : ∀ t (_ht : t ∈ Set.Ioo a T),
      h3PathVelocityShortWindowTemporalDominationAt244 hH3 t) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < velocityH3Dissipation1At u r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) := by
  apply h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_localShortWeakFTC244
    hH3 hClass hs hEscape
  intro t ht
  exact h3Path_shortWindowWeakFTC_of_temporalDomination244
    hH3 (hDom t ht)

/-- Contrapositive obstruction: without any local-domination premise, a
terminal top-dissipation escape forces at least one of three mechanisms:
lower dissipation growth, cofinal raw eighth moments, or failure of compact-
test temporal domination on some interior shortened restart interval.
The third branch is not inferred from mere separate continuity. -/
theorem h3Path_unboundedPhysicalTop_forces_lower_or_eight_or_temporalDominationFailure244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t) :
    (∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < velocityH3Dissipation1At u r) ∨
    (∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r) ∨
    (∃ t, t ∈ Set.Ioo a T ∧
      ¬ h3PathVelocityShortWindowTemporalDominationAt244 hH3 t) := by
  classical
  by_cases hAll : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityShortWindowTemporalDominationAt244 hH3 t
  · rcases
      h3Path_unboundedPhysicalTop_forces_dissipationOne_or_eightMoment_of_localTemporalDomination244
        hH3 hClass hs hEscape hAll with hLow | hEight
    · exact Or.inl hLow
    · exact Or.inr (Or.inl hEight)
  · right
    right
    by_contra hNo
    apply hAll
    intro t ht
    by_contra hNot
    exact hNo ⟨t, ht, hNot⟩

end
end PrimeTensor.FirstMonomialTriad
