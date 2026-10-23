import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopUniformProjectedRHS244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialCanonicalWeakFTCAbsoluteTransfer
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Leray.Weak.Determining
import Mathlib.Tactic

/-!
# Leray-fixedness and weak determination of the actual projected Hilbert FTC defect

The physical projected source is automatically continuous and Bochner integrable
on strict positive-time intervals. The previous module defined the discrepancy
between its integral and the actual physical velocity increment, without
claiming it vanishes.

This module proves the discrepancy lies in the Leray-fixed physical L² subspace.
Consequently every nonzero discrepancy is detected by some compact smooth
solenoidal test. Vanishing at all times of a strict interval is equivalent to
its solenoidal weak-FTC identity, by existing density and Bochner machinery.
The previously formalized canonical scalar weak FTC supplies precisely this
vanishing on a shortened restart interval whenever its analytic hypothesis
holds. Source continuity alone is NOT used to prove weak FTC or defect zero.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The actual physical Hilbert FTC defect is Leray-fixed on every strictly
preterminal closed interval. This is unconditional under H³ path admissibility:
both velocity snapshots and the entire projected source belong to the same
closed Leray-fixed subspace. -/
theorem h3Path_projectedFTCDefect_lerayFixed_onStrict244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3PathActualProjectedMomentumFTCDefect244 hH3 a b) := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hGInt : IntervalIntegrable G volume a b :=
    h3Path_actualProjectedMomentumSource_intervalIntegrableStrict244
      hH3 ha hab hb
  let L := h3PhysicalRealFinVectorL2HilbertLerayDefectContinuousLinearMap
  have hComm :
      L (∫ s in a..b, G s) = ∫ s in a..b, L (G s) :=
    (L.intervalIntegral_comp_comm hGInt).symm
  have hGZero (s : ℝ) : L (G s) = 0 := by
    have hFixed : H3PhysicalRealFinVectorL2HilbertLerayFixed (G s) := by
      exact h3Audit_initialActualProjectedRHS_lerayFixed_allTimes hH3 s
    have hs :=
      (mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff (G s)).2 hFixed
    unfold h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule at hs
    change L (G s) = 0 at hs
    exact hs
  have hIntegralFixed :
      H3PhysicalRealFinVectorL2HilbertLerayFixed
        (∫ s in a..b, G s) := by
    rw [← mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff]
    change L (∫ s in a..b, G s) = 0
    rw [hComm]
    have hZero : (fun s : ℝ => L (G s)) =
        (fun _s : ℝ => (0 : H3SpectralFinVectorState)) := by
      funext s
      exact hGZero s
    rw [hZero]
    simp
  have hA : H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3AuditInitialOldPhysicalHilbertTotal hH3 a) :=
    h3Audit_initialOldPhysicalHilbert_lerayFixed_at_positiveTime
      hH3 a ⟨ha, hab.trans hb⟩
  have hB : H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3AuditInitialOldPhysicalHilbertTotal hH3 b) :=
    h3Audit_initialOldPhysicalHilbert_lerayFixed_at_positiveTime
      hH3 b ⟨ha.trans hab, hb⟩
  have hDefFixed : H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3AuditInitialOldPhysicalHilbertTotal hH3 b -
        h3AuditInitialOldPhysicalHilbertTotal hH3 a -
        ∫ s in a..b, G s) :=
    (H3PhysicalRealFinVectorL2HilbertLerayFixed.sub
      (H3PhysicalRealFinVectorL2HilbertLerayFixed.sub hB hA)
      hIntegralFixed)
  exact hDefFixed

/-- Solenoidal compact test pairings determine whether the entire physical
L² evolution defect is zero, without a strong time derivative assumption. -/
theorem h3Path_projectedFTCDefect_eq_zero_iff_solenoidalPairings244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    h3PathActualProjectedMomentumFTCDefect244 hH3 a b = 0 ↔
      ∀ φ : H3WeakTestVector,
        H3WeakTestVectorDivergenceFree φ →
        inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3PathActualProjectedMomentumFTCDefect244 hH3 a b) = 0 := by
  constructor
  · intro hZero φ _hφ
    rw [hZero]
    simp
  · intro hPair
    exact
      h3PhysicalRealFinVectorL2Hilbert_eq_zero_of_lerayFixed_of_divergenceFreeWeakTest_pairing_eq_zero
        (h3PathActualProjectedMomentumFTCDefect244 hH3 a b)
        (h3Path_projectedFTCDefect_lerayFixed_onStrict244 hH3 ha hab hb)
        hPair

/-- Failure of physical Hilbert evolution is observable by a *particular*
compact divergence-free weak test. -/
theorem h3Path_nonzeroProjectedFTCDefect_has_solenoidalWitness244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hNonzero : h3PathActualProjectedMomentumFTCDefect244 hH3 a b ≠ 0) :
    ∃ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ ∧
      inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PathActualProjectedMomentumFTCDefect244 hH3 a b) ≠ 0 := by
  classical
  by_contra hNo
  apply hNonzero
  apply (h3Path_projectedFTCDefect_eq_zero_iff_solenoidalPairings244
    hH3 ha hab hb).2
  intro φ hφ
  by_contra hPair
  exact hNo ⟨φ, hφ, hPair⟩

/-- Existing solenoidal weak FTC and the now automatic physical source
continuity identify the entire physical Hilbert increment on a strict window. -/
theorem h3Path_projectedFTCDefect_zeroOn_of_solenoidalWeakFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hWeak : H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b) :
    ∀ r : ℝ, r ∈ Set.Icc a b →
      h3PathActualProjectedMomentumFTCDefect244 hH3 a r = 0 := by
  have hGCont := h3Path_actualProjectedMomentumSource_continuousOnStrict244
    hH3 ha hab hb
  have hFfixed : ∀ r : ℝ, r ∈ Set.Icc a b →
      H3PhysicalRealFinVectorL2HilbertLerayFixed
        (h3AuditInitialOldPhysicalHilbertTotal hH3 r) := by
    intro r hr
    exact h3Audit_initialOldPhysicalHilbert_lerayFixed_at_positiveTime
      hH3 r ⟨lt_of_lt_of_le ha hr.1, lt_of_le_of_lt hr.2 hb⟩
  have hGfixed : ∀ r : ℝ,
      H3PhysicalRealFinVectorL2HilbertLerayFixed
        (h3PathActualProjectedMomentumSource244 hH3 r) := by
    intro r
    exact h3Audit_initialActualProjectedRHS_lerayFixed_allTimes hH3 r
  intro r hr
  have hEvolution :=
    h3Audit_physicalSolenoidalWeakFTC_implies_HilbertEvolution
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3)
      a b hab hGCont hFfixed hGfixed hWeak r hr
  apply (h3Path_actualProjectedMomentumFTCDefect_eq_zero_iff244 hH3 a r).2
  rw [hEvolution]
  abel

/-- Conversely, the exact physical Hilbert evolution on *every* prefix of a
strict interval implies solenoidal scalar weak FTC by commutation of a
continuous linear functional with the Bochner integral. -/
theorem h3Path_solenoidalWeakFTC_of_projectedFTCDefect_zeroOn244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hZero : ∀ r : ℝ, r ∈ Set.Icc a b →
      h3PathActualProjectedMomentumFTCDefect244 hH3 a r = 0) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hGCont :=
    h3Path_actualProjectedMomentumSource_continuousOnStrict244
      hH3 ha hab hb
  intro φ _hφ r hr
  let ψ : H3PhysicalRealFinVectorL2Hilbert :=
    h3WeakTestVectorPhysicalL2Hilbert φ
  have hSub : Set.Icc a r ⊆ Set.Icc a b := by
    intro s hs
    exact ⟨hs.1, hs.2.trans hr.2⟩
  have hInt : IntervalIntegrable G volume a r :=
    (hGCont.mono hSub).intervalIntegrable_of_Icc hr.1
  have hComm :
      inner ℝ ψ (∫ s in a..r, G s) =
        ∫ s in a..r, inner ℝ ψ (G s) := by
    change ((innerSL ℝ) ψ) (∫ s in a..r, G s) =
      ∫ s in a..r, ((innerSL ℝ) ψ) (G s)
    exact (((innerSL ℝ) ψ).intervalIntegral_comp_comm hInt).symm
  have hEvolution :=
    (h3Path_actualProjectedMomentumFTCDefect_eq_zero_iff244 hH3 a r).1
      (hZero r hr)
  calc
    inner ℝ ψ
        (h3AuditInitialOldPhysicalHilbertTotal hH3 r -
          h3AuditInitialOldPhysicalHilbertTotal hH3 a) =
      inner ℝ ψ (∫ s in a..r, G s) := by
        rw [hEvolution]
    _ = ∫ s in a..r, inner ℝ ψ (G s) := hComm

/-- Under the unconditional source continuity and Leray-fixedness already
proved in this repository, physical Hilbert defect vanishing on all prefixes
is *equivalent* to the compact solenoidal weak-FTC identity. -/
theorem h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    (∀ r : ℝ, r ∈ Set.Icc a b →
      h3PathActualProjectedMomentumFTCDefect244 hH3 a r = 0) ↔
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b := by
  constructor
  · exact h3Path_solenoidalWeakFTC_of_projectedFTCDefect_zeroOn244
      hH3 ha hab hb
  · exact h3Path_projectedFTCDefect_zeroOn_of_solenoidalWeakFTC244
      hH3 ha hab hb

/-- Existing canonical old projected-RHS weak FTC on a shortened restart
window cancels the actual, absolute-time Hilbert evolution defect at every
intermediate observation. No extra spectral-source identification is needed. -/
theorem h3Path_projectedFTCDefect_zeroOn_of_shortCanonicalWeakFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S t tau E : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hShort : LoggedPreterminalH3PathAdmissible u S)
    (hST : S ≤ T)
    (ht : t ∈ Set.Ioo (0 : ℝ) S)
    (htau : 0 < tau)
    (hEnd : t + tau < S)
    (hTail : CanonicalH3TailDataFrom u t S E)
    (hWeakFTC :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hShort.navier_stokes ht htau hEnd hTail) :
    ∀ r : ℝ, r ∈ Set.Icc t (t + tau) →
      h3PathActualProjectedMomentumFTCDefect244 hH3 t r = 0 := by
  have htPos : 0 < t := ht.1
  have hUpper : t < t + tau := by linarith
  have hb : t + tau < T := lt_of_lt_of_le hEnd hST
  have hSolenoidal : H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3)
      t (t + tau) := by
    exact h3Audit_initialCanonicalWeakFTC_implies_absoluteSolenoidalWeakFTC
      hH3 hShort hST ht htau hEnd hTail hWeakFTC
  exact h3Path_projectedFTCDefect_zeroOn_of_solenoidalWeakFTC244
    hH3 htPos hUpper hb hSolenoidal

end
end PrimeTensor.FirstMonomialTriad
