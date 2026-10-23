import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopProjectedFTCDefectCocycle244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialAutomaticOldTimeMeasurability
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialSolenoidalWeakFTCStrongDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Differentiated solenoidal momentum versus the physical FTC defect

The physical velocity U and the projected Navier--Stokes source R are known,
without an old temporal weak-FTC assumption, to be continuous with values in
the physical L² Hilbert space at strictly positive times. Thus for any compact
solenoidal weak test phi, both scalar functions <phi,U(t)> and <phi,R(t)> are
continuous on a closed strict-time interval.

If the derivative of the first scalar function is the second at each *open*
interior time, the ordinary scalar fundamental theorem of calculus produces
weak momentum evolution on the *closed* interval. Leray-fixed weak-test
determination then kills the entire physical Hilbert FTC defect. Conversely,
weak FTC gives an actual strong Hilbert derivative on each interior point,
and hence all scalar weak derivatives. This exactly isolates the remaining
PDE/interchange-of-spatial-integration question.

The pointwise scalar derivative premise is NOT derived from separate continuity
or from the spatially pointwise classical PDE. Neither continuity of R nor
continuity of U alone implies it. In particular, this file does not claim an
unconditional eighth-moment theorem or unconditional Navier--Stokes closure.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A compact-solenoidal *pointwise differentiated* momentum identity suffices
for the exact scalar weak FTC. Crucially, the classical scalar FTC is applied
only after establishing continuity of the actual physical Hilbert velocity,
continuity of the projected source, and integrability of its test pairing. -/
theorem h3Path_solenoidalWeakFTC_of_pointwiseWeakMomentum244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hDerivative : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∀ s : ℝ, s ∈ Set.Ioo a b →
        HasDerivAt
          (fun r : ℝ => inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3AuditInitialOldPhysicalHilbertTotal hH3 r))
          (inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PathActualProjectedMomentumSource244 hH3 s)) s) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b := by
  let U : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let R : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hSub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hb⟩
  have hUContinuous : ContinuousOn U (Set.Icc a b) :=
    (h3Audit_initialOldPhysicalHilbert_continuousOn hH3).mono hSub
  have hRContinuous : ContinuousOn R (Set.Icc a b) :=
    h3Path_actualProjectedMomentumSource_continuousOnStrict244
      hH3 ha hab hb
  intro φ hφ r hr
  let ψ : H3PhysicalRealFinVectorL2Hilbert :=
    h3WeakTestVectorPhysicalL2Hilbert φ
  have hUScalar : ContinuousOn
      (fun s : ℝ => inner ℝ ψ (U s)) (Set.Icc a b) := by
    change ContinuousOn
      (fun s : ℝ => ((innerSL ℝ) ψ) (U s)) (Set.Icc a b)
    exact ((innerSL ℝ) ψ).continuous.comp_continuousOn hUContinuous
  have hRScalar : ContinuousOn
      (fun s : ℝ => inner ℝ ψ (R s)) (Set.Icc a b) := by
    change ContinuousOn
      (fun s : ℝ => ((innerSL ℝ) ψ) (R s)) (Set.Icc a b)
    exact ((innerSL ℝ) ψ).continuous.comp_continuousOn hRContinuous
  have hSubset : Set.Icc a r ⊆ Set.Icc a b := by
    intro s hs
    exact ⟨hs.1, hs.2.trans hr.2⟩
  have hIntegrable : IntervalIntegrable
      (fun s : ℝ => inner ℝ ψ (R s)) volume a r :=
    (hRScalar.mono hSubset).intervalIntegrable_of_Icc hr.1
  have hFTC :
      (∫ s in a..r, inner ℝ ψ (R s)) =
        inner ℝ ψ (U r) - inner ℝ ψ (U a) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hr.1 (hUScalar.mono hSubset)
      (by
        intro s hs
        have hsAB : s ∈ Set.Ioo a b :=
          ⟨hs.1, lt_of_lt_of_le hs.2 hr.2⟩
        exact hDerivative φ hφ s hsAB)
      hIntegrable
  change inner ℝ ψ (U r - U a) =
    ∫ s in a..r, inner ℝ ψ (R s)
  rw [inner_sub_right]
  exact hFTC.symm

/-- Hence pointwise scalar momentum differentiation annihilates the ACTUAL
physical Hilbert FTC defect on every prefix of a strict-time interval. -/
theorem h3Path_projectedFTCDefect_zeroOn_of_pointwiseWeakMomentum244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hDerivative : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∀ s : ℝ, s ∈ Set.Ioo a b →
        HasDerivAt
          (fun r : ℝ => inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3AuditInitialOldPhysicalHilbertTotal hH3 r))
          (inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PathActualProjectedMomentumSource244 hH3 s)) s) :
    ∀ r : ℝ, r ∈ Set.Icc a b →
      h3PathActualProjectedMomentumFTCDefect244 hH3 a r = 0 := by
  exact (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
    hH3 ha hab hb).2
      (h3Path_solenoidalWeakFTC_of_pointwiseWeakMomentum244
        hH3 ha hab hb hDerivative)

/-- Conversely, exact solenoidal weak FTC recovers every compact-test
pointwise scalar derivative. The strong Hilbert derivative is supplied by the
existing Leray-fixed weak-to-strong theorem, not postulated here. -/
theorem h3Path_pointwiseWeakMomentum_of_solenoidalWeakFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hWeak : H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b) :
    ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∀ s : ℝ, s ∈ Set.Ioo a b →
        HasDerivAt
          (fun r : ℝ => inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3AuditInitialOldPhysicalHilbertTotal hH3 r))
          (inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PathActualProjectedMomentumSource244 hH3 s)) s := by
  let U : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let R : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hRContinuous : ContinuousOn R (Set.Icc a b) :=
    h3Path_actualProjectedMomentumSource_continuousOnStrict244
      hH3 ha hab hb
  have hUFixed : ∀ s : ℝ, s ∈ Set.Icc a b →
      H3PhysicalRealFinVectorL2HilbertLerayFixed (U s) := by
    intro s hs
    exact h3Audit_initialOldPhysicalHilbert_lerayFixed_at_positiveTime
      hH3 s ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hb⟩
  have hRFixed : ∀ s : ℝ,
      H3PhysicalRealFinVectorL2HilbertLerayFixed (R s) := by
    intro s
    exact h3Audit_initialActualProjectedRHS_lerayFixed_allTimes hH3 s
  intro φ _hφ s hs
  let ψ : H3PhysicalRealFinVectorL2Hilbert :=
    h3WeakTestVectorPhysicalL2Hilbert φ
  have hStrong : HasDerivAt U (R s) s :=
    h3Audit_physicalSolenoidalWeakFTC_implies_HilbertHasDerivAt
      U R a b hab hRContinuous hUFixed hRFixed hWeak s hs
  have hMapped : HasDerivAt
      (fun r : ℝ => ((innerSL ℝ) ψ) (U r))
      (((innerSL ℝ) ψ) (R s)) s :=
    (((innerSL ℝ) ψ).hasFDerivAt).comp_hasDerivAt s hStrong
  exact hMapped

/-- The differentiated solenoidal momentum identity is equivalent to weak
FTC once the independently-proved velocity and source continuities are used.
No assumption of space-time joint continuity is smuggled into the equivalence. -/
theorem h3Path_pointwiseWeakMomentum_iff_solenoidalWeakFTC244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    (∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∀ s : ℝ, s ∈ Set.Ioo a b →
        HasDerivAt
          (fun r : ℝ => inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3AuditInitialOldPhysicalHilbertTotal hH3 r))
          (inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PathActualProjectedMomentumSource244 hH3 s)) s) ↔
      H3AuditPhysicalSolenoidalWeakFTCOn
        (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (h3PathActualProjectedMomentumSource244 hH3) a b := by
  constructor
  · exact h3Path_solenoidalWeakFTC_of_pointwiseWeakMomentum244
      hH3 ha hab hb
  · exact h3Path_pointwiseWeakMomentum_of_solenoidalWeakFTC244
      hH3 ha hab hb

/-- A nonzero Hilbert FTC defect therefore forces a genuinely identifiable
failure of scalar differentiation-under-the-compact-spatial-integral: there
is some solenoidal compact test and some STRICT interior physical time where
the actual derivative is not the projected-source pairing. -/
theorem h3Path_nonzeroProjectedFTCDefect_forces_pointwiseWeakMomentumFailure244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hNonzero : h3PathActualProjectedMomentumFTCDefect244 hH3 a b ≠ 0) :
    ∃ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ ∧
      ∃ s : ℝ, s ∈ Set.Ioo a b ∧
        ¬ HasDerivAt
          (fun r : ℝ => inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3AuditInitialOldPhysicalHilbertTotal hH3 r))
          (inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PathActualProjectedMomentumSource244 hH3 s)) s := by
  classical
  by_contra hNo
  have hAll : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∀ s : ℝ, s ∈ Set.Ioo a b →
        HasDerivAt
          (fun r : ℝ => inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3AuditInitialOldPhysicalHilbertTotal hH3 r))
          (inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PathActualProjectedMomentumSource244 hH3 s)) s := by
    intro φ hφ s hs
    by_contra hFail
    exact hNo ⟨φ, hφ, s, hs, hFail⟩
  have hZero := h3Path_projectedFTCDefect_zeroOn_of_pointwiseWeakMomentum244
    hH3 ha hab hb hAll
  exact hNonzero (hZero b ⟨hab.le, le_rfl⟩)

end
end PrimeTensor.FirstMonomialTriad
