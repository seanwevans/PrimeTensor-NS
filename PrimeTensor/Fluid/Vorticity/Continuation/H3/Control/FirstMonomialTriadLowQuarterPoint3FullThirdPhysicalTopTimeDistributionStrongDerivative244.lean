import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionKernelFTCBridge244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionFromWeakFTC244
import Mathlib.Tactic

/-!
# Physical momentum distributions and actual strong Hilbert time derivatives

The connected-interval distribution kernel and the outer-to-inner FTC bridge
allow one to *localize* a distributional momentum equation around every strict
interior time. Combining the resulting physical weak FTC with the established
Leray-fixed weak-to-strong derivative theorem shows that the old physical L²
velocity has an actual Hilbert derivative equal to the projected physical RHS.

Conversely, a strong Hilbert time derivative gives the exact scalar derivative
against every compact solenoidal test, then weak FTC and the actual scalar
time-distribution momentum equation on the same strict interval.

This proves equivalence of two REGULARITY CONCLUSIONS under H³ path
admissibility; it does not derive either one from the pointwise old NS PDE.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set TopologicalSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

/-- A physical distributional momentum identity on `(a,b)` forces a strong
`L²`-Hilbert derivative at every individual time in `(a,b)`. No differentiation
of a spatial integral is assumed: the proof first recovers exact weak FTC on
an interior closed window enclosing the chosen time. -/
theorem h3Path_physicalHilbertHasDerivAt_of_distributionalMomentum_onStrict244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hMomentum : h3PathSolenoidalDistributionalMomentumOn244 hH3 a b)
    (s : ℝ) (hs : s ∈ Set.Ioo a b) :
    HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3 s) s := by
  let c : ℝ := (a + s) / 2
  let d : ℝ := (s + b) / 2
  have hac : a < c := by dsimp [c]; linarith [hs.1]
  have hcs : c < s := by dsimp [c]; linarith [hs.1]
  have hsd : s < d := by dsimp [d]; linarith [hs.2]
  have hdb : d < b := by dsimp [d]; linarith [hs.2]
  have hcd : c < d := hcs.trans hsd
  have hc : 0 < c := ha.trans hac
  have hd : d < T := hdb.trans hb
  have hWeak : H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) c d :=
    h3Path_solenoidalWeakFTC_of_outerDistributionalMomentum244
      hH3 ha hac hcd hdb hb hMomentum
  have hRCont : ContinuousOn
      (h3PathActualProjectedMomentumSource244 hH3) (Set.Icc c d) :=
    h3Path_actualProjectedMomentumSource_continuousOnStrict244
      hH3 hc hcd hd
  have hUFixed : ∀ t : ℝ, t ∈ Set.Icc c d →
      H3PhysicalRealFinVectorL2HilbertLerayFixed
        (h3AuditInitialOldPhysicalHilbertTotal hH3 t) := by
    intro t ht
    exact h3Audit_initialOldPhysicalHilbert_lerayFixed_at_positiveTime
      hH3 t ⟨lt_of_lt_of_le hc ht.1, lt_of_le_of_lt ht.2 hd⟩
  have hRFixed : ∀ t : ℝ,
      H3PhysicalRealFinVectorL2HilbertLerayFixed
        (h3PathActualProjectedMomentumSource244 hH3 t) := by
    intro t
    exact h3Audit_initialActualProjectedRHS_lerayFixed_allTimes hH3 t
  exact h3Audit_physicalSolenoidalWeakFTC_implies_HilbertHasDerivAt
    (h3AuditInitialOldPhysicalHilbertTotal hH3)
    (h3PathActualProjectedMomentumSource244 hH3)
    c d hcd hRCont hUFixed hRFixed hWeak s ⟨hcs, hsd⟩

/-- A strong physical L² time derivative on the open interval yields the
genuine scalar distributional momentum PDE there, without a separately
assumed distributional momentum or weak-FTC identity. -/
theorem h3Path_distributionalMomentum_of_physicalHilbertHasDerivAt_onStrict244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hStrong : ∀ s : ℝ, s ∈ Set.Ioo a b →
      HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (h3PathActualProjectedMomentumSource244 hH3 s) s) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b := by
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
    have hMapped : HasDerivAt
        (fun r : ℝ => ((innerSL ℝ) ψ)
          (h3AuditInitialOldPhysicalHilbertTotal hH3 r))
        (((innerSL ℝ) ψ) (h3PathActualProjectedMomentumSource244 hH3 s)) s :=
      (((innerSL ℝ) ψ).hasFDerivAt).comp_hasDerivAt s (hStrong s hs)
    exact hMapped
  have hWeak : H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b :=
    h3Path_solenoidalWeakFTC_of_pointwiseWeakMomentum244
      hH3 ha hab hb hScalar
  exact h3Path_distributionalMomentum_of_physicalSolenoidalWeakFTC244
    hH3 ha hab hb hWeak

/-- **Same-interval characterization:** under the H³ admissibility already
available in this development, the distributional momentum identity on a
strict time interval is equivalent to a genuine strong `L²` time derivative
of the old physical velocity at every interior time. The pointwise classical
NS PDE-to-either-side implication remains a distinct analytic task. -/
theorem h3Path_distributionalMomentum_iff_physicalHilbertHasDerivAt_onStrict244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b ↔
      ∀ s : ℝ, s ∈ Set.Ioo a b →
        HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
          (h3PathActualProjectedMomentumSource244 hH3 s) s := by
  constructor
  · intro hMomentum s hs
    exact h3Path_physicalHilbertHasDerivAt_of_distributionalMomentum_onStrict244
      hH3 ha hab hb hMomentum s hs
  · intro hStrong
    exact h3Path_distributionalMomentum_of_physicalHilbertHasDerivAt_onStrict244
      hH3 ha hab hb hStrong

end
end PrimeTensor.FirstMonomialTriad
