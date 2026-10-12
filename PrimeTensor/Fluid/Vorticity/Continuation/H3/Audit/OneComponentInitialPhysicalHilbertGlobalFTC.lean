import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalHilbertTimeEvolution
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPositiveStrongDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Full positive-time physical Hilbert momentum FTC

The preceding audit constructed strong physical L² momentum derivatives on
canonical interior restart windows and at every strictly positive time, under
the independently specified old-branch temporal joint-continuity premise.

Here the reconstructed physical diffusion-minus-Leray source is proved
continuous over the entire open preterminal interval. It is therefore
Bochner-integrable between *any* two strictly positive times, even when the
endpoints occur in reverse order. The unrestricted Banach-valued fundamental
theorem of calculus then gives the exact physical L² vector increment.

The result is intrinsic to the actual old velocity, not a selected restart,
and involves no separately assumed two-time momentum identity or local
source-integrability family.

This does not prove the old temporal joint-continuity premise, nor an L¹
source estimate reaching zero time. Those, the initial relative-energy
residual, and terminal endpoint hypotheses remain independent.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeInitialPhysicalHilbertGlobalFTC
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 800000

/-- The actual projected physical RHS is strongly continuous throughout
the open preterminal time interval. This needs only the admitted H³ path,
not temporal-derivative joint continuity. -/
theorem h3Audit_initialActualProjectedRHS_continuousOn_positiveTime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    ContinuousOn
      (fun s : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 s -
          h3AuditInitialActualSpectralLerayTotal hH3 s)
      (Set.Ioo (0 : ℝ) T) := by
  have hU : ContinuousOn
      (h3AuditActualSpectralVelocityTotal hH3)
      (Set.Ioo (0 : ℝ) T) :=
    h3Audit_initialActualSpectralVelocity_continuousOn hH3
  have hD : ContinuousOn
      (h3AuditInitialActualSpectralLaplacianTotal hH3)
      (Set.Ioo (0 : ℝ) T) := by
    have hComp :=
      continuous_h3AuditSpectralPhysicalLaplacian.comp_continuousOn hU
    apply hComp.congr
    intro s hs
    simp only [h3AuditInitialActualSpectralLaplacianTotal,
      dite_eq_left hs, Function.comp_apply]
  have hN : ContinuousOn
      (h3AuditInitialActualSpectralLerayTotal hH3)
      (Set.Ioo (0 : ℝ) T) := by
    have hComp :=
      continuous_h3AuditSpectralPhysicalLerayForcing.comp_continuousOn hU
    apply hComp.congr
    intro s hs
    simp only [h3AuditInitialActualSpectralLerayTotal,
      dite_eq_left hs, Function.comp_apply]
  exact hD.sub hN

/-- No independent positive-subinterval Bochner integrability assumption is
needed. Any two positive preterminal times are contained in a closed strict
subinterval on which the projected source is continuous. This also handles
reversed and equal endpoint times. -/
theorem h3Audit_initialActualProjectedRHS_intervalIntegrable_between_positiveTimes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    IntervalIntegrable
      (fun r : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 r -
          h3AuditInitialActualSpectralLerayTotal hH3 r)
      volume s t := by
  let a : ℝ := min s t / 2
  let b : ℝ := (max s t + T) / 2
  have hMin : 0 < min s t := lt_min hs.1 ht.1
  have hMax : max s t < T := max_lt hs.2 ht.2
  have hOrdered : min s t ≤ max s t := min_le_max
  have ha : 0 < a := by
    dsimp only [a]
    linarith only [hMin]
  have hab : a < b := by
    dsimp only [a, b]
    linarith only [hMin, hMax, hOrdered]
  have hb : b < T := by
    dsimp only [b]
    linarith only [hMax]
  have hSub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T := by
    intro r hr
    exact ⟨lt_of_lt_of_le ha hr.1, lt_of_le_of_lt hr.2 hb⟩
  have hCont : ContinuousOn
      (fun r : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 r -
          h3AuditInitialActualSpectralLerayTotal hH3 r)
      (Set.Icc a b) :=
    (h3Audit_initialActualProjectedRHS_continuousOn_positiveTime hH3).mono hSub
  have hWhole : IntervalIntegrable
      (fun r : ℝ =>
        h3AuditInitialActualSpectralLaplacianTotal hH3 r -
          h3AuditInitialActualSpectralLerayTotal hH3 r)
      volume a b :=
    hCont.intervalIntegrable_of_Icc hab.le
  apply hWhole.mono_set
  intro r hr
  have hrSpan : r ∈ Set.Icc (min s t) (max s t) := hr
  have har : a ≤ r := by
    dsimp only [a]
    linarith only [hMin, hrSpan.1]
  have hrb : r ≤ b := by
    dsimp only [b]
    linarith only [hMax, hrSpan.2]
  simpa only [Set.uIcc_of_le hab.le] using
    (show r ∈ Set.Icc a b from ⟨har, hrb⟩)

/-- The actual physical old Hilbert velocity obeys the exact Bochner FTC
between arbitrary (possibly reversed) positive preterminal times. The
transported canonical weak FTC is consumed through the previously derived
strong derivative; no new two-time assumption is introduced. -/
theorem h3Audit_initialOldJoint_implies_physicalHilbertFTC_between_positiveTimes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3AuditInitialOldPhysicalHilbertTotal hH3 t -
      h3AuditInitialOldPhysicalHilbertTotal hH3 s =
        ∫ r in s..t,
          (h3AuditInitialActualSpectralLaplacianTotal hH3 r -
            h3AuditInitialActualSpectralLerayTotal hH3 r) := by
  have hIntegrable :=
    h3Audit_initialActualProjectedRHS_intervalIntegrable_between_positiveTimes
      hH3 s t hs ht
  have hFTC :
      (∫ r in s..t,
        (h3AuditInitialActualSpectralLaplacianTotal hH3 r -
          h3AuditInitialActualSpectralLerayTotal hH3 r)) =
      h3AuditInitialOldPhysicalHilbertTotal hH3 t -
        h3AuditInitialOldPhysicalHilbertTotal hH3 s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx =>
        h3Audit_initialOldJoint_implies_physicalHilbertHasDerivAt_at_positiveTime
          hH3 hOldJoint x
          (h3Audit_positiveUnorderedInterval_strict T s t hs ht hx))
      hIntegrable
  exact hFTC.symm

/-- A convenient forward evolution formula: its baseline is *any* strictly
positive time, with no requirement that both times lie in the same specified
canonical window. -/
theorem h3Audit_initialOldJoint_implies_physicalHilbertEvolution_between_positiveTimes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3AuditInitialOldPhysicalHilbertTotal hH3 t =
      h3AuditInitialOldPhysicalHilbertTotal hH3 s +
        ∫ r in s..t,
          (h3AuditInitialActualSpectralLaplacianTotal hH3 r -
            h3AuditInitialActualSpectralLerayTotal hH3 r) := by
  have hFTC :=
    h3Audit_initialOldJoint_implies_physicalHilbertFTC_between_positiveTimes
      hH3 hOldJoint s t hs ht
  exact (sub_eq_iff_eq_add.mp hFTC).trans (add_comm _ _)

/-- The positive-time momentum identity also gives ordinary strong
Fréchet differentiability of the actual physical Hilbert velocity. -/
theorem h3Audit_initialOldJoint_implies_physicalHilbertDifferentiableOn_positiveTime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T) :
    DifferentiableOn ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (Set.Ioo (0 : ℝ) T) := by
  intro s hs
  exact
    (h3Audit_initialOldJoint_implies_physicalHilbertHasDerivAt_at_positiveTime
      hH3 hOldJoint s hs).differentiableAt.differentiableWithinAt

end
end Euclidean
end Bridge
end PrimeTensor
