import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopL1WeakMomentumError244
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic

/-!
# Absolutely continuous solenoidal momentum and almost-everywhere temporal errors

Pointwise differentiation of spatially tested old momentum was an assumption
in the preceding L¹ weak error bridge. The appropriate analytic hypothesis
for a distributional-time construction is instead:

* each compact solenoidal scalar momentum pairing is absolutely continuous
  on the strict physical time interval;
* its a.e. time derivative is the projected source pairing plus an L¹ error;
* the scalar errors have a common a.e. L¹-in-time test-dual envelope.

Mathlib's absolute-continuity FTC then yields the integrated scalar identity,
which the repository's sharp Leray-fixed weak-test density turns into a Hilbert
L² FTC-defect bound. These hypotheses are NOT deduced here from the separated
pointwise classical Navier--Stokes equation. Absolute continuity is essential:
continuity plus an a.e. derivative identity does not in general yield FTC.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Distributional-time-compatible weak momentum interface: absolute
continuity plus an a.e. scalar derivative and an L¹ test-dual envelope.
No strong L² temporal derivative or pressure-gradient representative is assumed. -/
def h3PathACAEWeakMomentumErrorOn244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    AbsolutelyContinuousOnInterval
      (fun r : ℝ => inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3AuditInitialOldPhysicalHilbertTotal hH3 r)) a b ∧
    ∃ e : ℝ → ℝ,
      IntervalIntegrable e volume a b ∧
      (∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Ioc a b →
        HasDerivAt
          (fun r : ℝ => inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3AuditInitialOldPhysicalHilbertTotal hH3 r))
          (inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PathActualProjectedMomentumSource244 hH3 s) + e s) s) ∧
      (∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Ioc a b →
        |e s| ≤ g s * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖)

/-- Scalar absolute-continuity FTC: an almost-everywhere differentiated
weak momentum equation controls the ACTUAL Hilbert defect's test pairing.
This does not require the derivative identity at every time. -/
theorem h3Path_projectedFTCDefect_pairing_le_ACAEWeakError244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (g : ℝ → ℝ) (hg : IntervalIntegrable g volume a b)
    (hWeak : h3PathACAEWeakMomentumErrorOn244 hH3 a b g)
    (r : ℝ) (hr : r ∈ Set.Icc a b)
    (φ : H3WeakTestVector) (hφ : H3WeakTestVectorDivergenceFree φ) :
    ‖inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3PathActualProjectedMomentumFTCDefect244 hH3 a r)‖ ≤
      (∫ s in a..r, g s) * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖ := by
  let U : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let R : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  let ψ : H3PhysicalRealFinVectorL2Hilbert :=
    h3WeakTestVectorPhysicalL2Hilbert φ
  obtain ⟨hAC, e, heInt, heDeriv, heBound⟩ := hWeak φ hφ
  have hSub : Set.Icc a r ⊆ Set.Icc a b := by
    intro s hs
    exact ⟨hs.1, hs.2.trans hr.2⟩
  have hACr : AbsolutelyContinuousOnInterval
      (fun s : ℝ => inner ℝ ψ (U s)) a r := by
    apply hAC.mono
    rw [Set.uIcc_of_le hr.1, Set.uIcc_of_le hab.le]
    exact hSub
  have hRCont : ContinuousOn R (Set.Icc a r) :=
    (h3Path_actualProjectedMomentumSource_continuousOnStrict244
      hH3 ha hab hb).mono hSub
  have hRScalar : ContinuousOn
      (fun s : ℝ => inner ℝ ψ (R s)) (Set.Icc a r) := by
    change ContinuousOn (fun s : ℝ => ((innerSL ℝ) ψ) (R s)) (Set.Icc a r)
    exact ((innerSL ℝ) ψ).continuous.comp_continuousOn hRCont
  have hRInt : IntervalIntegrable
      (fun s : ℝ => inner ℝ ψ (R s)) volume a r :=
    hRScalar.intervalIntegrable_of_Icc hr.1
  have heIntR : IntervalIntegrable e volume a r := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hr.1).2
    have hIntOnB : IntegrableOn e (Set.Ioo a b) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).1 heInt
    exact hIntOnB.mono_set (by
      intro s hs
      exact ⟨hs.1, lt_of_lt_of_le hs.2 hr.2⟩)
  have hgIntR : IntervalIntegrable g volume a r := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hr.1).2
    have hIntOnB : IntegrableOn g (Set.Ioo a b) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).1 hg
    exact hIntOnB.mono_set (by
      intro s hs
      exact ⟨hs.1, lt_of_lt_of_le hs.2 hr.2⟩)
  have hDerivativeIntegral :
      (∫ s in a..r, inner ℝ ψ (R s) + e s) =
        inner ℝ ψ (U r) - inner ℝ ψ (U a) := by
    have hFTC := hACr.integral_deriv_eq_sub
    have hCongr :
        (∫ s in a..r, deriv (fun q : ℝ => inner ℝ ψ (U q)) s) =
          ∫ s in a..r, inner ℝ ψ (R s) + e s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [heDeriv] with s hsDeriv hs
      rw [Set.uIoc_of_le hr.1] at hs
      exact (hsDeriv ⟨hs.1, hs.2.trans hr.2⟩).deriv
    rw [hCongr] at hFTC
    exact hFTC
  rw [intervalIntegral.integral_add hRInt heIntR] at hDerivativeIntegral
  have hRVectorInt : IntervalIntegrable R volume a r :=
    hRCont.intervalIntegrable_of_Icc hr.1
  have hComm :
      inner ℝ ψ (∫ s in a..r, R s) =
        ∫ s in a..r, inner ℝ ψ (R s) := by
    change ((innerSL ℝ) ψ) (∫ s in a..r, R s) =
      ∫ s in a..r, ((innerSL ℝ) ψ) (R s)
    exact (((innerSL ℝ) ψ).intervalIntegral_comp_comm hRVectorInt).symm
  have hResidual :
      inner ℝ ψ (h3PathActualProjectedMomentumFTCDefect244 hH3 a r) =
        ∫ s in a..r, e s := by
    change inner ℝ ψ (U r - U a - ∫ s in a..r, R s) = _
    rw [inner_sub_right, inner_sub_right, hComm]
    linarith only [hDerivativeIntegral]
  have hMajorInt : IntervalIntegrable
      (fun s : ℝ => g s * ‖ψ‖) volume a r :=
    hgIntR.mul_const ‖ψ‖
  have hMajorAE :
      ∀ᵐ s ∂(volume : Measure ℝ),
        s ∈ Set.Ioc a r → ‖e s‖ ≤ g s * ‖ψ‖ := by
    filter_upwards [heBound] with s hsBound hs
    have hsAB : s ∈ Set.Ioc a b := ⟨hs.1, hs.2.trans hr.2⟩
    simpa only [Real.norm_eq_abs] using hsBound hsAB
  have hIntBound :
      ‖∫ s in a..r, e s‖ ≤
        ∫ s in a..r, g s * ‖ψ‖ :=
    intervalIntegral.norm_integral_le_of_norm_le hr.1 hMajorAE hMajorInt
  rw [hResidual]
  calc
    ‖∫ s in a..r, e s‖ ≤
        ∫ s in a..r, g s * ‖ψ‖ := hIntBound
    _ = (∫ s in a..r, g s) * ‖ψ‖ := by
      rw [intervalIntegral.integral_mul_const]

/-- The sharp solenoidal density estimate upgrades a.e. scalar weak
momentum differentiation, under absolute continuity, to a Hilbert L² bound. -/
theorem h3Path_projectedFTCDefect_norm_le_ACAEWeakError244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (g : ℝ → ℝ) (hg : IntervalIntegrable g volume a b)
    (hg0 : ∀ s : ℝ, s ∈ Set.Icc a b → 0 ≤ g s)
    (hWeak : h3PathACAEWeakMomentumErrorOn244 hH3 a b g) :
    ∀ r : ℝ, r ∈ Set.Icc a b →
      ‖h3PathActualProjectedMomentumFTCDefect244 hH3 a r‖ ≤
        ∫ s in a..r, g s := by
  intro r hr
  by_cases har : a < r
  · have hNonneg : 0 ≤ ∫ s in a..r, g s := by
      apply intervalIntegral.integral_nonneg har.le
      intro s hs
      exact hg0 s ⟨hs.1, hs.2.trans hr.2⟩
    apply h3PhysicalL2_norm_le_of_lerayFixed_solenoidalTestBound244
      (h3PathActualProjectedMomentumFTCDefect244 hH3 a r)
      (h3Path_projectedFTCDefect_lerayFixed_onStrict244
        hH3 ha har (lt_of_le_of_lt hr.2 hb)) hNonneg
    intro φ hφ
    exact h3Path_projectedFTCDefect_pairing_le_ACAEWeakError244
      hH3 ha hab hb g hg hWeak r hr φ hφ
  · have hra : r = a := le_antisymm (le_of_not_gt har) hr.1
    subst r
    simp [h3PathActualProjectedMomentumFTCDefect244]

/-- Vanishing a.e. weak momentum errors with absolutely continuous tested
velocity produce exact physical solenoidal weak FTC. This explicitly retains
absolute continuity as an analytic premise, rather than inferring it from
mere time continuity or the pointwise PDE. -/
theorem h3Path_solenoidalWeakFTC_of_vanishingACAEWeakError244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hSmall : ∀ η : ℝ, 0 < η →
      ∃ g : ℝ → ℝ,
        IntervalIntegrable g volume a b ∧
        (∀ s : ℝ, s ∈ Set.Icc a b → 0 ≤ g s) ∧
        h3PathACAEWeakMomentumErrorOn244 hH3 a b g ∧
        (∀ r : ℝ, r ∈ Set.Icc a b →
          (∫ s in a..r, g s) ≤ η)) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b := by
  apply (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
    hH3 ha hab hb).1
  intro r hr
  let D : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumFTCDefect244 hH3 a r
  by_contra hD
  have hPos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have hHalf : 0 < ‖D‖ / 2 := by positivity
  obtain ⟨g, hg, hg0, hWeak, hMass⟩ := hSmall (‖D‖ / 2) hHalf
  have hBound := h3Path_projectedFTCDefect_norm_le_ACAEWeakError244
    hH3 ha hab hb g hg hg0 hWeak r hr
  have hFinal : ‖D‖ ≤ ‖D‖ / 2 :=
    hBound.trans (hMass r hr)
  linarith

end
end PrimeTensor.FirstMonomialTriad
