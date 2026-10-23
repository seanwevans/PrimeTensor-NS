import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopPointwiseSolenoidalMomentum244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialAutomaticOldTimeMeasurability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Stability of physical projected FTC under consistent time-regularization

An exact smooth Hilbert-valued momentum equation for an approximating velocity
and source transfers to the actual physical path if both approximants converge
uniformly in L² on a compact strictly preterminal time interval.

The quantitative error is `2 ε + (b-a) ε`: the first two errors are the
velocity snapshots, and the last is the integrated projected-source error.
The key step is the vector-valued FTC for the approximant, followed by the
Bochner integral norm estimate. This is NOT an assertion that arbitrary time
mollification satisfies the differentiated Navier--Stokes equation: that
consistent-mollification identity is the remaining analytic obligation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A regularized Hilbert momentum pair with exact time derivative and
uniform physical L² approximation of the actual velocity and source. The
regularized source need not be a Navier--Stokes source itself. -/
def h3PathConsistentSmoothMomentumApproxOn244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b ε : ℝ) : Prop :=
  ∃ (V W : ℝ → H3PhysicalRealFinVectorL2Hilbert),
    ContinuousOn V (Set.Icc a b) ∧
    ContinuousOn W (Set.Icc a b) ∧
    (∀ t : ℝ, t ∈ Set.Ioo a b → HasDerivAt V (W t) t) ∧
    (∀ t : ℝ, t ∈ Set.Icc a b →
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t - V t‖ ≤ ε) ∧
    (∀ t : ℝ, t ∈ Set.Icc a b →
      ‖h3PathActualProjectedMomentumSource244 hH3 t - W t‖ ≤ ε)

/-- An exact differentiated equation for one smooth Hilbert approximant gives
a quantitative upper bound on the ACTUAL projected Hilbert FTC defect. -/
theorem h3Path_projectedFTCDefect_norm_le_of_smoothMomentumApprox244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b ε : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hApprox : h3PathConsistentSmoothMomentumApproxOn244 hH3 a b ε) :
    ‖h3PathActualProjectedMomentumFTCDefect244 hH3 a b‖ ≤
      (2 + (b - a)) * ε := by
  rcases hApprox with ⟨V, W, hVCont, hWCont, hVDeriv, hVClose, hWClose⟩
  let U : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let R : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hWInt : IntervalIntegrable W volume a b :=
    hWCont.intervalIntegrable_of_Icc hab.le
  have hRCont : ContinuousOn R (Set.Icc a b) :=
    h3Path_actualProjectedMomentumSource_continuousOnStrict244
      hH3 ha hab hb
  have hRInt : IntervalIntegrable R volume a b :=
    h3Path_actualProjectedMomentumSource_intervalIntegrableStrict244
      hH3 ha hab hb
  have hFTC : (∫ t in a..b, W t) = V b - V a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hab.le hVCont hVDeriv hWInt
  have hIntegralSub :
      (∫ t in a..b, W t - R t) =
        (∫ t in a..b, W t) - (∫ t in a..b, R t) :=
    intervalIntegral.integral_sub hWInt hRInt
  have hNorm :
      ‖∫ t in a..b, W t - R t‖ ≤ ε * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    have htIoc : t ∈ Set.Ioc a b := by
      simpa only [Set.uIoc_of_le hab.le] using ht
    have htIcc : t ∈ Set.Icc a b := ⟨htIoc.1.le, htIoc.2⟩
    simpa only [norm_sub_rev] using hWClose t htIcc
  have hExpr :
      h3PathActualProjectedMomentumFTCDefect244 hH3 a b =
        (U b - V b) - (U a - V a) +
          (∫ t in a..b, W t - R t) := by
    change U b - U a - (∫ t in a..b, R t) = _
    rw [hIntegralSub, hFTC]
    abel
  rw [hExpr]
  calc
    ‖(U b - V b) - (U a - V a) +
        (∫ t in a..b, W t - R t)‖ ≤
      ‖(U b - V b) - (U a - V a)‖ +
        ‖∫ t in a..b, W t - R t‖ := norm_add_le _ _
    _ ≤ (‖U b - V b‖ + ‖U a - V a‖) +
        ‖∫ t in a..b, W t - R t‖ :=
      add_le_add_left (norm_sub_le _ _) _
    _ ≤ (ε + ε) + ε * |b - a| :=
      add_le_add (add_le_add
        (hVClose b ⟨hab.le, le_rfl⟩)
        (hVClose a ⟨le_rfl, hab.le⟩)) hNorm
    _ = (2 + (b - a)) * ε := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab.le)]
      ring

/-- Arbitrarily accurate *consistent* smooth momentum approximations imply
exact physical Hilbert FTC on one strict interval. This is a stability theorem,
not an assertion that the approximants exist for the old solution. -/
theorem h3Path_projectedFTCDefect_zero_of_consistentSmoothApproximations244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hAll : ∀ ε : ℝ, 0 < ε →
      h3PathConsistentSmoothMomentumApproxOn244 hH3 a b ε) :
    h3PathActualProjectedMomentumFTCDefect244 hH3 a b = 0 := by
  let D : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumFTCDefect244 hH3 a b
  by_contra hNe
  have hPos : 0 < ‖D‖ := norm_pos_iff.mpr hNe
  let C : ℝ := 2 + (b - a)
  have hC : 0 < C := by
    dsimp only [C]
    linarith
  let ε : ℝ := ‖D‖ / (2 * C)
  have hε : 0 < ε := by
    dsimp only [ε]
    positivity
  have hBound :=
    h3Path_projectedFTCDefect_norm_le_of_smoothMomentumApprox244
      hH3 ha hab hb (hAll ε hε)
  have hHalf : C * ε = ‖D‖ / 2 := by
    dsimp only [ε]
    have hC0 : C ≠ 0 := ne_of_gt hC
    field_simp [hC0]
  change ‖D‖ ≤ C * ε at hBound
  rw [hHalf] at hBound
  linarith

/-- One family of uniformly convergent consistent smooth momentum pairs,
valid on the entire strict interval, kills ALL of its prefix FTC defects. -/
theorem h3Path_projectedFTCDefect_zeroOn_of_consistentSmoothApproximations244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (_hab : a < b) (hb : b < T)
    (hAll : ∀ ε : ℝ, 0 < ε →
      h3PathConsistentSmoothMomentumApproxOn244 hH3 a b ε) :
    ∀ r : ℝ, r ∈ Set.Icc a b →
      h3PathActualProjectedMomentumFTCDefect244 hH3 a r = 0 := by
  intro r hr
  rcases (lt_or_eq_of_le hr.1) with hlt | heq
  · apply h3Path_projectedFTCDefect_zero_of_consistentSmoothApproximations244
      hH3 ha hlt (lt_of_le_of_lt hr.2 hb)
    intro ε hε
    rcases hAll ε hε with
      ⟨V, W, hVCont, hWCont, hDeriv, hVClose, hWClose⟩
    have hSub : Set.Icc a r ⊆ Set.Icc a b := by
      intro s hs
      exact ⟨hs.1, hs.2.trans hr.2⟩
    refine ⟨V, W, hVCont.mono hSub, hWCont.mono hSub, ?_, ?_, ?_⟩
    · intro t ht
      exact hDeriv t ⟨ht.1, lt_of_lt_of_le ht.2 hr.2⟩
    · intro t ht
      exact hVClose t (hSub ht)
    · intro t ht
      exact hWClose t (hSub ht)
  · have hrEq : r = a := heq.symm
    subst r
    simp [h3PathActualProjectedMomentumFTCDefect244]

/-- Smooth momentum regularization, if both components converge consistently,
produces the exact solenoidal weak FTC without assuming a temporal pointwise
majorant for the classical old velocity derivative. -/
theorem h3Path_solenoidalWeakFTC_of_consistentSmoothApproximations244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hAll : ∀ ε : ℝ, 0 < ε →
      h3PathConsistentSmoothMomentumApproxOn244 hH3 a b ε) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b := by
  exact (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
    hH3 ha hab hb).1
    (h3Path_projectedFTCDefect_zeroOn_of_consistentSmoothApproximations244
      hH3 ha hab hb hAll)

end
end PrimeTensor.FirstMonomialTriad
