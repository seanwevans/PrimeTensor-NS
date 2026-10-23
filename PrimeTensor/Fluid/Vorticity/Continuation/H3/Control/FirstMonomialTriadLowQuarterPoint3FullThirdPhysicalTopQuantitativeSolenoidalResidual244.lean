import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopSolenoidalWeakResidual244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopProjectedFTCDefectWeakDetermination244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Identification
import Mathlib.Tactic

/-!
# Quantitative pressure-neutral residual determination in physical L²

Exact solenoidal weak-test annihilation determines any Leray-fixed physical
L² residual. Here we strengthen that fact to a SHARP quantitative estimate:

  |<phi, D>| <= eta * ||phi|| for all compact solenoidal tests
    ==> ||D|| <= eta.

This follows from the exact proved density of compact divergence-free tests
in the Leray-fixed physical L² subspace. The residual need not be presented as
a pressure-gradient L² field, and no pointwise temporal domination is used.

Applied to the old physical projected Hilbert FTC defect, it allows scalar
weak-momentum equations with arbitrarily small test-dual error to imply
actual Hilbert weak FTC on every positive-time interval prefix. The scalar
residual estimates themselves remain an analytic obligation, not a
consequence of the pointwise classical Navier--Stokes PDE alone.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Quantitative upgrade from compact divergence-free weak test bounds to
a physical L² norm bound, with the same constant. It uses the exact physical
Leray-fixed closed-span identity, not a distributional pressure estimate. -/
theorem h3PhysicalL2_norm_le_of_lerayFixed_solenoidalTestBound244
    (V : H3PhysicalRealFinVectorL2Hilbert)
    (hFixed : H3PhysicalRealFinVectorL2HilbertLerayFixed V)
    {η : ℝ} (hη : 0 ≤ η)
    (hWeak : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ‖inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ) V‖ ≤
        η * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖) :
    ‖V‖ ≤ η := by
  let S : Set H3PhysicalRealFinVectorL2Hilbert :=
    { Ψ | ‖inner ℝ Ψ V‖ ≤ η * ‖Ψ‖ }
  have hClosed : IsClosed S := by
    dsimp only [S]
    exact isClosed_le
      ((continuous_id.inner continuous_const).norm)
      (continuous_const.mul continuous_norm)
  have hSpanSubset :
      (h3DivergenceFreeWeakTestPhysicalL2Span :
        Set H3PhysicalRealFinVectorL2Hilbert) ⊆ S := by
    intro Ψ hΨ
    rw [h3DivergenceFreeWeakTestPhysicalL2Span_eq_submodule_zeroSpan] at hΨ
    change Ψ ∈ h3DivergenceFreeWeakTestPhysicalL2Set at hΨ
    rcases hΨ with ⟨φ, hφ, rfl⟩
    exact hWeak φ hφ
  have hClosureSubset :
      closure (h3DivergenceFreeWeakTestPhysicalL2Span :
        Set H3PhysicalRealFinVectorL2Hilbert) ⊆ S :=
    closure_minimal hSpanSubset hClosed
  have hVClosed :
      V ∈ h3DivergenceFreeWeakTestPhysicalL2ClosedSpan := by
    rw [h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule]
    exact (mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff V).2 hFixed
  have hVClosure :
      V ∈ closure (h3DivergenceFreeWeakTestPhysicalL2Span :
        Set H3PhysicalRealFinVectorL2Hilbert) := by
    unfold h3DivergenceFreeWeakTestPhysicalL2ClosedSpan at hVClosed
    exact hVClosed
  have hSelf : ‖inner ℝ V V‖ ≤ η * ‖V‖ :=
    hClosureSubset hVClosure
  have hSq : ‖V‖ ^ 2 ≤ η * ‖V‖ := by
    simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖V‖)] using hSelf
  by_cases hZero : ‖V‖ = 0
  · simpa only [hZero] using hη
  · have hPos : 0 < ‖V‖ :=
      lt_of_le_of_ne (norm_nonneg V) (Ne.symm hZero)
    nlinarith [hSq]

/-- A scalar physical momentum residual need only be bounded in the dual
norm of the compact solenoidal test space. Neither the old pressure gradient
nor the residual requires an individual L² representative. -/
def h3PathPhysicalSolenoidalScalarResidualBoundOn244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b η : ℝ) : Prop :=
  ∀ r : ℝ, r ∈ Set.Icc a b →
    ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ‖inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
          (h3AuditInitialOldPhysicalHilbertTotal hH3 r -
            h3AuditInitialOldPhysicalHilbertTotal hH3 a) -
        ∫ s in a..r,
          inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
            (h3PathActualProjectedMomentumSource244 hH3 s)‖ ≤
        η * ‖h3WeakTestVectorPhysicalL2Hilbert φ‖

/-- Sharp physical L² FTC-defect estimate from a scalar solenoidal dual
residual bound. The scalar condition does not presuppose Hilbert weak FTC. -/
theorem h3Path_projectedFTCDefect_norm_le_of_scalarResidualBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b η : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hη : 0 ≤ η)
    (hScalar : h3PathPhysicalSolenoidalScalarResidualBoundOn244
      hH3 a b η) :
    ‖h3PathActualProjectedMomentumFTCDefect244 hH3 a b‖ ≤ η := by
  apply h3PhysicalL2_norm_le_of_lerayFixed_solenoidalTestBound244
    (h3PathActualProjectedMomentumFTCDefect244 hH3 a b)
    (h3Path_projectedFTCDefect_lerayFixed_onStrict244 hH3 ha hab hb)
    hη
  intro φ hφ
  rw [h3Path_projectedFTCDefect_solenoidalPairing_eq_residual244
    hH3 ha hab hb φ]
  exact hScalar b ⟨hab.le, le_rfl⟩ φ hφ

/-- The same scalar-dual estimate controls every prefix of a strict
physical interval. The degenerate prefix is exactly zero by definition. -/
theorem h3Path_projectedFTCDefect_uniformNormOn_of_scalarResidualBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b η : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hη : 0 ≤ η)
    (hScalar : h3PathPhysicalSolenoidalScalarResidualBoundOn244
      hH3 a b η) :
    ∀ r : ℝ, r ∈ Set.Icc a b →
      ‖h3PathActualProjectedMomentumFTCDefect244 hH3 a r‖ ≤ η := by
  intro r hr
  rcases lt_or_eq_of_le hr.1 with har | har
  · exact h3Path_projectedFTCDefect_norm_le_of_scalarResidualBound244
      hH3 ha har (lt_of_le_of_lt hr.2 hb) hη
      (by
        intro s hs φ hφ
        exact hScalar s ⟨hs.1, hs.2.trans hr.2⟩ φ hφ)
  · have hrEq : r = a := har.symm
    subst r
    simpa [h3PathActualProjectedMomentumFTCDefect244] using hη

/-- Arbitrarily small scalar residuals against compact divergence-free tests
force the actual physical Hilbert evolution defect to vanish on every prefix.
No strong residual representation is assumed. -/
theorem h3Path_projectedFTCDefect_zeroOn_of_vanishingScalarResidualBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hSmall : ∀ η : ℝ, 0 < η →
      h3PathPhysicalSolenoidalScalarResidualBoundOn244 hH3 a b η) :
    ∀ r : ℝ, r ∈ Set.Icc a b →
      h3PathActualProjectedMomentumFTCDefect244 hH3 a r = 0 := by
  intro r hr
  let D : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumFTCDefect244 hH3 a r
  by_contra hNonzero
  have hPos : 0 < ‖D‖ := norm_pos_iff.mpr hNonzero
  have hHalfPos : 0 < ‖D‖ / 2 := by positivity
  have hBound :=
    h3Path_projectedFTCDefect_uniformNormOn_of_scalarResidualBound244
      hH3 ha hab hb hHalfPos.le
      (hSmall (‖D‖ / 2) hHalfPos) r hr
  change ‖D‖ ≤ ‖D‖ / 2 at hBound
  linarith

/-- The complete physical solenoidal weak FTC follows from arbitrarily
accurate scalar weak momentum residuals. This is the quantitative-dual
counterpart of the strong-momentum-regularization criterion. -/
theorem h3Path_solenoidalWeakFTC_of_vanishingScalarResidualBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hSmall : ∀ η : ℝ, 0 < η →
      h3PathPhysicalSolenoidalScalarResidualBoundOn244 hH3 a b η) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b := by
  exact (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
    hH3 ha hab hb).1
    (h3Path_projectedFTCDefect_zeroOn_of_vanishingScalarResidualBound244
      hH3 ha hab hb hSmall)

/-- If weak FTC fails for the actual physical path then the scalar test-dual
residual has a strictly positive error floor on this interval. -/
theorem h3Path_nonzeroProjectedFTCDefect_forces_scalarResidualBarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hNonzero : h3PathActualProjectedMomentumFTCDefect244 hH3 a b ≠ 0) :
    ∃ η : ℝ, 0 < η ∧
      ¬ h3PathPhysicalSolenoidalScalarResidualBoundOn244 hH3 a b η := by
  classical
  by_contra hNo
  have hSmall : ∀ η : ℝ, 0 < η →
      h3PathPhysicalSolenoidalScalarResidualBoundOn244 hH3 a b η := by
    intro η hη
    by_contra hFail
    exact hNo ⟨η, hη, hFail⟩
  have hZero := h3Path_projectedFTCDefect_zeroOn_of_vanishingScalarResidualBound244
    hH3 ha hab hb hSmall
  exact hNonzero (hZero b ⟨hab.le, le_rfl⟩)

end
end PrimeTensor.FirstMonomialTriad
