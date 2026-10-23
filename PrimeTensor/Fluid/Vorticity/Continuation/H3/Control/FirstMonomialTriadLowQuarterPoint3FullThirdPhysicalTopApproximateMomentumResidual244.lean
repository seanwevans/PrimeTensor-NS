import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopMollifiedMomentumStability244
import Mathlib.Tactic

/-!
# Stability under approximately differentiated physical momentum regularizations

The earlier consistency interface demanded `V' = W` for the approximating
physical velocity/source pair. A genuine regularization of the *classical*
Navier--Stokes PDE may instead carry a nonzero commutator or consistency
residual `E`, giving `V' = W + E`.

This file proves a quantitative defect estimate with three separate budgets:
velocity approximation, projected-source approximation, and momentum residual.
No exact approximate momentum equation is assumed. These estimates reduce the
analytic construction to approximations with all three errors tending to zero.

In particular, source continuity by itself does not show that the required
approximate physical momentum equations exist. The spatially classical OLD
pressure-gradient defect is a remaining obstruction to directly transferring
the projected L² source into the distributional time derivative.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- An approximate regularized momentum equation with independently sized
velocity, projected-source and commutator/residual errors.  The residual is
*not* assumed zero; it is a strongly continuous Hilbert-valued forcing. -/
def h3PathApproximateMomentumResidualOn244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b εU εR η : ℝ) : Prop :=
  ∃ (V W E : ℝ → H3PhysicalRealFinVectorL2Hilbert),
    ContinuousOn V (Set.Icc a b) ∧
    ContinuousOn W (Set.Icc a b) ∧
    ContinuousOn E (Set.Icc a b) ∧
    (∀ t : ℝ, t ∈ Set.Ioo a b →
      HasDerivAt V (W t + E t) t) ∧
    (∀ t : ℝ, t ∈ Set.Icc a b →
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t - V t‖ ≤ εU) ∧
    (∀ t : ℝ, t ∈ Set.Icc a b →
      ‖h3PathActualProjectedMomentumSource244 hH3 t - W t‖ ≤ εR) ∧
    (∀ t : ℝ, t ∈ Set.Icc a b → ‖E t‖ ≤ η)

/-- An approximately consistent equation is an exactly consistent one after
absorbing its residual into the regularized source.  The projected-source
error grows by at most the residual error. -/
theorem h3Path_consistentSmoothApprox_of_approximateMomentumResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b εU εR η : ℝ}
    (hApprox : h3PathApproximateMomentumResidualOn244
      hH3 a b εU εR η) :
    h3PathConsistentSmoothMomentumApproxOn244 hH3 a b
      (max εU (εR + η)) := by
  rcases hApprox with
    ⟨V, W, E, hVCont, hWCont, hECont, hDeriv, hVClose,
      hRClose, hEClose⟩
  refine ⟨V, (fun t => W t + E t), hVCont,
    hWCont.add hECont, ?_, ?_, ?_⟩
  · intro t ht
    exact hDeriv t ht
  · intro t ht
    exact (hVClose t ht).trans (le_max_left _ _)
  · intro t ht
    calc
      ‖h3PathActualProjectedMomentumSource244 hH3 t -
          (W t + E t)‖ =
          ‖(h3PathActualProjectedMomentumSource244 hH3 t - W t) - E t‖ := by
            congr 1
            abel
      _ ≤ ‖h3PathActualProjectedMomentumSource244 hH3 t - W t‖ +
            ‖E t‖ := norm_sub_le _ _
      _ ≤ εR + η := add_le_add (hRClose t ht) (hEClose t ht)
      _ ≤ max εU (εR + η) := le_max_right _ _

/-- Actual physical FTC defect with separate approximation and residual
budgets.  This is the form suitable for non-exact temporal mollification or
Galerkin constructions, where the commutator only tends to zero in L². -/
theorem h3Path_projectedFTCDefect_norm_le_of_approximateMomentumResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b εU εR η : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hApprox : h3PathApproximateMomentumResidualOn244
      hH3 a b εU εR η) :
    ‖h3PathActualProjectedMomentumFTCDefect244 hH3 a b‖ ≤
      (2 + (b - a)) * max εU (εR + η) := by
  exact h3Path_projectedFTCDefect_norm_le_of_smoothMomentumApprox244
    hH3 ha hab hb
    (h3Path_consistentSmoothApprox_of_approximateMomentumResidual244
      hH3 hApprox)

/-- Arbitrarily accurate velocity/source approximations with vanishing
regularized momentum residual imply exact weak momentum evolution, despite
there being no EXACT approximate momentum equation at finite resolution. -/
theorem h3Path_solenoidalWeakFTC_of_vanishingApproximateMomentumResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hApprox : ∀ ε : ℝ, 0 < ε →
      h3PathApproximateMomentumResidualOn244 hH3 a b ε ε ε) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b := by
  apply h3Path_solenoidalWeakFTC_of_consistentSmoothApproximations244
    hH3 ha hab hb
  intro ε hε
  have hεHalf : 0 < ε / 2 := by positivity
  have hExact :=
    h3Path_consistentSmoothApprox_of_approximateMomentumResidual244
      hH3 (hApprox (ε / 2) hεHalf)
  have hEq : max (ε / 2) (ε / 2 + ε / 2) = ε := by
    have hHalfLe : ε / 2 ≤ ε := by linarith
    have hSum : ε / 2 + ε / 2 = ε := by ring
    rw [hSum, max_eq_right hHalfLe]
  simpa only [hEq] using hExact

/-- The corresponding physical Hilbert FTC defect vanishes at every prefix.
This is the version used by the prior local eighth-moment transfer machinery. -/
theorem h3Path_projectedFTCDefect_zeroOn_of_vanishingApproximateMomentumResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hApprox : ∀ ε : ℝ, 0 < ε →
      h3PathApproximateMomentumResidualOn244 hH3 a b ε ε ε) :
    ∀ r : ℝ, r ∈ Set.Icc a b →
      h3PathActualProjectedMomentumFTCDefect244 hH3 a r = 0 := by
  exact (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
    hH3 ha hab hb).2
    (h3Path_solenoidalWeakFTC_of_vanishingApproximateMomentumResidual244
      hH3 ha hab hb hApprox)

/-- Any nonzero physical Hilbert FTC defect has a positive resolution floor:
not all three errors can simultaneously be made arbitrarily small by
regularized velocity/source pairs satisfying an approximate momentum PDE. -/
theorem h3Path_nonzeroProjectedFTCDefect_forces_approximateResidualBarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hNonzero : h3PathActualProjectedMomentumFTCDefect244 hH3 a b ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ¬ h3PathApproximateMomentumResidualOn244 hH3 a b ε ε ε := by
  classical
  by_contra hNo
  have hAll : ∀ ε : ℝ, 0 < ε →
      h3PathApproximateMomentumResidualOn244 hH3 a b ε ε ε := by
    intro ε hε
    by_contra hFail
    exact hNo ⟨ε, hε, hFail⟩
  have hZero :=
    h3Path_projectedFTCDefect_zeroOn_of_vanishingApproximateMomentumResidual244
      hH3 ha hab hb hAll
  exact hNonzero (hZero b ⟨hab.le, le_rfl⟩)

end
end PrimeTensor.FirstMonomialTriad
