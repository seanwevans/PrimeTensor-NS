import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopApproximateMomentumResidual244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialSolenoidalWeakFTCStrongDerivative
import Mathlib.Tactic

/-!
# Solenoidal weak regularizations and pressure-neutral momentum residuals

A regularization of classical Navier--Stokes need not have an L²-valued
pressure gradient. The projected momentum equation is naturally tested
only against compact solenoidal vector fields, where pressure cancels.

This file makes the actual approximation hypothesis weak: a regularized
velocity V and projected source W + E satisfy only the solenoidal scalar
weak FTC. If V and W + E are Leray-fixed, the established weak-to-strong
Hilbert derivative theorem upgrades that scalar evolution to V' = W + E.
Therefore the quantitative physical FTC defect estimate already proved for
approximate strong momentum equations applies unchanged.

An auxiliary scalar pressure-neutralization theorem removes an arbitrary
weak pressure pairing provided that pairing is zero for solenoidal tests.
It does not claim that the existing OLD pressure defect has a time-integrable
representative, nor that the weak regularizations have been constructed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The weak momentum equation for approximate fields is pressure-insensitive.
Only the projected velocity and projected forcing must be Leray-fixed; the
strong time derivative of V is NOT included among the assumptions. -/
def h3PathSolenoidalWeakResidualApproxOn244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b εU εR η : ℝ) : Prop :=
  ∃ (V W E : ℝ → H3PhysicalRealFinVectorL2Hilbert),
    ContinuousOn V (Set.Icc a b) ∧
    ContinuousOn W (Set.Icc a b) ∧
    ContinuousOn E (Set.Icc a b) ∧
    (∀ t : ℝ, t ∈ Set.Icc a b →
      H3PhysicalRealFinVectorL2HilbertLerayFixed (V t)) ∧
    (∀ t : ℝ,
      H3PhysicalRealFinVectorL2HilbertLerayFixed (W t + E t)) ∧
    H3AuditPhysicalSolenoidalWeakFTCOn V (fun t => W t + E t) a b ∧
    (∀ t : ℝ, t ∈ Set.Icc a b →
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t - V t‖ ≤ εU) ∧
    (∀ t : ℝ, t ∈ Set.Icc a b →
      ‖h3PathActualProjectedMomentumSource244 hH3 t - W t‖ ≤ εR) ∧
    (∀ t : ℝ, t ∈ Set.Icc a b → ‖E t‖ ≤ η)

/-- The old pressure is absent from the weak equation when its pairing
with every compact solenoidal test vanishes at each observation time.
No spacetime integrability or L² representative of the pressure is needed
for this purely scalar cancellation. -/
theorem h3Path_solenoidalWeakFTC_of_pressureNeutralScalarEvolution244
    (V W E : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (P : H3WeakTestVector → ℝ → ℝ)
    {a b : ℝ} (_hab : a ≤ b)
    (hEvolution : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∀ r : ℝ, r ∈ Set.Icc a b →
        inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
          (V r - V a) =
          (∫ s in a..r,
            inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
              (W s + E s)) +
          (∫ s in a..r, P φ s))
    (hPressureZero : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∀ s : ℝ, s ∈ Set.Icc a b → P φ s = 0) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      V (fun s => W s + E s) a b := by
  intro φ hφ r hr
  have hPZero : (∫ s in a..r, P φ s) = 0 := by
    have hIntegralEq :
        (∫ s in a..r, P φ s) =
          (∫ _s in a..r, (0 : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hsIcc : s ∈ Set.Icc a b := by
        rw [Set.uIcc_of_le hr.1] at hs
        exact ⟨hs.1, hs.2.trans hr.2⟩
      exact hPressureZero φ hφ s hsIcc
    simpa using hIntegralEq
  simpa only [hPZero, add_zero] using hEvolution φ hφ r hr

/-- The existing solenoidal weak-to-strong theorem upgrades a WEAK regularized
projected momentum identity to a Hilbert-valued approximate momentum equation.
The pressure gradient never needs an L² representative. -/
theorem h3Path_approximateMomentumResidual_of_solenoidalWeakResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b εU εR η : ℝ} (hab : a < b)
    (hWeak : h3PathSolenoidalWeakResidualApproxOn244
      hH3 a b εU εR η) :
    h3PathApproximateMomentumResidualOn244 hH3 a b εU εR η := by
  rcases hWeak with
    ⟨V, W, E, hVCont, hWCont, hECont, hVFixed, hWEFixed,
      hWeakFTC, hVClose, hWClose, hEClose⟩
  refine ⟨V, W, E, hVCont, hWCont, hECont, ?_,
    hVClose, hWClose, hEClose⟩
  intro t ht
  exact h3Audit_physicalSolenoidalWeakFTC_implies_HilbertHasDerivAt
    V (fun s => W s + E s) a b hab (hWCont.add hECont)
    hVFixed hWEFixed hWeakFTC t ht

/-- Quantitative physical defect control from a solenoidal WEAK approximate
momentum equation. This includes consistent approximations whose classical
pressure gradients are not controlled in physical L². -/
theorem h3Path_projectedFTCDefect_norm_le_of_solenoidalWeakResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b εU εR η : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hWeak : h3PathSolenoidalWeakResidualApproxOn244
      hH3 a b εU εR η) :
    ‖h3PathActualProjectedMomentumFTCDefect244 hH3 a b‖ ≤
      (2 + (b - a)) * max εU (εR + η) := by
  exact h3Path_projectedFTCDefect_norm_le_of_approximateMomentumResidual244
    hH3 ha hab hb
    (h3Path_approximateMomentumResidual_of_solenoidalWeakResidual244
      hH3 hab hWeak)

/-- Arbitrarily accurate projected SOLENOIDAL weak regularizations give the
actual physical scalar weak FTC. No old pressure-gradient L² bound occurs. -/
theorem h3Path_solenoidalWeakFTC_of_vanishingSolenoidalWeakResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hApprox : ∀ ε : ℝ, 0 < ε →
      h3PathSolenoidalWeakResidualApproxOn244 hH3 a b ε ε ε) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b := by
  apply h3Path_solenoidalWeakFTC_of_vanishingApproximateMomentumResidual244
    hH3 ha hab hb
  intro ε hε
  exact h3Path_approximateMomentumResidual_of_solenoidalWeakResidual244
    hH3 hab (hApprox ε hε)

/-- The resulting physical Hilbert FTC defect vanishes on ALL prefixes, not
only on the sampled time window's final endpoint. -/
theorem h3Path_projectedFTCDefect_zeroOn_of_vanishingSolenoidalWeakResidual244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hApprox : ∀ ε : ℝ, 0 < ε →
      h3PathSolenoidalWeakResidualApproxOn244 hH3 a b ε ε ε) :
    ∀ r : ℝ, r ∈ Set.Icc a b →
      h3PathActualProjectedMomentumFTCDefect244 hH3 a r = 0 := by
  exact (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
    hH3 ha hab hb).2
    (h3Path_solenoidalWeakFTC_of_vanishingSolenoidalWeakResidual244
      hH3 ha hab hb hApprox)

/-- If the true physical FTC defect is nonzero, pressure-insensitive weak
regularizations cannot simultaneously converge in velocity, projected source,
and projected residual at arbitrarily small error. -/
theorem h3Path_nonzeroProjectedFTCDefect_forces_solenoidalWeakResidualBarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hNonzero : h3PathActualProjectedMomentumFTCDefect244 hH3 a b ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ¬ h3PathSolenoidalWeakResidualApproxOn244 hH3 a b ε ε ε := by
  obtain ⟨ε, hε, hBarrier⟩ :=
    h3Path_nonzeroProjectedFTCDefect_forces_approximateResidualBarrier244
      hH3 ha hab hb hNonzero
  exact ⟨ε, hε, fun hWeak =>
    hBarrier (h3Path_approximateMomentumResidual_of_solenoidalWeakResidual244
      hH3 hab hWeak)⟩

end
end PrimeTensor.FirstMonomialTriad
