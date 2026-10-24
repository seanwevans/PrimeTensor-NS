import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticAngularGramDefect244
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Scalar physical Gram action and the exact transverse terminal criterion

For actual physical Hilbert velocity U, projected momentum source R and
D0 = -<U,R>, the source Gram determinant Δ = E0 * ‖R‖² - D0² satisfies
  Δ = E0 * ‖Q‖² = E0² * ‖N'‖²,
where E0 = ‖U‖² > 0, Q is the transverse source, and N = U / sqrt(E0).

Consequently the purely scalar physical Gram rates
  sqrt Δ / sqrt E0   and   sqrt Δ / E0
are exactly ‖Q‖ and ‖N'‖ respectively. On every strict positive-terminal-
kinetic tail, the integrated first rate equals the transverse-source action.
The previously proved terminal L² trace criterion is therefore expressed as
an entirely scalar Gram-action hypothesis, without any estimate on the
source phase or the higher H³ dissipation.

The hypothesis is not established merely by kinetic dissipation control.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The square root of the physical source Gram defect is exactly the
kinetic amplitude times the norm of transverse momentum forcing. -/
theorem h3Path_physicalSourceGram_sqrt_eq_sqrtKinetic_mul_transverseNorm244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 t) =
      Real.sqrt (velocityH3Energy0At u t) *
        ‖h3PathPhysicalTransverseSource244 hH3 t‖ := by
  let E : ℝ := velocityH3Energy0At u t
  let Q : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathPhysicalTransverseSource244 hH3 t
  have hGram : h3PathPhysicalSourceGramDefect244 hH3 t = E * ‖Q‖ ^ 2 :=
    h3Path_physicalSourceGram_eq_kinetic_mul_transverse_sq244 hH3 t ht hE
  calc
    Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 t) =
        Real.sqrt (E * ‖Q‖ ^ 2) := by rw [hGram]
    _ = Real.sqrt E * Real.sqrt (‖Q‖ ^ 2) := by
      rw [Real.sqrt_mul hE.le]
    _ = Real.sqrt E * ‖Q‖ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg Q)]

/-- Exactly recover transverse source magnitude from the scalar Gram defect. -/
theorem h3Path_physicalSourceGram_sqrt_div_sqrtKinetic_eq_transverseNorm244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 t) /
        Real.sqrt (velocityH3Energy0At u t) =
      ‖h3PathPhysicalTransverseSource244 hH3 t‖ := by
  have hRoot : 0 < Real.sqrt (velocityH3Energy0At u t) :=
    Real.sqrt_pos.2 hE
  rw [h3Path_physicalSourceGram_sqrt_eq_sqrtKinetic_mul_transverseNorm244
    hH3 t ht hE]
  calc
    (Real.sqrt (velocityH3Energy0At u t) *
        ‖h3PathPhysicalTransverseSource244 hH3 t‖) /
        Real.sqrt (velocityH3Energy0At u t) =
      (‖h3PathPhysicalTransverseSource244 hH3 t‖ *
        Real.sqrt (velocityH3Energy0At u t)) /
        Real.sqrt (velocityH3Energy0At u t) := by rw [mul_comm]
    _ = ‖h3PathPhysicalTransverseSource244 hH3 t‖ :=
      mul_div_cancel_right₀ _ (ne_of_gt hRoot)

/-- Exactly recover instantaneous physical Hilbert angular speed from the
scalar Gram defect divided by kinetic energy. -/
theorem h3Path_physicalSourceGram_sqrt_div_kinetic_eq_angularSpeed244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 t) /
        velocityH3Energy0At u t =
      ‖deriv (h3PathPhysicalUnitVelocity244 hH3) t‖ := by
  let E : ℝ := velocityH3Energy0At u t
  let Q : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathPhysicalTransverseSource244 hH3 t
  have hRoot : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hGram : Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 t) =
      Real.sqrt E * ‖Q‖ :=
    h3Path_physicalSourceGram_sqrt_eq_sqrtKinetic_mul_transverseNorm244
      hH3 t ht hE
  have hDeriv : deriv (h3PathPhysicalUnitVelocity244 hH3) t =
      (Real.sqrt E)⁻¹ • Q :=
    (h3Path_physicalUnitVelocity_hasDerivAt_angular244 hH3 t ht hE).deriv
  have hNorm : ‖deriv (h3PathPhysicalUnitVelocity244 hH3) t‖ =
      ‖Q‖ / Real.sqrt E := by
    rw [hDeriv]
    exact h3Path_physicalAngularRate_norm_eq_transverse_div_sqrt244 hH3 t hE
  rw [hGram, hNorm]
  apply (div_eq_iff (ne_of_gt hE)).2
  calc
    Real.sqrt E * ‖Q‖ = ‖Q‖ * Real.sqrt E := mul_comm _ _
    _ = (‖Q‖ / Real.sqrt E) * E := by
      calc
        ‖Q‖ * Real.sqrt E =
            (‖Q‖ / Real.sqrt E) *
              (Real.sqrt E * Real.sqrt E) := by
          rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hRoot)]
        _ = (‖Q‖ / Real.sqrt E) * E := by
          rw [Real.mul_self_sqrt hE.le]

/-- The scalar Gram norm rate integrates to exactly the physical transverse
source-norm action on any compact strict positive-kinetic interval. -/
theorem h3Path_physicalGramAction_integral_eq_transverseAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (s t : ℝ) (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t) :
    (∫ r in s..t,
      Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
        Real.sqrt (velocityH3Energy0At u r)) =
      (∫ r in s..t, ‖h3PathPhysicalTransverseSource244 hH3 r‖) := by
  apply intervalIntegral.integral_congr_Ioo_of_le hst
  intro r hr
  have hrTail : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  have hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hrTail.1, hrTail.2⟩
  exact h3Path_physicalSourceGram_sqrt_div_sqrtKinetic_eq_transverseNorm244
    hH3 r hrAbs
      (h3Path_physicalKinetic_positive_of_positiveTerminal244
        hH3 hClass hL r hrTail)

/-- Uniformly vanishing terminal scalar Gram-source action, written with
E0 and the physical projected RHS norm rather than a vector Q integral. -/
def H3PhysicalGramTerminalTailVanishing244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ s : ℝ in 𝓝[<] T,
      s ∈ Set.Ioo a T ∧
        ∀ t : ℝ, t ∈ Set.Ioo a T → s ≤ t →
          (∫ r in s..t,
            Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
              Real.sqrt (velocityH3Energy0At u r)) < ε

/-- On positive-terminal-mass tails, the scalar Gram criterion is equivalent
to the already established transverse-source terminal action criterion. -/
theorem h3Path_physicalGramTailVanishing_iff_transverseTailVanishing244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T) :
    H3PhysicalGramTerminalTailVanishing244 (a := a) hH3 ↔
      H3PhysicalTransverseTerminalTailVanishing244 (a := a) hH3 := by
  constructor
  · intro hG ε hε
    have hSmall := hG ε hε
    filter_upwards [hSmall] with s hs
    refine ⟨hs.1, ?_⟩
    intro t ht hst
    have hEq := h3Path_physicalGramAction_integral_eq_transverseAction244
      hH3 hClass hL s t hs.1 ht hst
    rw [← hEq]
    exact hs.2 t ht hst
  · intro hQ ε hε
    have hSmall := hQ ε hε
    filter_upwards [hSmall] with s hs
    refine ⟨hs.1, ?_⟩
    intro t ht hst
    have hEq := h3Path_physicalGramAction_integral_eq_transverseAction244
      hH3 hClass hL s t hs.1 ht hst
    rw [hEq]
    exact hs.2 t ht hst

/-- The purely scalar Gram action suffices for an actual physical terminal
L2 trace carrying precisely the established terminal kinetic mass. -/
theorem h3Path_physicalVelocity_terminalL2Trace_of_GramAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hGram : H3PhysicalGramTerminalTailVanishing244 (a := a) hH3) :
    ∃ V : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 V) ∧
        ‖V‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T := by
  have hQ : H3PhysicalTransverseTerminalTailVanishing244 (a := a) hH3 :=
    (h3Path_physicalGramTailVanishing_iff_transverseTailVanishing244
      hH3 hClass hL).mp hGram
  exact h3Path_physicalVelocity_terminalL2Trace_and_exactKineticMass244
    hH3 hClass hQ

/-- The scalar Gram tail hypothesis also yields convergence to a unit
physical Hilbert direction, without tracking the vector Q in the premise. -/
theorem h3Path_physicalUnitVelocity_terminalUnitTrace_of_GramAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hGram : H3PhysicalGramTerminalTailVanishing244 (a := a) hH3) :
    ∃ V : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3PathPhysicalUnitVelocity244 hH3) (𝓝[<] T) (𝓝 V) ∧
        ‖V‖ = 1 := by
  have hQ : H3PhysicalTransverseTerminalTailVanishing244 (a := a) hH3 :=
    (h3Path_physicalGramTailVanishing_iff_transverseTailVanishing244
      hH3 hClass hL).mp hGram
  exact h3Path_physicalUnitVelocity_terminalUnitTrace_of_transverse244
    hH3 hClass hL hQ

end
end PrimeTensor.FirstMonomialTriad
