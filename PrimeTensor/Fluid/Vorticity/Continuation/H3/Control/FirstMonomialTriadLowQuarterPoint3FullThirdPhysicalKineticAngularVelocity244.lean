import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticTerminalTransverseTrace244
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Physical velocity direction and exact angular momentum-source derivative

For U the actual physical L² velocity, R its projected Hilbert source,
E = ‖U‖² and D = -⟪U,R⟫, the previous source decomposition proves
R = -(D/E) U + Q, where Q is orthogonal to U whenever E>0.

This module differentiates the *actual normalized direction*

    N(t) = U(t) / sqrt(E(t)).

The longitudinal term cancels the derivative of the normalization:

    N'(t) = Q(t) / sqrt(E(t)),    ‖N(t)‖ = 1,   ⟪N(t),N'(t)⟫ = 0.

Thus transverse forcing is exactly the angular velocity of the physical
momentum direction (up to the kinetic amplitude), not merely a residual
in a triangle estimate. If the canonical kinetic limit L is positive, the
angular displacement over [s,t] is bounded by (1/sqrt L) ∫_s^t ‖Q‖.
The already proved conditional strong trace gives a unit-direction terminal
trace under the established transverse-tail hypothesis.

This does not establish integrability of Q near the endpoint, and does not
bound H³ dissipation or imply smooth Navier--Stokes continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Exact physical L² unit direction; the total definition is used only
under the positive kinetic-energy hypothesis in the geometric theorems. -/
noncomputable def h3PathPhysicalUnitVelocity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : H3PhysicalRealFinVectorL2Hilbert :=
  (Real.sqrt (velocityH3Energy0At u t))⁻¹ •
    h3AuditInitialOldPhysicalHilbertTotal hH3 t

/-- Normalizing by the kinetic square root puts the actual physical
Hilbert velocity on the L² unit sphere. -/
theorem h3Path_physicalUnitVelocity_norm_eq_one244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    ‖h3PathPhysicalUnitVelocity244 hH3 t‖ = 1 := by
  let E : ℝ := velocityH3Energy0At u t
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  have hRoot : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hNorm : ‖U‖ = Real.sqrt E :=
    h3Audit_initialOldPhysicalHilbert_norm_eq_sqrt_kineticEnergy hH3 t ht
  change ‖(Real.sqrt E)⁻¹ • U‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRoot), hNorm]
  exact inv_mul_cancel₀ (ne_of_gt hRoot)

/-- The physical kinetic energy itself has derivative -2D, transported
from the established physical Hilbert norm-square identity. -/
theorem h3Path_physicalEnergy0_hasDerivAt_negTwoDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (velocityH3Energy0At u)
      (-2 * velocityH3Dissipation0At u t) t := by
  have hSame : (velocityH3Energy0At u) =ᶠ[𝓝 t]
      (fun r : ℝ => ‖h3AuditInitialOldPhysicalHilbertTotal hH3 r‖ ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact (h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
      hH3 r hr).symm
  exact (h3Path_physicalKineticHasDerivAt_negDissipation0_positiveTime244
    hH3 t ht).congr_of_eventuallyEq hSame

/-- The longitudinal component cancels *exactly* against the derivative
of sqrt(E)^{-1}. The remaining velocity-direction derivative is Q/sqrt(E). -/
theorem h3Path_physicalUnitVelocity_hasDerivAt_angular244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    HasDerivAt (h3PathPhysicalUnitVelocity244 hH3)
      ((Real.sqrt (velocityH3Energy0At u t))⁻¹ •
        h3PathPhysicalTransverseSource244 hH3 t) t := by
  let E : ℝ := velocityH3Energy0At u t
  let D : ℝ := velocityH3Dissipation0At u t
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  let R : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3 t
  have hRoot : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hEnergy : HasDerivAt (velocityH3Energy0At u) (-2 * D) t :=
    h3Path_physicalEnergy0_hasDerivAt_negTwoDissipation244 hH3 t ht
  have hSqrt : HasDerivAt
      (fun r : ℝ => Real.sqrt (velocityH3Energy0At u r))
      ((-2 * D) / (2 * Real.sqrt E)) t :=
    hEnergy.sqrt (ne_of_gt hE)
  have hInv : HasDerivAt
      (fun r : ℝ => (Real.sqrt (velocityH3Energy0At u r))⁻¹)
      (-((-2 * D) / (2 * Real.sqrt E)) / (Real.sqrt E) ^ 2) t :=
    hSqrt.inv (ne_of_gt hRoot)
  have hU : HasDerivAt
      (h3AuditInitialOldPhysicalHilbertTotal hH3) R t :=
    h3Path_physicalHilbertHasDerivAt_fromH3Admissible244 hH3 ht
  have hCombined := hInv.smul hU
  have hCoeff :
      -((-2 * D) / (2 * Real.sqrt E)) / (Real.sqrt E) ^ 2 =
        (Real.sqrt E)⁻¹ * (D / E) := by
    rw [Real.sq_sqrt hE.le]
    field_simp [ne_of_gt hRoot, ne_of_gt hE]
    change D = D * E * E⁻¹
    have hEnz : E ≠ 0 := ne_of_gt hE
    calc
      D = D * 1 := (mul_one D).symm
      _ = D * (E * E⁻¹) := by rw [mul_inv_cancel₀ hEnz]
      _ = D * E * E⁻¹ := (mul_assoc D E E⁻¹).symm
  apply hCombined.congr_deriv
  change (Real.sqrt E)⁻¹ • R +
        (-((-2 * D) / (2 * Real.sqrt E)) / (Real.sqrt E) ^ 2) • U =
      (Real.sqrt E)⁻¹ • (R + (D / E) • U)
  rw [smul_add, smul_smul, hCoeff]

/-- The derivative of normalized velocity is tangent to the Hilbert
unit sphere: its inner product with the direction is exactly zero. -/
theorem h3Path_physicalUnitVelocity_angular_orthogonal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    inner ℝ (h3PathPhysicalUnitVelocity244 hH3 t)
      ((Real.sqrt (velocityH3Energy0At u t))⁻¹ •
        h3PathPhysicalTransverseSource244 hH3 t) = 0 := by
  let E : ℝ := velocityH3Energy0At u t
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  let Q : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathPhysicalTransverseSource244 hH3 t
  have hOrth : inner ℝ U Q = 0 :=
    h3Path_physicalTransverse_orthogonal244 hH3 t ht hE
  change inner ℝ ((Real.sqrt E)⁻¹ • U) ((Real.sqrt E)⁻¹ • Q) = 0
  rw [real_inner_smul_left, real_inner_smul_right, hOrth]
  ring

/-- The exact norm of physical angular velocity is the transverse-source
norm divided by the kinetic amplitude. -/
theorem h3Path_physicalAngularRate_norm_eq_transverse_div_sqrt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ)
    (hE : 0 < velocityH3Energy0At u t) :
    ‖(Real.sqrt (velocityH3Energy0At u t))⁻¹ •
        h3PathPhysicalTransverseSource244 hH3 t‖ =
      ‖h3PathPhysicalTransverseSource244 hH3 t‖ /
        Real.sqrt (velocityH3Energy0At u t) := by
  let E : ℝ := velocityH3Energy0At u t
  let Q : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathPhysicalTransverseSource244 hH3 t
  have hRoot : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  change ‖(Real.sqrt E)⁻¹ • Q‖ = ‖Q‖ / Real.sqrt E
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRoot)]
  simp only [div_eq_mul_inv]
  ring

/-- On every strict positive-kinetic tail, the unit direction obeys a
Bochner angular FTC and the physical chord is at most the angular action. -/
theorem h3Path_physicalUnitVelocity_increment_le_angularAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (s t : ℝ) (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t) :
    ‖h3PathPhysicalUnitVelocity244 hH3 t -
        h3PathPhysicalUnitVelocity244 hH3 s‖ ≤
      ∫ r in s..t,
        ‖(Real.sqrt (velocityH3Energy0At u r))⁻¹ •
          h3PathPhysicalTransverseSource244 hH3 r‖ := by
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    fun r => (Real.sqrt (velocityH3Energy0At u r))⁻¹ •
      h3PathPhysicalTransverseSource244 hH3 r
  have hSet : Set.Icc s t ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hAbs : Set.Ioo a T ⊆ Set.Ioo (0 : ℝ) T := by
    intro r hr
    exact ⟨lt_trans hClass.terminal_start.1 hr.1, hr.2⟩
  have hECont : ContinuousOn (velocityH3Energy0At u) (Set.Ioo a T) :=
    (h3Audit_initialKineticEnergy_continuousOn_positiveInterval hH3).mono hAbs
  have hRootCont : ContinuousOn
      (fun r : ℝ => Real.sqrt (velocityH3Energy0At u r)) (Set.Ioo a T) :=
    Real.continuous_sqrt.comp_continuousOn hECont
  have hInvCont : ContinuousOn
      (fun r : ℝ => (Real.sqrt (velocityH3Energy0At u r))⁻¹)
      (Set.Ioo a T) := by
    exact hRootCont.inv₀ (fun r hr => ne_of_gt (Real.sqrt_pos.2
      (h3Path_physicalKinetic_positive_of_positiveTerminal244
        hH3 hClass hL r hr)))
  have hQCont : ContinuousOn
      (h3PathPhysicalTransverseSource244 hH3) (Set.Ioo a T) :=
    (h3Path_physicalSourceChannels_continuousOn_positiveTerminal244
      hH3 hClass hL).2
  have hGCont : ContinuousOn G (Set.Ioo a T) :=
    hInvCont.smul hQCont
  have hInt : IntervalIntegrable G volume s t :=
    (hGCont.mono hSet).intervalIntegrable_of_Icc hst
  have hsAbs := hAbs hs
  have htAbs := hAbs ht
  have hFTC :
      (∫ r in s..t, G r) =
        h3PathPhysicalUnitVelocity244 hH3 t -
          h3PathPhysicalUnitVelocity244 hH3 s := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr => ?_) hInt
    have hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
      h3Audit_positiveUnorderedInterval_strict T s t hsAbs htAbs hr
    have hr : r ∈ Set.Ioo a T := by
      have hrClosed : r ∈ Set.Icc s t := by
        simpa only [uIcc_of_le hst] using hr
      exact ⟨lt_of_lt_of_le hs.1 hrClosed.1, hrAbs.2⟩
    -- A uniform lower bound E(r) ≥ L is inherited from the kinetic infimum.
    simpa only [G] using
      (h3Path_physicalUnitVelocity_hasDerivAt_angular244 hH3 r hrAbs
        (h3Path_physicalKinetic_positive_of_positiveTerminal244
          hH3 hClass hL r hr))
  rw [← hFTC]
  exact intervalIntegral.norm_integral_le_integral_norm hst

/-- A terminal strong L² velocity trace and positive terminal kinetic mass
produce a genuine unit physical direction at the endpoint. -/
theorem h3Path_physicalUnitVelocity_terminalUnitTrace_of_transverse244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hQ : H3PhysicalTransverseTerminalTailVanishing244 (a := a) hH3) :
    ∃ V : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3PathPhysicalUnitVelocity244 hH3) (𝓝[<] T) (𝓝 V) ∧
        ‖V‖ = 1 := by
  let L : ℝ := h3PathCanonicalTerminalKineticEnergyAt u a T
  have hRoot : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  obtain ⟨U, hU, hUNormSq⟩ :=
    h3Path_physicalVelocity_terminalL2Trace_and_exactKineticMass244
      hH3 hClass hQ
  have hENorm : ‖U‖ = Real.sqrt L := by
    have h := congrArg Real.sqrt hUNormSq
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg U)] using h
  have hELimit : Tendsto (velocityH3Energy0At u) (𝓝[<] T) (𝓝 L) :=
    h3PathCanonical_terminalKineticEnergy_tendsto_noCanonicalData hH3 hClass
  have hRootLimit : Tendsto
      (fun r : ℝ => Real.sqrt (velocityH3Energy0At u r))
      (𝓝[<] T) (𝓝 (Real.sqrt L)) := by
    simpa only [Function.comp_def] using
      ((Real.continuous_sqrt.tendsto L).comp hELimit)
  have hInvLimit : Tendsto
      (fun r : ℝ => (Real.sqrt (velocityH3Energy0At u r))⁻¹)
      (𝓝[<] T) (𝓝 (Real.sqrt L)⁻¹) :=
    hRootLimit.inv₀ (ne_of_gt hRoot)
  have hDirection : Tendsto (h3PathPhysicalUnitVelocity244 hH3)
      (𝓝[<] T) (𝓝 ((Real.sqrt L)⁻¹ • U)) := by
    change Tendsto
      (fun r : ℝ => (Real.sqrt (velocityH3Energy0At u r))⁻¹ •
        h3AuditInitialOldPhysicalHilbertTotal hH3 r)
      (𝓝[<] T) (𝓝 ((Real.sqrt L)⁻¹ • U))
    exact hInvLimit.smul hU
  refine ⟨(Real.sqrt L)⁻¹ • U, hDirection, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRoot), hENorm]
  exact inv_mul_cancel₀ (ne_of_gt hRoot)

end
end PrimeTensor.FirstMonomialTriad
