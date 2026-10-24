import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticAngularVelocity244
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Physical source Gram determinant and angular velocity

For actual physical velocity U, its actual projected momentum derivative R,
kinetic energy E=‖U‖², and dissipation D=-⟪U,R⟫, define the scalar Gram defect

  Δ = E * ‖R‖² - D².

When E>0 the previously formalized orthogonal splitting identifies this
exactly with E * ‖Q‖², where Q is transverse to U. Consequently Δ≥0,
and equality holds exactly when the transverse source is zero.

The new derivative identity also yields the geometrically intrinsic formula

  Δ = E² * ‖N'‖²,    N = U / sqrt E.

In particular, Δ measures angular rather than dissipative longitudinal
motion, without invoking 3-dimensional cross products on the infinite-
dimensional physical L² Hilbert space. All equalities are interior pointwise
identities; no endpoint integrability, H³ regularity gain, or continuation is
inferred.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Gram determinant of the actual physical Hilbert velocity and its
projected momentum source. Defined also at zero kinetic mass. -/
noncomputable def h3PathPhysicalSourceGramDefect244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : ℝ :=
  velocityH3Energy0At u t *
      ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ^ 2 -
    velocityH3Dissipation0At u t ^ 2

/-- The source Gram defect is *exactly* the transverse energy-weighted
source norm square, not just bounded by it. -/
theorem h3Path_physicalSourceGram_eq_kinetic_mul_transverse_sq244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    h3PathPhysicalSourceGramDefect244 hH3 t =
      velocityH3Energy0At u t *
        ‖h3PathPhysicalTransverseSource244 hH3 t‖ ^ 2 := by
  let E : ℝ := velocityH3Energy0At u t
  let D : ℝ := velocityH3Dissipation0At u t
  let R : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3 t
  let Q : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathPhysicalTransverseSource244 hH3 t
  have hSource : ‖R‖ ^ 2 = ‖Q‖ ^ 2 + D ^ 2 / E :=
    h3Path_physicalSource_norm_sq_eq_transverse_add_kineticCost244
      hH3 t ht hE
  have hCancel : E * (D ^ 2 / E) = D ^ 2 := by
    calc
      E * (D ^ 2 / E) = (D ^ 2 / E) * E := mul_comm _ _
      _ = D ^ 2 := div_mul_cancel₀ _ (ne_of_gt hE)
  change E * ‖R‖ ^ 2 - D ^ 2 = E * ‖Q‖ ^ 2
  rw [hSource, mul_add, hCancel]
  ring

/-- The physical source Gram defect is nonnegative whenever the physical
velocity has nonzero kinetic energy. -/
theorem h3Path_physicalSourceGram_nonneg244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    0 ≤ h3PathPhysicalSourceGramDefect244 hH3 t := by
  rw [h3Path_physicalSourceGram_eq_kinetic_mul_transverse_sq244
    hH3 t ht hE]
  exact mul_nonneg hE.le (sq_nonneg _)

/-- Saturation of the physical scalar source-cost inequality is equivalent
to vanishing of the transverse force. -/
theorem h3Path_physicalSourceGram_eq_zero_iff_transverse_eq_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    h3PathPhysicalSourceGramDefect244 hH3 t = 0 ↔
      h3PathPhysicalTransverseSource244 hH3 t = 0 := by
  let E : ℝ := velocityH3Energy0At u t
  let Q : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathPhysicalTransverseSource244 hH3 t
  rw [h3Path_physicalSourceGram_eq_kinetic_mul_transverse_sq244
    hH3 t ht hE]
  change E * ‖Q‖ ^ 2 = 0 ↔ Q = 0
  constructor
  · intro h
    have hSq : ‖Q‖ ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left (ne_of_gt hE)
    have hNorm : ‖Q‖ = 0 := by
      nlinarith [norm_nonneg Q]
    exact norm_eq_zero.mp hNorm
  · intro h
    rw [h, norm_zero]
    ring

/-- A zero Gram defect means the projected momentum source is purely
longitudinal at that instant. -/
theorem h3Path_physicalSourceGram_eq_zero_iff_pureLongitudinal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    h3PathPhysicalSourceGramDefect244 hH3 t = 0 ↔
      h3PathActualProjectedMomentumSource244 hH3 t =
        h3PathPhysicalLongitudinalSource244 hH3 t := by
  rw [h3Path_physicalSourceGram_eq_zero_iff_transverse_eq_zero244
    hH3 t ht hE]
  have hDecomp := h3Path_physicalSource_eq_longitudinal_add_transverse244
    hH3 t
  constructor
  · intro hQ
    rw [hQ, add_zero] at hDecomp
    exact hDecomp
  · intro hR
    rw [hR] at hDecomp
    have hEq : h3PathPhysicalLongitudinalSource244 hH3 t +
        h3PathPhysicalTransverseSource244 hH3 t =
          h3PathPhysicalLongitudinalSource244 hH3 t + 0 := by
      simpa only [add_zero] using hDecomp.symm
    exact add_left_cancel hEq

/-- The kinetic energy cancels the normalization denominator in the
squared norm of physical angular velocity. -/
theorem h3Path_physicalAngularRate_energy_mul_norm_sq244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (hE : 0 < velocityH3Energy0At u t) :
    velocityH3Energy0At u t *
      ‖(Real.sqrt (velocityH3Energy0At u t))⁻¹ •
          h3PathPhysicalTransverseSource244 hH3 t‖ ^ 2 =
        ‖h3PathPhysicalTransverseSource244 hH3 t‖ ^ 2 := by
  let E : ℝ := velocityH3Energy0At u t
  let Q : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathPhysicalTransverseSource244 hH3 t
  have hRoot : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hNorm : ‖(Real.sqrt E)⁻¹ • Q‖ = ‖Q‖ / Real.sqrt E :=
    h3Path_physicalAngularRate_norm_eq_transverse_div_sqrt244 hH3 t hE
  change E * ‖(Real.sqrt E)⁻¹ • Q‖ ^ 2 = ‖Q‖ ^ 2
  rw [hNorm]
  have hCancel : Real.sqrt E * (‖Q‖ / Real.sqrt E) = ‖Q‖ := by
    calc
      Real.sqrt E * (‖Q‖ / Real.sqrt E) =
          (‖Q‖ / Real.sqrt E) * Real.sqrt E := mul_comm _ _
      _ = ‖Q‖ := div_mul_cancel₀ _ (ne_of_gt hRoot)
  calc
    E * (‖Q‖ / Real.sqrt E) ^ 2 =
        (Real.sqrt E) ^ 2 * (‖Q‖ / Real.sqrt E) ^ 2 := by
      rw [Real.sq_sqrt hE.le]
    _ = (Real.sqrt E * (‖Q‖ / Real.sqrt E)) ^ 2 := by
      rw [mul_pow]
    _ = ‖Q‖ ^ 2 := by rw [hCancel]

/-- Exact physical angular Gram identity: the scalar Gram determinant
is E₀² times squared Hilbert-sphere angular speed. -/
theorem h3Path_physicalSourceGram_eq_energy_sq_mul_unitVelocity_deriv_sq244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    h3PathPhysicalSourceGramDefect244 hH3 t =
      (velocityH3Energy0At u t) ^ 2 *
        ‖deriv (h3PathPhysicalUnitVelocity244 hH3) t‖ ^ 2 := by
  let E : ℝ := velocityH3Energy0At u t
  let Q : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathPhysicalTransverseSource244 hH3 t
  have hDerivative :
      deriv (h3PathPhysicalUnitVelocity244 hH3) t =
        (Real.sqrt E)⁻¹ • Q :=
    (h3Path_physicalUnitVelocity_hasDerivAt_angular244 hH3 t ht hE).deriv
  have hAngular : E * ‖deriv (h3PathPhysicalUnitVelocity244 hH3) t‖ ^ 2 =
      ‖Q‖ ^ 2 := by
    rw [hDerivative]
    exact h3Path_physicalAngularRate_energy_mul_norm_sq244 hH3 t hE
  calc
    h3PathPhysicalSourceGramDefect244 hH3 t = E * ‖Q‖ ^ 2 :=
      h3Path_physicalSourceGram_eq_kinetic_mul_transverse_sq244
        hH3 t ht hE
    _ = E * (E * ‖deriv (h3PathPhysicalUnitVelocity244 hH3) t‖ ^ 2) := by
      rw [hAngular]
    _ = E ^ 2 * ‖deriv (h3PathPhysicalUnitVelocity244 hH3) t‖ ^ 2 := by
      ring

/-- Vanishing Gram defect is also equivalent to stationary physical unit
direction at the specified strict time, provided kinetic energy is positive. -/
theorem h3Path_physicalSourceGram_eq_zero_iff_angularDeriv_eq_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    h3PathPhysicalSourceGramDefect244 hH3 t = 0 ↔
      deriv (h3PathPhysicalUnitVelocity244 hH3) t = 0 := by
  rw [h3Path_physicalSourceGram_eq_zero_iff_transverse_eq_zero244
    hH3 t ht hE]
  have hDerivative :=
    (h3Path_physicalUnitVelocity_hasDerivAt_angular244 hH3 t ht hE).deriv
  rw [hDerivative]
  have hRoot : (Real.sqrt (velocityH3Energy0At u t))⁻¹ ≠ 0 :=
    ne_of_gt (inv_pos.mpr (Real.sqrt_pos.2 hE))
  constructor
  · intro hQ
    rw [hQ, smul_zero]
  · intro hSmul
    exact (smul_eq_zero.mp hSmul).resolve_left hRoot

end
end PrimeTensor.FirstMonomialTriad
