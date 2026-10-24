import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticTerminalTail244
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Exact physical kinetic/transverse momentum-source decomposition

The actual physical Hilbert velocity U and projected momentum source R obey

  ‖U‖² = E₀,    ⟪U,R⟫ = -D₀.

Consequently the division-free weighted transverse source W = E₀ R + D₀ U
is exactly orthogonal to U. On positive kinetic energy, the normalized
transverse source Q = R + (D₀/E₀) • U satisfies

  R = Q - (D₀/E₀) • U,
  ⟪U,Q⟫ = 0,
  ‖R‖² = ‖Q‖² + D₀²/E₀.

This isolates the genuinely transverse physical source from its dissipative
kinetic projection. The scalar kinetic-energy budget controls only the latter;
no integrability of Q or terminal Hilbert trace is asserted. An already
established strictly positive terminal kinetic limit supplies E₀>0 on the
whole corresponding H³ tail, allowing this split throughout the tail.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The weighted transverse projected momentum source, defined even when
kinetic energy vanishes (no quotient or special case). -/
noncomputable def h3PathPhysicalWeightedTransverseSource244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : H3PhysicalRealFinVectorL2Hilbert :=
  (velocityH3Energy0At u t) • (h3PathActualProjectedMomentumSource244 hH3 t) +
    (velocityH3Dissipation0At u t) •
      (h3AuditInitialOldPhysicalHilbertTotal hH3 t)

/-- The unweighted transverse source, meaningful whenever kinetic energy
is positive. Its algebraic definition is total; the geometric properties
below require E₀>0. -/
noncomputable def h3PathPhysicalTransverseSource244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : H3PhysicalRealFinVectorL2Hilbert :=
  h3PathActualProjectedMomentumSource244 hH3 t +
    (velocityH3Dissipation0At u t / velocityH3Energy0At u t) •
      (h3AuditInitialOldPhysicalHilbertTotal hH3 t)

/-- Exact weighted tangency of the actual projected Navier--Stokes source,
with no nonzero kinetic-mass assumption. -/
theorem h3Path_physicalWeightedTransverse_orthogonal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
      (h3PathPhysicalWeightedTransverseSource244 hH3 t) = 0 := by
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  let R : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3 t
  let E : ℝ := velocityH3Energy0At u t
  let D : ℝ := velocityH3Dissipation0At u t
  have hPair : inner ℝ U R = -D :=
    h3Path_physicalHilbertPairing_eq_negDissipation0_positiveTime244 hH3 t ht
  have hKin : inner ℝ U U = E := by
    rw [real_inner_self_eq_norm_sq]
    exact h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy hH3 t ht
  change inner ℝ U (E • R + D • U) = 0
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    hPair, hKin]
  ring

/-- When E₀>0, multiplying the normalized transverse source by E₀
recovers the division-free transverse source. -/
theorem h3Path_physicalTransverse_scaled_eq_weighted244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ)
    (hE : 0 < velocityH3Energy0At u t) :
    (velocityH3Energy0At u t) • h3PathPhysicalTransverseSource244 hH3 t =
      h3PathPhysicalWeightedTransverseSource244 hH3 t := by
  let E : ℝ := velocityH3Energy0At u t
  let D : ℝ := velocityH3Dissipation0At u t
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  let R : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3 t
  have hCoeff : E * (D / E) = D := by
    calc
      E * (D / E) = D * (E / E) := by
        simp only [div_eq_mul_inv]
        ring
      _ = D := by
        rw [div_self (ne_of_gt hE), mul_one]
  change E • (R + (D / E) • U) = E • R + D • U
  rw [smul_add, smul_smul, hCoeff]

/-- Exact orthogonality of the physical transverse source to physical velocity. -/
theorem h3Path_physicalTransverse_orthogonal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
      (h3PathPhysicalTransverseSource244 hH3 t) = 0 := by
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  let Q : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathPhysicalTransverseSource244 hH3 t
  let E : ℝ := velocityH3Energy0At u t
  have hScaled : E • Q = h3PathPhysicalWeightedTransverseSource244 hH3 t :=
    h3Path_physicalTransverse_scaled_eq_weighted244 hH3 t hE
  have hWeighted : inner ℝ U (h3PathPhysicalWeightedTransverseSource244 hH3 t) = 0 :=
    h3Path_physicalWeightedTransverse_orthogonal244 hH3 t ht
  have hMul : E * inner ℝ U Q = 0 := by
    calc
      E * inner ℝ U Q = inner ℝ U (E • Q) := by rw [real_inner_smul_right]
      _ = inner ℝ U (h3PathPhysicalWeightedTransverseSource244 hH3 t) := by rw [hScaled]
      _ = 0 := hWeighted
  exact (mul_eq_zero.mp hMul).resolve_left (ne_of_gt hE)

/-- Full Pythagorean separation of the physical momentum source into
its kinetic-loss component and the transverse component. -/
theorem h3Path_physicalSource_pythagorean_transverse244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ^ 2 =
      ‖h3PathPhysicalTransverseSource244 hH3 t‖ ^ 2 +
      ‖(velocityH3Dissipation0At u t / velocityH3Energy0At u t) •
        (h3AuditInitialOldPhysicalHilbertTotal hH3 t)‖ ^ 2 := by
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  let R : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3 t
  let Q : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathPhysicalTransverseSource244 hH3 t
  let E : ℝ := velocityH3Energy0At u t
  let D : ℝ := velocityH3Dissipation0At u t
  have hUQ : inner ℝ U Q = 0 :=
    h3Path_physicalTransverse_orthogonal244 hH3 t ht hE
  have hOrth : inner ℝ (-((D / E) • U)) Q = 0 := by
    rw [inner_neg_left, real_inner_smul_left, hUQ]
    ring
  have hQ : Q = R + (D / E) • U := rfl
  have hSum : -((D / E) • U) + Q = R := by
    rw [hQ]
    abel
  calc
    ‖R‖ ^ 2 = ‖-((D / E) • U) + Q‖ ^ 2 := by rw [hSum]
    _ = ‖-((D / E) • U)‖ ^ 2 + ‖Q‖ ^ 2 := by
      simpa only [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
          (-((D / E) • U)) Q hOrth)
    _ = ‖Q‖ ^ 2 + ‖(D / E) • U‖ ^ 2 := by rw [norm_neg]; ring

/-- The kinetic-loss component has squared norm exactly D₀²/E₀. -/
theorem h3Path_physicalRadialSource_norm_sq244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    ‖(velocityH3Dissipation0At u t / velocityH3Energy0At u t) •
      (h3AuditInitialOldPhysicalHilbertTotal hH3 t)‖ ^ 2 =
      velocityH3Dissipation0At u t ^ 2 / velocityH3Energy0At u t := by
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  let E : ℝ := velocityH3Energy0At u t
  let D : ℝ := velocityH3Dissipation0At u t
  have hKin : ‖U‖ ^ 2 = E :=
    h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy hH3 t ht
  calc
    ‖(D / E) • U‖ ^ 2 = (|D / E| * ‖U‖) ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs]
    _ = (D / E) ^ 2 * E := by rw [mul_pow, sq_abs, hKin]
    _ = D ^ 2 / E := by field_simp [ne_of_gt hE]

/-- Exact source-norm budget: the scalar kinetic estimate leaves a
nonnegative, explicitly orthogonal transverse-source gap. -/
theorem h3Path_physicalSource_norm_sq_eq_transverse_add_kineticCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ^ 2 =
      ‖h3PathPhysicalTransverseSource244 hH3 t‖ ^ 2 +
        velocityH3Dissipation0At u t ^ 2 / velocityH3Energy0At u t := by
  rw [h3Path_physicalSource_pythagorean_transverse244 hH3 t ht hE,
    h3Path_physicalRadialSource_norm_sq244 hH3 t ht hE]

/-- The transverse remainder sharpens the Cauchy--Schwarz source-cost
estimate, with equality only when the transverse source vanishes. -/
theorem h3Path_physicalKineticCost_sq_le_source_sq244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    velocityH3Dissipation0At u t ^ 2 / velocityH3Energy0At u t ≤
      ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ^ 2 := by
  have hEq :=
    h3Path_physicalSource_norm_sq_eq_transverse_add_kineticCost244 hH3 t ht hE
  have hNonneg : 0 ≤ ‖h3PathPhysicalTransverseSource244 hH3 t‖ ^ 2 :=
    sq_nonneg _
  linarith only [hEq, hNonneg]

/-- A strictly positive terminal kinetic infimum rules out zero kinetic
mass at every physical time on its H³ energy-class tail. -/
theorem h3Path_physicalKinetic_positive_of_positiveTerminal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) :
    0 < velocityH3Energy0At u t :=
  lt_of_lt_of_le hL (h3PathCanonical_terminalKineticEnergy_le_anchor (u := u) ht)

/-- Positive terminal kinetic mass guarantees the exact transverse source
norm decomposition on the entire strict energy-class tail. -/
theorem h3Path_physicalSource_norm_sq_terminalTransverse244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) :
    ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ^ 2 =
      ‖h3PathPhysicalTransverseSource244 hH3 t‖ ^ 2 +
        velocityH3Dissipation0At u t ^ 2 / velocityH3Energy0At u t := by
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  exact h3Path_physicalSource_norm_sq_eq_transverse_add_kineticCost244
    hH3 t htAbs (h3Path_physicalKinetic_positive_of_positiveTerminal244
      hH3 hClass hL t ht)

end
end PrimeTensor.FirstMonomialTriad
