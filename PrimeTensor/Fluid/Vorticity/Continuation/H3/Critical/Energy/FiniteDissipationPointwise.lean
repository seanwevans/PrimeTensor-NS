import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.ThirdOrderAbsorption
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialCofinalKineticAnchorsRelativeEnergy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceH3EnergyEscape244
import Mathlib.Tactic

/-!
# Finite full H³ dissipation: pointwise energy and projected-source control

An independent additive proof layer. The exact source comes from the already
verified physical L² projected momentum representative; no new PDE or Fourier
identification is introduced. This is only the pointwise portion of the proposed
finite-dissipation terminal-trace argument. Temporal integrability and a
terminal Cauchy lemma remain separate obligations.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set
open PrimeTensor.FirstMonomialTriad

noncomputable section
set_option maxHeartbeats 800000

/-- The existing fourth-moment Young inequality with K = ε = 1. -/
theorem h3Critical_energy3_le_energy0_add_dissipation3
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3Energy3At u t ≤
      velocityH3Dissipation3At u t + velocityH3Energy0At u t := by
  have hYoung :=
    mul_velocityH3Energy3At_le_dissipation3_add_quartic_remainder
      (K := (1 : ℝ)) (ε := (1 : ℝ))
      hH3 hClass ht (by norm_num) (by norm_num)
  simpa only [one_mul, one_pow, div_one] using hYoung

/-- The full H³ energy is linearly dominated by kinetic energy and
full H³ dissipation, with constants independent of the time slice. -/
theorem h3Critical_energy_le_kinetic_add_dissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3EnergyAt u t ≤
      1 + 6 * velocityH3Energy0At u t +
        3 * velocityH3DissipationAt u t := by
  have hTotal :=
    velocityH3EnergyAt_le_one_add_three_mul_energy0_add_energy3_on_h3Path
      hH3 hClass ht
  have hTop := h3Critical_energy3_le_energy0_add_dissipation3 hH3 hClass ht
  have hD := velocityH3Dissipation3At_le_dissipationAt u t
  linarith only [hTotal, hTop, hD]

/-- On any later terminal subtail, use the kinetic anchor rather than
an additional uniform-in-time H³ hypothesis. -/
theorem h3Critical_energy_le_kinetic_anchor_add_dissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    velocityH3EnergyAt u t ≤
      1 + 6 * velocityH3Energy0At u b +
        3 * velocityH3DissipationAt u t := by
  have hb0 : b ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hb.1, hb.2⟩
  have ht0 : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hb0.1 ht.1, ht.2⟩
  have hKinetic : velocityH3Energy0At u t ≤ velocityH3Energy0At u b :=
    (h3Audit_initialKineticEnergy_antitoneOn_positiveInterval hH3)
      hb0 ht0 ht.1.le
  have hEnergy := h3Critical_energy_le_kinetic_add_dissipation
    hH3 hClass ⟨lt_trans hb.1 ht.1, ht.2⟩
  linarith only [hEnergy, hKinetic]

/-- The actual projected momentum source obeys a time-uniform affine
majorant in the full H³ dissipation; the temporal L¹ step is next. -/
theorem h3Critical_projected_source_le_kinetic_anchor_add_dissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ≤
      (3 + h3AuditInitialLerayEnergyCoefficient) *
        (1 + 6 * velocityH3Energy0At u b +
          3 * velocityH3DissipationAt u t) := by
  have ht0 : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 ht.1), ht.2⟩
  have hSource := h3Path_physicalProjectedSource_norm_le_H3Energy244
    hH3 t ht0
  have hEnergy := h3Critical_energy_le_kinetic_anchor_add_dissipation
    hH3 hClass hb ht
  have hCoefficient : (0 : ℝ) ≤ 3 + h3AuditInitialLerayEnergyCoefficient := by
    have h := h3AuditInitialLerayEnergyCoefficient_nonneg
    linarith only [h]
  exact hSource.trans (mul_le_mul_of_nonneg_left hEnergy hCoefficient)

end
end PrimeTensor.Bridge.Euclidean
