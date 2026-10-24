import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopUnconditionalHilbertFTCKinetic244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalIntegratedKineticLogPhaseBudget244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialRightKineticTraceReduction
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPathSmoothingClosure
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Physical Hilbert momentum source equals the genuine viscous kinetic loss

The previous checkpoint proved the physical strong L² derivative and the
physical L² kinetic norm-square derivative. The existing order-zero H³ PDE
energy argument independently proves the same kinetic derivative to be the
zeroth-order diffusion rate, and whole-space integration by parts identifies
that rate with `-2 * velocityH3Dissipation0At`.

There is an essential identification step: the actual old physical Hilbert
norm-square equals the old scalar kinetic energy at *every positive time*.
Use equality on a neighborhood to transport HasDerivAt before comparing rates.

The resulting Hilbert pairing is a *signed, exact* PDE statement:

    inner U(t) R(t) = -D0(t),

not a bound on the source norm or a new pressure regularity assumption.
Since D0 = E1 is differentiable at every strict time, it is continuous on
(0,T), giving the compact-time integrated physical energy-dissipation law.

No statement is made at the initial/terminal endpoints. The earlier selected
physical evolution / curl weak-FTC dependencies remain inherited.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Synchronize physical L² kinetic differentiation with the separate
order-zero Navier--Stokes energy equation. Both are derivatives of the same
actual kinetic energy on the open preterminal time interval. -/
theorem h3Path_physicalKineticHilbertPairing_eq_diffusion0_positiveTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    2 * inner ℝ
        (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
        (h3PathActualProjectedMomentumSource244 hH3 t) =
      velocityH3DiffusionDerivative0At u t := by
  obtain ⟨a, hClass, htClass⟩ :=
    h3Audit_h3Path_positiveEnergyClassCover hH3 t ht
  have hPDE :=
    h3Path_physicalKinetic_derivative_eq_diffusion0_244
      hH3 hClass htClass
  have hSame :
      (velocityH3Energy0At u) =ᶠ[𝓝 t]
        (fun r : ℝ => ‖h3AuditInitialOldPhysicalHilbertTotal hH3 r‖ ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact (h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
      hH3 r hr).symm
  have hPhysical :=
    h3Path_physicalL2KineticHasDerivAt_positiveTime244 hH3 t ht
  have hEnergy := hPhysical.congr_of_eventuallyEq hSame
  exact hEnergy.deriv.symm.trans hPDE

/-- Whole-space viscous integration by parts applies on a locally selected
H³ energy class at every strict positive preterminal time. -/
theorem h3Path_diffusion0_eq_negTwoDissipation0_positiveTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    velocityH3DiffusionDerivative0At u t =
      -2 * velocityH3Dissipation0At u t := by
  obtain ⟨a, hClass, htClass⟩ :=
    h3Audit_h3Path_positiveEnergyClassCover hH3 t ht
  have hIBP : H3DiffusionIntegrationByPartsAt u t :=
    h3PathEnergyClassProducesDiffusionIntegrationByParts_closed
      u T hH3 a hClass t htClass
  exact velocityH3DiffusionDerivative0At_eq_neg_two_mul_dissipation0 hIBP

/-- The projected canonical source has exactly the dissipative pairing with
the actual physical old L² velocity. In particular its kinetic projection
has a nonpositive sign without a pointwise pressure-force estimate. -/
theorem h3Path_physicalHilbertPairing_eq_negDissipation0_positiveTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    inner ℝ
        (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
        (h3PathActualProjectedMomentumSource244 hH3 t) =
      -velocityH3Dissipation0At u t := by
  have hPair :=
    h3Path_physicalKineticHilbertPairing_eq_diffusion0_positiveTime244
      hH3 t ht
  have hD :=
    h3Path_diffusion0_eq_negTwoDissipation0_positiveTime244
      hH3 t ht
  linarith only [hPair, hD]

/-- The genuine physical norm-square has an exact derivative `-2 D0`, with
no extra old temporal joint-continuity or pressure-integrability premise. -/
theorem h3Path_physicalKineticHasDerivAt_negDissipation0_positiveTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun r : ℝ => ‖h3AuditInitialOldPhysicalHilbertTotal hH3 r‖ ^ 2)
      (-2 * velocityH3Dissipation0At u t) t := by
  have hPair :=
    h3Path_physicalHilbertPairing_eq_negDissipation0_positiveTime244
      hH3 t ht
  exact (h3Path_physicalL2KineticHasDerivAt_positiveTime244
    hH3 t ht).congr_deriv (by rw [hPair]; ring)

/-- The first physical H³ energy block is exactly the zeroth viscous
dissipation mass, hence its existing differentiability makes D0 continuous
on all strict physical times. -/
theorem h3Path_dissipation0_continuousOn_positiveTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    ContinuousOn (velocityH3Dissipation0At u) (Set.Ioo (0 : ℝ) T) := by
  change ContinuousOn (velocityH3Energy1At u) (Set.Ioo (0 : ℝ) T)
  apply continuousOn_of_forall_continuousAt
  intro t ht
  obtain ⟨a, hClass, htClass⟩ :=
    h3Audit_h3Path_positiveEnergyClassCover hH3 t ht
  exact ((h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
    u T hH3 a hClass t htClass).2.1).continuousAt

/-- Exact physical positive-time kinetic dissipation budget on every ordered
strict-time interval. Its time-integrability is derived from H³ regularity,
not supplied as an independent premise. -/
theorem h3Path_physicalKinetic_integratedDissipation0_positiveTimes244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t) :
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2 +
        2 * (∫ r in s..t, velocityH3Dissipation0At u r) =
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ ^ 2 := by
  let U : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  have hSub : Set.Icc s t ⊆ Set.Ioo (0 : ℝ) T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hUContinuous : ContinuousOn U (Set.Icc s t) :=
    (h3Audit_initialOldPhysicalHilbert_continuousOn hH3).mono hSub
  have hKContinuous :
      ContinuousOn (fun r : ℝ => ‖U r‖ ^ 2) (Set.Icc s t) :=
    (continuous_norm.comp_continuousOn hUContinuous).pow 2
  have hDContinuous :
      ContinuousOn (velocityH3Dissipation0At u) (Set.Icc s t) :=
    (h3Path_dissipation0_continuousOn_positiveTime244 hH3).mono hSub
  have hDIntegrable :
      IntervalIntegrable (velocityH3Dissipation0At u) volume s t :=
    hDContinuous.intervalIntegrable_of_Icc hst
  have hRateIntegrable :
      IntervalIntegrable
        (fun r : ℝ => (-2 : ℝ) * velocityH3Dissipation0At u r)
        volume s t :=
    hDIntegrable.const_mul (-2)
  have hFTC :
      (∫ r in s..t, (-2 : ℝ) * velocityH3Dissipation0At u r) =
        ‖U t‖ ^ 2 - ‖U s‖ ^ 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hst hKContinuous
      (by
        intro r hr
        exact h3Path_physicalKineticHasDerivAt_negDissipation0_positiveTime244
          hH3 r (hSub ⟨hr.1.le, hr.2.le⟩))
      hRateIntegrable
  rw [intervalIntegral.integral_const_mul] at hFTC
  dsimp only [U] at hFTC
  linarith only [hFTC]

/-- The integral budget is for the exact old scalar order-zero energy,
by its independently proved identification with the actual Hilbert norm. -/
theorem h3Path_energy0_integratedDissipation0_positiveTimes244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t) :
    velocityH3Energy0At u t +
        2 * (∫ r in s..t, velocityH3Dissipation0At u r) =
      velocityH3Energy0At u s := by
  have hBudget := h3Path_physicalKinetic_integratedDissipation0_positiveTimes244
    hH3 s t hs ht hst
  rw [h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy hH3 t ht,
    h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy hH3 s hs] at hBudget
  exact hBudget

end
end PrimeTensor.FirstMonomialTriad
