import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionStrongDerivative244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalHilbertTimeEvolution
import Mathlib.Tactic

/-!
# Joint physical temporal regularity supplies the momentum time distribution

The existing classical old Navier--Stokes PDE, combined with a separately
stated *joint* (time,space) continuity hypothesis for its old temporal
velocity derivative, already supplies the actual strong physical `L²`
Hilbert derivative at every positive time: this is the earlier theorem
`h3Audit_initialOldJoint_implies_physicalHilbertHasDerivAt_at_positiveTime`.

The newly completed connected-time distribution kernel and the strong
Hilbert-derivative characterization let us transfer that fact into the
genuine real-time distributional momentum equation, compact temporal weak
tests and the actual closed-window solenoidal FTC. This is a PDE-facing
sufficient condition rather than another assumed distributional identity.

Joint temporal/spatial derivative continuity is an explicit extra premise:
it is *not* inferred from separate continuity or from H³ admissibility.
None of these theorems assert unconditional regularity or continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set TopologicalSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

/-- The classical preterminal Navier--Stokes dynamics, with the *explicit*
joint continuity of the old physical temporal derivative, produces the
actual scalar momentum PDE as an equality of regular time distributions.
No distributional momentum equation or weak FTC is assumed. -/
theorem h3Path_distributionalMomentum_of_oldTemporalDerivativeJointlyContinuous244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b := by
  apply (h3Path_distributionalMomentum_iff_physicalHilbertHasDerivAt_onStrict244
    hH3 ha hab hb).2
  intro s hs
  change HasDerivAt
    (h3AuditInitialOldPhysicalHilbertTotal hH3)
    (h3AuditInitialActualSpectralLaplacianTotal hH3 s -
      h3AuditInitialActualSpectralLerayTotal hH3 s) s
  exact h3Audit_initialOldJoint_implies_physicalHilbertHasDerivAt_at_positiveTime
    hH3 hOldJoint s ⟨ha.trans hs.1, hs.2.trans hb⟩

/-- The same PDE-side regularity yields the *literal* compact temporal test
identity, including its distributional minus sign and the actual physical
projected RHS, without postulating a test identity. -/
theorem h3Path_timeTestMomentum_of_oldTemporalDerivativeJointlyContinuous244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    h3PathSolenoidalTimeTestMomentumOn244 hH3 a b := by
  exact (h3Path_distributionalMomentum_iff_timeTestMomentum244
    hH3 ha hab hb).mp
    (h3Path_distributionalMomentum_of_oldTemporalDerivativeJointlyContinuous244
      hH3 hOldJoint ha hab hb)

/-- Under the same concrete classical-PDE regularity premise, the scalar
distribution result gives the genuine physical Hilbert-valued weak FTC on
any strict closed time interval. -/
theorem h3Path_solenoidalWeakFTC_of_oldTemporalDerivativeJointlyContinuous244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    H3AuditPhysicalSolenoidalWeakFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3) a b := by
  have hStrong : ∀ s : ℝ, s ∈ Set.Ioo a b →
      HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (h3PathActualProjectedMomentumSource244 hH3 s) s := by
    intro s hs
    change HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3AuditInitialActualSpectralLaplacianTotal hH3 s -
        h3AuditInitialActualSpectralLerayTotal hH3 s) s
    exact h3Audit_initialOldJoint_implies_physicalHilbertHasDerivAt_at_positiveTime
      hH3 hOldJoint s ⟨ha.trans hs.1, hs.2.trans hb⟩
  -- Use the direct scalar-derivative FTC theorem on the same closed interval;
  -- no artificial outer-interval extension is required.
  apply h3Path_solenoidalWeakFTC_of_pointwiseWeakMomentum244
    hH3 ha hab hb
  intro φ _hφ s hs
  let ψ : H3PhysicalRealFinVectorL2Hilbert :=
    h3WeakTestVectorPhysicalL2Hilbert φ
  exact (((innerSL ℝ) ψ).hasFDerivAt).comp_hasDerivAt s (hStrong s hs)

/-- A nonvanishing actual physical FTC defect rules out the joint-regularity
hypothesis for the old PDE: its failure is a concrete necessary obstruction,
not a false conclusion that the physical H³ path is ill-defined. -/
theorem h3Path_nonzeroPhysicalFTCDefect_forces_oldJointFailure244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hNonzero : h3PathActualProjectedMomentumFTCDefect244 hH3 a b ≠ 0) :
    ¬ H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T := by
  intro hOldJoint
  have hWeak := h3Path_solenoidalWeakFTC_of_oldTemporalDerivativeJointlyContinuous244
    hH3 hOldJoint ha hab hb
  have hZero := (h3Path_projectedFTCDefect_zeroOn_iff_solenoidalWeakFTC244
    hH3 ha hab hb).2 hWeak
  exact hNonzero (hZero b ⟨hab.le, le_rfl⟩)

end
end PrimeTensor.FirstMonomialTriad
