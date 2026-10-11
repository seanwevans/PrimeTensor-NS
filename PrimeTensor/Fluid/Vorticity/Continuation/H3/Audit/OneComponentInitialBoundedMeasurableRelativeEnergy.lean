import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialIntegralGronwallNoContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Initial comparison integrability from bounded measurable kinetic energy

The no-continuity Gronwall theorem requires the scalar comparison energy to
be integrable on an initial interval. Here we give a second, physically
recognizable sufficient condition: measurability and a uniform pointwise
bound for the nonnegative comparison energy on the strict initial interval.

The finite measure of `(0,b)` makes that bounded measurable scalar energy
integrable. We then reuse the existing continuous-coefficient,
vanishing-residual uniqueness machinery, WITHOUT reintroducing positive-time
energy continuity or independent coefficient-product integrability.

This is a trade of analytic hypotheses, not a consequence of the open-time
Navier--Stokes class by itself. In particular, it remains to prove the
actual bound, measurability, and PDE relative-energy estimate from the
physical old-solution equations. No terminal regularity hypothesis is
removed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- On a finite initial interval, a nonnegative, a.e.-measurable scalar
energy with a uniform upper bound is interval-integrable. No continuity
at the initial or interior times is required. -/
theorem h3Audit_initialBoundedMeasurableEnergy_intervalIntegrable
    (e : ℝ → ℝ) (b M : ℝ) (hb : 0 ≤ b)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (hMeas : AEStronglyMeasurable e
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) b)))
    (hBound : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b → e s ≤ M) :
    IntervalIntegrable e volume 0 b := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hb).2
  have hFinite : (volume : Measure ℝ) (Set.Ioo (0 : ℝ) b) <
      (⊤ : ENNReal) := measure_Ioo_lt_top
  refine IntegrableOn.of_bound hFinite hMeas M ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  simpa only [Real.norm_eq_abs, abs_of_nonneg (heNonneg s)] using
    hBound s hs

/-- The exact integrated-coefficient Gronwall comparison closes without
assuming `IntervalIntegrable e` separately: that property comes from a
measurable uniform bound on the nonnegative energy. -/
theorem h3Audit_initialBoundedMeasurableEnergy_zero_of_continuousCoefficient
    (e : ℝ → ℝ) (b K M : ℝ) (hb : 0 < b)
    (heZero : e 0 = 0)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (hMeas : AEStronglyMeasurable e
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) b)))
    (hBound : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b → e s ≤ M)
    (hEpsilon : ∀ ε : ℝ, 0 < ε →
      ∃ (κ R : ℝ → ℝ),
        ContinuousOn κ (Set.Icc (0 : ℝ) b) ∧
        (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K) ∧
        IntervalIntegrable (fun s => |R s|) volume 0 b ∧
        (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
        ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
          e t ≤ (∫ s in (0 : ℝ)..t, κ s * e s) +
            (∫ s in (0 : ℝ)..t, |R s|))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b) :
    e t = 0 := by
  have heInt : IntervalIntegrable e volume 0 b :=
    h3Audit_initialBoundedMeasurableEnergy_intervalIntegrable
      e b M hb.le heNonneg hMeas hBound
  have hExact : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b →
      e s ≤ K * ∫ r in (0 : ℝ)..s, e r :=
    h3Audit_initialRelativeEnergy_exact_of_continuousIntegratedCoefficient
      e b K hb.le heZero heNonneg heInt hEpsilon
  exact h3Audit_initialIntegrableScalarEnergy_zero_without_continuity
    e b K hb heNonneg heInt hExact t ht

/-- PDE-facing initial comparison with a finite kinetic-energy ceiling.
`e` is the actual old-minus-selected physical squared `L²` difference.
The measurable bound replaces the independent `L¹` premise, and all
approximate PDE residual inequalities remain explicit. -/
def H3AuditInitialCanonicalBoundedMeasurableRelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∃ (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (hFourier0 : VelocityH3FourierCompatibleAt u 0 hInt0 hMeas0)
    (A : ℝ) (hA : 0 < A)
    (hU₀ : ‖velocityH3SpectralStateAt u 0 hInt0 hMeas0 hFourier0‖ ≤ A)
    (b : ℝ),
    0 < b ∧ b < T ∧
    b ≤ h3FinHeatLerayRestartRadius 1 A ∧
    ∃ (M K : ℝ),
      AEStronglyMeasurable
        (fun s => ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ s‖ ^ 2)
        ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) b)) ∧
      (∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b →
        ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ s‖ ^ 2 ≤ M) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ (κ R : ℝ → ℝ),
          ContinuousOn κ (Set.Icc (0 : ℝ) b) ∧
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K) ∧
          IntervalIntegrable (fun s => |R s|) volume 0 b ∧
          (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (∫ s in (0 : ℝ)..t,
                κ s * ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|)

/-- Bounded measurable initial comparison energy yields the exact `L¹`
input expected by the preceding no-continuity relative-energy criterion. -/
theorem h3Audit_initialBoundedMeasurable_implies_noContinuityData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalBoundedMeasurableRelativeEnergyData hH3) :
    H3AuditInitialCanonicalContinuousIntegratedCoefficientNoEnergyContinuityData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, M, K, hEnergyMeas, hBound, hEpsilon⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, ?_, hEpsilon⟩
  exact h3Audit_initialBoundedMeasurableEnergy_intervalIntegrable
    (fun s => ‖h3AuditInitialCanonicalPhysicalDifference
      hH3 hFourier0 A hA hU₀ s‖ ^ 2)
    b M hb.le (fun s => sq_nonneg _) hEnergyMeas hBound

/-- Initial physical compact weak-test equality follows from measurable
energy and a uniform comparison-energy ceiling plus the actual residual
estimates; the initial old/selected equality is not an assumption. -/
theorem h3Audit_initialBoundedMeasurable_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalBoundedMeasurableRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialContinuousCoefficientNoEnergyContinuity_implies_compactWeakComparisonData
    hH3 (h3Audit_initialBoundedMeasurable_implies_noContinuityData
      hH3 hData)

/-- The old physical initial `L²` jet and `H³` upper energy trace follow
from the same bounded measurable relative-energy hypothesis. -/
theorem h3Audit_initialBoundedMeasurable_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalBoundedMeasurableRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialContinuousCoefficientNoEnergyContinuity_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialBoundedMeasurable_implies_noContinuityData
      hH3 hData)

/-- The terminal strong-`H³` actual-vorticity endpoint is independent;
initial bounded measurable relative energy supplies only the initial side. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialBoundedMeasurable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalBoundedMeasurableRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialContinuousCoefficientNoEnergyContinuity
    hH3 hClass i hPhysical
    (h3Audit_initialBoundedMeasurable_implies_noContinuityData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
