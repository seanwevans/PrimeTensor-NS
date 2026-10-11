import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialContinuousIntegratedCoefficientRelativeEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integral Gronwall without scalar-energy continuity

For a nonnegative interval-integrable function `e`, the pointwise integral
comparison `e(t) ≤ K ∫₀ᵗ e` forces `e` to vanish on `[0,b]` even if `e` is
not continuous at any positive time. The proof does NOT differentiate `e`:
it applies the already formalized continuous scalar Gronwall lemma to the
continuous integral primitive `H(t) = ∫₀ᵗ e`.

The PDE-facing initial comparison can therefore omit the entire positive-time
scalar-energy continuity hypothesis. Product integrability of a coefficient
remains explicit unless supplied by an independent regularity estimate.
The relative-energy comparison, initial interval integrability, and shrinking
residual mass are still mathematical hypotheses, not deductions from the
open-time Navier--Stokes admissibility predicate. The terminal actual-vorticity
strong-H³ endpoint remains separate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- The integral form of Gronwall requires only integrability of the
nonnegative scalar energy, not continuity. Apply the continuous Gronwall
theorem to its forward integral primitive rather than to the energy itself.
The real coefficient `K` need not be assumed nonnegative. -/
theorem h3Audit_initialIntegrableScalarEnergy_zero_without_continuity
    (e : ℝ → ℝ) (b K : ℝ) (hb : 0 < b)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (heInt : IntervalIntegrable e volume 0 b)
    (hExact : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) b →
      e t ≤ K * ∫ s in (0 : ℝ)..t, e s)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b) :
    e t = 0 := by
  -- The nonnegative clamp does not change the primitive for `0 ≤ s`,
  -- but supplies the globally nonnegative input to the existing lemma.
  let H : ℝ → ℝ := fun s =>
    ∫ r in (0 : ℝ)..(max (0 : ℝ) s), e r
  have hContinuousU :
      ContinuousOn (fun s : ℝ => ∫ r in (0 : ℝ)..s, e r)
        (Set.uIcc (0 : ℝ) b) := by
    exact intervalIntegral.continuousOn_primitive_interval'
      heInt left_mem_uIcc
  have hRawContinuous :
      ContinuousOn (fun s : ℝ => ∫ r in (0 : ℝ)..s, e r)
        (Set.Icc (0 : ℝ) b) := by
    simpa only [Set.uIcc_of_le hb.le] using hContinuousU
  have hHAgree : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b →
      H s = ∫ r in (0 : ℝ)..s, e r := by
    intro s hs
    simp [H, max_eq_right hs.1]
  have hContinuous : ContinuousOn H (Set.Icc (0 : ℝ) b) := by
    apply hRawContinuous.congr
    intro s hs
    exact hHAgree s hs
  have hHIntegrable : IntervalIntegrable H volume 0 b :=
    hContinuous.intervalIntegrable_of_Icc hb.le
  have hHNonneg : ∀ s : ℝ, 0 ≤ H s := by
    intro s
    dsimp only [H]
    exact intervalIntegral.integral_nonneg
      (le_max_left (0 : ℝ) s) (fun r _hr => heNonneg r)
  have hHIntegralBound :
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b →
        H s ≤ K * ∫ r in (0 : ℝ)..s, H r := by
    intro s hs
    have hSub : Set.uIcc (0 : ℝ) s ⊆ Set.uIcc (0 : ℝ) b := by
      rw [Set.uIcc_of_le hs.1, Set.uIcc_of_le hb.le]
      intro r hr
      exact ⟨hr.1, hr.2.trans hs.2⟩
    have heIntS : IntervalIntegrable e volume 0 s :=
      heInt.mono_set hSub
    have hHIntS : IntervalIntegrable H volume 0 s :=
      hHIntegrable.mono_set hSub
    have hKHIntS :
        IntervalIntegrable (fun r : ℝ => K * H r) volume 0 s :=
      hHIntS.const_mul K
    have hPointwise : ∀ r ∈ Set.Icc (0 : ℝ) s,
        e r ≤ K * H r := by
      intro r hr
      rw [hHAgree r ⟨hr.1, hr.2.trans hs.2⟩]
      exact hExact r ⟨hr.1, hr.2.trans hs.2⟩
    have hMonotone :
        (∫ r in (0 : ℝ)..s, e r) ≤
          ∫ r in (0 : ℝ)..s, K * H r :=
      intervalIntegral.integral_mono_on
        hs.1 heIntS hKHIntS hPointwise
    calc
      H s = ∫ r in (0 : ℝ)..s, e r := hHAgree s hs
      _ ≤ ∫ r in (0 : ℝ)..s, K * H r := hMonotone
      _ = K * ∫ r in (0 : ℝ)..s, H r := by
        rw [intervalIntegral.integral_const_mul]
  have hHZero : H t = 0 :=
    h3Audit_initialScalarEnergy_integralGronwall
      H b K hb
      hHNonneg
      hContinuous hHIntegralBound t ht
  have hBound : e t ≤ K * H t := by
    rw [hHAgree t ht]
    exact hExact t ht
  rw [hHZero, mul_zero] at hBound
  exact le_antisymm hBound (heNonneg t)

/-- An arbitrary-small integrated residual comparison closes scalar energy
without any positive-time continuity hypothesis. -/
theorem h3Audit_initialScalarEnergy_zero_of_timeIntegratedCoefficient_noContinuity
    (e : ℝ → ℝ) (b K : ℝ) (hb : 0 < b)
    (heZero : e 0 = 0)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (heInt : IntervalIntegrable e volume 0 b)
    (hEpsilon : ∀ ε : ℝ, 0 < ε →
      ∃ (κ R : ℝ → ℝ),
        (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K) ∧
        IntervalIntegrable (fun s => κ s * e s) volume 0 b ∧
        IntervalIntegrable (fun s => |R s|) volume 0 b ∧
        (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
        ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
          e t ≤ (∫ s in (0 : ℝ)..t, κ s * e s) +
            (∫ s in (0 : ℝ)..t, |R s|))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b) :
    e t = 0 := by
  exact h3Audit_initialIntegrableScalarEnergy_zero_without_continuity
    e b K hb heNonneg heInt
    (h3Audit_initialRelativeEnergy_exact_of_timeIntegratedCoefficient
      e b K heZero heNonneg heInt hEpsilon) t ht

/-- Initial comparison with time-integrated coefficients and arbitrarily
small residuals, but no continuity assumption on the scalar energy.
The full initial physical comparison is still an independent PDE estimate. -/
def H3AuditInitialCanonicalTimeIntegratedCoefficientNoContinuityData
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
    ∃ K : ℝ,
      IntervalIntegrable
        (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2)
        volume 0 b ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ (κ R : ℝ → ℝ),
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K) ∧
          IntervalIntegrable
            (fun s => κ s *
              ‖h3AuditInitialCanonicalPhysicalDifference
                hH3 hFourier0 A hA hU₀ s‖ ^ 2)
            volume 0 b ∧
          IntervalIntegrable (fun s => |R s|) volume 0 b ∧
          (∫ s in (0 : ℝ)..b, |R s|) ≤ ε ∧
          ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
            ‖h3AuditInitialCanonicalPhysicalDifference
              hH3 hFourier0 A hA hU₀ t‖ ^ 2 ≤
              (∫ s in (0 : ℝ)..t,
                κ s * ‖h3AuditInitialCanonicalPhysicalDifference
                  hH3 hFourier0 A hA hU₀ s‖ ^ 2) +
              (∫ s in (0 : ℝ)..t, |R s|)

/-- The continuous scalar-energy interface is now a CONSEQUENCE, not a
premise: Gronwall forces the integrable comparison energy to vanish
pointwise, making its restriction to `[0,b]` a continuous zero function. -/
theorem h3Audit_initialTimeIntegratedNoContinuity_implies_scalarRelativeEnergyData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalTimeIntegratedCoefficientNoContinuityData hH3) :
    H3AuditInitialCanonicalScalarRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hEnergyInt, hEpsilon⟩ := hData
  let e : ℝ → ℝ := fun s =>
    ‖h3AuditInitialCanonicalPhysicalDifference
      hH3 hFourier0 A hA hU₀ s‖ ^ 2
  have heZero : e 0 = 0 := by simp [e]
  have heNonneg : ∀ s : ℝ, 0 ≤ e s := by
    intro s
    exact sq_nonneg _
  have hExact : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b →
      e s ≤ K * ∫ r in (0 : ℝ)..s, e r :=
    h3Audit_initialRelativeEnergy_exact_of_timeIntegratedCoefficient
      e b K heZero heNonneg hEnergyInt hEpsilon
  have hVanishing : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → e s = 0 := by
    intro s hs
    exact h3Audit_initialIntegrableScalarEnergy_zero_without_continuity
      e b K hb heNonneg hEnergyInt hExact s hs
  have hScalar : ContinuousOn e (Set.Icc (0 : ℝ) b) := by
    have hConst : ContinuousOn (fun _ : ℝ => (0 : ℝ))
        (Set.Icc (0 : ℝ) b) := continuousOn_const
    apply hConst.congr
    intro s hs
    exact hVanishing s hs
  exact ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hScalar, hExact⟩

/-- All compact physical weak-test pairings agree with the canonical
selected restart, without presupposing continuity of the difference energy. -/
theorem h3Audit_initialTimeIntegratedNoContinuity_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalTimeIntegratedCoefficientNoContinuityData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialScalarRelativeEnergy_implies_compactWeakComparisonData
    hH3 (h3Audit_initialTimeIntegratedNoContinuity_implies_scalarRelativeEnergyData
      hH3 hData)

/-- Recover the initial physical `L²` trace and upper `H³` energy trace
without any positive-time scalar-energy continuity hypothesis. -/
theorem h3Audit_initialTimeIntegratedNoContinuity_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalTimeIntegratedCoefficientNoContinuityData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialScalarRelativeEnergy_implies_physicalZeroJetAndEnergyUpper
    hH3 (h3Audit_initialTimeIntegratedNoContinuity_implies_scalarRelativeEnergyData
      hH3 hData)

/-- Conditional full-time transverse homogeneous `Ḣ^(3/2)` conclusion.
The terminal actual-vorticity strong-`H³` endpoint is still independent. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialTimeIntegratedNoContinuity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalTimeIntegratedCoefficientNoContinuityData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialScalarRelativeEnergy
    hH3 hClass i hPhysical
    (h3Audit_initialTimeIntegratedNoContinuity_implies_scalarRelativeEnergyData
      hH3 hData)

/-- Continuous coefficients also eliminate the weighted-product integrability
premise. Compared with the previous continuous-coefficient interface, the
positive-time continuity of the energy is NO LONGER assumed. -/
def H3AuditInitialCanonicalContinuousIntegratedCoefficientNoEnergyContinuityData
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
    ∃ K : ℝ,
      IntervalIntegrable
        (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2)
        volume 0 b ∧
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

/-- Derive weighted-product integrability from coefficient continuity; no
regularity of the original comparison energy beyond `L¹` is required. -/
theorem h3Audit_initialContinuousCoefficientNoEnergyContinuity_implies_integratedData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalContinuousIntegratedCoefficientNoEnergyContinuityData hH3) :
    H3AuditInitialCanonicalTimeIntegratedCoefficientNoContinuityData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hEnergyInt, hEpsilon⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hEnergyInt, ?_⟩
  intro ε hε
  obtain ⟨κ, R, hκCont, hκBound, hRInt, hMass, hApprox⟩ :=
    hEpsilon ε hε
  refine ⟨κ, R, hκBound, ?_, hRInt, hMass, hApprox⟩
  exact h3Audit_initialContinuousCoefficient_product_integrable
    (fun s => ‖h3AuditInitialCanonicalPhysicalDifference
      hH3 hFourier0 A hA hU₀ s‖ ^ 2)
    κ b hb.le hEnergyInt hκCont

/-- Derive canonical compact weak-test comparison using only energy `L¹`,
continuous coefficients, and arbitrarily small integrated PDE residuals. -/
theorem h3Audit_initialContinuousCoefficientNoEnergyContinuity_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalContinuousIntegratedCoefficientNoEnergyContinuityData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialTimeIntegratedNoContinuity_implies_compactWeakComparisonData
    hH3
    (h3Audit_initialContinuousCoefficientNoEnergyContinuity_implies_integratedData
      hH3 hData)

/-- Physical initial `L²` and `H³` energy upper traces follow without
positive-time scalar energy continuity or product-integrability premises. -/
theorem h3Audit_initialContinuousCoefficientNoEnergyContinuity_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalContinuousIntegratedCoefficientNoEnergyContinuityData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialTimeIntegratedNoContinuity_implies_physicalZeroJetAndEnergyUpper
    hH3
    (h3Audit_initialContinuousCoefficientNoEnergyContinuity_implies_integratedData
      hH3 hData)

/-- The independent terminal actual-vorticity strong-H³ endpoint remains
an explicit hypothesis for the full-time transverse result. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialContinuousCoefficientNoEnergyContinuity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalContinuousIntegratedCoefficientNoEnergyContinuityData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialTimeIntegratedNoContinuity
    hH3 hClass i hPhysical
    (h3Audit_initialContinuousCoefficientNoEnergyContinuity_implies_integratedData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
