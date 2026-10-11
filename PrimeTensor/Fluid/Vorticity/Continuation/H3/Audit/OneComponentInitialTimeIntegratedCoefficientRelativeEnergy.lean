import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialVariableTimeCoefficientRelativeEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Initial old/selected uniqueness with time-integrated comparison coefficients

The preceding initial relative-energy interface allows a time-varying
coefficient outside the primitive: `κ(t) * ∫₀ᵗ e`. Weak-energy estimates and
a time-dependent transport envelope more naturally yield `∫₀ᵗ κ(s) e(s)`.

This file proves that a uniform upper bound on `κ` reduces the latter to the
constant-coefficient integral inequality, using interval-integral monotonicity.
The product `κ * e` is explicitly assumed integrable; this is an analytic
requirement when `κ` is an arbitrary function rather than a smooth envelope.
The resulting criterion requires no value or comparison estimate from the
Navier--Stokes PDE at the artificial time-zero anchor.

The epsilon-accurate integrated residual inequality, initial comparison
integrability and positive-time continuity are still substantive hypotheses.
This is not a derivation of the missing Navier--Stokes weak--strong estimate.
The terminal actual-vorticity strong-H³ endpoint remains independent.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- A coefficient inside the energy integral can be replaced by the uniform
ceiling `K` when the comparison energy is nonnegative and both products are
interval-integrable. -/
theorem h3Audit_initialTimeIntegratedCoefficient_integral_le
    (e κ : ℝ → ℝ) (b K t : ℝ)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (heInt : IntervalIntegrable e volume 0 b)
    (hProductInt : IntervalIntegrable (fun s => κ s * e s) volume 0 b)
    (hκ : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K)
    (ht : t ∈ Set.Ioc (0 : ℝ) b) :
    (∫ s in (0 : ℝ)..t, κ s * e s) ≤
      K * ∫ s in (0 : ℝ)..t, e s := by
  have hSub : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc (0 : ℝ) b := by
    rw [Set.uIcc_of_le ht.1.le, Set.uIcc_of_le (le_trans ht.1.le ht.2)]
    intro s hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have heIntT : IntervalIntegrable e volume 0 t :=
    heInt.mono_set hSub
  have hProductIntT :
      IntervalIntegrable (fun s => κ s * e s) volume 0 t :=
    hProductInt.mono_set hSub
  have hKIntT :
      IntervalIntegrable (fun s => K * e s) volume 0 t :=
    heIntT.const_mul K
  have hPointwise : ∀ s ∈ Set.Icc (0 : ℝ) t,
      κ s * e s ≤ K * e s := by
    intro s hs
    exact mul_le_mul_of_nonneg_right
      (hκ s ⟨hs.1, hs.2.trans ht.2⟩) (heNonneg s)
  have hIntegral :
      (∫ s in (0 : ℝ)..t, κ s * e s) ≤
        ∫ s in (0 : ℝ)..t, K * e s :=
    intervalIntegral.integral_mono_on
      ht.1.le hProductIntT hKIntT hPointwise
  simpa only [intervalIntegral.integral_const_mul] using hIntegral

/-- A positive-time weak-energy comparison with an integrated coefficient
reduces to the existing fixed-coefficient approximate comparison. -/
theorem h3Audit_initialTimeIntegratedCoefficient_reduction
    (e κ R : ℝ → ℝ) (b K : ℝ)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (heInt : IntervalIntegrable e volume 0 b)
    (hProductInt : IntervalIntegrable (fun s => κ s * e s) volume 0 b)
    (hκ : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b → κ s ≤ K)
    (hApprox : ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) b →
      e t ≤ (∫ s in (0 : ℝ)..t, κ s * e s) +
        (∫ s in (0 : ℝ)..t, |R s|))
    (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) b) :
    e t ≤ (K * ∫ s in (0 : ℝ)..t, e s) +
      (∫ s in (0 : ℝ)..t, |R s|) := by
  have hCoefficient :
      (∫ s in (0 : ℝ)..t, κ s * e s) ≤
        K * ∫ s in (0 : ℝ)..t, e s :=
    h3Audit_initialTimeIntegratedCoefficient_integral_le
      e κ b K t heNonneg heInt hProductInt hκ ht
  exact (hApprox t ht).trans (add_le_add hCoefficient (le_refl _))

/-- Epsilon-accurate time-integrated coefficients and residuals imply the
exact initial scalar energy inequality, with no pointwise equality assumed. -/
theorem h3Audit_initialRelativeEnergy_exact_of_timeIntegratedCoefficient
    (e : ℝ → ℝ) (b K : ℝ)
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
            (∫ s in (0 : ℝ)..t, |R s|)) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) b →
      e t ≤ K * ∫ s in (0 : ℝ)..t, e s := by
  apply h3Audit_initialRelativeEnergy_exact_of_positiveTimeResidual
    e b K heZero heNonneg
  intro ε hε
  obtain ⟨κ, R, hκ, hProductInt, hRInt, hMass, hApprox⟩ :=
    hEpsilon ε hε
  refine ⟨K, R, le_rfl, hRInt, hMass, ?_⟩
  intro t ht
  exact h3Audit_initialTimeIntegratedCoefficient_reduction
    e κ R b K heNonneg heInt hProductInt hκ hApprox t ht

/-- Scalar initial uniqueness for an integrated coefficient, without
assuming the initial right-zero trace independently. -/
theorem h3Audit_initialScalarEnergy_zero_of_timeIntegratedCoefficient
    (e : ℝ → ℝ) (b K : ℝ) (hb : 0 < b)
    (heZero : e 0 = 0)
    (heNonneg : ∀ s : ℝ, 0 ≤ e s)
    (heInt : IntervalIntegrable e volume 0 b)
    (hePositive : ContinuousOn e (Set.Ioc (0 : ℝ) b))
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
  have hExact : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) b →
      e s ≤ K * ∫ r in (0 : ℝ)..s, e r :=
    h3Audit_initialRelativeEnergy_exact_of_timeIntegratedCoefficient
      e b K heZero heNonneg heInt hEpsilon
  have hRightZero : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    h3Audit_initialScalarRightZero_of_integrableExactEnergy
      e b K hb heNonneg heInt hExact
  have hRight : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 (e 0)) := by
    simpa only [heZero] using hRightZero
  have hClosed : ContinuousOn e (Set.Icc (0 : ℝ) b) :=
    h3Audit_initialScalarClosedContinuous_of_positiveAndRightTrace
      e b hb hePositive hRight
  exact h3Audit_initialScalarEnergy_integralGronwall
    e b K hb heNonneg hClosed hExact t ht

/-- The canonical physical initial comparison with a coefficient INSIDE the
energy integral. The old-minus-selected energy is nonnegative by its form,
so only integrability, positive-time scalar continuity, a coefficient bound,
and arbitrarily small PDE residuals are needed for the reduction. -/
def H3AuditInitialCanonicalTimeIntegratedCoefficientRelativeEnergyData
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
      ContinuousOn
        (fun t => ‖h3AuditInitialCanonicalPhysicalDifference
          hH3 hFourier0 A hA hU₀ t‖ ^ 2)
        (Set.Ioc (0 : ℝ) b) ∧
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

/-- A time-integrated coefficient reduces to the existing positive-time
approximate residual contract, preserving the same physical comparison. -/
theorem h3Audit_initialTimeIntegratedCoefficient_implies_positiveTimeResidualData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalTimeIntegratedCoefficientRelativeEnergyData hH3) :
    H3AuditInitialCanonicalPositiveTimeResidualRelativeEnergyData hH3 := by
  obtain ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hContinuous, hIntegrable, hEpsilon⟩ := hData
  refine ⟨hInt0, hMeas0, hFourier0, A, hA, hU₀,
    b, hb, hbT, hbR, K, hContinuous, hIntegrable, ?_⟩
  intro ε hε
  obtain ⟨κ, R, hκ, hProd, hRInt, hMass, hApprox⟩ := hEpsilon ε hε
  refine ⟨K, R, le_rfl, hRInt, hMass, ?_⟩
  intro t ht
  exact h3Audit_initialTimeIntegratedCoefficient_reduction
    (fun s => ‖h3AuditInitialCanonicalPhysicalDifference
      hH3 hFourier0 A hA hU₀ s‖ ^ 2)
    κ R b K (fun s => sq_nonneg _) hIntegrable hProd hκ hApprox t ht

/-- Canonical compact physical weak-test agreement derived from the
conditional integrated-coefficient relative-energy data. -/
theorem h3Audit_initialTimeIntegratedCoefficient_implies_compactWeakComparisonData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalTimeIntegratedCoefficientRelativeEnergyData hH3) :
    H3AuditInitialCanonicalCompactWeakComparisonData hH3 := by
  exact h3Audit_initialPositiveTimeResidual_implies_compactWeakComparisonData
    hH3
    (h3Audit_initialTimeIntegratedCoefficient_implies_positiveTimeResidualData
      hH3 hData)

/-- The corresponding initial physical L² trace and upper H³ energy trace. -/
theorem h3Audit_initialTimeIntegratedCoefficient_implies_physicalZeroJetAndEnergyUpper
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hData : H3AuditInitialCanonicalTimeIntegratedCoefficientRelativeEnergyData hH3) :
    H3AuditInitialPhysicalZeroJetL2AndEnergyUpper hH3 := by
  exact h3Audit_initialPositiveTimeResidual_implies_physicalZeroJetAndEnergyUpper
    hH3
    (h3Audit_initialTimeIntegratedCoefficient_implies_positiveTimeResidualData
      hH3 hData)

/-- Conditional full-time transverse conclusion, retaining the distinct
terminal actual-vorticity strong-H³ hypothesis. -/
theorem h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialTimeIntegratedCoefficient
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (i : Fin 3)
    (hPhysical : H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hData : H3AuditInitialCanonicalTimeIntegratedCoefficientRelativeEnergyData hH3) :
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityPositiveComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) ∧
    MemLp
      (h3AuditActualVelocityIntrinsicThreeHalvesTimeSeminorm hH3
        (h3TerminalActualVorticityNegativeComplementPair i))
      2 (volume.restrict (Set.Ioo (0 : ℝ) T)) := by
  exact h3Audit_onePhysicalEndpoint_twoIntrinsicThreeHalves_fullTime_of_initialPositiveTimeResidual
    hH3 hClass i hPhysical
    (h3Audit_initialTimeIntegratedCoefficient_implies_positiveTimeResidualData
      hH3 hData)

end
end Euclidean
end Bridge
end PrimeTensor
