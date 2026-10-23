import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopACAEWeakMomentumError244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopProjectedFTCDefectCocycle244
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Tactic

/-!
# Real-time distributional momentum testing for the actual physical H³ path

The physical velocity and Leray-projected momentum source are independently
continuous in physical L² on every strictly preterminal interval. Consequently
their scalar pairings against compact solenoidal spatial tests are locally
integrable on the *open temporal interval* and define genuine scalar regular
distributions (not zero-by-nonintegrability placeholders).

This file gives the exact equivalence between a scalar distributional derivative
identity and the classical compact-time-test formulation, with the negative
sign imposed by distributional differentiation. It also packages the passage
from a time-tested equation with a pressure-functional remainder to a projected
time-distribution equation when the remainder vanishes on solenoidal tests.

Crucially, no distributional momentum identity is asserted to follow from the
separately classical preterminal PDE here. Proving it, and proving the uniqueness
of the resulting continuous temporal primitive, are distinct analytic steps.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set TopologicalSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

/-- Open time domain for a strictly positive preterminal physical window. -/
def h3PathStrictTimeOpen244 (a b : ℝ) : Opens ℝ :=
  ⟨Set.Ioo a b, isOpen_Ioo⟩

/-- Compact spatial-test physical momentum, viewed as a scalar time function. -/
noncomputable def h3PathPhysicalTestMomentumTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (φ : H3WeakTestVector) : ℝ → ℝ :=
  fun t => inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
    (h3AuditInitialOldPhysicalHilbertTotal hH3 t)

/-- The paired physical projected RHS as a scalar time function. -/
noncomputable def h3PathPhysicalTestProjectedSourceTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (φ : H3WeakTestVector) : ℝ → ℝ :=
  fun t => inner ℝ (h3WeakTestVectorPhysicalL2Hilbert φ)
    (h3PathActualProjectedMomentumSource244 hH3 t)

/-- Actual physical scalar momentum is locally time integrable on each open
strict interval. This follows from already-proved strong L² continuity. -/
theorem h3Path_physicalTestMomentum_locallyIntegrableOnStrict244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (_hab : a < b) (hb : b < T)
    (φ : H3WeakTestVector) :
    LocallyIntegrableOn
      (h3PathPhysicalTestMomentumTime244 hH3 φ)
      (h3PathStrictTimeOpen244 a b) (volume : Measure ℝ) := by
  have hSub : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨ha.trans ht.1, ht.2.trans hb⟩
  have hUCont : ContinuousOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3) (Set.Ioo a b) :=
    (h3Audit_initialOldPhysicalHilbert_continuousOn hH3).mono hSub
  have hScalar : ContinuousOn
      (h3PathPhysicalTestMomentumTime244 hH3 φ) (Set.Ioo a b) := by
    change ContinuousOn
      (fun t : ℝ => ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ))
        (h3AuditInitialOldPhysicalHilbertTotal hH3 t)) (Set.Ioo a b)
    exact ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ)).continuous.comp_continuousOn
      hUCont
  exact hScalar.locallyIntegrableOn measurableSet_Ioo

/-- The paired actual projected Navier--Stokes source is locally integrable
in physical time without any old pointwise temporal domination. -/
theorem h3Path_physicalTestSource_locallyIntegrableOnStrict244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (φ : H3WeakTestVector) :
    LocallyIntegrableOn
      (h3PathPhysicalTestProjectedSourceTime244 hH3 φ)
      (h3PathStrictTimeOpen244 a b) (volume : Measure ℝ) := by
  have hRCont : ContinuousOn
      (h3PathActualProjectedMomentumSource244 hH3) (Set.Ioo a b) :=
    (h3Path_actualProjectedMomentumSource_continuousOnStrict244
      hH3 ha hab hb).mono Set.Ioo_subset_Icc_self
  have hScalar : ContinuousOn
      (h3PathPhysicalTestProjectedSourceTime244 hH3 φ) (Set.Ioo a b) := by
    change ContinuousOn
      (fun t : ℝ => ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ))
        (h3PathActualProjectedMomentumSource244 hH3 t)) (Set.Ioo a b)
    exact ((innerSL ℝ) (h3WeakTestVectorPhysicalL2Hilbert φ)).continuous.comp_continuousOn
      hRCont
  exact hScalar.locallyIntegrableOn measurableSet_Ioo

/-- The regular scalar time distribution is built with the constructor
available in the project's pinned mathlib. `Distribution.ofFun` was added in
a later mathlib revision; the test-function integral CLM already exists here. -/
noncomputable def h3PathRegularTimeDistribution244
    (Ω : Opens ℝ) (f : ℝ → ℝ) : Distribution Ω ℝ ⊤ :=
  (UniformConvergenceCLM.ofFun (RingHom.id ℝ) ℝ
    {S : Set (TestFunction Ω ℝ ⊤) | IsCompact S})
      (TestFunction.integralAgainstBilinCLM
        (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure ℝ) f)

/-- Evaluation of this distribution at a compactly supported time test,
under the independently established local integrability premise. -/
theorem h3Path_regularTimeDistribution_apply244
    (Ω : Opens ℝ) (f : ℝ → ℝ)
    (hf : LocallyIntegrableOn f Ω (volume : Measure ℝ))
    (θ : TestFunction Ω ℝ ⊤) :
    h3PathRegularTimeDistribution244 Ω f θ =
      ∫ t : ℝ, θ t • f t := by
  -- The pinned `Distribution` is a compact-convergence *type copy* of
  -- `ContinuousLinearMap`.  Unwrap that copy before applying its integral API.
  change
    (TestFunction.integralAgainstBilinCLM
      (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure ℝ) f) θ =
        ∫ t : ℝ, θ t • f t
  exact TestFunction.integralAgainstBilinCLM_eq_integral hf

/-- Genuine distributional physical momentum evolution, tested in time and
in compact divergence-free spatial directions. No time differentiability of
physical velocity is built into the definition. -/
def h3PathSolenoidalDistributionalMomentumOn244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b : ℝ) : Prop :=
  ∀ φ : H3WeakTestVector, H3WeakTestVectorDivergenceFree φ →
    Distribution.lineDerivCLM (1 : ℝ)
        (h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 a b)
          (h3PathPhysicalTestMomentumTime244 hH3 φ)) =
      h3PathRegularTimeDistribution244 (h3PathStrictTimeOpen244 a b)
        (h3PathPhysicalTestProjectedSourceTime244 hH3 φ)

/-- The explicit compact-time-test identity, including the distributional
minus sign. The spatial test is fixed while the smooth temporal test varies. -/
def h3PathSolenoidalTimeTestMomentumOn244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b : ℝ) : Prop :=
  ∀ φ : H3WeakTestVector, H3WeakTestVectorDivergenceFree φ →
    ∀ θ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
      -(∫ t : ℝ,
          (TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) θ) t •
            h3PathPhysicalTestMomentumTime244 hH3 φ t) =
        ∫ t : ℝ, θ t • h3PathPhysicalTestProjectedSourceTime244 hH3 φ t

/-- The genuine regular-distribution equation is exactly the classical
compact-time-test weak momentum identity. Both regular distributions have
already been shown to arise from locally integrable scalar functions. -/
theorem h3Path_distributionalMomentum_iff_timeTestMomentum244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b ↔
      h3PathSolenoidalTimeTestMomentumOn244 hH3 a b := by
  constructor
  · intro hDist φ hφ θ
    have hM := h3Path_physicalTestMomentum_locallyIntegrableOnStrict244
      hH3 ha hab hb φ
    have hR := h3Path_physicalTestSource_locallyIntegrableOnStrict244
      hH3 ha hab hb φ
    have hApply := congrArg
      (fun D : Distribution (h3PathStrictTimeOpen244 a b) ℝ ⊤ => D θ)
      (hDist φ hφ)
    rw [Distribution.lineDerivCLM_apply,
      h3Path_regularTimeDistribution_apply244 _ _ hM,
      h3Path_regularTimeDistribution_apply244 _ _ hR] at hApply
    exact hApply
  · intro hTests φ hφ
    have hM := h3Path_physicalTestMomentum_locallyIntegrableOnStrict244
      hH3 ha hab hb φ
    have hR := h3Path_physicalTestSource_locallyIntegrableOnStrict244
      hH3 ha hab hb φ
    ext θ
    rw [Distribution.lineDerivCLM_apply,
      h3Path_regularTimeDistribution_apply244 _ _ hM,
      h3Path_regularTimeDistribution_apply244 _ _ hR]
    exact hTests φ hφ θ

/-- An arbitrary pressure functional drops out of the time-tested momentum
equation once it annihilates divergence-free spatial tests. No L² pressure
field or product-measure Fubini theorem is assumed in this cancellation. -/
theorem h3Path_timeTestMomentum_of_pressureNeutralTimeTests244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b : ℝ)
    (P : H3WeakTestVector →
      TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤ → ℝ)
    (hEquation : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∀ θ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
        -(∫ t : ℝ,
          (TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) θ) t •
            h3PathPhysicalTestMomentumTime244 hH3 φ t) =
        (∫ t : ℝ, θ t • h3PathPhysicalTestProjectedSourceTime244 hH3 φ t) +
          P φ θ)
    (hPressure : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∀ θ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
        P φ θ = 0) :
    h3PathSolenoidalTimeTestMomentumOn244 hH3 a b := by
  intro φ hφ θ
  simpa only [hPressure φ hφ θ, add_zero] using hEquation φ hφ θ

/-- The same pressure-neutral time tests produce an equality of physical
regular temporal distributions, under already-proved local integrability. -/
theorem h3Path_distributionalMomentum_of_pressureNeutralTimeTests244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (P : H3WeakTestVector →
      TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤ → ℝ)
    (hEquation : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∀ θ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
        -(∫ t : ℝ,
          (TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) θ) t •
            h3PathPhysicalTestMomentumTime244 hH3 φ t) =
        (∫ t : ℝ, θ t • h3PathPhysicalTestProjectedSourceTime244 hH3 φ t) +
          P φ θ)
    (hPressure : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∀ θ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
        P φ θ = 0) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b := by
  apply (h3Path_distributionalMomentum_iff_timeTestMomentum244
    hH3 ha hab hb).2
  exact h3Path_timeTestMomentum_of_pressureNeutralTimeTests244
    hH3 a b P hEquation hPressure

/-- Snapshotwise annihilation of a scalar pressure pairing implies its
entire compact-time-test contribution is exactly zero. In particular, this
does not require a spacetime integrability estimate on the pressure gradient:
the scalar tested integrand vanishes at every time before integration. -/
theorem h3Path_timeTestPressureIntegral_eq_zero_of_snapshotwise244
    (a b : ℝ)
    (P : H3WeakTestVector → ℝ → ℝ)
    (hPressure : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∀ t : ℝ, P φ t = 0)
    (φ : H3WeakTestVector) (hφ : H3WeakTestVectorDivergenceFree φ)
    (θ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤) :
    (∫ t : ℝ, θ t * P φ t) = 0 := by
  have hZero : (fun t : ℝ => θ t * P φ t) = (fun _ : ℝ => (0 : ℝ)) := by
    funext t
    rw [hPressure φ hφ t]
    simp
  rw [hZero]
  simp

/-- A pressure term that cancels snapshotwise against solenoidal spatial
tests also cancels in the real-time distributional momentum equation. This
reduces the future PDE obligation to establishing the tested momentum identity
before pressure cancellation, rather than bounding pressure in physical L². -/
theorem h3Path_distributionalMomentum_of_snapshotwisePressureTimeTests244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (P : H3WeakTestVector → ℝ → ℝ)
    (hEquation : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∀ θ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
        -(∫ t : ℝ,
          (TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) θ) t •
            h3PathPhysicalTestMomentumTime244 hH3 φ t) =
        (∫ t : ℝ, θ t • h3PathPhysicalTestProjectedSourceTime244 hH3 φ t) +
          (∫ t : ℝ, θ t * P φ t))
    (hPressure : ∀ φ : H3WeakTestVector,
      H3WeakTestVectorDivergenceFree φ →
      ∀ t : ℝ, P φ t = 0) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b := by
  apply (h3Path_distributionalMomentum_iff_timeTestMomentum244
    hH3 ha hab hb).2
  intro φ hφ θ
  have hZero := h3Path_timeTestPressureIntegral_eq_zero_of_snapshotwise244
    a b P hPressure φ hφ θ
  simpa only [hZero, add_zero] using hEquation φ hφ θ

end
end PrimeTensor.FirstMonomialTriad
