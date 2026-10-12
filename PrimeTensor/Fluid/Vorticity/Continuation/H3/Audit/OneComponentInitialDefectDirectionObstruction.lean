import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialAnchoredSchwartzWeakSequence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialWeakIdentifiedQuantitativeTrace

/-!
# Initial physical L² mismatch and its single-direction weak obstruction

Subcritical H³ growth and positive-time physical momentum evolution yield a
strong right-zero physical L² limit `L` with an explicit convergence rate.
No positive-time derivative or source estimate can by itself identify this
integration constant with the separately stipulated physical initial `U₀`.

Here the unresolved initial mismatch `L - U₀` is quantified: the physical
L² jump norm at time t differs from `‖L - U₀‖` by at most the same
`t^(1-α)` modulus. A nonzero initial mismatch therefore cannot disappear
through arbitrarily small-time sampling.

Instead of postulating a weak sequence for every Schwartz probe, it is enough
to have one weak sequence in the *single Hilbert direction `L - U₀`*, once
`L` has been independently constructed from the physical projected RHS.
That scalar sequence identifies the initial datum, and the existing proven
quantitative initial physical and kinetic bounds then apply unchanged.

The defect-direction weak sequence is an independent initial-value input,
not a consequence of open-time Navier--Stokes H³ admissibility. The terminal
physical vorticity H³ endpoint also remains separate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- Quantitative physical L² mismatch: perturbing a strongly convergent
momentum state by `δ` changes the norm of its difference to *any* prescribed
initial state by at most `δ`, giving an explicit lower bound for a jump. -/
theorem h3Audit_initialPhysicalMismatch_normModulus_and_lower
    (x L U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (δ : ℝ) (hIncrement : ‖x - L‖ ≤ δ) :
    |‖x - U₀‖ - ‖L - U₀‖| ≤ δ ∧
      ‖L - U₀‖ - δ ≤ ‖x - U₀‖ := by
  have hDifference : (x - U₀) - (L - U₀) = x - L := by
    abel
  have hAbs : |‖x - U₀‖ - ‖L - U₀‖| ≤ δ := by
    calc
      |‖x - U₀‖ - ‖L - U₀‖| ≤
          ‖(x - U₀) - (L - U₀)‖ :=
        abs_norm_sub_norm_le (x - U₀) (L - U₀)
      _ = ‖x - L‖ := by rw [hDifference]
      _ ≤ δ := hIncrement
  refine ⟨hAbs, ?_⟩
  have hLower := (abs_le.mp hAbs).1
  linarith only [hLower]

/-- A subcritical projected physical source produces a sharp quantitative
classification of the possible initial L² mismatch, without *any* initial
weak sequence or time-zero continuity premise. In particular the lower bound
exposes any nonzero jump relative to the actual `u(0)` physical L² jet. -/
theorem h3Audit_initialSubcriticalEnergyRate_physicalMismatchModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b α M : ℝ) (hb : 0 < b) (hbT : b < T)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hM : 0 ≤ M)
    (hRate : ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) b →
      velocityH3EnergyAt u s ≤ M * s ^ (-α)) :
    ∃ L : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        (|‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ -
          ‖L - h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖| ≤
            ((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
              (t ^ (-α + 1) / (-α + 1))) ∧
        (‖L - h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ -
            ((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
              (t ^ (-α + 1) / (-α + 1)) ≤
          ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
            h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖) := by
  obtain ⟨L, hL, hModulus⟩ :=
    h3Audit_initialSubcriticalEnergyRate_physicalMomentum_rightLimitRate
      hH3 hOldJoint b α M hb hbT hα0 hα1 hM hRate
  refine ⟨L, hL, ?_⟩
  intro t ht
  exact h3Audit_initialPhysicalMismatch_normModulus_and_lower
    (h3AuditInitialOldPhysicalHilbertTotal hH3 t) L
    (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
    (((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
      (t ^ (-α + 1) / (-α + 1)))
    (hModulus t ht)

/-- The real-Hilbert *single defect-direction* pairing on one right-zero
sequence is sufficient to identify an independently constructed strong
physical limit with the prescribed initial datum. No dense test family,
Schwartz condition, or initial anchored weak FTC is required here. -/
theorem h3Audit_initialStrongPhysicalLimit_eq_of_defectDirectionSequence
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (L U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (hStrong : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L))
    (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)))
    (hDefect : Tendsto
      (fun n : ℕ => inner ℝ (F (τ n)) (L - U₀))
      atTop (𝓝 (inner ℝ U₀ (L - U₀)))) :
    L = U₀ := by
  have hStrongSequence : Tendsto (fun n : ℕ => F (τ n))
      atTop (𝓝 L) := by
    simpa only [Function.comp_def] using hStrong.comp hτ
  have hInnerContinuous :
      Continuous (fun z : H3PhysicalRealFinVectorL2Hilbert =>
        inner ℝ z (L - U₀)) :=
    continuous_id.inner continuous_const
  have hStrongPairing : Tendsto
      (fun n : ℕ => inner ℝ (F (τ n)) (L - U₀))
      atTop (𝓝 (inner ℝ L (L - U₀))) :=
    hInnerContinuous.continuousAt.tendsto.comp hStrongSequence
  have hPair : inner ℝ L (L - U₀) =
      inner ℝ U₀ (L - U₀) :=
    tendsto_nhds_unique hStrongPairing hDefect
  have hZeroInner : inner ℝ (L - U₀) (L - U₀) = 0 := by
    rw [inner_sub_left]
    exact sub_eq_zero.mpr hPair
  have hNormSq : ‖L - U₀‖ ^ 2 = 0 := by
    simpa only [real_inner_self_eq_norm_sq] using hZeroInner
  have hNormZero : ‖L - U₀‖ = 0 := by
    nlinarith [norm_nonneg (L - U₀)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hNormZero)

/-- Weak matching of the actual time-zero datum is needed along only ONE
sequence, in the adaptively determined `L-U₀` direction for the physically
constructed right limit `L`. It is not a full Schwartz- or Hilbert-test
family of initial weak sequences. -/
def H3AuditInitialDefectDirectionWeakSequence
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (U₀ : H3PhysicalRealFinVectorL2Hilbert) : Prop :=
  ∀ L : H3PhysicalRealFinVectorL2Hilbert,
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L) →
      ∃ τ : ℕ → ℝ,
        Tendsto τ atTop (𝓝[>] (0 : ℝ)) ∧
        Tendsto (fun n : ℕ => inner ℝ (F (τ n)) (L - U₀))
          atTop (𝓝 (inner ℝ U₀ (L - U₀)))

/-- The single defect-direction weak sequence forces the *derived* physical
strong limit to coincide with the prescribed physical initial velocity. -/
theorem h3Audit_initialDefectDirectionWeakSequence_identifies_strongLimit
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (U₀ L : H3PhysicalRealFinVectorL2Hilbert)
    (hL : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hDefect : H3AuditInitialDefectDirectionWeakSequence F U₀) :
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
  obtain ⟨τ, hτ, hPair⟩ := hDefect L hL
  have hIdentify : L = U₀ :=
    h3Audit_initialStrongPhysicalLimit_eq_of_defectDirectionSequence
      F L U₀ hL τ hτ hPair
  simpa only [hIdentify] using hL

/-- A *single* initial defect-direction weak sequence suffices for the same
physical momentum and kinetic quantitative right-limit rates previously
obtained from every Hilbert weak pairing. The strong limit is constructed
from the actual diffusion-minus-Leray source, not postulated. -/
theorem h3Audit_initialSubcriticalDefectSequence_identifies_physicalAndKineticRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOldJoint : H3PreterminalLoggedVelocityTemporalDerivativeJointlyContinuous u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b α M : ℝ) (hb : 0 < b) (hbT : b < T)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hM : 0 ≤ M)
    (hRate : ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) b →
      velocityH3EnergyAt u s ≤ M * s ^ (-α))
    (hDefect : H3AuditInitialDefectDirectionWeakSequence
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) :
    (Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[>] (0 : ℝ))
        (𝓝 (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ≤
          ((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
            (t ^ (-α + 1) / (-α + 1))) ∧
    (Tendsto (velocityH3Energy0At u)
        (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3Energy0At u 0)) ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        |velocityH3Energy0At u t - velocityH3Energy0At u 0| ≤
          (((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
            (t ^ (-α + 1) / (-α + 1))) *
          (2 * ‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ +
            ((3 + h3AuditInitialLerayEnergyCoefficient) * M) *
              (t ^ (-α + 1) / (-α + 1)))) := by
  obtain ⟨L, hL, _hModulus⟩ :=
    h3Audit_initialSubcriticalEnergyRate_physicalMomentum_rightLimitRate
      hH3 hOldJoint b α M hb hbT hα0 hα1 hM hRate
  have hInitial : Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) :=
    h3Audit_initialDefectDirectionWeakSequence_identifies_strongLimit
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
      L hL hDefect
  have hWeak : ∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto
        (fun t : ℝ =>
          inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 t) ψ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ
          (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0) ψ)) := by
    intro ψ
    have hInnerContinuous :
        Continuous (fun z : H3PhysicalRealFinVectorL2Hilbert =>
          inner ℝ z ψ) :=
      continuous_id.inner continuous_const
    exact hInnerContinuous.continuousAt.tendsto.comp hInitial
  exact ⟨
    h3Audit_initialSubcriticalEnergyRate_weakIdentifies_physicalMomentumRate
      hH3 hOldJoint hInt0 hMeas0 b α M hb hbT hα0 hα1 hM
      hRate hWeak,
    h3Audit_initialSubcriticalEnergyRate_weakIdentifies_kineticRate
      hH3 hOldJoint hInt0 hMeas0 b α M hb hbT hα0 hα1 hM
      hRate hWeak⟩

end
end Euclidean
end Bridge
end PrimeTensor
