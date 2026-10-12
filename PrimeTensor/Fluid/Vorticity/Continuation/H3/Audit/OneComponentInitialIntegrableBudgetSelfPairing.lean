import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialSampledKineticSelfPairing
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialIntegratedKineticBudgetRelativeEnergy

/-!
# Initial kinetic L¹ budget replaces a sampled kinetic ceiling

A subcritical projected physical RHS yields a strong right physical Hilbert
limit L and a kinetic right limit ‖L‖², both with quantitative rates. The
previous audit identified L with the actual physical initial U₀ assuming
an exact kinetic-energy ceiling along one right-zero sequence and a scalar
initial self-pairing limit along that sequence.

Here the exact sampled ceiling is removed. Instead, a PDE-facing initial
kinetic inequality is allowed to carry an integrable signed defect r:

    E₀(t) ≤ E₀(0) + ∫₀ᵗ |r(s)| ds,   0 < t < b.

Because the L¹ primitive vanishes at zero, the ALREADY DERIVED kinetic right
limit satisfies ‖L‖² ≤ E₀(0) = ‖U₀‖². This is sufficient to combine with
one independently supplied initial self-pairing along any right-zero
sequence and identify L = U₀. Both quantitative rates survive unchanged.

The initial kinetic budget and the single sampled self-pairing remain
independent initial-value inputs. The positive-time PDE cannot by itself
select the integration constant at time zero. No terminal regularity
statement or unconditional Navier--Stokes result is claimed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- A kinetic observable with a finite right limit cannot have a limiting
energy surplus over an initial anchor if its only upper error is an
integrable temporal primitive. No exact pointwise or sampled ceiling is
needed; the error need not vanish identically. -/
theorem h3Audit_initialIntegrableKineticBudget_rightLimitUpper
    (E r : ℝ → ℝ) (b C L : ℝ)
    (hb : 0 < b)
    (hR : IntervalIntegrable (fun s : ℝ => |r s|) volume 0 b)
    (hBudget : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      E t ≤ C + ∫ s in (0 : ℝ)..t, |r s|)
    (hLimit : Tendsto E (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    L ≤ C := by
  have hPrimitive :
      Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..t, |r s|)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    h3Audit_initialScalarWeakPrimitive_tendsto_zero
      (fun s : ℝ => |r s|) b hb hR
  have hUpperLimit :
      Tendsto (fun t : ℝ => C + ∫ s in (0 : ℝ)..t, |r s|)
        (𝓝[>] (0 : ℝ)) (𝓝 C) := by
    have h := (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => C) (𝓝[>] (0 : ℝ)) (𝓝 C)).add
      hPrimitive
    simpa only [add_zero] using h
  have hStrict : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with t ht0 htb
    exact ⟨ht0, htb⟩
  have hEventually : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      E t ≤ C + ∫ s in (0 : ℝ)..t, |r s| := by
    filter_upwards [hStrict] with t ht
    exact hBudget t ht
  exact le_of_tendsto_of_tendsto hLimit hUpperLimit hEventually

/-- The integrable kinetic budget gives a one-sided bound on a derived
Hilbert right limit. A self-pairing limit against the known initial datum
along just one sequence then forces equality, by polarization. -/
theorem h3Audit_initialStrongHilbertLimit_eq_of_integrableBudget_selfPairSequence
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (E r : ℝ → ℝ)
    (L U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (b : ℝ) (hb : 0 < b)
    (hR : IntervalIntegrable (fun s : ℝ => |r s|) volume 0 b)
    (hBudget : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      E t ≤ ‖U₀‖ ^ 2 + ∫ s in (0 : ℝ)..t, |r s|)
    (hStrong : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hKinetic : Tendsto E (𝓝[>] (0 : ℝ)) (𝓝 (‖L‖ ^ 2)))
    (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)))
    (hSelfPair : Tendsto
      (fun n : ℕ => inner ℝ (F (τ n)) U₀)
      atTop (𝓝 (‖U₀‖ ^ 2))) :
    L = U₀ := by
  have hKineticBound : ‖L‖ ^ 2 ≤ ‖U₀‖ ^ 2 :=
    h3Audit_initialIntegrableKineticBudget_rightLimitUpper
      E r b (‖U₀‖ ^ 2) (‖L‖ ^ 2) hb hR hBudget hKinetic
  have hStrongSeq : Tendsto (fun n : ℕ => F (τ n))
      atTop (𝓝 L) := by
    simpa only [Function.comp_def] using hStrong.comp hτ
  have hInnerContinuous :
      Continuous (fun V : H3PhysicalRealFinVectorL2Hilbert =>
        inner ℝ V U₀) :=
    continuous_id.inner continuous_const
  have hSelfLimit :
      Tendsto (fun n : ℕ => inner ℝ (F (τ n)) U₀)
        atTop (𝓝 (inner ℝ L U₀)) :=
    hInnerContinuous.continuousAt.tendsto.comp hStrongSeq
  have hSelfEquality : inner ℝ L U₀ = ‖U₀‖ ^ 2 :=
    tendsto_nhds_unique hSelfLimit hSelfPair
  exact h3Audit_initialHilbert_identify_of_kineticCeiling_and_selfPairing
    L U₀ hKineticBound hSelfEquality.ge

/-- Initial kinetic budget with an L¹ defect, plus ONE weak self-correlation
sequence against the actual physical time-zero velocity. Neither a precise
sampled kinetic ceiling nor a full-Hilbert weak trace is assumed. -/
def H3AuditInitialIntegrableKineticBudgetSelfPairingTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (b : ℝ) : Prop :=
  ∃ (r : ℝ → ℝ),
    IntervalIntegrable (fun s : ℝ => |r s|) volume 0 b ∧
    (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      velocityH3Energy0At u t ≤
        velocityH3Energy0At u 0 +
          ∫ s in (0 : ℝ)..t, |r s|) ∧
    ∃ τ : ℕ → ℝ,
      Tendsto τ atTop (𝓝[>] (0 : ℝ)) ∧
      Tendsto
        (fun n : ℕ =>
          inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 (τ n))
            (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0))
        atTop
        (𝓝 (‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2))

/-- The actual old physical kinetic budget with integrable defect and one
initial-data self-correlation sequence identify the initial momentum and
kinetic limits and preserve both explicit subcritical initial rates. -/
theorem h3Audit_initialSubcriticalIntegrableBudgetSelfPairing_identifies_physicalAndKineticRate
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
    (hInitial : H3AuditInitialIntegrableKineticBudgetSelfPairingTrace
      hH3 hInt0 hMeas0 b) :
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
  let F : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let U₀ : H3PhysicalRealFinVectorL2Hilbert :=
    h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0
  obtain ⟨r, hR, hBudget, τ, hτ, hSelfPair⟩ := hInitial
  obtain ⟨L, hL, hKinetic, _hModulus⟩ :=
    h3Audit_initialSubcriticalEnergyRate_kinetic_rightLimitRate
      hH3 hOldJoint b α M hb hbT hα0 hα1 hM hRate
  have hZero : ‖U₀‖ ^ 2 = velocityH3Energy0At u 0 :=
    h3Audit_initialActualPhysicalHilbertAtZero_norm_sq_eq_kineticEnergy
      hInt0 hMeas0
  have hBudget' : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
      velocityH3Energy0At u t ≤
        ‖U₀‖ ^ 2 + ∫ s in (0 : ℝ)..t, |r s| := by
    simpa only [hZero] using hBudget
  have hIdentify : L = U₀ :=
    h3Audit_initialStrongHilbertLimit_eq_of_integrableBudget_selfPairSequence
      F (velocityH3Energy0At u) r L U₀ b hb hR hBudget'
      hL hKinetic τ hτ hSelfPair
  have hStrong : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 U₀) := by
    simpa only [hIdentify] using hL
  have hWeak : ∀ ψ : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto
        (fun t : ℝ => inner ℝ (F t) ψ)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ U₀ ψ)) := by
    intro ψ
    have hInnerContinuous :
        Continuous (fun z : H3PhysicalRealFinVectorL2Hilbert =>
          inner ℝ z ψ) :=
      continuous_id.inner continuous_const
    exact hInnerContinuous.continuousAt.tendsto.comp hStrong
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
