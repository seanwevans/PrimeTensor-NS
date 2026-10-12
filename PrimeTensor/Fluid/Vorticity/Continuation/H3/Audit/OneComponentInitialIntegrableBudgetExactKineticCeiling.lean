import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialIntegrableBudgetSelfPairing
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialCofinalKineticAnchorsRelativeEnergy

/-!
# Upgrade an integrable initial kinetic budget to an exact kinetic ceiling

At strictly positive times, the physical order-zero Navier--Stokes energy
is antitone on the entire preterminal H³ path. The previous initial trace
criterion assumes a kinetic budget

  E₀(t) ≤ E₀(0) + ∫₀ᵗ |r(s)| ds,   r ∈ L¹(0,b).

Integrability makes the primitive vanish as t → 0+. Thus, for any later
positive time t and any positive ε, there is an earlier positive s < t
with E₀(s) ≤ E₀(0) + ε. The already-proved positive-time kinetic
antitonicity eliminates ε and yields the EXACT bound

  E₀(t) ≤ E₀(0),   0 < t < T.

Unlike the previous right-limit upper theorem, this conclusion does not
use the subcritical H³ rate, joint temporal continuity, or an initially
known finite kinetic right limit. It still REQUIRES the initial budget
anchored to the actual time-zero physical datum: positive-time PDE
identities alone do not furnish that initial-value boundary condition.

An additional polarization inequality quantifies the one-sided
initial self-correlation deficit if the independently derived strong
right limit differs from the prescribed datum.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- A one-sided initial kinetic budget with an integrable temporal
defect produces arbitrarily early approximate energy anchors below any
positive later time, independently of any kinetic right-limit theorem. -/
theorem h3Audit_initialIntegrableBudget_cofinalApproximateAnchors
    (E r : ℝ → ℝ) (b C : ℝ)
    (hb : 0 < b)
    (hR : IntervalIntegrable (fun s : ℝ => |r s|) volume 0 b)
    (hBudget : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b →
      E s ≤ C + ∫ x in (0 : ℝ)..s, |r x|)
    (t : ℝ) (ht : 0 < t) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) t ∧ E s ≤ C + ε := by
  have hPrimitive :
      Tendsto (fun s : ℝ => ∫ x in (0 : ℝ)..s, |r x|)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    h3Audit_initialScalarWeakPrimitive_tendsto_zero
      (fun s : ℝ => |r s|) b hb hR
  have hSmall :
      ∀ᶠ s : ℝ in (𝓝[>] (0 : ℝ)),
        (∫ x in (0 : ℝ)..s, |r x|) < ε :=
    hPrimitive.eventually (Iio_mem_nhds hε)
  have hNearT :
      ∀ᶠ s : ℝ in (𝓝[>] (0 : ℝ)),
        s ∈ Set.Ioo (0 : ℝ) t := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds ht)] with s hs0 hst
    exact ⟨hs0, hst⟩
  have hNearB :
      ∀ᶠ s : ℝ in (𝓝[>] (0 : ℝ)),
        s ∈ Set.Ioo (0 : ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hb)] with s hs0 hsb
    exact ⟨hs0, hsb⟩
  obtain ⟨s, ⟨hsT, hsB⟩, hsSmall⟩ :=
    ((hNearT.and hNearB).and hSmall).exists
  refine ⟨s, hsT, ?_⟩
  linarith only [hBudget s hsB, hsSmall]

/-- Every positive-time kinetic energy is at most the ACTUAL kinetic
energy at time zero. The initial L¹ budget supplies cofinal approximate
anchors, while the previously proved H³-path kinetic antitonicity
removes the error and extends the result to all of (0,T). -/
theorem h3Audit_initialIntegrableBudget_exactPositiveKineticCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (r : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hR : IntervalIntegrable (fun s : ℝ => |r s|) volume 0 b)
    (hBudget : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b →
      velocityH3Energy0At u s ≤
        velocityH3Energy0At u 0 +
          ∫ x in (0 : ℝ)..s, |r x|) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      velocityH3Energy0At u t ≤ velocityH3Energy0At u 0 := by
  apply h3Audit_initialKineticEnergy_le_initial_of_cofinalApproximateAnchors hH3
  intro t ht ε hε
  exact h3Audit_initialIntegrableBudget_cofinalApproximateAnchors
    (velocityH3Energy0At u) r b (velocityH3Energy0At u 0)
    hb hR hBudget t ht.1 ε hε

/-- The same integrable initial kinetic budget bounds the norm of
the *actual old physical* Hilbert velocity on the full positive
preterminal interval, without a subcritical H³ envelope. -/
theorem h3Audit_initialIntegrableBudget_globalPhysicalNormCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (r : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hR : IntervalIntegrable (fun s : ℝ => |r s|) volume 0 b)
    (hBudget : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b →
      velocityH3Energy0At u s ≤
        velocityH3Energy0At u 0 +
          ∫ x in (0 : ℝ)..s, |r x|) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ≤
        Real.sqrt (velocityH3Energy0At u 0) := by
  exact h3Audit_initialOldPhysicalHilbert_norm_le_of_kineticCeiling
    hH3 T (velocityH3Energy0At u 0) (le_refl T)
    (h3Audit_initialIntegrableBudget_exactPositiveKineticCeiling
      hH3 r b hb hR hBudget)

/-- Once the strong right limit cannot carry more kinetic energy
than the prescribed datum, its initial-vector self-correlation must
lose at least HALF the squared L² jump. This makes any remaining
nonzero initial mismatch quantitatively visible. -/
theorem h3Audit_initialHilbert_selfPairDeficit_of_kineticCeiling
    (L U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (hKinetic : ‖L‖ ^ 2 ≤ ‖U₀‖ ^ 2) :
    inner ℝ L U₀ + ‖L - U₀‖ ^ 2 / 2 ≤ ‖U₀‖ ^ 2 := by
  have hExpand :
      ‖L - U₀‖ ^ 2 =
        ‖L‖ ^ 2 - 2 * inner ℝ L U₀ + ‖U₀‖ ^ 2 :=
    norm_sub_sq_real L U₀
  linarith only [hExpand, hKinetic]

/-- A derived subcritical physical L² right limit, coupled to an
initial L¹ kinetic budget, obeys an explicit one-vector correlation
deficit at the ACTUAL physical time-zero velocity.

If the initial mismatch is nonzero, the right-limit correlation must
fall strictly below the prescribed initial norm square. No sampled
self-pairing convergence is assumed in this obstruction theorem. -/
theorem h3Audit_initialSubcriticalBudget_physicalSelfPairDeficit
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
    (r : ℝ → ℝ)
    (hR : IntervalIntegrable (fun s : ℝ => |r s|) volume 0 b)
    (hBudget : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b →
      velocityH3Energy0At u s ≤
        velocityH3Energy0At u 0 +
          ∫ x in (0 : ℝ)..s, |r x|) :
    ∃ L : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      Tendsto
        (fun t : ℝ =>
          inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
            (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0))
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ L
          (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0))) ∧
      inner ℝ L (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0) +
        ‖L - h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2 / 2 ≤
        ‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2 := by
  let U₀ : H3PhysicalRealFinVectorL2Hilbert :=
    h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0
  obtain ⟨L, hL, hKinetic, _hModulus⟩ :=
    h3Audit_initialSubcriticalEnergyRate_kinetic_rightLimitRate
      hH3 hOldJoint b α M hb hbT hα0 hα1 hM hRate
  have hInitialIdentity : ‖U₀‖ ^ 2 = velocityH3Energy0At u 0 :=
    h3Audit_initialActualPhysicalHilbertAtZero_norm_sq_eq_kineticEnergy
      hInt0 hMeas0
  have hKineticBound : ‖L‖ ^ 2 ≤ ‖U₀‖ ^ 2 := by
    have hBound :=
      h3Audit_initialIntegrableKineticBudget_rightLimitUpper
        (velocityH3Energy0At u) r b (velocityH3Energy0At u 0)
        (‖L‖ ^ 2) hb hR hBudget hKinetic
    simpa only [← hInitialIdentity] using hBound
  have hPairContinuous :
      Continuous (fun z : H3PhysicalRealFinVectorL2Hilbert =>
        inner ℝ z U₀) :=
    continuous_id.inner continuous_const
  refine ⟨L, hL, ?_, ?_⟩
  · exact hPairContinuous.continuousAt.tendsto.comp hL
  · exact h3Audit_initialHilbert_selfPairDeficit_of_kineticCeiling
      L U₀ hKineticBound

end
end Euclidean
end Bridge
end PrimeTensor
