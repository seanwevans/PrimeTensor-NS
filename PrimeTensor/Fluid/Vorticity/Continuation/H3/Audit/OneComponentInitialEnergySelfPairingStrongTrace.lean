import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialIntegrableBudgetExactKineticCeiling

/-!
# Strong initial physical trace from the energy ceiling and ONE self-pairing

The preceding theorem upgrades an initial-anchored L¹ kinetic energy budget
to E₀(t) ≤ E₀(0) on the entire positive-time path, with no subcritical
H³ growth or strong positive-time Bochner derivative hypotheses.

Here a quantitative real Hilbert polarization inequality shows:

  ‖F(t)-U₀‖² ≤ 2 (‖U₀‖² - ⟪F(t),U₀⟫).

Thus a single one-vector self-pairing right trace gives STRONG physical
L² right continuity and right kinetic energy continuity directly; no
previously constructed strong right limit L is needed. We also retain a
finite-time squared-defect estimate for any correlation modulus, and
obtain a strong trace ALONG ONE SEQUENCE when only a sampled self-pairing
is available.

The anchored initial kinetic budget and fixed initial self-pairing remain
two genuinely independent initial-value obligations. Open-time H³ path
admissibility alone does not guarantee them, and no endpoint H³
regularity or unconditional Navier--Stokes result is claimed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- Quantitative Hilbert-space initial jump bound from a kinetic ceiling
and one lower scalar pairing against the prescribed initial vector. -/
theorem h3Audit_initialEnergySelfPairing_squaredDefect_le
    (x U₀ : H3PhysicalRealFinVectorL2Hilbert) (c : ℝ)
    (hEnergy : ‖x‖ ^ 2 ≤ ‖U₀‖ ^ 2)
    (hCross : ‖U₀‖ ^ 2 ≤ inner ℝ x U₀ + c) :
    ‖x - U₀‖ ^ 2 ≤ 2 * c := by
  have h := h3Audit_initialHilbert_energyCorrelation_defectBudget
    x U₀ 0 c (by simpa only [add_zero] using hEnergy) hCross
  simpa only [zero_add] using h

/-- Radon--Riesz in the special one-test form: the kinetic ceiling
and convergence of the ONE pairing against the initial vector imply
strong convergence, for any source filter. No weak test family, source
integrability, preconstructed strong limit or derivative premise. -/
theorem h3Audit_initialHilbert_strong_of_energyCeiling_selfPairing
    {ι : Type*} (l : Filter ι)
    (F : ι → H3PhysicalRealFinVectorL2Hilbert)
    (U₀ : H3PhysicalRealFinVectorL2Hilbert)
    (hEnergy : ∀ᶠ t in l, ‖F t‖ ^ 2 ≤ ‖U₀‖ ^ 2)
    (hPair : Tendsto (fun t => inner ℝ (F t) U₀) l
      (𝓝 (‖U₀‖ ^ 2))) :
    Tendsto F l (𝓝 U₀) := by
  have hGap :
      Tendsto (fun t => 2 * (‖U₀‖ ^ 2 - inner ℝ (F t) U₀))
        l (𝓝 (0 : ℝ)) := by
    have hConstant : Tendsto
        (fun _ : ι => ‖U₀‖ ^ 2) l (𝓝 (‖U₀‖ ^ 2)) :=
      tendsto_const_nhds
    have h := (hConstant.sub hPair).const_mul 2
    simpa only [sub_self, mul_zero] using h
  have hSquare :
      Tendsto (fun t => ‖F t - U₀‖ ^ 2) l (𝓝 (0 : ℝ)) := by
    apply squeeze_zero'
      (Eventually.of_forall (fun t => sq_nonneg (‖F t - U₀‖)))
      ?_ hGap
    filter_upwards [hEnergy] with t ht
    have hCross :
        ‖U₀‖ ^ 2 ≤ inner ℝ (F t) U₀ +
          (‖U₀‖ ^ 2 - inner ℝ (F t) U₀) := by
      exact le_of_eq (by ring)
    exact h3Audit_initialEnergySelfPairing_squaredDefect_le
      (F t) U₀ (‖U₀‖ ^ 2 - inner ℝ (F t) U₀) ht hCross
  have hSqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hSquare
  have hNorm :
      Tendsto (fun t => ‖F t - U₀‖) l (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
      abs_norm, Real.sqrt_zero] using hSqrt
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hNorm

/-- A concrete finite-time physical jump bound that depends ONLY on the
initial L¹ kinetic budget and an approximate initial-vector correlation.
Neither a subcritical H³ majorant nor time-derivative joint continuity
is assumed. -/
theorem h3Audit_initialBudget_selfPairing_physicalSquaredDefect
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (r : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hR : IntervalIntegrable (fun s : ℝ => |r s|) volume 0 b)
    (hBudget : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b →
      velocityH3Energy0At u s ≤
        velocityH3Energy0At u 0 +
          ∫ x in (0 : ℝ)..s, |r x|)
    (c : ℝ → ℝ)
    (hCross : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      ‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2 ≤
        inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
          (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0) + c t) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
        h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2
      ≤ 2 * c t := by
  have hCeiling :=
    h3Audit_initialIntegrableBudget_exactPositiveKineticCeiling
      hH3 r b hb hR hBudget
  have hInitialEnergy :
      ‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2 =
        velocityH3Energy0At u 0 :=
    h3Audit_initialActualPhysicalHilbertAtZero_norm_sq_eq_kineticEnergy
      hInt0 hMeas0
  intro t ht
  have hOldEnergy :
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2 =
        velocityH3Energy0At u t :=
    h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
      hH3 t ht
  apply h3Audit_initialEnergySelfPairing_squaredDefect_le
    (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
    (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
    (c t) ?_ (hCross t ht)
  rw [hOldEnergy, hInitialEnergy]
  exact hCeiling t ht

/-- An initial-anchored L¹ kinetic budget and convergence of ONE
self-correlation on the full initial right filter imply the actual
physical strong L² right trace AND kinetic energy right continuity.
Notably NO subcritical H³ rate and NO temporal joint-continuity premise
is needed, unlike the earlier quantitative source-based route. -/
theorem h3Audit_initialBudget_selfPairing_implies_physicalAndKineticRightTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ))
    (r : ℝ → ℝ) (b : ℝ) (hb : 0 < b) (hbT : b < T)
    (hR : IntervalIntegrable (fun s : ℝ => |r s|) volume 0 b)
    (hBudget : ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) b →
      velocityH3Energy0At u s ≤
        velocityH3Energy0At u 0 +
          ∫ x in (0 : ℝ)..s, |r x|)
    (hPair : Tendsto
      (fun t : ℝ =>
        inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
          (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0))
      (𝓝[>] (0 : ℝ))
      (𝓝 (‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2))) :
    Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (𝓝[>] (0 : ℝ))
      (𝓝 (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)) ∧
    Tendsto (velocityH3Energy0At u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (velocityH3Energy0At u 0)) := by
  let F : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let U₀ : H3PhysicalRealFinVectorL2Hilbert :=
    h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0
  have hCeiling :=
    h3Audit_initialIntegrableBudget_exactPositiveKineticCeiling
      hH3 r b hb hR hBudget
  have hZero : ‖U₀‖ ^ 2 = velocityH3Energy0At u 0 :=
    h3Audit_initialActualPhysicalHilbertAtZero_norm_sq_eq_kineticEnergy
      hInt0 hMeas0
  have hT : 0 < T := lt_trans hb hbT
  have hNear : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      t ∈ Set.Ioo (0 : ℝ) T := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hT)] with t ht0 htT
    exact ⟨ht0, htT⟩
  have hNormCeiling : ∀ᶠ t : ℝ in (𝓝[>] (0 : ℝ)),
      ‖F t‖ ^ 2 ≤ ‖U₀‖ ^ 2 := by
    filter_upwards [hNear] with t ht
    calc
      ‖F t‖ ^ 2 = velocityH3Energy0At u t :=
        h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
          hH3 t ht
      _ ≤ velocityH3Energy0At u 0 := hCeiling t ht
      _ = ‖U₀‖ ^ 2 := hZero.symm
  have hStrong : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 U₀) :=
    h3Audit_initialHilbert_strong_of_energyCeiling_selfPairing
      (𝓝[>] (0 : ℝ)) F U₀ hNormCeiling hPair
  have hSquared : Tendsto
      (fun t : ℝ => ‖F t‖ ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (‖U₀‖ ^ 2)) := by
    have hNorm := (continuous_norm.tendsto U₀).comp hStrong
    simpa only [Function.comp_def] using hNorm.pow 2
  have hEq : (velocityH3Energy0At u) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ‖F t‖ ^ 2) := by
    filter_upwards [hNear] with t ht
    exact (h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
      hH3 t ht).symm
  have hKinetic : Tendsto (velocityH3Energy0At u)
      (𝓝[>] (0 : ℝ)) (𝓝 (velocityH3Energy0At u 0)) := by
    rw [← hZero]
    exact hSquared.congr' hEq.symm
  exact ⟨hStrong, hKinetic⟩

end
end Euclidean
end Bridge
end PrimeTensor
