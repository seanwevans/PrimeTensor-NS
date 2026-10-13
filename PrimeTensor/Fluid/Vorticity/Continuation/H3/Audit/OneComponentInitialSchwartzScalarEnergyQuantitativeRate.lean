import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialSchwartzScalarFTCStrongTrace

/-!
# Quantitative finite-time initial physical momentum error from scalar FTC

The previous theorem derives a strong initial L² trace from Schwartz-test
initial momentum evolution and an independently anchored L¹ kinetic budget.
Its convergence result does not expose an explicit finite-time bound in terms
of the two separate initial temporal defects and spatial test approximation.

Here, at an individual positive time, an approximate kinetic inequality
with energy error e, a bound B on the old physical L² norm, and one spatial
probe ψ give

  ‖V-U₀‖² ≤ e + 2 (|⟪V,ψ⟫-⟪U₀,ψ⟫| + (B+‖U₀‖)‖U₀-ψ‖).

The already-proved initial L¹ kinetic budget provides e as a temporal
primitive and B as a single finite upper norm bound. Test-dependent
Schwartz scalar FTC provides the actual scalar primitive. Thus an explicit
pointwise physical squared-error estimate follows WITHOUT first invoking
positive-time kinetic antitonicity, the dense-weak right-limit theorem,
or a subcritical H³ rate. A sharper corollary invokes kinetic antitonicity
when the latter is available.

No quantitative spatial approximation rate or uniform temporal Schwartz
source modulus is derived here. The anchored kinetic budget and scalar
initial-value equations remain independent PDE-facing obligations.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- A pointwise Hilbert-space error estimate using an *approximate*
kinetic ceiling, an independent norm ceiling, and ONE arbitrary probe.
Unlike the exact-ceiling version, this does not use kinetic monotonicity. -/
theorem h3Audit_initialHilbert_approxProbeSquaredDefect_of_energyError
    (V U ψ : H3PhysicalRealFinVectorL2Hilbert)
    (e B : ℝ)
    (hEnergy : ‖V‖ ^ 2 ≤ ‖U‖ ^ 2 + e)
    (hNormBound : ‖V‖ ≤ B) :
    ‖V - U‖ ^ 2 ≤ e +
      2 * (|inner ℝ V ψ - inner ℝ U ψ| +
        (B + ‖U‖) * ‖U - ψ‖) := by
  have hDiffBound : ‖V - U‖ ≤ B + ‖U‖ :=
    (norm_sub_le V U).trans (add_le_add hNormBound (le_refl ‖U‖))
  have hError : ‖V - U‖ * ‖U - ψ‖ ≤
      (B + ‖U‖) * ‖U - ψ‖ :=
    mul_le_mul_of_nonneg_right hDiffBound (norm_nonneg _)
  have hPairError :
      ‖U‖ ^ 2 - inner ℝ V U ≤
        |inner ℝ V ψ - inner ℝ U ψ| +
          (B + ‖U‖) * ‖U - ψ‖ := by
    have hIdentity :
        ‖U‖ ^ 2 - inner ℝ V U =
          -(inner ℝ (V - U) ψ) -
            inner ℝ (V - U) (U - ψ) := by
      calc
        ‖U‖ ^ 2 - inner ℝ V U =
            -(inner ℝ (V - U) U) := by
          rw [inner_sub_left, real_inner_self_eq_norm_sq]
          ring
        _ = -(inner ℝ (V - U) ψ) -
              inner ℝ (V - U) (U - ψ) := by
          rw [inner_sub_right]
          ring
    calc
      ‖U‖ ^ 2 - inner ℝ V U =
          -(inner ℝ (V - U) ψ) -
            inner ℝ (V - U) (U - ψ) := hIdentity
      _ ≤ |inner ℝ (V - U) ψ| +
          ‖V - U‖ * ‖U - ψ‖ := by
        exact add_le_add (neg_le_abs _)
          ((neg_le_abs _).trans (abs_real_inner_le_norm _ _))
      _ ≤ |inner ℝ V ψ - inner ℝ U ψ| +
          (B + ‖U‖) * ‖U - ψ‖ := by
        rw [inner_sub_left]
        exact add_le_add (le_refl _) hError
  have hCross : ‖U‖ ^ 2 ≤ inner ℝ V U +
      (|inner ℝ V ψ - inner ℝ U ψ| +
        (B + ‖U‖) * ‖U - ψ‖) := by
    linarith only [hPairError]
  exact h3Audit_initialHilbert_energyCorrelation_defectBudget
    V U e _ hEnergy hCross

/-- A pointwise quantitative initial physical L² estimate: the source
is an individual test-dependent scalar L¹ function `g`, the kinetic
defect is the separate L¹ function `r`, and the test-approximation term
vanishes as Schwartz probes approach the actual physical initial datum.
The proof deliberately uses only the initial integrated kinetic budget,
not kinetic monotonicity or an already established initial strong trace. -/
theorem h3Audit_initialSchwartzScalarFTC_quantitativePhysicalSquaredError
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
    (hFTC : H3AuditInitialSchwartzAnchoredScalarFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
      b)
    (Φ : H3PhysicalRealFinVectorSchwartz) :
    ∃ g : ℝ → ℝ,
      IntervalIntegrable g volume 0 b ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2 ≤
          (∫ s in (0 : ℝ)..t, |r s|) +
            2 * (|∫ s in (0 : ℝ)..t, g s| +
              (Real.sqrt (velocityH3Energy0At u 0 +
                  ∫ s in (0 : ℝ)..b, |r s|) +
                ‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖) *
                  ‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0 -
                    h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ‖) := by
  let U₀ : H3PhysicalRealFinVectorL2Hilbert :=
    h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0
  let F : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3
  let ψ : H3PhysicalRealFinVectorL2Hilbert :=
    h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ
  let B : ℝ := Real.sqrt (velocityH3Energy0At u 0 +
    ∫ s in (0 : ℝ)..b, |r s|)
  obtain ⟨g, hg, hScalar⟩ := hFTC Φ
  refine ⟨g, hg, ?_⟩
  have hNorm : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b → ‖F t‖ ≤ B :=
    h3Audit_initialOldPhysicalHilbert_norm_le_of_integratedKineticBudget
      hH3 r b hbT.le hR hBudget
  have hInitialIdentity : ‖U₀‖ ^ 2 = velocityH3Energy0At u 0 :=
    h3Audit_initialActualPhysicalHilbertAtZero_norm_sq_eq_kineticEnergy
      hInt0 hMeas0
  intro t ht
  have htT : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨ht.1, lt_trans ht.2 hbT⟩
  have hOldIdentity : ‖F t‖ ^ 2 = velocityH3Energy0At u t :=
    h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy
      hH3 t htT
  have hEnergy : ‖F t‖ ^ 2 ≤
      ‖U₀‖ ^ 2 + ∫ s in (0 : ℝ)..t, |r s| := by
    rw [hOldIdentity, hInitialIdentity]
    exact hBudget t ht
  have hPair :
      |inner ℝ (F t) ψ - inner ℝ U₀ ψ| =
        |∫ s in (0 : ℝ)..t, g s| :=
    congrArg abs (hScalar t ht)
  have hBound :=
    h3Audit_initialHilbert_approxProbeSquaredDefect_of_energyError
      (F t) U₀ ψ
      (∫ s in (0 : ℝ)..t, |r s|) B hEnergy (hNorm t ht)
  simpa only [F, U₀, ψ, B, hPair] using hBound

/-- Under the exact positive kinetic ceiling, the same scalar Schwartz
FTC gives a sharper finite-time estimate without the kinetic source
primitive or the global initial norm ceiling. -/
theorem h3Audit_initialSchwartzScalarFTC_quantitativePhysicalSquaredError_exactCeiling
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
    (hFTC : H3AuditInitialSchwartzAnchoredScalarFTCOn
      (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
      b)
    (Φ : H3PhysicalRealFinVectorSchwartz) :
    ∃ g : ℝ → ℝ,
      IntervalIntegrable g volume 0 b ∧
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) b →
        ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2 ≤
          2 * (|∫ s in (0 : ℝ)..t, g s| +
            2 * ‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ *
              ‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0 -
                h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ‖) := by
  obtain ⟨g, hg, hScalar⟩ := hFTC Φ
  refine ⟨g, hg, ?_⟩
  have hCeiling :=
    h3Audit_initialIntegrableBudget_exactPositiveKineticCeiling
      hH3 r b hb hR hBudget
  have hInitialIdentity :
      ‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2 =
        velocityH3Energy0At u 0 :=
    h3Audit_initialActualPhysicalHilbertAtZero_norm_sq_eq_kineticEnergy
      hInt0 hMeas0
  intro t ht
  have htT : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨ht.1, lt_trans ht.2 hbT⟩
  have hEnergy :
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2 ≤
        ‖h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0‖ ^ 2 := by
    rw [h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy hH3 t htT,
      hInitialIdentity]
    exact hCeiling t htT
  have hBound :=
    h3Audit_initialHilbert_approxProbeSquaredDefect_le
      (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
      (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
      (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) hEnergy
  have hPair :
      |inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
        (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ) -
        inner ℝ (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)| =
        |∫ s in (0 : ℝ)..t, g s| :=
    congrArg abs (hScalar t ht)
  simpa only [hPair] using hBound

end
end Euclidean
end Bridge
end PrimeTensor
