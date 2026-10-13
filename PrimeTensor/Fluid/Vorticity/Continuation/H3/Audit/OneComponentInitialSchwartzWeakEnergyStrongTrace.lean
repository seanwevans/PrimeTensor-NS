import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialEnergySelfPairingStrongTrace
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialSchwartzDualL1KineticControl

/-!
# Dense Schwartz weak initial data + kinetic ceiling give strong L² trace

At the previous checkpoint, the energy inequality plus convergence of
the single self-pairing ⟪old(t),u(0)⟫ yielded strong physical initial L²
continuity without subcritical H³ rate assumptions.

Here the self-pairing premise is replaced by the natural initial-value
distributional weak trace against physical Schwartz vector tests. The
Schwartz range is dense in the exact real three-component physical L²
carrier. A uniform kinetic ceiling makes all scalar pairings
equi-Lipschitz in the probe and permits approximation of the fixed
initial datum by Schwartz tests.

The resulting norm-square bound and an epsilon/Schwartz approximation
argument give strong L² convergence, which also recovers kinetic right
continuity. No positive-time L² strong limit is postulated or used.

IMPORTANT: the Schwartz initial weak trace and initial-anchored L¹
kinetic budget are still independent initial-value inputs. Open-time
Navier--Stokes H³ admissibility alone does not imply either.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal Interval InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

/-- Under an exact kinetic ceiling, one approximate spatial probe
controls the entire squared initial physical velocity jump. The
approximation error is twice the initial norm times the probe error. -/
theorem h3Audit_initialHilbert_approxProbeSquaredDefect_le
    (V U ψ : H3PhysicalRealFinVectorL2Hilbert)
    (hEnergy : ‖V‖ ^ 2 ≤ ‖U‖ ^ 2) :
    ‖V - U‖ ^ 2 ≤
      2 * (|inner ℝ V ψ - inner ℝ U ψ| +
        2 * ‖U‖ * ‖U - ψ‖) := by
  have hNormBound : ‖V‖ ≤ ‖U‖ := by
    nlinarith only [hEnergy, norm_nonneg V, norm_nonneg U]
  have hDiffBound : ‖V - U‖ ≤ 2 * ‖U‖ := by
    have h := norm_sub_le V U
    linarith only [h, hNormBound]
  have hError : ‖V - U‖ * ‖U - ψ‖ ≤
      (2 * ‖U‖) * ‖U - ψ‖ :=
    mul_le_mul_of_nonneg_right hDiffBound (norm_nonneg _)
  have hPairError :
      ‖U‖ ^ 2 - inner ℝ V U ≤
        |inner ℝ V ψ - inner ℝ U ψ| +
        2 * ‖U‖ * ‖U - ψ‖ := by
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
          2 * ‖U‖ * ‖U - ψ‖ := by
        rw [inner_sub_left]
        exact add_le_add (le_refl _) hError
  have hCross : ‖U‖ ^ 2 ≤
      inner ℝ V U +
        (|inner ℝ V ψ - inner ℝ U ψ| +
          2 * ‖U‖ * ‖U - ψ‖) := by
    linarith only [hPairError]
  exact h3Audit_initialEnergySelfPairing_squaredDefect_le
    V U _ hEnergy hCross

/-- Real Hilbert strong convergence from weak pairing convergence
on a dense range and an eventually exact kinetic ceiling.
This proof uses no existence or uniqueness theorem for a strong
initial right limit and requires no vector-valued temporal source. -/
theorem h3Audit_initialHilbert_strong_of_denseWeak_energyCeiling
    {ι J : Type*} (l : Filter ι)
    (D : J → H3PhysicalRealFinVectorL2Hilbert)
    (hDense : DenseRange D)
    (F : ι → H3PhysicalRealFinVectorL2Hilbert)
    (U : H3PhysicalRealFinVectorL2Hilbert)
    (hEnergy : ∀ᶠ t in l, ‖F t‖ ^ 2 ≤ ‖U‖ ^ 2)
    (hWeak : ∀ j : J,
      Tendsto (fun t => inner ℝ (F t) (D j)) l
        (𝓝 (inner ℝ U (D j)))) :
    Tendsto F l (𝓝 U) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η : ℝ := ε ^ 2 / (16 * (‖U‖ + 1))
  have hUPos : 0 < ‖U‖ + 1 := by positivity
  have hη : 0 < η := by
    dsimp only [η]
    positivity
  obtain ⟨j, hj⟩ := hDense.exists_dist_lt U hη
  let ψ : H3PhysicalRealFinVectorL2Hilbert := D j
  have hApprox : ‖U - ψ‖ < η := by
    simpa only [ψ, dist_eq_norm] using hj
  have hScalar : Tendsto
      (fun t => |inner ℝ (F t) ψ - inner ℝ U ψ|)
      l (𝓝 (0 : ℝ)) := by
    have h := ((hWeak j).sub
      (tendsto_const_nhds :
        Tendsto (fun _ : ι => inner ℝ U (D j))
          l (𝓝 (inner ℝ U (D j))))).abs
    simpa only [ψ, sub_self, abs_zero] using h
  have hSmall : ∀ᶠ t in l,
      |inner ℝ (F t) ψ - inner ℝ U ψ| < ε ^ 2 / 8 :=
    hScalar.eventually (Iio_mem_nhds (by positivity))
  have hNormNonneg : 0 ≤ ‖U‖ := norm_nonneg U
  have hTerm :
      4 * ‖U‖ * ‖U - ψ‖ < ε ^ 2 / 4 := by
    have hA : 4 * ‖U‖ * ‖U - ψ‖ ≤
        4 * (‖U‖ + 1) * ‖U - ψ‖ := by
      have hh := mul_le_mul_of_nonneg_right
        (show 4 * ‖U‖ ≤ 4 * (‖U‖ + 1) by linarith)
        (norm_nonneg (U - ψ))
      simpa only [mul_assoc] using hh
    have hB : 4 * (‖U‖ + 1) * ‖U - ψ‖ <
        4 * (‖U‖ + 1) * η := by
      exact mul_lt_mul_of_pos_left hApprox (by positivity)
    have hC : 4 * (‖U‖ + 1) * η = ε ^ 2 / 4 := by
      dsimp only [η]
      field_simp [ne_of_gt hUPos]
      <;> ring
    exact lt_of_le_of_lt hA (hB.trans_eq hC)
  filter_upwards [hEnergy, hSmall] with t ht htSmall
  change dist (F t) U < ε
  rw [dist_eq_norm]
  have hSquared :=
    h3Audit_initialHilbert_approxProbeSquaredDefect_le
      (F t) U ψ ht
  have hBound : ‖F t - U‖ ^ 2 < ε ^ 2 := by
    calc
      ‖F t - U‖ ^ 2 ≤
          2 * (|inner ℝ (F t) ψ - inner ℝ U ψ| +
            2 * ‖U‖ * ‖U - ψ‖) := hSquared
      _ = 2 * |inner ℝ (F t) ψ - inner ℝ U ψ| +
          4 * ‖U‖ * ‖U - ψ‖ := by ring
      _ < ε ^ 2 := by
        have hSqPos : 0 < ε ^ 2 := by positivity
        linarith only [htSmall, hTerm, hSqPos]
  nlinarith only [hBound, hε, norm_nonneg (F t - U)]

/-- Initial distributional weak trace of the actual old velocity
against all physical Schwartz vector tests. Unlike an initial Hilbert
strong trace, this is a PDE-facing weak initial datum condition. -/
def H3AuditInitialSchwartzRightWeakTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hInt0 : VelocityH3IntegrableAt u (0 : ℝ))
    (hMeas0 : VelocityH3MeasurableAt u (0 : ℝ)) : Prop :=
  ∀ Φ : H3PhysicalRealFinVectorSchwartz,
    Tendsto
      (fun t : ℝ =>
        inner ℝ (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
          (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (inner ℝ
        (h3Audit_initialActualPhysicalHilbertAtZero hInt0 hMeas0)
        (h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert Φ)))

/-- Exact positive-time kinetic inequality from a separately supplied
initial L¹ energy budget, plus only Schwartz-test distributional weak
initial data, produces the actual physical strong L² right trace and
kinetic-energy right continuity. No subcritical H³ growth or temporal
derivative joint continuity is required. -/
theorem h3Audit_initialBudget_SchwartzWeak_implies_physicalAndKineticRightTrace
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
    (hWeak : H3AuditInitialSchwartzRightWeakTrace
      hH3 hInt0 hMeas0) :
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
    h3Audit_initialHilbert_strong_of_denseWeak_energyCeiling
      (𝓝[>] (0 : ℝ))
      h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert
      denseRange_h3PhysicalRealFinVectorSchwartzPhysicalL2Hilbert
      F U₀ hNormCeiling hWeak
  have hSelf : Tendsto
      (fun t : ℝ => inner ℝ (F t) U₀)
      (𝓝[>] (0 : ℝ)) (𝓝 (‖U₀‖ ^ 2)) := by
    have hContinuous :
        Continuous (fun V : H3PhysicalRealFinVectorL2Hilbert =>
          inner ℝ V U₀) :=
      continuous_id.inner continuous_const
    have h := hContinuous.continuousAt.tendsto.comp hStrong
    simpa only [Function.comp_def, real_inner_self_eq_norm_sq] using h
  exact h3Audit_initialBudget_selfPairing_implies_physicalAndKineticRightTrace
    hH3 hInt0 hMeas0 r b hb hbT hR hBudget hSelf

end
end Euclidean
end Bridge
end PrimeTensor
