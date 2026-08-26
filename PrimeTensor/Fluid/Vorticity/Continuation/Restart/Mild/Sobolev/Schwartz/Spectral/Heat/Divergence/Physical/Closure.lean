import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Derivative.Physical.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Velocity.Kernel

/-!
# Physical closure under finite heat divergence

The preceding scalar closure transports genuine Schwartz-product anchors
through one positive-time heat derivative.  The pre-Leray velocity kernel is
the finite divergence

    i ↦ ∑ j : Fin 3, e^{νtΔ} ∂ⱼ (Uᵢ Vⱼ).

Only a finite sum remains.  This file packages the corresponding physical
`L²` closure.  Each of the three differentiated product coordinates is
approximated independently, and the triangle inequality transports those
approximations through the divergence sum.

Thus the decoded finite heat-divergence of the weighted H³ outer product lies
in the physical `L²` closure of vectors built from finite sums of genuine
Schwartz-product heat-derivative anchors.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- Finite three-coordinate vector of complex physical `L²` scalar states. -/
abbrev H3ComplexPhysicalFinVectorL2 : Type :=
  Fin 3 → H3ComplexPhysicalScalarL2

/-- Decode a finite weighted H³ spectral vector coordinatewise into complex
physical `L²`. -/
noncomputable def h3SpectralFinVectorDecodeComplexL2
    (W : H3SpectralFinVectorState) :
    H3ComplexPhysicalFinVectorL2 :=
  fun i => h3SpectralScalarDecodeComplexL2 (W i)

@[simp]
theorem h3SpectralFinVectorDecodeComplexL2_apply
    (W : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3SpectralFinVectorDecodeComplexL2 W i
      = h3SpectralScalarDecodeComplexL2 (W i) :=
  rfl

/-- Exact finite-sum linearity of the complex decoder. -/
theorem h3SpectralScalarDecodeComplexL2_sum
    {ι : Type}
    (s : Finset ι)
    (F : ι → H3SpectralScalarState) :
    h3SpectralScalarDecodeComplexL2 (s.sum F)
      =
    s.sum (fun j => h3SpectralScalarDecodeComplexL2 (F j)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih]

/-- Decoding commutes with the finite heat-divergence sum. -/
theorem h3SpectralFinTensorHeatDivergence_decodeComplexL2_apply
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (T : H3SpectralFinTensorState)
    (i : Fin 3) :
    h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinTensorHeatDivergenceApply ν t hν ht T) i
      =
    ∑ j : Fin 3,
      h3SpectralScalarDecodeComplexL2
        (h3SpectralScalarHeatDerivativeApply ν t hν ht j (T i j)) := by
  unfold h3SpectralFinVectorDecodeComplexL2
  unfold h3SpectralFinTensorHeatDivergenceApply
  exact
    h3SpectralScalarDecodeComplexL2_sum
      Finset.univ
      (fun j : Fin 3 =>
        h3SpectralScalarHeatDerivativeApply ν t hν ht j (T i j))

/-- A physical finite vector is a heat-divergence Schwartz anchor when each
output coordinate is a finite sum of the three positive-time heat derivatives
of genuine Schwartz-product spectral anchors. -/
def H3SchwartzHeatDivergencePhysicalFinVectorL2Anchor
    (ν t : ℝ)
    (hν : 0 < ν)
    (ht : 0 < t)
    (u : H3ComplexPhysicalFinVectorL2) : Prop :=
  ∃ A : Fin 3 → Fin 3 → H3ComplexPhysicalScalarL2,
    (∀ i j : Fin 3,
      H3SchwartzHeatDerivativePhysicalL2Anchor ν t hν ht j (A i j)) ∧
    u = fun i => ∑ j : Fin 3, A i j

/-- Epsilon realization of the complete finite heat-divergence of the spectral
outer product by a physical finite sum of genuine Schwartz-product
heat-derivative anchors. -/
theorem exists_h3SchwartzHeatDivergencePhysicalFinVectorL2Anchor_dist_lt
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : H3SpectralFinVectorState)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ u : H3ComplexPhysicalFinVectorL2,
      H3SchwartzHeatDivergencePhysicalFinVectorL2Anchor ν t hν ht u ∧
      dist
        (h3SpectralFinVectorDecodeComplexL2
          (h3SpectralFinVelocityHeatDivergenceApply ν t hν ht U V))
        u < ε := by
  have hδ : 0 < ε / 6 := by
    linarith

  choose A hAAnchor hADist using
    fun i j : Fin 3 =>
      exists_h3SchwartzHeatDerivativePhysicalL2Anchor_dist_lt
        hν ht j (U i) (V j) hδ

  let u : H3ComplexPhysicalFinVectorL2 :=
    fun i => ∑ j : Fin 3, A i j

  refine ⟨u, ?_, ?_⟩
  · exact ⟨A, hAAnchor, rfl⟩
  · rw [dist_eq_norm]
    have hhalf : 0 ≤ ε / 2 := by
      linarith
    have hNorm :
        ‖h3SpectralFinVectorDecodeComplexL2
              (h3SpectralFinVelocityHeatDivergenceApply ν t hν ht U V) -
            u‖
          ≤ ε / 2 := by
      apply (pi_norm_le_iff_of_nonneg hhalf).2
      intro i
      change
        ‖h3SpectralFinVectorDecodeComplexL2
              (h3SpectralFinVelocityHeatDivergenceApply ν t hν ht U V) i -
            u i‖
          ≤ ε / 2
      rw [show
        h3SpectralFinVectorDecodeComplexL2
            (h3SpectralFinVelocityHeatDivergenceApply ν t hν ht U V) i
          =
        ∑ j : Fin 3,
          h3SpectralScalarDecodeComplexL2
            (h3SpectralScalarHeatDerivativeApply
              ν t hν ht j (h3SpectralFinOuterProduct U V i j)) by
          unfold h3SpectralFinVelocityHeatDivergenceApply
          exact
            h3SpectralFinTensorHeatDivergence_decodeComplexL2_apply
              hν ht (h3SpectralFinOuterProduct U V) i]
      change
        ‖(∑ j : Fin 3,
              h3SpectralScalarDecodeComplexL2
                (h3SpectralScalarHeatDerivativeApply
                  ν t hν ht j
                  (h3WeightedRawProductConvolutionL2 (U i) (V j)))) -
            ∑ j : Fin 3, A i j‖
          ≤ ε / 2
      rw [← Finset.sum_sub_distrib]
      calc
        ‖∑ j : Fin 3,
            (h3SpectralScalarDecodeComplexL2
                (h3SpectralScalarHeatDerivativeApply
                  ν t hν ht j
                  (h3WeightedRawProductConvolutionL2 (U i) (V j))) -
              A i j)‖
            ≤
          ∑ j : Fin 3,
            ‖h3SpectralScalarDecodeComplexL2
                (h3SpectralScalarHeatDerivativeApply
                  ν t hν ht j
                  (h3WeightedRawProductConvolutionL2 (U i) (V j))) -
              A i j‖ := by
                exact
                  norm_sum_le
                    Finset.univ
                    (fun j : Fin 3 =>
                      h3SpectralScalarDecodeComplexL2
                          (h3SpectralScalarHeatDerivativeApply
                            ν t hν ht j
                            (h3WeightedRawProductConvolutionL2 (U i) (V j))) -
                        A i j)
        _ ≤ ∑ _j : Fin 3, ε / 6 := by
              apply Finset.sum_le_sum
              intro j hj
              have hij := hADist i j
              rw [dist_eq_norm] at hij
              exact hij.le
        _ = ε / 2 := by
              simp
              ring
    exact hNorm.trans_lt (by linarith)

/-- Closure form for the full pre-Leray velocity heat-divergence output. -/
theorem h3SpectralFinVelocityHeatDivergence_decodeComplexL2_mem_closure
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : H3SpectralFinVectorState) :
    h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinVelocityHeatDivergenceApply ν t hν ht U V)
      ∈ closure
        {u : H3ComplexPhysicalFinVectorL2 |
          H3SchwartzHeatDivergencePhysicalFinVectorL2Anchor
            ν t hν ht u} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨u, hAnchor, hDist⟩ :=
    exists_h3SchwartzHeatDivergencePhysicalFinVectorL2Anchor_dist_lt
      hν ht U V hε
  exact ⟨u, hAnchor, hDist⟩

end

end Euclidean
end Bridge
end PrimeTensor
