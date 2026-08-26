import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Outer.Product.Physical.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Bilinear

/-!
# Physical closure under the positive-time heat derivative

The decoded outer-product closure is an `L²` statement.  Bare differentiation
cannot be pushed through such a closure because `∂ⱼ : L² → L²` is unbounded.
The mild kernel never uses a bare derivative, however: it uses

    exp (ν t Δ) ∂ⱼ

at strictly positive time.  On the weighted spectral side this is the bounded
multiplier `h3SpectralScalarHeatDerivativeApply`, with norm at most
`(sqrt (ν t))⁻¹`.

This file records the corresponding decoded Lipschitz estimate and uses it to
transport the exact Schwartz-product spectral anchors through one
heat-smoothed derivative.  In particular every differentiated coordinate of
the finite spectral outer product lies in the physical `L²` closure of images
of genuine Schwartz products under the exact positive-time heat derivative.

This is the scalar coordinate bridge needed before taking the finite divergence
sum.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- A physical `L²` state is a positive-time heat-derivative Schwartz-product
anchor when it is obtained by decoding one heat-derivative applied to an exact
Schwartz-product spectral anchor. -/
def H3SchwartzHeatDerivativePhysicalL2Anchor
    (ν t : ℝ)
    (hν : 0 < ν)
    (ht : 0 < t)
    (j : Fin 3)
    (u : H3ComplexPhysicalScalarL2) : Prop :=
  ∃ H : H3SpectralScalarState,
    H3SchwartzProductSpectralAnchor H ∧
    u = h3SpectralScalarDecodeComplexL2
      (h3SpectralScalarHeatDerivativeApply ν t hν ht j H)

/-- The decoded positive-time heat derivative is Lipschitz with the same
Fourier multiplier constant as the weighted spectral operator. -/
theorem dist_h3SpectralScalarDecodeComplexL2_heatDerivativeApply_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (j : Fin 3)
    (F G : H3SpectralScalarState) :
    dist
        (h3SpectralScalarDecodeComplexL2
          (h3SpectralScalarHeatDerivativeApply ν t hν ht j F))
        (h3SpectralScalarDecodeComplexL2
          (h3SpectralScalarHeatDerivativeApply ν t hν ht j G))
      ≤
    (Real.sqrt (ν * t))⁻¹ * dist F G := by
  simp only [dist_eq_norm]
  rw [← h3SpectralScalarDecodeComplexL2_sub]
  rw [← h3SpectralScalarHeatDerivativeApply_sub]
  exact
    (norm_h3SpectralScalarDecodeComplexL2_le
      (h3SpectralScalarHeatDerivativeApply
        ν t hν ht j (F - G))).trans
      (norm_h3SpectralScalarHeatDerivativeApply_le
        hν ht j (F - G))

/-- Epsilon realization after one heat-smoothed derivative: the decoded
positive-time derivative of an arbitrary weighted H³ product convolution is
arbitrarily close to the corresponding derivative of an exact Schwartz-product
spectral anchor. -/
theorem exists_h3SchwartzHeatDerivativePhysicalL2Anchor_dist_lt
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (j : Fin 3)
    (F G : H3SpectralScalarState)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ u : H3ComplexPhysicalScalarL2,
      H3SchwartzHeatDerivativePhysicalL2Anchor ν t hν ht j u ∧
      dist
        (h3SpectralScalarDecodeComplexL2
          (h3SpectralScalarHeatDerivativeApply
            ν t hν ht j
            (h3WeightedRawProductConvolutionL2 F G)))
        u < ε := by
  let C : ℝ := (Real.sqrt (ν * t))⁻¹
  let K : ℝ := C + 1
  let δ : ℝ := ε / (2 * K)

  have hC : 0 ≤ C := by
    dsimp [C]
    positivity

  have hK : 0 < K := by
    dsimp [K]
    linarith

  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos hε (mul_pos (by norm_num) hK)

  obtain ⟨H, hAnchor, hDist⟩ :=
    exists_h3SchwartzProductSpectralAnchor_dist_lt F G hδ

  let u : H3ComplexPhysicalScalarL2 :=
    h3SpectralScalarDecodeComplexL2
      (h3SpectralScalarHeatDerivativeApply ν t hν ht j H)

  refine ⟨u, ?_, ?_⟩
  · exact ⟨H, hAnchor, rfl⟩
  · have hLip :=
      dist_h3SpectralScalarDecodeComplexL2_heatDerivativeApply_le
        hν ht j (h3WeightedRawProductConvolutionL2 F G) H

    have hCK : C ≤ K := by
      dsimp [K]
      linarith

    have hKδ : K * δ = ε / 2 := by
      dsimp [δ]
      field_simp [ne_of_gt hK]

    calc
      dist
          (h3SpectralScalarDecodeComplexL2
            (h3SpectralScalarHeatDerivativeApply
              ν t hν ht j
              (h3WeightedRawProductConvolutionL2 F G)))
          u
          ≤ C * dist (h3WeightedRawProductConvolutionL2 F G) H := by
            simpa [C, u] using hLip
      _ ≤ K * dist (h3WeightedRawProductConvolutionL2 F G) H := by
            exact mul_le_mul_of_nonneg_right hCK (dist_nonneg)
      _ < K * δ := by
            exact mul_lt_mul_of_pos_left hDist hK
      _ = ε / 2 := hKδ
      _ < ε := by linarith

/-- Closure form of the positive-time derivative realization theorem. -/
theorem h3SpectralScalarDecodeComplexL2_heatDerivative_product_mem_closure
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (j : Fin 3)
    (F G : H3SpectralScalarState) :
    h3SpectralScalarDecodeComplexL2
        (h3SpectralScalarHeatDerivativeApply
          ν t hν ht j
          (h3WeightedRawProductConvolutionL2 F G))
      ∈ closure
        {u : H3ComplexPhysicalScalarL2 |
          H3SchwartzHeatDerivativePhysicalL2Anchor ν t hν ht j u} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨u, hAnchor, hDist⟩ :=
    exists_h3SchwartzHeatDerivativePhysicalL2Anchor_dist_lt
      hν ht j F G hε
  exact ⟨u, hAnchor, hDist⟩

/-- Concrete outer-product coordinate form: after one positive-time
heat-smoothed coordinate derivative, each decoded `(i,j)` nonlinear product
lies in the physical `L²` closure of differentiated genuine Schwartz-product
anchors. -/
theorem h3SpectralFinOuterProduct_heatDerivative_decodeComplexL2_mem_closure
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3) :
    h3SpectralScalarDecodeComplexL2
        (h3SpectralScalarHeatDerivativeApply
          ν t hν ht j
          (h3SpectralFinOuterProduct U V i j))
      ∈ closure
        {u : H3ComplexPhysicalScalarL2 |
          H3SchwartzHeatDerivativePhysicalL2Anchor ν t hν ht j u} := by
  simpa [h3SpectralFinOuterProduct] using
    h3SpectralScalarDecodeComplexL2_heatDerivative_product_mem_closure
      hν ht j (U i) (V j)

end

end Euclidean
end Bridge
end PrimeTensor
