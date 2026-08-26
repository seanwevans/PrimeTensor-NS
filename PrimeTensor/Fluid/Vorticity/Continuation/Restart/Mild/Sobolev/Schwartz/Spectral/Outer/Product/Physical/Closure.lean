import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Convolution.Physical.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Vorticity.Flux

/-!
# Physical L² closure of the finite H³ spectral outer product

The scalar weighted product convolution has now been identified, after exact
complex decoding, as an `L²` limit of genuine pointwise Schwartz products.
The heat--Leray restart kernel does not use one scalar product in isolation:
its nonlinear input is the finite tensor

    (U ⊗ V)ᵢⱼ = B(Uᵢ,Vⱼ).

This file lifts the scalar physical-realization theorem to that exact
`Fin 3 × Fin 3` tensor boundary.

Because the tensor norm is the iterated finite product sup norm, choosing every
coordinate within `ε / 2` gives one simultaneous tensor approximation within
`ε`.  Thus the decoded spectral outer product lies in the physical `L²` closure
of tensors whose every coordinate is an actual pointwise Schwartz product.

No heat, derivative, Leray, or time-integration argument is used here.  The
result is the physical tensor input needed for the next divergence/Leray bridge.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal ContDiff FourierTransform Topology

noncomputable section

/-- Finite three-by-three tensor of complex physical `L²` scalar states. -/
abbrev H3ComplexPhysicalFinTensorL2 : Type :=
  Fin 3 → Fin 3 → H3ComplexPhysicalScalarL2

/-- Decode a finite weighted H³ spectral tensor coordinatewise into physical
complex `L²`. -/
noncomputable def h3SpectralFinTensorDecodeComplexL2
    (T : H3SpectralFinTensorState) :
    H3ComplexPhysicalFinTensorL2 :=
  fun i j => h3SpectralScalarDecodeComplexL2 (T i j)

@[simp]
theorem h3SpectralFinTensorDecodeComplexL2_apply
    (T : H3SpectralFinTensorState)
    (i j : Fin 3) :
    h3SpectralFinTensorDecodeComplexL2 T i j
      = h3SpectralScalarDecodeComplexL2 (T i j) :=
  rfl

/-- A physical finite tensor is a Schwartz-product anchor when each coordinate
is the `L²` class of a genuine pointwise Schwartz product. -/
def H3SchwartzPhysicalProductFinTensorL2Anchor
    (A : H3ComplexPhysicalFinTensorL2) : Prop :=
  ∀ i j : Fin 3,
    H3SchwartzPhysicalProductL2Anchor (A i j)

/-- Every decoded coordinate of the finite spectral outer product already lies
in the scalar physical Schwartz-product closure. -/
theorem h3SpectralFinOuterProduct_decodeComplexL2_coordinate_mem_closure
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3) :
    h3SpectralFinTensorDecodeComplexL2
        (h3SpectralFinOuterProduct U V) i j
      ∈ closure
        {u : H3ComplexPhysicalScalarL2 |
          H3SchwartzPhysicalProductL2Anchor u} := by
  simpa [h3SpectralFinTensorDecodeComplexL2, h3SpectralFinOuterProduct] using
    h3SpectralScalarDecodeComplexL2_weightedRawProductConvolutionL2_mem_closure
      (U i) (V j)

/-- Simultaneous finite-tensor epsilon realization: one physical tensor whose
nine coordinates are genuine pointwise Schwartz products approximates the
whole decoded spectral outer product in the product sup norm. -/
theorem exists_h3SchwartzPhysicalProductFinTensorL2Anchor_dist_lt
    (U V : H3SpectralFinVectorState)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ A : H3ComplexPhysicalFinTensorL2,
      H3SchwartzPhysicalProductFinTensorL2Anchor A ∧
      dist
        (h3SpectralFinTensorDecodeComplexL2
          (h3SpectralFinOuterProduct U V))
        A < ε := by
  have hhalf : 0 < ε / 2 := by linarith

  choose A hAAnchor hADist using
    fun i j : Fin 3 =>
      exists_h3SchwartzPhysicalProductL2Anchor_dist_lt
        (U i) (V j) hhalf

  refine ⟨A, ?_, ?_⟩
  · intro i j
    exact hAAnchor i j
  · rw [dist_eq_norm]
    have hhalf_nonneg : 0 ≤ ε / 2 := hhalf.le
    have hNorm :
        ‖h3SpectralFinTensorDecodeComplexL2
              (h3SpectralFinOuterProduct U V) - A‖
          ≤ ε / 2 := by
      apply (pi_norm_le_iff_of_nonneg hhalf_nonneg).2
      intro i
      apply (pi_norm_le_iff_of_nonneg hhalf_nonneg).2
      intro j
      have hij := hADist i j
      rw [dist_eq_norm] at hij
      change
        ‖h3SpectralScalarDecodeComplexL2
              (h3WeightedRawProductConvolutionL2 (U i) (V j)) -
            A i j‖
          ≤ ε / 2
      exact hij.le
    exact hNorm.trans_lt (by linarith)

/-- The complete decoded finite H³ spectral outer product belongs to the
physical `L²` closure of finite tensors made coordinatewise from genuine
pointwise Schwartz products. -/
theorem h3SpectralFinOuterProduct_decodeComplexL2_mem_closure
    (U V : H3SpectralFinVectorState) :
    h3SpectralFinTensorDecodeComplexL2
        (h3SpectralFinOuterProduct U V)
      ∈ closure
        {A : H3ComplexPhysicalFinTensorL2 |
          H3SchwartzPhysicalProductFinTensorL2Anchor A} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨A, hAnchor, hDist⟩ :=
    exists_h3SchwartzPhysicalProductFinTensorL2Anchor_dist_lt U V hε
  exact ⟨A, hAnchor, hDist⟩

end

end Euclidean
end Bridge
end PrimeTensor
