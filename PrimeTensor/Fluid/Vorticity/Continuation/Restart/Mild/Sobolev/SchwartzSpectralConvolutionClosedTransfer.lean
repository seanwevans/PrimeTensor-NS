import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralConvolutionClosure

/-!
# Closed-property transfer from exact Schwartz products to weighted H³ convolution

`SchwartzSpectralConvolutionClosure` proves the epsilon statement: the genuine
weighted H³ product convolution of arbitrary spectral states can be approached
arbitrarily closely by compact spectral approximants whose convolution is
exactly the weighted Fourier transform of a Schwartz physical product.

This file packages those exact approximating outputs as a predicate and turns
the epsilon theorem into a closure theorem.  The main consequence is a reusable
transfer principle: any closed property of weighted spectral scalar states that
holds for every exact Schwartz-product anchor also holds for the genuine
weighted H³ convolution of arbitrary inputs.

Thus later arguments can prove a property on the concrete Schwartz physical
products, prove that the property is closed, and inherit it for the full H³
nonlinearity without repeating the density construction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal ContDiff FourierTransform Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralConvolutionClosedTransfer
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A weighted spectral scalar state is an exact Schwartz-product anchor when
it is the bundled weighted convolution of two smooth compact weighted spectral
states and that convolution is pointwise the weighted Fourier transform of the
corresponding Schwartz physical product. -/
def H3SchwartzProductSpectralAnchor
    (H : H3SpectralScalarState) : Prop :=
  ∃ F' G' : H3SpectralScalarState,
    ∃ f g : H3FourierPoint3 → ℂ,
      ∃ Sf Sg : SchwartzMap H3FourierPoint3 ℂ,
        (F' : H3FourierPoint3 → ℂ) =ᵐ[volume] f ∧
        HasCompactSupport f ∧
        ContDiff ℝ ∞ f ∧
        (G' : H3FourierPoint3 → ℂ) =ᵐ[volume] g ∧
        HasCompactSupport g ∧
        ContDiff ℝ ∞ g ∧
        H = h3WeightedRawProductConvolutionL2 F' G' ∧
        ∀ ξ : H3FourierPoint3,
          h3WeightedRawProductConvolution F' G' ξ
            =
          (h3SobolevFrequencyWeight ξ : ℂ) *
            𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
                (𝓕⁻ Sf) (𝓕⁻ Sg)) ξ

/-- Epsilon form stripped down to the output state: every genuine weighted H³
convolution is arbitrarily close to an exact Schwartz-product spectral anchor. -/
theorem exists_h3SchwartzProductSpectralAnchor_dist_lt
    (F G : H3SpectralScalarState)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ H : H3SpectralScalarState,
      H3SchwartzProductSpectralAnchor H ∧
      dist (h3WeightedRawProductConvolutionL2 F G) H < ε := by
  obtain ⟨δ, hδ, F', G', f, g, Sf, Sg,
      hF, hfcompact, hfsmooth,
      hG, hgcompact, hgsmooth,
      hRawF, hRawG,
      hFapprox, hGapprox, hConvLt, hExact⟩ :=
    exists_h3SmoothCompact_spectralProductAnchor_output_lt F G hε

  refine ⟨h3WeightedRawProductConvolutionL2 F' G', ?_, ?_⟩
  · exact ⟨F', G', f, g, Sf, Sg,
      hF, hfcompact, hfsmooth,
      hG, hgcompact, hgsmooth,
      rfl, hExact⟩
  · simpa only [dist_eq_norm] using hConvLt

/-- The genuine weighted H³ product convolution belongs to the norm closure of
the exact Schwartz physical-product anchors. -/
theorem h3WeightedRawProductConvolutionL2_mem_closure_schwartzProductAnchors
    (F G : H3SpectralScalarState) :
    h3WeightedRawProductConvolutionL2 F G
      ∈ closure {H : H3SpectralScalarState | H3SchwartzProductSpectralAnchor H} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨H, hAnchor, hDist⟩ :=
    exists_h3SchwartzProductSpectralAnchor_dist_lt F G hε
  exact ⟨H, hAnchor, hDist⟩

/-- Closed-property transfer principle for the H³ product convolution.

To prove `P` for the genuine convolution of arbitrary H³ states it is enough to
show that the set cut out by `P` is closed and that every exact Schwartz-product
anchor satisfies `P`. -/
theorem h3WeightedRawProductConvolutionL2_closed_property
    (P : H3SpectralScalarState → Prop)
    (hClosed : IsClosed {H : H3SpectralScalarState | P H})
    (hAnchor :
      ∀ H : H3SpectralScalarState,
        H3SchwartzProductSpectralAnchor H → P H)
    (F G : H3SpectralScalarState) :
    P (h3WeightedRawProductConvolutionL2 F G) := by
  have hSubset :
      {H : H3SpectralScalarState | H3SchwartzProductSpectralAnchor H}
        ⊆
      {H : H3SpectralScalarState | P H} := by
    intro H hH
    exact hAnchor H hH

  have hMem :
      h3WeightedRawProductConvolutionL2 F G
        ∈ closure
          {H : H3SpectralScalarState | H3SchwartzProductSpectralAnchor H} :=
    h3WeightedRawProductConvolutionL2_mem_closure_schwartzProductAnchors F G

  exact (closure_minimal hSubset hClosed) hMem

end

end Euclidean
end Bridge
end PrimeTensor
