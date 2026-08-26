import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.Derivative.L1.Bound

/-!
# Pointwise spatial derivative bound for the nonlinear Duhamel kernel

The previous module proves that one Fourier coordinate derivative of the
positive-lag nonlinear forcing belongs to `L¹`, with an explicit retarded
`(t-s)⁻¹/²` path majorant.

Fourier inversion converts that `L¹` estimate into a uniform pointwise bound
for the corresponding classical spatial derivative amplitude.  This file
packages the inverse-Fourier derivative representative and proves

    ‖D_j K_{t-s}(x)‖ ≤ derivativePathMajorant(s)

for every spatial point `x` and every interior source time `0 < s < t`.

This is the domination statement needed by the next layer when moving one
spatial derivative through the near-endpoint Duhamel time integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform
open scoped ENNReal NNReal Topology Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingPathDerivativePointwiseBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Classical inverse-Fourier representative of one coordinate derivative of
one positive-lag raw nonlinear forcing coordinate. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3) : ℂ :=
  FourierTransformInv.fourierInv
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol j ξ *
        h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i ξ)
    x

/-- Fourier inversion is uniformly bounded by the `L¹` mass of the derivative
amplitude. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_le_integral
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ U V i j x‖
      ≤
    ∫ ξ : H3FourierPoint3,
      ‖h3FourierDerivativeSymbol j ξ *
        h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i ξ‖ := by
  unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
  rw [Real.fourierInv_eq_fourier_neg]
  rw [Real.fourier_eq]

  calc
    ‖∫ ξ : H3FourierPoint3,
        𝐞 (-(inner ℝ ξ (-x))) •
          (h3FourierDerivativeSymbol j ξ *
            h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ)‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖𝐞 (-(inner ℝ ξ (-x))) •
          (h3FourierDerivativeSymbol j ξ *
            h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ)‖ :=
      norm_integral_le_integral_norm _
    _ =
      ∫ ξ : H3FourierPoint3,
        ‖h3FourierDerivativeSymbol j ξ *
          h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ‖ := by
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [Circle.norm_smul]

/-- Under uniform spectral path bounds, the classical derivative
representative is pointwise dominated by the same integrable scalar majorant
as its Fourier `L¹` mass. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_le_pathMajorant
    {ν t MU MV s : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hs : s ∈ Set.Ioo (0 : ℝ) t)
    (hU : ‖U s‖ ≤ MU)
    (hV : ‖V s‖ ≤ MV)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν (t - s) (U s) (V s) i j x‖
      ≤
    h3NonlinearForcingHeatFirstDerivativePathMajorant
      ν t MU MV s := by
  have hτ : 0 < t - s := sub_pos.mpr hs.2
  exact
    (norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_le_integral
      hν hτ (U s) (V s) i j x).trans
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_derivative_norm_integral_le_pathMajorant
        hν hMU hMV U V hs hU hV i j)

end

end Euclidean
end Bridge
end PrimeTensor
