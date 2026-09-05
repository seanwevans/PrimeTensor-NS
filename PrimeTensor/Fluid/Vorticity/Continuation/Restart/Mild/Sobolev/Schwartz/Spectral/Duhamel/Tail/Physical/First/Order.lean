import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.FirstOrder
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Spatial.Derivative

/-!
# First-order limit of the physical nonlinear Duhamel reconstruction

`FirstOrder` proves the shrinking-tail limit directly for the interval integral

    ∫ s in 0..h, H_{h-s} F(U(s), V(s))(x).

The classical nonlinear Duhamel reconstruction introduced by the spatial
differentiation layer is exactly that retarded interval integral.  This file
packages the existing limit under the named Duhamel object itself.

The sign here is deliberately positive: this is the positive Leray--divergence
Duhamel operator.  The Navier--Stokes minus sign belongs to the surrounding
mild equation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralDuhamelTailPhysicalFirstOrder
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The normalized named physical Duhamel term has first-order right limit
equal to the instantaneous unheated Leray--divergence forcing. -/
theorem tendsto_h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_normalized_zero_right
    {ν MU MV : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν h U V i x)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (U 0) (V 0) i x)) := by
  simpa only [
    h3RawFinLerayOuterProductDivergenceHeatC3Duhamel,
    h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath,
    zero_add
  ] using
    (tendsto_h3RawFinLerayOuterProductDivergenceHeatC3NormalizedShortTail
      (a := (0 : ℝ))
      hν hMU hMV U V hUcont hVcont hU hV i x)

end

end Euclidean
end Bridge
end PrimeTensor
