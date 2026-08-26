import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Product.Convolution.Kernel
import Mathlib.Analysis.Fourier.LpSpace

/-!
# Schwartz density in the weighted H³ spectral state space

The smooth product-convolution theorem is now proved on Schwartz functions.
To extend it to the genuine H³ solver state, the first required topological
fact is that Schwartz functions are dense in the exact weighted spectral
`L²` space used by PrimeTensor.

This file records that fact directly at the project type
`H3SpectralScalarState` and exposes an epsilon-approximation form convenient
for the later bilinear limiting argument.

The approximation occurs in the *weighted spectral state itself*.  Thus if
`G = W₃ f̂`, a Schwartz approximant `S` satisfies `S → G` in the same `L²`
norm controlled by the already-proved weighted convolution bilinear bound.
No product identity is extended here yet.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped ENNReal

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralDensity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Schwartz frequency functions are dense in the exact weighted scalar H³
spectral state space. -/
theorem h3Schwartz_denseRange_toSpectralScalar :
    DenseRange
      (fun f : SchwartzMap H3FourierPoint3 ℂ =>
        f.toLp 2 (volume : Measure H3FourierPoint3)) := by
  have h :
      DenseRange
        (SchwartzMap.toLpCLM ℝ ℂ (2 : ENNReal)
          (volume : Measure H3FourierPoint3)) :=
    SchwartzMap.denseRange_toLpCLM
      (E := H3FourierPoint3)
      (F := ℂ)
      (p := (2 : ENNReal))
      ENNReal.ofNat_ne_top
  have hfun :
      (fun f : SchwartzMap H3FourierPoint3 ℂ =>
        f.toLp 2 (volume : Measure H3FourierPoint3)) =
      (SchwartzMap.toLpCLM ℝ ℂ (2 : ENNReal)
        (volume : Measure H3FourierPoint3) :
          SchwartzMap H3FourierPoint3 ℂ → H3SpectralScalarState) := by
    funext f
    rfl
  rw [hfun]
  exact h

/-- Every weighted scalar H³ state admits an arbitrarily close Schwartz
frequency representative. -/
theorem exists_h3Schwartz_spectralApprox_dist
    (G : H3SpectralScalarState)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ f : SchwartzMap H3FourierPoint3 ℂ,
      dist G (f.toLp 2 (volume : Measure H3FourierPoint3)) < ε := by
  exact h3Schwartz_denseRange_toSpectralScalar.exists_dist_lt G hε

/-- Norm form of the weighted Schwartz approximation theorem. -/
theorem exists_h3Schwartz_spectralApprox_norm
    (G : H3SpectralScalarState)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ f : SchwartzMap H3FourierPoint3 ℂ,
      ‖G - f.toLp 2 (volume : Measure H3FourierPoint3)‖ < ε := by
  simpa only [dist_eq_norm] using
    exists_h3Schwartz_spectralApprox_dist G hε

end

end Euclidean
end Bridge
end PrimeTensor
