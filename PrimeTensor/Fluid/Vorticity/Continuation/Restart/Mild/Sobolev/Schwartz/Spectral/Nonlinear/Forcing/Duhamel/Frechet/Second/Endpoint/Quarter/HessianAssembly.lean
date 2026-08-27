import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Assembly
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Finite-dimensional Hessian assembly for the H³ Fourier carrier

The first-order Fréchet layer already assembles three coordinate coefficients
into one continuous real-linear map.  At second order we need the analogous
rank-two object

    H3FourierPoint3 →L[ℝ] (H3FourierPoint3 →L[ℝ] ℂ).

For a matrix of mixed coordinate coefficients `M j k`, the outer direction is
`k` and the inner direction is `j`.  Thus the assembled operator satisfies

    H(e_k)(e_j) = M j k

on the three canonical coordinate directions.

This file contains only finite-dimensional bookkeeping.  No endpoint estimate
is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Filter
open scoped Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterHessianAssembly
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Rank-two lift of a complex coefficient into a continuous real
bilinear operator on the H³ Fourier carrier.  The first spatial argument is
the outer coordinate `k`; the second is the inner coordinate `j`.

This is built entirely from Mathlib's bundled continuous rank-one operator
`ContinuousLinearMap.smulRightL`, avoiding any finite-dimensional coercion from
an unbundled `LinearMap`. -/
noncomputable def h3FourierSecondCoordinateLiftCLM
    (j k : Fin 3) :
    ℂ →L[ℝ]
      (H3FourierPoint3 →L[ℝ] (H3FourierPoint3 →L[ℝ] ℂ)) :=
  ((ContinuousLinearMap.smulRightL
      ℝ
      H3FourierPoint3
      (H3FourierPoint3 →L[ℝ] ℂ))
      (h3FourierCoordinateCLM (h3AxisOfFin3 k))).comp
    (h3FourierCoordinateLiftCLM (h3AxisOfFin3 j))

@[simp]
theorem h3FourierSecondCoordinateLiftCLM_apply
    (j k : Fin 3)
    (z : ℂ)
    (h₁ h₂ : H3FourierPoint3) :
    h3FourierSecondCoordinateLiftCLM j k z h₁ h₂
      =
    (h₁ (h3AxisOfFin3 k)) •
      ((h₂ (h3AxisOfFin3 j)) • z) := by
  simp [h3FourierSecondCoordinateLiftCLM]

/-- Assemble the nine mixed coordinate coefficients into one continuous
bilinear operator. -/
noncomputable def h3AssembleSecondCoordinateDerivative
    (M : Fin 3 → Fin 3 → ℂ) :
    H3FourierPoint3 →L[ℝ]
      (H3FourierPoint3 →L[ℝ] ℂ) :=
  ∑ k : Fin 3,
    ∑ j : Fin 3,
      h3FourierSecondCoordinateLiftCLM j k (M j k)

@[simp]
theorem h3AssembleSecondCoordinateDerivative_apply
    (M : Fin 3 → Fin 3 → ℂ)
    (h₁ h₂ : H3FourierPoint3) :
    h3AssembleSecondCoordinateDerivative M h₁ h₂
      =
    ∑ k : Fin 3,
      ∑ j : Fin 3,
        (h₁ (h3AxisOfFin3 k)) •
          ((h₂ (h3AxisOfFin3 j)) • M j k) := by
  simp [h3AssembleSecondCoordinateDerivative]

/-- The assembled second-order operator recovers exactly the prescribed mixed
coordinate coefficient on canonical coordinate directions. -/
@[simp]
theorem h3AssembleSecondCoordinateDerivative_axis_axis
    (M : Fin 3 → Fin 3 → ℂ)
    (j k : Fin 3) :
    h3AssembleSecondCoordinateDerivative M
        (h3FourierAxisDirection (h3AxisOfFin3 k))
        (h3FourierAxisDirection (h3AxisOfFin3 j))
      =
    M j k := by
  fin_cases j <;> fin_cases k <;>
    simp [h3AssembleSecondCoordinateDerivative_apply, Fin.sum_univ_three]

end
end Euclidean
end Bridge
end PrimeTensor
