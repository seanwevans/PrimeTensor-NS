import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.Diagonal.Right.Quotient
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Selected Duhamel classical diagonal right derivative

`DiagonalRightQuotient` closed the literal classical Duhamel difference
quotient in the exact zero-right form

    h⁻¹ • (D(t+h) - D(t)) ⟶ G(t),    h ↓ 0.

This file converts that limit into Mathlib's derivative language.

The conversion is deliberately generic.  For a map `f : ℝ → E`, first
translate the base point:

    g(h) = f(x+h).

The zero-right quotient hypothesis is exactly the slope criterion for

    HasDerivWithinAt g f' (Ioi 0) 0.

Then compose with `y ↦ y - x`, whose derivative is `1` and which maps
`Ioi x` into `Ioi 0`.  The composition is identically `f`, yielding

    HasDerivWithinAt f f' (Ioi x) x.

Applying this once to the selected classical Duhamel diagonal packages the
landed right quotient as an actual one-sided derivative with canonical value

    ν · trace(D² D(t)) + F(W(t),W(t)).

The next checkpoint can therefore use the right-derivative FTC theorem
directly, without any further quotient/filter bookkeeping.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace BigOperators

noncomputable section

noncomputable local instance axisFintypeH3DuhamelDiagonalRightDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- A zero-right normalized difference-quotient limit is exactly a right
`HasDerivWithinAt` statement after translating the base point. -/
theorem hasDerivWithinAt_Ioi_of_tendsto_slope_zero_right
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {f : ℝ → E}
    {x : ℝ}
    {f' : E}
    (h :
      Tendsto
        (fun r : ℝ =>
          r⁻¹ • (f (x + r) - f x))
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 f')) :
    HasDerivWithinAt f f' (Set.Ioi x) x := by
  let g : ℝ → E :=
    fun r => f (x + r)

  have hg :
      HasDerivWithinAt g f' (Set.Ioi (0 : ℝ)) 0 := by
    rw [
      hasDerivWithinAt_iff_tendsto_slope'
        (show (0 : ℝ) ∉ Set.Ioi (0 : ℝ) by simp)
    ]
    unfold slope
    dsimp only [g]
    simpa only [
      vsub_eq_sub,
      sub_zero,
      add_zero
    ] using h

  have hinner :
      HasDerivWithinAt
        (fun y : ℝ => y - x)
        1
        (Set.Ioi x)
        x := by
    exact
      ((hasDerivAt_id x).sub_const x).hasDerivWithinAt

  have hmaps :
      MapsTo
        (fun y : ℝ => y - x)
        (Set.Ioi x)
        (Set.Ioi (0 : ℝ)) := by
    intro y hy
    change x < y at hy
    change 0 < y - x
    exact sub_pos.mpr hy

  have hcomp :=
    hg.scomp_of_eq x hinner hmaps (by ring)

  have hfun :
      (g ∘ fun y : ℝ => y - x) = f := by
    funext y
    dsimp only [g, Function.comp_apply]
    congr 1
    ring

  rw [hfun] at hcomp
  simpa only [one_smul] using hcomp

/-- The selected literal classical Duhamel diagonal has the canonical
right derivative at every positive base time inside the restart radius. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_hasDerivWithinAt_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    HasDerivWithinAt
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν r W W i x)
      ((ν : ℂ) *
          (∑ j : Fin 3,
            h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
              ν t W W i x
              (h3FourierAxisDirection (h3AxisOfFin3 j))
              (h3FourierAxisDirection (h3AxisOfFin3 j)))
        +
      h3RawFinLerayOuterProductDivergenceC0Representative
        (W t) (W t) i x)
      (Set.Ioi t)
      t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : ℝ → ℂ :=
    fun r =>
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν r W W i x

  let G : ℂ :=
    (ν : ℂ) *
        (∑ j : Fin 3,
          h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
            ν t W W i x
            (h3FourierAxisDirection (h3AxisOfFin3 j))
            (h3FourierAxisDirection (h3AxisOfFin3 j)))
      +
    h3RawFinLerayOuterProductDivergenceC0Representative
      (W t) (W t) i x

  have hQ :=
    tendsto_inv_smul_sub_h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_zero_right_eq_viscosity_hessianTrace_add_forcing
      hν U₀ hA hU₀ ht htR i x

  have hQt :
      Tendsto
        (fun h : ℝ =>
          h⁻¹ • (D (t + h) - D t))
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 G) := by
    dsimp only [D, G, W]
    exact hQ

  have hDeriv :
      HasDerivWithinAt D G (Set.Ioi t) t :=
    hasDerivWithinAt_Ioi_of_tendsto_slope_zero_right hQt

  dsimp only [D, G, W] at hDeriv ⊢
  exact hDeriv

end

end Euclidean
end Bridge
end PrimeTensor
