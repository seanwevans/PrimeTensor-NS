import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Plancherel
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.MeasureTheory.Function.Holder

/-!
# Classical L² directional derivatives as weak derivatives

`Sobolev.Plancherel` isolates the missing analytic boundary between the
project's pointwise derivative slots and the Fourier multiplier identities
needed by the weighted H³ solver state.

This file closes the generic functional-analytic part of that boundary.

Suppose real-valued functions `f,g` on the Euclidean Fourier carrier satisfy

* `f ∈ L²`,
* `g ∈ L²`,
* `g` is the classical directional derivative of `f` in direction `v`
  at every point.

Then the complex `L²` classes determined by `f` and `g`, embedded into
tempered distributions, satisfy

    ∂_v [f] = [g].

The proof tests against a Schwartz function `φ`.  Since Schwartz functions
and all their directional derivatives lie in `L²`, Hölder gives the three
`L¹` products required by Mathlib's integration-by-parts theorem:

    g φ,    f (∂_v φ),    f φ.

Thus no global `L¹` assumption on `f` or `g`, and no Schwartz assumption on
the velocity field, is introduced.

The remaining project-specific task is purely geometric/calculus:
transport `spatial3.d i f` from the sup-norm `Point3` presentation to the
Euclidean carrier and produce the required `HasLineDerivAt` witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal SchwartzMap LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3WeakDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Real `L²` functions as complex `L²` classes -/

/--
Turn a real raw `L²` function on the Euclidean carrier into the corresponding
complex `L²` class.
-/
def h3RealMemLpToComplexL2
    {f : H3FourierPoint3 → ℝ}
    (hf : MemLp f 2 volume) :
    H3FourierComplexL2 :=
  Complex.ofRealCLM.compLp (hf.toLp f)

/-- The complex `L²` class has the expected raw representative a.e. -/
theorem h3RealMemLpToComplexL2_coeFn
    {f : H3FourierPoint3 → ℝ}
    (hf : MemLp f 2 volume) :
    (h3RealMemLpToComplexL2 hf : H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    fun x => (f x : ℂ) := by
  unfold h3RealMemLpToComplexL2
  filter_upwards [
    Complex.ofRealCLM.coeFn_compLp (hf.toLp f),
    MeasureTheory.MemLp.coeFn_toLp hf
  ] with x hComplex hReal
  rw [hComplex, hReal]
  rfl


/--
Real scalar multiplication on complex numbers, bundled as a continuous
real-bilinear map.
-/
def h3RealComplexBilinear : ℝ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).comp Complex.ofRealCLM

@[simp]
theorem h3RealComplexBilinear_apply
    (r : ℝ) (z : ℂ) :
    h3RealComplexBilinear r z = r • z := by
  simp [h3RealComplexBilinear, smul_eq_mul]

/-! ## Hölder helpers for the weak derivative proof -/

/--
Two `L²` functions paired by a continuous real-bilinear map give an
integrable function.
-/
theorem h3_integrable_bilin_of_memLp_two
    {E F G : Type*}
    [NormedAddCommGroup E]
    [NormedAddCommGroup F]
    [NormedAddCommGroup G]
    [NormedSpace ℝ E]
    [NormedSpace ℝ F]
    [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G)
    {f : H3FourierPoint3 → E}
    {g : H3FourierPoint3 → F}
    (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    Integrable (fun x => B (f x) (g x)) volume := by
  rw [← MeasureTheory.memLp_one_iff_integrable]
  exact B.memLp_of_bilin 1 hf hg

/--
Real scalar multiplication of a complex `L²` function is integrable.
-/
theorem h3_integrable_real_smul_of_memLp_two
    {f : H3FourierPoint3 → ℝ}
    {g : H3FourierPoint3 → ℂ}
    (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    Integrable (fun x => f x • g x) volume := by
  exact
    h3_integrable_bilin_of_memLp_two
      h3RealComplexBilinear hf hg

/-! ## The generic weak derivative theorem -/

/--
A classical directional derivative which is itself `L²` agrees with the weak
/ tempered-distribution directional derivative.

This is the central reusable bridge needed by the H³ snapshot construction.
-/
theorem h3RealL2_classicalLineDerivative_eq_weak
    {f g : H3FourierPoint3 → ℝ}
    (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume)
    (v : H3FourierPoint3)
    (hderiv :
      ∀ x : H3FourierPoint3,
        HasLineDerivAt ℝ f (g x) x v) :
    ∂_{v}
        ((h3RealMemLpToComplexL2 hf : H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ))
      =
        ((h3RealMemLpToComplexL2 hg : H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ)) := by
  ext φ

  let B : ℝ →L[ℝ] ℂ →L[ℝ] ℂ :=
    h3RealComplexBilinear

  have hφ : MemLp (φ : H3FourierPoint3 → ℂ) 2 volume :=
    φ.memLp 2 volume

  have hDφ :
      MemLp
        ((∂_{v} φ : 𝓢(H3FourierPoint3, ℂ)) :
          H3FourierPoint3 → ℂ)
        2 volume :=
    (∂_{v} φ : 𝓢(H3FourierPoint3, ℂ)).memLp 2 volume

  have hgφ :
      Integrable
        (fun x : H3FourierPoint3 =>
          B (g x) (φ x))
        volume :=
    h3_integrable_bilin_of_memLp_two B hg hφ

  have hfDφ :
      Integrable
        (fun x : H3FourierPoint3 =>
          B (f x) ((∂_{v} φ : 𝓢(H3FourierPoint3, ℂ)) x))
        volume :=
    h3_integrable_bilin_of_memLp_two B hf hDφ

  have hfφ :
      Integrable
        (fun x : H3FourierPoint3 =>
          B (f x) (φ x))
        volume :=
    h3_integrable_bilin_of_memLp_two B hf hφ

  have hφderiv :
      ∀ x : H3FourierPoint3,
        HasLineDerivAt ℝ
          (φ : H3FourierPoint3 → ℂ)
          ((∂_{v} φ : 𝓢(H3FourierPoint3, ℂ)) x)
          x v := by
    intro x
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      (φ.hasFDerivAt x).hasLineDerivAt v

  have hIBP :
      (∫ x : H3FourierPoint3,
          B (f x) ((∂_{v} φ : 𝓢(H3FourierPoint3, ℂ)) x)
          ∂volume)
        =
      - ∫ x : H3FourierPoint3,
          B (g x) (φ x)
          ∂volume := by
    exact
      integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
        (B := B)
        hgφ hfDφ hfφ
        (fun x _ => hderiv x)
        (fun x _ => hφderiv x)

  have hfCoe :=
    h3RealMemLpToComplexL2_coeFn hf

  have hgCoe :=
    h3RealMemLpToComplexL2_coeFn hg

  rw [TemperedDistribution.lineDerivOp_apply_apply]
  simp only [MeasureTheory.Lp.toTemperedDistribution_apply]

  calc
    (∫ x : H3FourierPoint3,
        (-∂_{v} φ : 𝓢(H3FourierPoint3, ℂ)) x •
          h3RealMemLpToComplexL2 hf x
        ∂volume)
        =
      ∫ x : H3FourierPoint3,
        -(B (f x)
          ((∂_{v} φ : 𝓢(H3FourierPoint3, ℂ)) x))
        ∂volume := by
          apply integral_congr_ae
          filter_upwards [hfCoe] with x hx
          rw [hx]
          simp [B, smul_eq_mul, mul_comm]
    _ =
      - ∫ x : H3FourierPoint3,
          B (f x)
            ((∂_{v} φ : 𝓢(H3FourierPoint3, ℂ)) x)
          ∂volume := by
            rw [integral_neg]
    _ =
      ∫ x : H3FourierPoint3,
          B (g x) (φ x)
          ∂volume := by
            rw [hIBP]
            simp
    _ =
      ∫ x : H3FourierPoint3,
          φ x • h3RealMemLpToComplexL2 hg x
          ∂volume := by
            apply integral_congr_ae
            filter_upwards [hgCoe] with x hx
            rw [hx]
            simp [B, smul_eq_mul, mul_comm]

/--
Convenient predicate form of the generic weak derivative relation.
-/
def H3WeakLineDerivative
    (v : H3FourierPoint3)
    (F G : H3FourierComplexL2) : Prop :=
  ∂_{v} (F : 𝓢'(H3FourierPoint3, ℂ))
    =
  (G : 𝓢'(H3FourierPoint3, ℂ))

/--
The classical `L²` directional derivative theorem packaged as
`H3WeakLineDerivative`.
-/
theorem h3WeakLineDerivative_of_classical
    {f g : H3FourierPoint3 → ℝ}
    (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume)
    (v : H3FourierPoint3)
    (hderiv :
      ∀ x : H3FourierPoint3,
        HasLineDerivAt ℝ f (g x) x v) :
    H3WeakLineDerivative v
      (h3RealMemLpToComplexL2 hf)
      (h3RealMemLpToComplexL2 hg) := by
  exact
    h3RealL2_classicalLineDerivative_eq_weak
      hf hg v hderiv

end

end Euclidean
end Bridge
end PrimeTensor
