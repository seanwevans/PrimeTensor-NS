import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterRealSchwartz
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadCyclicIntegral
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Physical.L2.Energy.Axis.Bridge

/-!
# Canonical-axis realization of the explicit real quarter-scale Schwartz velocity

The previously proved Hermitian-to-real converse is applied on the actual
Euclidean carrier `H3FourierPoint3` indexed by `Axis Depth.three`.

The Fin-three coordinate packet is transported through the already proved
three-axis equivalence. Reindexing is exact: no phase, scalar amplitude, or
frequency is changed. Its inverse transform has real Schwartz components.
The recovered Fourier polarizations agree with the reindexed sharp packet,
and Fourier incompressibility implies actual coordinate divergence zero.

The full six-dimensional integral on the canonical carrier (requiring the
product-volume change of coordinates) and the actual first-monomial physical
aggregate are subsequent, separate steps.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory
open scoped SchwartzMap FourierTransform ComplexConjugate Topology BigOperators LineDeriv

noncomputable section

private abbrev Axis3 := PrimeTensor.Axis Depth.three
private abbrev CanonicalE := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeQuarterCanonical (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

private abbrev axes : Fin 3 ≃ Axis3 :=
  PrimeTensor.Bridge.Euclidean.h3Fin3EquivAxisThree

/-- Permute coordinates from intrinsic depth-three axes to Fin 3. -/
noncomputable def lowNormalQuarterAxisToFin :
    (Axis3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Axis3 => ℝ) axes).symm

@[simp] theorem lowNormalQuarterAxisToFin_apply
    (p : Axis3 → ℝ) (i : Fin 3) :
    lowNormalQuarterAxisToFin p i = p (axes i) := by
  rfl

/-- Fourier carrier converted from the canonical Euclidean Hilbert structure
into the original Fin-three frequency coordinates. -/
noncomputable def lowNormalQuarterAxisHilbertToFin :
    CanonicalE ≃L[ℝ] (Fin 3 → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Axis3 => ℝ)).trans
    lowNormalQuarterAxisToFin

@[simp] theorem lowNormalQuarterAxisHilbertToFin_apply
    (ξ : CanonicalE) (i : Fin 3) :
    lowNormalQuarterAxisHilbertToFin ξ i = ξ (axes i) := by
  change lowNormalQuarterAxisToFin (WithLp.ofLp ξ) i = _
  exact lowNormalQuarterAxisToFin_apply _ _

/-- The explicit spectral packet, transported to an ACTUAL canonical-axis
scalar Schwartz function for each of the three physical velocity slots. -/
noncomputable def lowNormalQuarterAxisFourierComponent
    (ρ : ℝ) (hρ : 0 < ρ) (j : Axis3) : 𝓢(CanonicalE, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    lowNormalQuarterAxisHilbertToFin
    (lowNormalQuarterWindowedFourierComponent ρ hρ (axes.symm j))

@[simp] theorem lowNormalQuarterAxisFourierComponent_apply
    (ρ : ℝ) (hρ : 0 < ρ) (j : Axis3) (ξ : CanonicalE) :
    lowNormalQuarterAxisFourierComponent ρ hρ j ξ =
      lowNormalQuarterWeightedFourier
        (lowNormalQuarterEvenWindow ρ hρ)
        (fun i : Fin 3 => ξ (axes i)) (axes.symm j) := by
  change lowNormalQuarterWindowedFourierComponent ρ hρ (axes.symm j)
    (lowNormalQuarterAxisHilbertToFin ξ) = _
  rw [lowNormalQuarterWindowedFourierComponent_apply]
  congr 1

/-- The canonical-axis Fourier component has pointwise Hermitian symmetry. -/
theorem lowNormalQuarterAxisFourierComponent_hermitian
    (ρ : ℝ) (hρ : 0 < ρ) (j : Axis3) (ξ : CanonicalE) :
    lowNormalQuarterAxisFourierComponent ρ hρ j (-ξ) =
      star (lowNormalQuarterAxisFourierComponent ρ hρ j ξ) := by
  simp only [lowNormalQuarterAxisFourierComponent_apply,
    WithLp.ofLp_neg, Pi.neg_apply]
  exact congrFun
    (lowNormalQuarterWindowedFourier_reality ρ hρ
      (fun i : Fin 3 => ξ (axes i))) (axes.symm j)

/-- Hermitian-to-real Fourier inversion on the project\'s canonical Axis carrier.
This is the same integral argument as the Fin-three result, now established
in the exact physical Hilbert space instead of postulating a carrier bridge. -/
theorem lowNormalQuarterAxisHermitianSchwartz_fourierInv_conj
    (F : 𝓢(CanonicalE, ℂ))
    (hHermitian : ∀ ξ : CanonicalE, F (-ξ) = star (F ξ))
    (x : CanonicalE) :
    star ((𝓕⁻ F) x) = (𝓕⁻ F) x := by
  have hInv : (𝓕⁻ F) x = 𝓕⁻ (F : CanonicalE → ℂ) x :=
    congrFun (SchwartzMap.fourierInv_coe F) x
  simp only [hInv, Complex.star_def, Real.fourierInv_eq]
  rw [← integral_conj]
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards with ξ
  change star ((𝐞 (inner ℝ (-ξ) x) : ℂ) * F (-ξ)) =
    (𝐞 (inner ℝ ξ x) : ℂ) * F ξ
  rw [hHermitian ξ, star_mul', star_star, Circle.star_addChar]
  simp only [inner_neg_left, neg_neg]

/-- Every canonical-axis Hermitian Schwartz spectrum has a real inverse. -/
theorem lowNormalQuarterAxisHermitianSchwartz_fourierInv_im_zero
    (F : 𝓢(CanonicalE, ℂ))
    (hHermitian : ∀ ξ : CanonicalE, F (-ξ) = star (F ξ))
    (x : CanonicalE) :
    ((𝓕⁻ F) x).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simpa only [Complex.star_def] using
    lowNormalQuarterAxisHermitianSchwartz_fourierInv_conj F hHermitian x

/-- Genuine real Schwartz scalar on PrimeTensor's H3 Fourier/physical Hilbert carrier. -/
noncomputable def lowNormalQuarterAxisRealSchwartzComponent
    (ρ : ℝ) (hρ : 0 < ρ) (j : Axis3) : 𝓢(CanonicalE, ℝ) :=
  (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM)
    (𝓕⁻ (lowNormalQuarterAxisFourierComponent ρ hρ j))

/-- Realness is proved through the general Hermitian inverse-Fourier theorem;
there is no separately imposed real-velocity assumption. -/
theorem lowNormalQuarterAxisRealSchwartz_complexify_eq_inverse
    (ρ : ℝ) (hρ : 0 < ρ) (j : Axis3) :
    PrimeTensor.Bridge.Euclidean.h3SchwartzComplexify
      (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j) =
    𝓕⁻ (lowNormalQuarterAxisFourierComponent ρ hρ j) := by
  ext x
  change ((((𝓕⁻ (lowNormalQuarterAxisFourierComponent ρ hρ j)) x).re : ℝ) : ℂ) =
    (𝓕⁻ (lowNormalQuarterAxisFourierComponent ρ hρ j)) x
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simp only [Complex.ofReal_im]
    exact (lowNormalQuarterAxisHermitianSchwartz_fourierInv_im_zero _
      (lowNormalQuarterAxisFourierComponent_hermitian ρ hρ j) x).symm

/-- Exact Fourier recovery for a real velocity component on the canonical carrier. -/
theorem lowNormalQuarterAxisRealSchwartz_fourier_component
    (ρ : ℝ) (hρ : 0 < ρ) (j : Axis3) :
    𝓕 (PrimeTensor.Bridge.Euclidean.h3SchwartzComplexify
      (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j)) =
    lowNormalQuarterAxisFourierComponent ρ hρ j := by
  rw [lowNormalQuarterAxisRealSchwartz_complexify_eq_inverse]
  exact FourierTransform.fourier_fourierInv_eq _

/-- The complete canonical-axis Fourier polarization equals the original
explicit Fin-three packet after exact reindexing of BOTH domain and range. -/
theorem lowNormalQuarterAxisRealSchwartz_fourier_vector
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : CanonicalE) :
    (fun j : Axis3 =>
      𝓕 (PrimeTensor.Bridge.Euclidean.h3SchwartzComplexify
        (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j)) ξ) =
    (fun j : Axis3 =>
      lowNormalQuarterWeightedFourier
        (lowNormalQuarterEvenWindow ρ hρ)
        (fun i : Fin 3 => ξ (axes i)) (axes.symm j)) := by
  funext j
  rw [lowNormalQuarterAxisRealSchwartz_fourier_component]
  exact lowNormalQuarterAxisFourierComponent_apply ρ hρ j ξ

/-- Spectral solenoidality transferred to the canonical axis carrier. -/
theorem lowNormalQuarterAxisRealSchwartz_fourier_divergence
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : CanonicalE) :
    mixedDot (WithLp.ofLp ξ)
      (fun j : Axis3 =>
        𝓕 (PrimeTensor.Bridge.Euclidean.h3SchwartzComplexify
          (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j)) ξ) = 0 := by
  rw [lowNormalQuarterAxisRealSchwartz_fourier_vector]
  let w := lowNormalQuarterEvenWindow ρ hρ
  let q : Fin 3 → ℝ := fun i => ξ (axes i)
  change (∑ j : Axis3,
    ((WithLp.ofLp ξ j : ℝ) : ℂ) *
      lowNormalQuarterWeightedFourier w q (axes.symm j)) = 0
  have hReindex :
      (∑ j : Axis3,
        ((WithLp.ofLp ξ j : ℝ) : ℂ) *
          lowNormalQuarterWeightedFourier w q (axes.symm j)) =
      ∑ i : Fin 3, (q i : ℂ) * lowNormalQuarterWeightedFourier w q i := by
    simpa only [q] using
      (Fintype.sum_equiv axes
        (fun i : Fin 3 => (q i : ℂ) * lowNormalQuarterWeightedFourier w q i)
        (fun j : Axis3 => ((WithLp.ofLp ξ j : ℝ) : ℂ) *
          lowNormalQuarterWeightedFourier w q (axes.symm j))
        (fun i => by simp only [Equiv.symm_apply_apply]; rfl)).symm
  rw [hReindex]
  exact lowNormalQuarterWindowedFourier_divergence ρ hρ q

/-- The canonical REAL velocity is actually divergence free in Euclidean
physical coordinates, not merely divergence free in Fourier space. -/
theorem lowNormalQuarterAxisRealSchwartz_physical_divergence
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ x : CanonicalE,
      ∑ j : Axis3,
        fderiv ℝ
          (PrimeTensor.Bridge.Euclidean.h3SchwartzComplexify
            (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j))
          x (PrimeTensor.Bridge.Euclidean.h3FourierAxisDirection j) = 0 := by
  let F : Axis3 → 𝓢(CanonicalE, ℂ) := fun j =>
    PrimeTensor.Bridge.Euclidean.h3SchwartzComplexify
      (lowNormalQuarterAxisRealSchwartzComponent ρ hρ j)
  have hFourierZero :
      𝓕 (PrimeTensor.Bridge.Euclidean.h3SchwartzDivergence F) = 0 := by
    ext ξ
    rw [PrimeTensor.Bridge.Euclidean.h3SchwartzDivergence_fourier
      F (WithLp.ofLp ξ)]
    have hDiv :
        mixedDot (WithLp.ofLp ξ)
          (PrimeTensor.Bridge.Euclidean.h3SchwartzTriadPolarization F
            (WithLp.ofLp ξ)) = 0 := by
      change mixedDot (WithLp.ofLp ξ)
        (fun j : Axis3 => 𝓕 (F j) ξ) = 0
      exact lowNormalQuarterAxisRealSchwartz_fourier_divergence ρ hρ ξ
    rw [hDiv]
    simp
  have hPhysicalZero : PrimeTensor.Bridge.Euclidean.h3SchwartzDivergence F = 0 := by
    have h := congrArg
      (fun G : 𝓢(CanonicalE, ℂ) => (𝓕⁻ G : 𝓢(CanonicalE, ℂ)))
      hFourierZero
    simpa using h
  intro x
  have hx := congrArg (fun G : 𝓢(CanonicalE, ℂ) => G x) hPhysicalZero
  simpa only [PrimeTensor.Bridge.Euclidean.h3SchwartzDivergence_apply,
    zero_apply] using hx

end
end PrimeTensor.FirstMonomialTriad
