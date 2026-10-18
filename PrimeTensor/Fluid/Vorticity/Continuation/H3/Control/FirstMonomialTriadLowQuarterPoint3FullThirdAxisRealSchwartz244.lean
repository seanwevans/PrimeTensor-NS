import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdAxisInverseFourier244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterCanonicalAxisReal
import Mathlib.Tactic

/-!
# Real-valued physical realization of the full-third axis Hermitian packet

The six-frequency, exactly solenoidal, compactly supported Hermitian Fourier
profile has already been constructed on `Axis Depth.three` and transported to
`H3FourierPoint3` by an exact Schwartz inverse-Fourier bridge.  Here the
previously proved canonical-axis Hermitian-to-real Fourier theorem upgrades
its complex inverse to a real Schwartz velocity with no new reality axiom.

The Fourier transform of the complexification is exactly the specified packet.
We also transfer the pointwise spectral divergence identity to the *actual*
physical Schwartz divergence, using Fourier inversion and injectivity.

This does NOT evaluate the complete third-order transport coefficient of the
constructed velocity.  In particular, a negative integral for one labelled
local sector does not yet imply noncancellation of all twelve coherent sectors.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped SchwartzMap FourierTransform ComplexConjugate Topology BigOperators LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdReal244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The actual Hilbert-frequency scalar spectrum satisfies the reality
involution pointwise, before any inverse transform is taken. -/
theorem thirdFullAxisHilbertFourierComponent_hermitian244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (j : A3) (ξ : V3) :
    thirdFullAxisHilbertFourierComponent244 ρ hρ A B C j (-ξ) =
      star (thirdFullAxisHilbertFourierComponent244 ρ hρ A B C j ξ) := by
  simp only [thirdFullAxisHilbertFourierComponent_apply244, WithLp.ofLp_neg]
  exact congrFun
    (thirdFullAxisSixFourierPacket_reality244 ρ hρ A B C (WithLp.ofLp ξ)) j

/-- No a.e. qualification: every spatial Schwartz value of the inverse
Fourier component has vanishing imaginary part. -/
theorem thirdFullAxisInverseSchwartz_im_zero244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (j : A3) (x : V3) :
    (thirdFullAxisInverseSchwartzComponent244 ρ hρ A B C j x).im = 0 := by
  exact lowNormalQuarterAxisHermitianSchwartz_fourierInv_im_zero
    (thirdFullAxisHilbertFourierComponent244 ρ hρ A B C j)
    (thirdFullAxisHilbertFourierComponent_hermitian244 ρ hρ A B C j) x

/-- The concrete real-valued Schwartz velocity components produced from
the prescribed full-third complex Fourier spectrum. -/
noncomputable def thirdFullAxisRealSchwartzComponent244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (j : A3) :
    𝓢(V3, ℝ) :=
  (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM)
    (thirdFullAxisInverseSchwartzComponent244 ρ hρ A B C j)

@[simp] theorem thirdFullAxisRealSchwartzComponent_apply244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244)
    (j : A3) (x : V3) :
    thirdFullAxisRealSchwartzComponent244 ρ hρ A B C j x =
      (thirdFullAxisInverseSchwartzComponent244 ρ hρ A B C j x).re := rfl

/-- Complexifying each real spatial velocity component recovers the entire
inverse-Fourier Schwartz function, not merely its real part a.e. -/
theorem thirdFullAxisRealSchwartz_complexify_eq_inverse244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (j : A3) :
    h3SchwartzComplexify
      (thirdFullAxisRealSchwartzComponent244 ρ hρ A B C j) =
      thirdFullAxisInverseSchwartzComponent244 ρ hρ A B C j := by
  ext x
  change (((thirdFullAxisInverseSchwartzComponent244 ρ hρ A B C j x).re : ℝ) : ℂ) =
    thirdFullAxisInverseSchwartzComponent244 ρ hρ A B C j x
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simp only [Complex.ofReal_im]
    exact (thirdFullAxisInverseSchwartz_im_zero244 ρ hρ A B C j x).symm

/-- EXACT Schwartz Fourier reconstruction from the real physical velocity. -/
theorem thirdFullAxisRealSchwartz_fourier_component244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (j : A3) :
    𝓕 (h3SchwartzComplexify
      (thirdFullAxisRealSchwartzComponent244 ρ hρ A B C j)) =
      thirdFullAxisHilbertFourierComponent244 ρ hρ A B C j := by
  rw [thirdFullAxisRealSchwartz_complexify_eq_inverse244]
  exact thirdFullAxisInverseSchwartz_fourier_component244 ρ hρ A B C j

/-- The full THREE-component real Schwartz velocity: a genuine velocity
family, not an abstract collection of Fourier amplitudes. -/
noncomputable def thirdFullAxisRealSchwartzVelocity244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) : A3 → 𝓢(V3, ℝ) :=
  fun j => thirdFullAxisRealSchwartzComponent244 ρ hρ A B C j

/-- The real velocity's complexified Fourier transform is IDENTICAL to the
prescribed Hermitian six-window frequency field on every axis and frequency. -/
theorem thirdFullAxisRealSchwartz_fourier_vector244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (ξ : V3) :
    (fun j : A3 =>
      𝓕 (h3SchwartzComplexify
        (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C j)) ξ) =
      thirdFullAxisSixFourierPacket244 ρ hρ A B C (WithLp.ofLp ξ) := by
  funext j
  change 𝓕 (h3SchwartzComplexify
    (thirdFullAxisRealSchwartzComponent244 ρ hρ A B C j)) ξ = _
  rw [thirdFullAxisRealSchwartz_fourier_component244]
  exact thirdFullAxisHilbertFourierComponent_apply244 ρ hρ A B C j ξ

/-- The REAL spatial Schwartz velocity obeys zero Fourier divergence at
all frequencies, with precisely the true axis-index contraction. -/
theorem thirdFullAxisRealSchwartz_fourier_divergence244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (ξ : V3) :
    mixedDot (WithLp.ofLp ξ)
      (fun j : A3 =>
        𝓕 (h3SchwartzComplexify
          (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C j)) ξ) = 0 := by
  rw [thirdFullAxisRealSchwartz_fourier_vector244]
  change thirdFullAxisComplexDot244 (WithLp.ofLp ξ)
    (thirdFullAxisSixFourierPacket244 ρ hρ A B C (WithLp.ofLp ξ)) = 0
  exact thirdFullAxisSixFourierPacket_solenoidal244 ρ hρ A B C (WithLp.ofLp ξ)

/-- The actual spatial vector has zero Euclidean divergence at EVERY point.
The conclusion follows by the precise Schwartz divergence Fourier multiplier
and inverse-Fourier injectivity, not from a formal solenoidal declaration. -/
theorem thirdFullAxisRealSchwartz_physical_divergence244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    ∀ x : V3,
      ∑ j : A3,
        fderiv ℝ
          (h3SchwartzComplexify
            (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C j))
          x (h3FourierAxisDirection j) = 0 := by
  let F : A3 → 𝓢(V3, ℂ) := fun j =>
    h3SchwartzComplexify (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C j)
  have hFourierZero : 𝓕 (h3SchwartzDivergence F) = 0 := by
    ext ξ
    rw [h3SchwartzDivergence_fourier F (WithLp.ofLp ξ)]
    have hDiv :
        mixedDot (WithLp.ofLp ξ)
          (h3SchwartzTriadPolarization F (WithLp.ofLp ξ)) = 0 := by
      change mixedDot (WithLp.ofLp ξ)
        (fun j : A3 => 𝓕 (F j) ξ) = 0
      exact thirdFullAxisRealSchwartz_fourier_divergence244 ρ hρ A B C ξ
    rw [hDiv]
    simp
  have hPhysicalZero : h3SchwartzDivergence F = 0 := by
    have h := congrArg
      (fun G : 𝓢(V3, ℂ) => (𝓕⁻ G : 𝓢(V3, ℂ)))
      hFourierZero
    simpa using h
  intro x
  have hx := congrArg (fun G : 𝓢(V3, ℂ) => G x) hPhysicalZero
  simpa only [h3SchwartzDivergence_apply, zero_apply] using hx

end
end PrimeTensor.FirstMonomialTriad
