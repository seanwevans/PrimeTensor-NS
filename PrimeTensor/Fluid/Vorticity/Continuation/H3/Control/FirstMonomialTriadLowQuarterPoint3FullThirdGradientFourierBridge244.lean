import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalPhaseOrbit244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadFourier
import Mathlib.Tactic

/-!
# Exact seven-derivative Fourier bridge for the *gradient* part of H3 transport

The existing project theorem `h3Schwartz_firstMonomial_integral_eq_triad`
covers the 3+2+2 interpolation terms, not the four 3+3+1 gradient terms.
We apply the actual Schwartz Fourier product/convolution identity to three
third-, third-, and first-order derivatives. This constructs the weighted
frequency kernel on the true Euclidean carrier and proves its integrability,
including the exact `(2πi)^7` phase. The four gradient patterns are retained
individually, with the factor two from the physical energy pairing.

Unlike the finite polynomial phase-orbit result, this is an identity between
actual absolutely convergent Schwartz integrals. It does NOT yet establish
localization of a Hermitian divergence-free packet or noncancellation of the
full physical integral: those require additional proofs.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv FourierTransform

noncomputable section
set_option maxHeartbeats 800000

private abbrev V3 := H3FourierPoint3
private abbrev A3 := PrimeTensor.Axis Depth.three

noncomputable local instance axisFintypeGradientFourier244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- One true 3+3+1 Fourier integrand at frequencies (p,q,r), q=-p-r.
Each derivative direction remains explicit; neither an artificial symbol
nor a sign convention is substituted for the actual Fourier transform. -/
def thirdGradientSchwartzKernel244
    (f g h : SchwartzMap V3 ℂ)
    (a b c d e k v : V3) (z : V3 × V3) : ℂ :=
  let p := z.1
  let q := -(z.1 + z.2)
  let r := z.2
  (((((inner ℝ p a : ℂ) * (inner ℝ p b : ℂ) *
       (inner ℝ p c : ℂ)) * (𝓕 f) p) *
      (((inner ℝ q d : ℂ) * (inner ℝ q e : ℂ) *
        (inner ℝ q k : ℂ)) * (𝓕 g) q)) *
      ((inner ℝ r v : ℂ) * (𝓕 h) r))

/-- Absolute convergence of the exact seven-derivative gradient kernel.
The proof uses Schwartz stability under *seven* frequency multipliers. -/
theorem thirdGradientSchwartzKernel_integrable244
    (f g h : SchwartzMap V3 ℂ)
    (a b c d e k v : V3) :
    Integrable (thirdGradientSchwartzKernel244 f g h a b c d e k v)
      (volume.prod volume) := by
  let F := h3Schwartz_frequencyWeight a
    (h3Schwartz_frequencyWeight b (h3Schwartz_frequencyWeight c (𝓕 f)))
  let G := h3Schwartz_frequencyWeight d
    (h3Schwartz_frequencyWeight e (h3Schwartz_frequencyWeight k (𝓕 g)))
  let H := h3Schwartz_frequencyWeight v (𝓕 h)
  have hi := h3Schwartz_triad_integrable F G H
  apply hi.congr
  filter_upwards with z
  simp only [F, G, H, thirdGradientSchwartzKernel244,
    h3Schwartz_frequencyWeight_apply]
  ring

/-- The missing Fourier theorem for the 3+3+1 gradient structure. The
project's actual triple-product Fourier transform and directional-derivative
multiplier give the same odd seventh power as the interpolation channel. -/
theorem thirdGradientSchwartz_integral_eq_triad244
    (f g h : SchwartzMap V3 ℂ)
    (a b c d e k v : V3) :
    (∫ x : V3,
      (((∂_{a} (∂_{b} (∂_{c} f))) x) *
        ((∂_{d} (∂_{e} (∂_{k} g))) x)) *
        ((∂_{v} h) x)) =
      (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
        ∫ z : V3 × V3,
          thirdGradientSchwartzKernel244 f g h a b c d e k v z
          ∂volume.prod volume := by
  rw [h3Schwartz_triple_integral_eq_triad]
  calc
    _ = ∫ z : V3 × V3,
      (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
        thirdGradientSchwartzKernel244 f g h a b c d e k v z
        ∂volume.prod volume := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [h3Schwartz_fourier_lineDeriv_apply]
      unfold thirdGradientSchwartzKernel244
      ring
    _ = _ := integral_const_mul _ _

/-- Physical factor two is retained in the four-term complex Schwartz
energy pairing; the mixed products have their original transport indices. -/
private abbrev gradJet3C244 (u : A3 → SchwartzMap V3 ℂ)
    (j i k l : A3) : SchwartzMap V3 ℂ :=
  ∂_{h3FourierAxisDirection i}
    (∂_{h3FourierAxisDirection k}
      (∂_{h3FourierAxisDirection l} (u j)))

private abbrev gradJet1C244 (u : A3 → SchwartzMap V3 ℂ)
    (j r : A3) : SchwartzMap V3 ℂ :=
  ∂_{h3FourierAxisDirection r} (u j)

noncomputable def thirdGradientSchwartzAxisComplex244
    (u : A3 → SchwartzMap V3 ℂ) (j i k l r : A3) : ℂ :=
  2 * (∫ x : V3,
    (gradJet3C244 u j i k l x * gradJet3C244 u r i k l x) *
      gradJet1C244 u j r x) +
  2 * (∫ x : V3,
    (gradJet3C244 u j i k l x * gradJet3C244 u j i k r x) *
      gradJet1C244 u r l x) +
  2 * (∫ x : V3,
    (gradJet3C244 u j i k l x * gradJet3C244 u j i r l x) *
      gradJet1C244 u r k x) +
  2 * (∫ x : V3,
    (gradJet3C244 u j i k l x * gradJet3C244 u j r k l x) *
      gradJet1C244 u r i x)

noncomputable def thirdGradientSchwartzAxisFourier244
    (u : A3 → SchwartzMap V3 ℂ) (j i k l r : A3) : ℂ :=
  2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
    ((∫ z : V3 × V3,
      thirdGradientSchwartzKernel244 (u j) (u r) (u j)
        (h3FourierAxisDirection i) (h3FourierAxisDirection k)
        (h3FourierAxisDirection l) (h3FourierAxisDirection i)
        (h3FourierAxisDirection k) (h3FourierAxisDirection l)
        (h3FourierAxisDirection r) z ∂volume.prod volume) +
     (∫ z : V3 × V3,
      thirdGradientSchwartzKernel244 (u j) (u j) (u r)
        (h3FourierAxisDirection i) (h3FourierAxisDirection k)
        (h3FourierAxisDirection l) (h3FourierAxisDirection i)
        (h3FourierAxisDirection k) (h3FourierAxisDirection r)
        (h3FourierAxisDirection l) z ∂volume.prod volume) +
     (∫ z : V3 × V3,
      thirdGradientSchwartzKernel244 (u j) (u j) (u r)
        (h3FourierAxisDirection i) (h3FourierAxisDirection k)
        (h3FourierAxisDirection l) (h3FourierAxisDirection i)
        (h3FourierAxisDirection r) (h3FourierAxisDirection l)
        (h3FourierAxisDirection k) z ∂volume.prod volume) +
     (∫ z : V3 × V3,
      thirdGradientSchwartzKernel244 (u j) (u j) (u r)
        (h3FourierAxisDirection i) (h3FourierAxisDirection k)
        (h3FourierAxisDirection l) (h3FourierAxisDirection r)
        (h3FourierAxisDirection k) (h3FourierAxisDirection l)
        (h3FourierAxisDirection i) z ∂volume.prod volume))

/-- A FOUR-term actual complex Schwartz energy pairing is precisely its
four phase-correct Fourier integrals. The seven-derivative sign is not guessed. -/
theorem thirdGradientSchwartzAxisComplex_eq_fourier244
    (u : A3 → SchwartzMap V3 ℂ) (j i k l r : A3) :
    thirdGradientSchwartzAxisComplex244 u j i k l r =
      thirdGradientSchwartzAxisFourier244 u j i k l r := by
  unfold thirdGradientSchwartzAxisComplex244
    thirdGradientSchwartzAxisFourier244 gradJet3C244 gradJet1C244
  rw [thirdGradientSchwartz_integral_eq_triad244 (u j) (u r) (u j)
        (h3FourierAxisDirection i) (h3FourierAxisDirection k)
        (h3FourierAxisDirection l) (h3FourierAxisDirection i)
        (h3FourierAxisDirection k) (h3FourierAxisDirection l)
        (h3FourierAxisDirection r),
      thirdGradientSchwartz_integral_eq_triad244 (u j) (u j) (u r)
        (h3FourierAxisDirection i) (h3FourierAxisDirection k)
        (h3FourierAxisDirection l) (h3FourierAxisDirection i)
        (h3FourierAxisDirection k) (h3FourierAxisDirection r)
        (h3FourierAxisDirection l),
      thirdGradientSchwartz_integral_eq_triad244 (u j) (u j) (u r)
        (h3FourierAxisDirection i) (h3FourierAxisDirection k)
        (h3FourierAxisDirection l) (h3FourierAxisDirection i)
        (h3FourierAxisDirection r) (h3FourierAxisDirection l)
        (h3FourierAxisDirection k),
      thirdGradientSchwartz_integral_eq_triad244 (u j) (u j) (u r)
        (h3FourierAxisDirection i) (h3FourierAxisDirection k)
        (h3FourierAxisDirection l) (h3FourierAxisDirection r)
        (h3FourierAxisDirection k) (h3FourierAxisDirection l)
        (h3FourierAxisDirection i)]
  ring

/-- Exact complex Fourier bridge for the *entire* gradient transport axis
aggregate, with all five 3-component index sums and no lost coefficients. -/
noncomputable def thirdGradientSchwartzTotalComplex244
    (u : A3 → SchwartzMap V3 ℂ) : ℂ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
    thirdGradientSchwartzAxisComplex244 u j i k l r

noncomputable def thirdGradientFourierTotalComplex244
    (u : A3 → SchwartzMap V3 ℂ) : ℂ :=
  ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
    thirdGradientSchwartzAxisFourier244 u j i k l r

theorem thirdGradientSchwartzTotalComplex_eq_fourier244
    (u : A3 → SchwartzMap V3 ℂ) :
    thirdGradientSchwartzTotalComplex244 u =
      thirdGradientFourierTotalComplex244 u := by
  unfold thirdGradientSchwartzTotalComplex244 thirdGradientFourierTotalComplex244
  simp_rw [thirdGradientSchwartzAxisComplex_eq_fourier244]

end
end PrimeTensor.FirstMonomialTriad
