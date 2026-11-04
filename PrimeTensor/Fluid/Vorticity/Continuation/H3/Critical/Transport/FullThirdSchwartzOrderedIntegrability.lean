import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSchwartzSixOrbitIntegral
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGradientFourierBridge244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadFourier
import Mathlib.Tactic

/-!
# Unconditional absolute integrability of the corrected full-third ordered Fourier kernel

The complex six-order radial-flux theorem was previously conditional on the
integrability of the corrected ordered kernel. Here this hypothesis is proved
for *every* complex Schwartz velocity: expand its two polarization contractions
and three frequency dots into the actual five finite physical-axis sums.
Each of the resulting summands is exactly one already-proved absolutely
integrable Schwartz Fourier triple: the 3+3+1 gradient kernel or the
3+2+2 interpolation kernel. In particular, no spectral support cutoff or
frequency-envelope premise is added.

The unconditional six-orbit flux integral is the direct consequence. This
file does not yet identify it with the five-index *physical* signed H3
commutator; that normalization is a separate last equality to formalize.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeOrderedSchwartz244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The exact finite sum of seven-derivative Fourier integrands. The first and
third terms are 3+3+1; the middle term is 3+2+2. The coefficients three are
those already present in the fully corrected physical ordered symbol. -/
noncomputable def thirdFullSchwartzOrderedSevenKernel244
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) : ℂ :=
  ∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
    (thirdGradientSchwartzKernel244 (u j) (u m) (u j)
      (h3FourierAxisDirection i) (h3FourierAxisDirection k)
      (h3FourierAxisDirection l) (h3FourierAxisDirection i)
      (h3FourierAxisDirection k) (h3FourierAxisDirection l)
      (h3FourierAxisDirection m) z +
    3 * h3FirstMonomialSchwartzKernel (u j) (u m) (u j)
      (h3FourierAxisDirection l) (h3FourierAxisDirection i)
      (h3FourierAxisDirection k) (h3FourierAxisDirection m) z +
    3 * thirdGradientSchwartzKernel244 (u j) (u j) (u m)
      (h3FourierAxisDirection i) (h3FourierAxisDirection k)
      (h3FourierAxisDirection l) (h3FourierAxisDirection i)
      (h3FourierAxisDirection k) (h3FourierAxisDirection m)
      (h3FourierAxisDirection l) z)

/-- Unconditional integration of the actual seven-derivative finite sum. -/
theorem thirdFullSchwartzOrderedSevenKernel_integrable244
    (u : A3 → SchwartzMap V3 ℂ) :
    Integrable (thirdFullSchwartzOrderedSevenKernel244 u)
      (volume.prod volume) := by
  unfold thirdFullSchwartzOrderedSevenKernel244
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro m _
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro l _
  exact ((thirdGradientSchwartzKernel_integrable244 (u j) (u m) (u j)
    (h3FourierAxisDirection i) (h3FourierAxisDirection k)
    (h3FourierAxisDirection l) (h3FourierAxisDirection i)
    (h3FourierAxisDirection k) (h3FourierAxisDirection l)
    (h3FourierAxisDirection m)).add
    ((h3FirstMonomialSchwartzKernel_integrable (u j) (u m) (u j)
      (h3FourierAxisDirection l) (h3FourierAxisDirection i)
      (h3FourierAxisDirection k) (h3FourierAxisDirection m)).const_mul (3 : ℂ))).add
    ((thirdGradientSchwartzKernel_integrable244 (u j) (u j) (u m)
      (h3FourierAxisDirection i) (h3FourierAxisDirection k)
      (h3FourierAxisDirection l) (h3FourierAxisDirection i)
      (h3FourierAxisDirection k) (h3FourierAxisDirection m)
      (h3FourierAxisDirection l)).const_mul (3 : ℂ))

/-- Five independent physical-axis sums separate also over the complex
numbers; the earlier real lemma is not silently applied to Fourier data. -/
private theorem fullThirdFiveComplexIndependentSums244
    (f g h v w : A3 → ℂ) :
    (∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
      f j * g m * h i * v k * w l) =
      (∑ j : A3, f j) * (∑ m : A3, g m) *
        (∑ i : A3, h i) * (∑ k : A3, v k) *
        (∑ l : A3, w l) := by
  calc
    _ = ∑ j : A3, f j *
          (∑ m : A3, g m *
            (∑ i : A3, h i *
              (∑ k : A3, v k * (∑ l : A3, w l)))) := by
          simp only [Finset.mul_sum, mul_assoc]
    _ = (∑ j : A3, f j) *
          ((∑ m : A3, g m) *
            ((∑ i : A3, h i) *
              ((∑ k : A3, v k) * (∑ l : A3, w l)))) := by
          simp only [Finset.sum_mul]
    _ = _ := by ring

/-- Algebraic expansion of the corrected complex ordered physical symbol.
Every one of the 5 index sums is a genuine momentum or polarization
contraction, and none of the complex amplitudes are conjugated. -/
private theorem fullThirdComplexFiveCoordinateContraction244
    (p q r U V W : A3 → ℂ) :
    (∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
      ((U j * W j) * (r m * V m) * (p i * q i) *
        (p k * q k) * (p l * q l) +
       3 * ((U j * W j) * (r m * V m) * (p i * q i) *
        (p k * q k) * (p l * r l)) +
       3 * ((U j * V j) * (q m * W m) * (p i * q i) *
        (p k * q k) * (p l * r l)))) =
      ((∑ j : A3, U j * W j) * (∑ m : A3, r m * V m)) *
        ((∑ i : A3, p i * q i) ^ 3 +
          3 * (∑ i : A3, p i * q i) ^ 2 *
            (∑ l : A3, p l * r l)) +
      ((∑ j : A3, U j * V j) * (∑ m : A3, q m * W m)) *
        (3 * (∑ i : A3, p i * q i) ^ 2 *
          (∑ l : A3, p l * r l)) := by
  let f1 : A3 → A3 → A3 → A3 → A3 → ℂ :=
    fun j m i k l => (U j * W j) * (r m * V m) *
      (p i * q i) * (p k * q k) * (p l * q l)
  let f2 : A3 → A3 → A3 → A3 → A3 → ℂ :=
    fun j m i k l => (U j * W j) * (r m * V m) *
      (p i * q i) * (p k * q k) * (p l * r l)
  let f3 : A3 → A3 → A3 → A3 → A3 → ℂ :=
    fun j m i k l => (U j * V j) * (q m * W m) *
      (p i * q i) * (p k * q k) * (p l * r l)
  have h1 :
      (∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
        f1 j m i k l) =
      (∑ j : A3, U j * W j) * (∑ m : A3, r m * V m) *
        (∑ i : A3, p i * q i) ^ 3 := by
    dsimp only [f1]
    rw [fullThirdFiveComplexIndependentSums244]
    ring
  have h2 :
      (∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
        f2 j m i k l) =
      (∑ j : A3, U j * W j) * (∑ m : A3, r m * V m) *
        (∑ i : A3, p i * q i) ^ 2 *
        (∑ l : A3, p l * r l) := by
    dsimp only [f2]
    rw [fullThirdFiveComplexIndependentSums244]
    ring
  have h3 :
      (∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
        f3 j m i k l) =
      (∑ j : A3, U j * V j) * (∑ m : A3, q m * W m) *
        (∑ i : A3, p i * q i) ^ 2 *
        (∑ l : A3, p l * r l) := by
    dsimp only [f3]
    rw [fullThirdFiveComplexIndependentSums244]
    ring
  calc
    _ = (∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
          f1 j m i k l) +
        3 * (∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
          f2 j m i k l) +
        3 * (∑ j : A3, ∑ m : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
          f3 j m i k l) := by
      dsimp only [f1, f2, f3]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by rw [h1, h2, h3]; ring

/-- The corrected ordered symbol is precisely the five-index sum of the
PREVIOUSLY PROVED actual Schwartz seven-derivative Fourier integrands.
This is the formerly missing polynomial/analytic identification at the
ordered-kernel level, without a frozen polarization or fixed packet. -/
theorem thirdFullSchwartzComplexOrdered_eq_sevenKernel244
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) :
    thirdFullSchwartzComplexOrderedKernel244 u z =
      thirdFullSchwartzOrderedSevenKernel244 u z := by
  let p : A3 → ℂ := fun i => ((WithLp.ofLp z.1) i : ℂ)
  let q : A3 → ℂ := fun i => ((WithLp.ofLp (-(z.1 + z.2))) i : ℂ)
  let r : A3 → ℂ := fun i => ((WithLp.ofLp z.2) i : ℂ)
  let U : A3 → ℂ := h3SchwartzTriadPolarization u (WithLp.ofLp z.1)
  let V : A3 → ℂ := h3SchwartzTriadPolarization u (WithLp.ofLp (-(z.1 + z.2)))
  let W : A3 → ℂ := h3SchwartzTriadPolarization u (WithLp.ofLp z.2)
  have hOrdered : thirdFullSchwartzComplexOrderedKernel244 u z =
      ((∑ j : A3, U j * W j) * (∑ m : A3, r m * V m)) *
        ((∑ i : A3, p i * q i) ^ 3 +
          3 * (∑ i : A3, p i * q i) ^ 2 *
            (∑ l : A3, p l * r l)) +
      ((∑ j : A3, U j * V j) * (∑ m : A3, q m * W m)) *
        (3 * (∑ i : A3, p i * q i) ^ 2 *
          (∑ l : A3, p l * r l)) := by
    unfold thirdFullSchwartzComplexOrderedKernel244
      thirdFullComplexOrderedSymbol244 thirdFullComplexPolarizationDot244
    dsimp only [p, q, r, U, V, W]
    simp only [mixedDot, thirdTriadAxisDot244]
    push_cast
    ring
  have hOne (j m i k l : A3) :
      thirdGradientSchwartzKernel244 (u j) (u m) (u j)
          (h3FourierAxisDirection i) (h3FourierAxisDirection k)
          (h3FourierAxisDirection l) (h3FourierAxisDirection i)
          (h3FourierAxisDirection k) (h3FourierAxisDirection l)
          (h3FourierAxisDirection m) z +
        3 * h3FirstMonomialSchwartzKernel (u j) (u m) (u j)
          (h3FourierAxisDirection l) (h3FourierAxisDirection i)
          (h3FourierAxisDirection k) (h3FourierAxisDirection m) z +
        3 * thirdGradientSchwartzKernel244 (u j) (u j) (u m)
          (h3FourierAxisDirection i) (h3FourierAxisDirection k)
          (h3FourierAxisDirection l) (h3FourierAxisDirection i)
          (h3FourierAxisDirection k) (h3FourierAxisDirection m)
          (h3FourierAxisDirection l) z =
      (U j * W j) * (r m * V m) * (p i * q i) *
        (p k * q k) * (p l * q l) +
      3 * ((U j * W j) * (r m * V m) * (p i * q i) *
        (p k * q k) * (p l * r l)) +
      3 * ((U j * V j) * (q m * W m) * (p i * q i) *
        (p k * q k) * (p l * r l)) := by
    dsimp only [p, q, r, U, V, W]
    simp only [thirdGradientSchwartzKernel244,
      h3FirstMonomialSchwartzKernel, inner_h3FourierAxisDirection,
      h3SchwartzTriadPolarization, WithLp.toLp_ofLp]
    ring
  rw [hOrdered]
  unfold thirdFullSchwartzOrderedSevenKernel244
  simp_rw [hOne]
  exact (fullThirdComplexFiveCoordinateContraction244 p q r U V W).symm

/-- Unconditional absolute integrability of the CORRECTED COMPLEX ORDERED
H³ Fourier kernel for every complex Schwartz field. -/
theorem thirdFullSchwartzComplexOrderedKernel_integrable244
    (u : A3 → SchwartzMap V3 ℂ) :
    Integrable (thirdFullSchwartzComplexOrderedKernel244 u)
      (volume.prod volume) := by
  exact (thirdFullSchwartzOrderedSevenKernel_integrable244 u).congr
    (Filter.Eventually.of_forall (fun z =>
      (thirdFullSchwartzComplexOrdered_eq_sevenKernel244 u z).symm))

/-- For every complex Schwartz polarization field satisfying Fourier
incompressibility, the exact SIXTH-POWER radial energy flux is integrable
without any separate L1 hypothesis on its ordered kernel. -/
theorem thirdFullSchwartzComplexSixthPowerFlux_integrable244
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ ξ : A3 → ℝ,
      mixedDot ξ (h3SchwartzTriadPolarization u ξ) = 0) :
    Integrable (thirdFullSchwartzComplexSixthPowerFlux244 u)
      (volume.prod volume) :=
  thirdFullSchwartzComplexSixthPowerFlux_integrable_of_ordered244
    u hDiv (thirdFullSchwartzComplexOrderedKernel_integrable244 u)

/-- Unconditional (on integrability) exact six-to-one Schwartz Fourier flux
identity. Only Fourier incompressibility remains as a physical condition. -/
theorem thirdFullSchwartzComplexSixthPowerFlux_integral244
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ ξ : A3 → ℝ,
      mixedDot ξ (h3SchwartzTriadPolarization u ξ) = 0) :
    (∫ z : V3 × V3,
      thirdFullSchwartzComplexSixthPowerFlux244 u z
        ∂volume.prod volume) =
      6 * ∫ z : V3 × V3,
        thirdFullSchwartzComplexOrderedKernel244 u z
          ∂volume.prod volume := by
  exact thirdFullSchwartzComplexSixthPowerFlux_integral_eq_sixOrdered244
    u hDiv (thirdFullSchwartzComplexOrderedKernel_integrable244 u)

/-- The same assertion for EVERY real physically divergence-free Schwartz
velocity. No selected Fourier packets and no additional integrability
hypothesis are imposed. -/
theorem thirdFullRealSchwartz_sixthPowerFlux_integral244
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f) :
    (∫ z : V3 × V3,
      thirdFullSchwartzComplexSixthPowerFlux244
        (fun j => h3SchwartzComplexify (f j)) z
          ∂volume.prod volume) =
      6 * ∫ z : V3 × V3,
        thirdFullSchwartzComplexOrderedKernel244
          (fun j => h3SchwartzComplexify (f j)) z
          ∂volume.prod volume := by
  exact thirdFullRealSchwartz_sixthPowerFlux_integral_of_point3Solenoidal244
    f hDiv (thirdFullSchwartzComplexOrderedKernel_integrable244
      (fun j => h3SchwartzComplexify (f j)))

end
end PrimeTensor.FirstMonomialTriad
