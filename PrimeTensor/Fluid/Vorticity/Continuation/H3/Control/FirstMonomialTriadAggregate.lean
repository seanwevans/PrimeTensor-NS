import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadFourier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fourier.Derivative

/-!
# The full Schwartz first-monomial aggregate and shell cancellation

Work on the project's Euclidean Fourier carrier. Sum all coordinate slots,
identify their polynomial with the existing triad kernel, and exchange the
two outer frequencies in the product measure. The pairing factor two cancels
the symmetrization denominator. The result is a shell-difference identity,
not a sign estimate or a continuation theorem.
-/

namespace PrimeTensor.Bridge.Euclidean

open MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3TriadAggregate (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

local notation "A3" => PrimeTensor.Axis Depth.three
local notation "V3" => H3FourierPoint3

/-- Fourier polarization on the coordinate carrier used by the algebraic identity. -/
def h3SchwartzTriadPolarization (u : A3 → SchwartzMap V3 ℂ)
    (p : A3 → ℝ) (j : A3) : ℂ := 𝓕 (u j) (WithLp.toLp 2 p)

def h3SchwartzTriadKernel (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) : ℂ :=
  FirstMonomialTriad.amplitudeKernel (h3SchwartzTriadPolarization u)
    (WithLp.ofLp z.1, WithLp.ofLp z.2)

def h3SchwartzTriadShellKernel (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) : ℂ :=
  FirstMonomialTriad.shellKernel (h3SchwartzTriadPolarization u)
    (WithLp.ofLp z.1, WithLp.ofLp z.2)

/-- One coordinate slot of the first monomial, in frequency space. -/
def h3SchwartzFirstMonomialSlotKernel (u : A3 → SchwartzMap V3 ℂ)
    (i k l v j : A3) : V3 × V3 → ℂ :=
  h3FirstMonomialSchwartzKernel (u j) (u v) (u j)
    (h3FourierAxisDirection i) (h3FourierAxisDirection k)
    (h3FourierAxisDirection l) (h3FourierAxisDirection v)

theorem h3SchwartzTriadKernel_eq_sum (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) :
    h3SchwartzTriadKernel u z =
      ∑ i, ∑ k, ∑ l, ∑ v, ∑ j, h3SchwartzFirstMonomialSlotKernel u i k l v j z := by
  classical
  rw [h3SchwartzTriadKernel, FirstMonomialTriad.amplitudeKernel_eq_coordinate_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro j _
  simp only [h3SchwartzFirstMonomialSlotKernel, h3FirstMonomialSchwartzKernel,
    inner_h3FourierAxisDirection]
  rfl

theorem h3SchwartzFirstMonomialSlotKernel_integrable (u : A3 → SchwartzMap V3 ℂ)
    (i k l v j : A3) :
    Integrable (h3SchwartzFirstMonomialSlotKernel u i k l v j) (volume.prod volume) :=
  h3FirstMonomialSchwartzKernel_integrable _ _ _ _ _ _ _

theorem h3SchwartzTriadKernel_integrable (u : A3 → SchwartzMap V3 ℂ) :
    Integrable (h3SchwartzTriadKernel u) (volume.prod volume) := by
  classical
  have hs : Integrable (fun z : V3 × V3 =>
      ∑ i, ∑ k, ∑ l, ∑ v, ∑ j, h3SchwartzFirstMonomialSlotKernel u i k l v j z)
      (volume.prod volume) := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro k _
    apply integrable_finsetSum
    intro l _
    apply integrable_finsetSum
    intro v _
    apply integrable_finsetSum
    intro j _
    exact h3SchwartzFirstMonomialSlotKernel_integrable u i k l v j
  exact hs.congr (Filter.Eventually.of_forall (fun z =>
    (h3SchwartzTriadKernel_eq_sum u z).symm))

/-- The finite coordinate sum commutes with the absolutely convergent integral. -/
theorem h3SchwartzTriadKernel_integral_eq_sum (u : A3 → SchwartzMap V3 ℂ) :
    (∫ z, h3SchwartzTriadKernel u z ∂volume.prod volume) =
      ∑ i, ∑ k, ∑ l, ∑ v, ∑ j,
        ∫ z, h3SchwartzFirstMonomialSlotKernel u i k l v j z ∂volume.prod volume := by
  classical
  have h4 (i k l v : A3) := integrable_finsetSum Finset.univ
    (fun j _ => h3SchwartzFirstMonomialSlotKernel_integrable u i k l v j)
  have h3 (i k l : A3) := integrable_finsetSum Finset.univ (fun v _ => h4 i k l v)
  have h2 (i k : A3) := integrable_finsetSum Finset.univ (fun l _ => h3 i k l)
  have h1 (i : A3) := integrable_finsetSum Finset.univ (fun k _ => h2 i k)
  simp_rw [h3SchwartzTriadKernel_eq_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => h1 i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun k _ => h2 i k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finsetSum Finset.univ (fun l _ => h3 i k l)]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_finsetSum Finset.univ (fun v _ => h4 i k l v)]
  apply Finset.sum_congr rfl
  intro v _
  exact integral_finsetSum Finset.univ
    (fun j _ => h3SchwartzFirstMonomialSlotKernel_integrable u i k l v j)

/-- A physical Schwartz monomial slot on the Euclidean carrier. -/
def h3SchwartzFirstMonomialSlot (u : A3 → SchwartzMap V3 ℂ) (i k l v j : A3) : ℂ :=
  ∫ x, (((∂_{h3FourierAxisDirection i}
    (∂_{h3FourierAxisDirection k} (∂_{h3FourierAxisDirection l} (u j)))) x) *
    ((∂_{h3FourierAxisDirection k} (∂_{h3FourierAxisDirection l} (u v))) x)) *
    ((∂_{h3FourierAxisDirection i} (∂_{h3FourierAxisDirection v} (u j))) x)

/-- Complex first-monomial sum; the real energy pairing is twice its real part. -/
def h3SchwartzFirstMonomialAggregate (u : A3 → SchwartzMap V3 ℂ) : ℂ :=
  ∑ i, ∑ k, ∑ l, ∑ v, ∑ j, h3SchwartzFirstMonomialSlot u i k l v j

theorem h3SchwartzFirstMonomialAggregate_eq_triad (u : A3 → SchwartzMap V3 ℂ) :
    h3SchwartzFirstMonomialAggregate u =
      (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
        ∫ z, h3SchwartzTriadKernel u z ∂volume.prod volume := by
  classical
  unfold h3SchwartzFirstMonomialAggregate
  rw [h3SchwartzTriadKernel_integral_eq_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro j _
  exact h3Schwartz_firstMonomial_integral_eq_triad _ _ _ _ _ _ _

/-- Incompressibility gives the shell identity pointwise on Euclidean frequencies. -/
theorem h3SchwartzTriadKernel_add_swap (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ q : A3 → ℝ, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0)
    (z : V3 × V3) :
    h3SchwartzTriadKernel u z + h3SchwartzTriadKernel u z.swap =
      h3SchwartzTriadShellKernel u z :=
  FirstMonomialTriad.amplitudeKernel_add_swap _ hDiv
    (WithLp.ofLp z.1, WithLp.ofLp z.2)

theorem h3SchwartzTriadShellKernel_integrable (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ q : A3 → ℝ, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    Integrable (h3SchwartzTriadShellKernel u) (volume.prod volume) :=
  ((h3SchwartzTriadKernel_integrable u).add
    (h3SchwartzTriadKernel_integrable u).swap).congr
    (Filter.Eventually.of_forall (h3SchwartzTriadKernel_add_swap u hDiv))

theorem h3SchwartzTriadShellKernel_integral (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ q : A3 → ℝ, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    (∫ z, h3SchwartzTriadShellKernel u z ∂volume.prod volume) =
      2 * ∫ z, h3SchwartzTriadKernel u z ∂volume.prod volume := by
  have hi := h3SchwartzTriadKernel_integrable u
  have hswap : Integrable (fun z : V3 × V3 => h3SchwartzTriadKernel u z.swap)
      (volume.prod volume) := hi.swap
  calc
    _ = ∫ z, h3SchwartzTriadKernel u z + h3SchwartzTriadKernel u z.swap
        ∂volume.prod volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z =>
        (h3SchwartzTriadKernel_add_swap u hDiv z).symm)
    _ = (∫ z, h3SchwartzTriadKernel u z ∂volume.prod volume) +
        ∫ z, h3SchwartzTriadKernel u z.swap ∂volume.prod volume :=
      integral_add hi hswap
    _ = _ := by
      rw [integral_prod_swap]
      ring

/-- The physical pairing's factor two cancels the exchange denominator exactly. -/
theorem h3SchwartzFirstMonomialAggregate_twice_eq_shell (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ q : A3 → ℝ, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    2 * h3SchwartzFirstMonomialAggregate u =
      (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
        ∫ z, h3SchwartzTriadShellKernel u z ∂volume.prod volume := by
  rw [h3SchwartzFirstMonomialAggregate_eq_triad, h3SchwartzTriadShellKernel_integral u hDiv]
  ring

/-- Signed shell formula for the real Schwartz first-monomial pairing. -/
theorem h3SchwartzFirstMonomialAggregate_twice_re_eq_shell_im
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ q : A3 → ℝ, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    2 * (h3SchwartzFirstMonomialAggregate u).re =
      (2 * Real.pi) ^ 7 *
        (∫ z, h3SchwartzTriadShellKernel u z ∂volume.prod volume).im := by
  have h := congrArg Complex.re (h3SchwartzFirstMonomialAggregate_twice_eq_shell u hDiv)
  rw [h3FirstMonomial_fourier_phase] at h
  have htwo_re : (2 : ℂ).re = 2 := rfl
  have htwo_im : (2 : ℂ).im = 0 := rfl
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    htwo_re, htwo_im] at h
  convert h using 1 <;> ring

end
end PrimeTensor.Bridge.Euclidean
