import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowSharpness

/-!
# Six-order symmetrization of the Schwartz triad integral

The six permutations of the momentum triad are realized by measurable
volume-preserving equivalences of the two free frequency variables.
Consequently the complete coefficient is integrable and its integral is
six times the ordered integral. This identifies the physical interpolation
with the imaginary part of the complete six-order integral.
-/

namespace PrimeTensor.Bridge.Euclidean

open MeasureTheory
open scoped BigOperators

noncomputable section

noncomputable local instance axisFintypeH3TriadSixIntegral (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

local notation "A3" => PrimeTensor.Axis Depth.three
local notation "V3" => H3FourierPoint3

private def h3TriadSwapEquiv : V3 × V3 ≃ᵐ V3 × V3 := MeasurableEquiv.prodComm

/-- In order: pqr, prq, qpr, qrp, rpq, rqp, with q=-(p+r). -/
def h3TriadPermutation : Fin 6 → (V3 × V3 ≃ᵐ V3 × V3) :=
  ![MeasurableEquiv.refl _, h3TriadMiddleEquiv,
    (h3TriadMiddleEquiv.trans h3TriadSwapEquiv).trans h3TriadMiddleEquiv,
    h3TriadMiddleEquiv.trans h3TriadSwapEquiv,
    h3TriadSwapEquiv.trans h3TriadMiddleEquiv, h3TriadSwapEquiv]

theorem h3TriadPermutation_preserving (k : Fin 6) :
    MeasurePreserving (h3TriadPermutation k) (volume.prod volume) (volume.prod volume) := by
  have hM := h3TriadMiddleEquiv_preserving
  have hS : MeasurePreserving h3TriadSwapEquiv (volume.prod volume) (volume.prod volume) :=
    Measure.measurePreserving_swap (μ := (volume : Measure V3)) (ν := (volume : Measure V3))
  fin_cases k
  · exact MeasurePreserving.id _
  · exact hM
  · exact hM.comp (hS.comp hM)
  · exact hS.comp hM
  · exact hM.comp hS
  · exact hS

/-- Sum over all six momentum-variable changes. -/
def h3TriadSixOrbit (K : V3 × V3 → ℂ) (z : V3 × V3) : ℂ :=
  ∑ k : Fin 6, K (h3TriadPermutation k z)

theorem h3TriadPermutation_integrable (K : V3 × V3 → ℂ)
    (hK : Integrable K (volume.prod volume)) (k : Fin 6) :
    Integrable (fun z => K (h3TriadPermutation k z)) (volume.prod volume) :=
  ((h3TriadPermutation_preserving k).integrable_comp hK.aestronglyMeasurable).mpr hK

theorem h3TriadSixOrbit_integrable (K : V3 × V3 → ℂ)
    (hK : Integrable K (volume.prod volume)) :
    Integrable (h3TriadSixOrbit K) (volume.prod volume) := by
  unfold h3TriadSixOrbit
  exact integrable_finsetSum Finset.univ (fun k _ => h3TriadPermutation_integrable K hK k)

theorem h3TriadPermutation_integral (K : V3 × V3 → ℂ) (k : Fin 6) :
    (∫ z, K (h3TriadPermutation k z) ∂volume.prod volume) =
      ∫ z, K z ∂volume.prod volume :=
  (h3TriadPermutation_preserving k).integral_comp (h3TriadPermutation k).measurableEmbedding K

theorem h3TriadSixOrbit_integral (K : V3 × V3 → ℂ)
    (hK : Integrable K (volume.prod volume)) :
    (∫ z, h3TriadSixOrbit K z ∂volume.prod volume) =
      6 * ∫ z, K z ∂volume.prod volume := by
  unfold h3TriadSixOrbit
  rw [integral_finsetSum Finset.univ (fun k _ => h3TriadPermutation_integrable K hK k)]
  simp only [h3TriadPermutation_integral]
  simp [nsmul_eq_mul]

/-- Actual complete coefficient, using the Fourier amplitudes of one field. -/
def h3SchwartzTriadSixKernel (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) : ℂ :=
  FirstMonomialTriad.sixOrderTriadCoefficient
    (WithLp.ofLp z.1) (WithLp.ofLp (-(z.1 + z.2))) (WithLp.ofLp z.2)
    (h3SchwartzTriadPolarization u (WithLp.ofLp z.1))
    (h3SchwartzTriadPolarization u (WithLp.ofLp (-(z.1 + z.2))))
    (h3SchwartzTriadPolarization u (WithLp.ofLp z.2))

private theorem h3SchwartzTriadKernel_eq_ordered
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) :
    h3SchwartzTriadKernel u z = FirstMonomialTriad.orderedTriadCoefficient
      (WithLp.ofLp z.1) (WithLp.ofLp (-(z.1 + z.2))) (WithLp.ofLp z.2)
      (h3SchwartzTriadPolarization u (WithLp.ofLp z.1))
      (h3SchwartzTriadPolarization u (WithLp.ofLp (-(z.1 + z.2))))
      (h3SchwartzTriadPolarization u (WithLp.ofLp z.2)) := rfl

/-- The six changes of variables produce precisely the six ordered terms;
no divergence hypothesis is used for this identification. -/
theorem h3SchwartzTriadSixKernel_eq_orbit (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) :
    h3SchwartzTriadSixKernel u z = h3TriadSixOrbit (h3SchwartzTriadKernel u) z := by
  have h1 : -(z.1 + -(z.1 + z.2)) = z.2 := by abel
  have h2 : -(-(z.1 + z.2) + z.1) = z.2 := by abel
  have h3 : -(z.2 + -(z.1 + z.2)) = z.1 := by abel
  have h4 : -(-(z.1 + z.2) + z.2) = z.1 := by abel
  -- Ordinary `simp` evaluates the fixed Fin-6 permutation vector and
  -- the measurable-equivalence compositions. Unfold the product swap, but
  -- do NOT install global add_comm / add_left_comm / add_assoc simp rules.
  simp [h3SchwartzTriadSixKernel,
    FirstMonomialTriad.sixOrderTriadCoefficient,
    h3TriadSixOrbit, Fin.sum_univ_succ, h3TriadPermutation,
    h3TriadMiddleEquiv, h3TriadSwapEquiv,
    h3SchwartzTriadKernel_eq_ordered,
    MeasurableEquiv.prodComm, h1, h2, h3, h4] <;>
    ac_rfl

theorem h3SchwartzTriadSixKernel_integrable (u : A3 → SchwartzMap V3 ℂ) :
    Integrable (h3SchwartzTriadSixKernel u) (volume.prod volume) := by
  have h := h3TriadSixOrbit_integrable _ (h3SchwartzTriadKernel_integrable u)
  exact h.congr (Filter.Eventually.of_forall (fun z => (h3SchwartzTriadSixKernel_eq_orbit u z).symm))

theorem h3SchwartzTriadSixKernel_integral (u : A3 → SchwartzMap V3 ℂ) :
    (∫ z, h3SchwartzTriadSixKernel u z ∂volume.prod volume) =
      6 * ∫ z, h3SchwartzTriadKernel u z ∂volume.prod volume := by
  calc
    _ = ∫ z, h3TriadSixOrbit (h3SchwartzTriadKernel u) z ∂volume.prod volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (h3SchwartzTriadSixKernel_eq_orbit u)
    _ = _ := h3TriadSixOrbit_integral _ (h3SchwartzTriadKernel_integrable u)

theorem h3SchwartzTriadSixKernel_integral_eq_three_shell
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ q : A3 → ℝ, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    (∫ z, h3SchwartzTriadSixKernel u z ∂volume.prod volume) =
      3 * ∫ z, h3SchwartzTriadShellKernel u z ∂volume.prod volume := by
  rw [h3SchwartzTriadSixKernel_integral, h3SchwartzTriadShellKernel_integral u hDiv]
  ring

/-- The existing physical interpolation is the imaginary part of the
complete six-order integral, with no residual symmetrization denominator. -/
theorem h3PathCanonicalInterpolation_eq_six_integral_of_realSchwartz
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j, loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hDiv : ∀ x : Point3, ∑ j, spatial3.d j (loggedVelocityComponent u t j) x = 0) :
    thirdOrderInterpolationTransportSum u t = (2 * Real.pi)^7 *
      (∫ z, h3SchwartzTriadSixKernel (fun j => h3SchwartzComplexify (f j)) z
        ∂volume.prod volume).im := by
  have hd := h3SchwartzTriadPolarization_divergence_zero _
    (h3TriadComplexify_physical_divergence u t f hRealization hDiv)
  rw [h3PathCanonicalInterpolation_eq_shell_of_realSchwartz hH3 hClass ht f hRealization hDiv,
    h3SchwartzTriadSixKernel_integral_eq_three_shell _ hd]
  have h3re : (3 : ℂ).re = 3 := rfl
  have h3im : (3 : ℂ).im = 0 := rfl
  simp only [Complex.mul_im, h3re, h3im, zero_mul, add_zero]
  ring

end
end PrimeTensor.Bridge.Euclidean
