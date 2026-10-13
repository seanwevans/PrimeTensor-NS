import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowOuter

/-!
# The full shell integral and physical first-monomial bound

Ordering the two outer radii covers every triad. The overlap has equal
radii and hence a zero shell kernel. Combining the two ordered estimates
gives 4 E3 M1, including comparable frequencies, and the physical identity
transfers it with its exact Fourier and interpolation constants.
-/

namespace PrimeTensor.Bridge.Euclidean

open MeasureTheory
open scoped BigOperators

noncomputable section

noncomputable local instance axisFintypeH3TriadGlobalBound (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

local notation "A3" => PrimeTensor.Axis Depth.three
local notation "V3" => H3FourierPoint3

def h3TriadThirdOrderEnergy (u : A3 → SchwartzMap V3 ℂ) : ℝ :=
  ∫ p, (‖p‖ ^ 3 * h3TriadSpectralAmplitude u p) ^ 2

def h3TriadFirstOrderMoment (u : A3 → SchwartzMap V3 ℂ) : ℝ :=
  ∫ q, ‖q‖ * h3TriadSpectralAmplitude u q

/-- The overlap of the two ordered outer regions contributes exactly zero. -/
theorem h3SchwartzTriadShellKernel_eq_zero_of_norm_eq
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) (h : ‖z.1‖ = ‖z.2‖) :
    h3SchwartzTriadShellKernel u z = 0 := by
  simp only [h3SchwartzTriadShellKernel, FirstMonomialTriad.shellKernel,
    FirstMonomialTriad.complexShellCoefficient, h3Triad_dot_eq_inner,
    real_inner_self_eq_norm_sq, h, sub_self, Complex.ofReal_zero, mul_zero, zero_mul]

/-- Exact two-sector decomposition; no boundary contribution is discarded. -/
theorem h3SchwartzTriadShellKernel_eq_ordered_sum
    (u : A3 → SchwartzMap V3 ℂ) (z : V3 × V3) :
    h3SchwartzTriadShellKernel u z =
      h3SchwartzTriadLowLeftKernel u 1 z + h3SchwartzTriadLowRightKernel u 1 z := by
  classical
  by_cases hp : ‖z.1‖ ≤ ‖z.2‖
  · by_cases hr : ‖z.2‖ ≤ ‖z.1‖
    · have hz := h3SchwartzTriadShellKernel_eq_zero_of_norm_eq u z (le_antisymm hp hr)
      simp [h3SchwartzTriadLowLeftKernel, h3SchwartzTriadLowRightKernel,
        h3TriadLowLeftSet, Set.indicator, hp, hr, hz]
    · simp [h3SchwartzTriadLowLeftKernel, h3SchwartzTriadLowRightKernel,
        h3TriadLowLeftSet, Set.indicator, hp, hr]
  · have hr : ‖z.2‖ ≤ ‖z.1‖ := le_of_lt (lt_of_not_ge hp)
    simp [h3SchwartzTriadLowLeftKernel, h3SchwartzTriadLowRightKernel,
      h3TriadLowLeftSet, Set.indicator, hp, hr]

theorem h3SchwartzTriadLowRightKernel_integrable
    (u : A3 → SchwartzMap V3 ℂ) (ε : ℝ)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    Integrable (h3SchwartzTriadLowRightKernel u ε) (volume.prod volume) := by
  have heq : h3SchwartzTriadLowRightKernel u ε =
      fun z => h3SchwartzTriadLowLeftKernel u ε z.swap :=
    funext (h3SchwartzTriadLowRightKernel_eq_swap u ε hDiv)
  rw [heq]
  exact (h3SchwartzTriadLowLeftKernel_integrable u ε hDiv).swap

/-- A global shell bound, including comparable-frequency interactions. -/
theorem h3SchwartzTriadShellKernel_integral_norm_le_energy_moment
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ q, FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0) :
    ‖∫ z, h3SchwartzTriadShellKernel u z ∂volume.prod volume‖ ≤
      4 * h3TriadThirdOrderEnergy u * h3TriadFirstOrderMoment u := by
  have hi := h3SchwartzTriadLowLeftKernel_integrable u 1 hDiv
  have hj := h3SchwartzTriadLowRightKernel_integrable u 1 hDiv
  have heq : (∫ z, h3SchwartzTriadShellKernel u z ∂volume.prod volume) =
      (∫ z, h3SchwartzTriadLowLeftKernel u 1 z ∂volume.prod volume) +
      ∫ z, h3SchwartzTriadLowRightKernel u 1 z ∂volume.prod volume := by
    calc
      _ = ∫ z, h3SchwartzTriadLowLeftKernel u 1 z + h3SchwartzTriadLowRightKernel u 1 z
          ∂volume.prod volume := by
        apply integral_congr_ae
        filter_upwards with z
        exact h3SchwartzTriadShellKernel_eq_ordered_sum u z
      _ = _ := integral_add hi hj
  rw [heq]
  calc
    _ ≤ ‖∫ z, h3SchwartzTriadLowLeftKernel u 1 z ∂volume.prod volume‖ +
        ‖∫ z, h3SchwartzTriadLowRightKernel u 1 z ∂volume.prod volume‖ := norm_add_le _ _
    _ ≤ (2 * 1 * h3TriadThirdOrderEnergy u * h3TriadFirstOrderMoment u) +
        (2 * 1 * h3TriadThirdOrderEnergy u * h3TriadFirstOrderMoment u) :=
      add_le_add (h3SchwartzTriadLowLeftKernel_integral_norm_le u 1 (by norm_num) hDiv)
        (h3SchwartzTriadLowRightKernel_integral_norm_le u 1 (by norm_num) hDiv)
    _ = _ := by ring

/-- The genuine physical aggregate satisfies the global estimate with the
Fourier phase factor retained. The real Schwartz realization is explicit. -/
theorem h3PathCanonicalFirstMonomialAggregate_abs_le_energy_moment
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j, loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hDiv : ∀ x : Point3, ∑ j, spatial3.d j (loggedVelocityComponent u t j) x = 0) :
    |h3PathCanonicalFirstMonomialAggregateAt u t| ≤
      4 * (2 * Real.pi) ^ 7 *
        h3TriadThirdOrderEnergy (fun j => h3SchwartzComplexify (f j)) *
        h3TriadFirstOrderMoment (fun j => h3SchwartzComplexify (f j)) := by
  let U := fun j => h3SchwartzComplexify (f j)
  have hFourier := h3SchwartzTriadPolarization_divergence_zero U
    (h3TriadComplexify_physical_divergence u t f hRealization hDiv)
  have hbound := h3SchwartzTriadShellKernel_integral_norm_le_energy_moment U hFourier
  have hphase : 0 ≤ (2 * Real.pi) ^ 7 := by positivity
  rw [h3PathCanonicalFirstMonomialAggregate_eq_shell_of_realSchwartz u t f hRealization hDiv,
    abs_mul, abs_of_nonneg hphase]
  change (2 * Real.pi) ^ 7 * |(∫ z, h3SchwartzTriadShellKernel U z ∂volume.prod volume).im| ≤ _
  calc
    _ ≤ (2 * Real.pi) ^ 7 * ‖∫ z, h3SchwartzTriadShellKernel U z ∂volume.prod volume‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) hphase
    _ ≤ (2 * Real.pi) ^ 7 * (4 * h3TriadThirdOrderEnergy U * h3TriadFirstOrderMoment U) :=
      mul_le_mul_of_nonneg_left hbound hphase
    _ = _ := by dsimp [U]; ring

/-- Recover the interpolation multiplicity three, giving the constant twelve. -/
theorem h3PathCanonicalInterpolation_abs_le_energy_moment
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j, loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hDiv : ∀ x : Point3, ∑ j, spatial3.d j (loggedVelocityComponent u t j) x = 0) :
    |thirdOrderInterpolationTransportSum u t| ≤
      12 * (2 * Real.pi) ^ 7 *
        h3TriadThirdOrderEnergy (fun j => h3SchwartzComplexify (f j)) *
        h3TriadFirstOrderMoment (fun j => h3SchwartzComplexify (f j)) := by
  rw [h3PathCanonical_interpolation_eq_three_firstMonomialAggregate hH3 hClass ht,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  calc
    _ ≤ 3 * (4 * (2 * Real.pi) ^ 7 *
        h3TriadThirdOrderEnergy (fun j => h3SchwartzComplexify (f j)) *
        h3TriadFirstOrderMoment (fun j => h3SchwartzComplexify (f j))) :=
      mul_le_mul_of_nonneg_left
        (h3PathCanonicalFirstMonomialAggregate_abs_le_energy_moment u t f hRealization hDiv)
        (by norm_num)
    _ = _ := by ring

end
end PrimeTensor.Bridge.Euclidean
