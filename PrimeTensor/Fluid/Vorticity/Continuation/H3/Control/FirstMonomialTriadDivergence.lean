import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadAggregate

/-!
# Physical Schwartz divergence supplies Fourier triad incompressibility

Fourier transformation takes the coordinate divergence to 2πi times q·U(q).
Since 2πi is nonzero, physical divergence zero implies precisely the
polarization condition needed by the shell cancellation theorem.

The physical condition is stated using the actual Frechet derivatives of the
Schwartz components on H3FourierPoint3. No spectral divergence hypothesis is
required in the final shell formula.
-/

namespace PrimeTensor.Bridge.Euclidean

open MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3TriadDivergence (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

local notation "A3" => PrimeTensor.Axis Depth.three
local notation "V3" => H3FourierPoint3

/-- Coordinate divergence bundled as a scalar Schwartz function. -/
def h3SchwartzDivergence (u : A3 → SchwartzMap V3 ℂ) : SchwartzMap V3 ℂ :=
  ∑ j, ∂_{h3FourierAxisDirection j} (u j)

theorem h3SchwartzDivergence_apply (u : A3 → SchwartzMap V3 ℂ) (x : V3) :
    h3SchwartzDivergence u x =
      ∑ j, fderiv ℝ (u j) x (h3FourierAxisDirection j) := by
  classical
  simp only [h3SchwartzDivergence, sum_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- Exact Fourier symbol of the physical coordinate divergence. -/
theorem h3SchwartzDivergence_fourier (u : A3 → SchwartzMap V3 ℂ) (q : A3 → ℝ) :
    𝓕 (h3SchwartzDivergence u) (WithLp.toLp 2 q) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) := by
  classical
  change ((FourierTransform.fourierCLM ℂ (SchwartzMap V3 ℂ))
    (∑ j, ∂_{h3FourierAxisDirection j} (u j))) (WithLp.toLp 2 q) = _
  rw [map_sum]
  simp only [sum_apply]
  change (∑ j, 𝓕 (∂_{h3FourierAxisDirection j} (u j)) (WithLp.toLp 2 q)) = _
  simp only [h3Schwartz_fourier_lineDeriv_apply, inner_h3FourierAxisDirection]
  unfold FirstMonomialTriad.mixedDot h3SchwartzTriadPolarization
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (2 * (Real.pi : ℂ) * Complex.I) * (q j : ℂ) * 𝓕 (u j) (WithLp.toLp 2 q) = _
  ring

/-- The derivative multiplier can be cancelled without dividing by frequency. -/
theorem h3SchwartzDivergence_phase_ne_zero :
    (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  apply mul_ne_zero
  · apply mul_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
  · exact Complex.I_ne_zero

/-- Physical divergence zero implies the precise Fourier polarization condition. -/
theorem h3SchwartzTriadPolarization_divergence_zero
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3, ∑ j, fderiv ℝ (u j) x (h3FourierAxisDirection j) = 0) :
    ∀ q : A3 → ℝ,
      FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0 := by
  have hz : h3SchwartzDivergence u = 0 := by
    ext x
    simpa only [h3SchwartzDivergence_apply, zero_apply] using hDiv x
  intro q
  have hf := congrArg (fun f : SchwartzMap V3 ℂ => 𝓕 f (WithLp.toLp 2 q)) hz
  rw [h3SchwartzDivergence_fourier] at hf
  have hm : (2 * (Real.pi : ℂ) * Complex.I) *
      FirstMonomialTriad.mixedDot q (h3SchwartzTriadPolarization u q) = 0 := by
    simpa using hf
  exact (mul_eq_zero.mp hm).resolve_left h3SchwartzDivergence_phase_ne_zero

/-- Shell-kernel integrability from physical incompressibility alone. -/
theorem h3SchwartzTriadShellKernel_integrable_of_physical_divergence
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3, ∑ j, fderiv ℝ (u j) x (h3FourierAxisDirection j) = 0) :
    Integrable (h3SchwartzTriadShellKernel u) (volume.prod volume) :=
  h3SchwartzTriadShellKernel_integrable u
    (h3SchwartzTriadPolarization_divergence_zero u hDiv)

/-- Full Schwartz aggregate shell identity with a physical divergence hypothesis. -/
theorem h3SchwartzFirstMonomialAggregate_twice_eq_shell_of_physical_divergence
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3, ∑ j, fderiv ℝ (u j) x (h3FourierAxisDirection j) = 0) :
    2 * h3SchwartzFirstMonomialAggregate u =
      (2 * (Real.pi : ℂ) * Complex.I) ^ 7 *
        ∫ z, h3SchwartzTriadShellKernel u z ∂volume.prod volume :=
  h3SchwartzFirstMonomialAggregate_twice_eq_shell u
    (h3SchwartzTriadPolarization_divergence_zero u hDiv)

/-- Signed physical Schwartz pairing with no separate spectral assumption. -/
theorem h3SchwartzFirstMonomialAggregate_twice_re_eq_shell_im_of_physical_divergence
    (u : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3, ∑ j, fderiv ℝ (u j) x (h3FourierAxisDirection j) = 0) :
    2 * (h3SchwartzFirstMonomialAggregate u).re =
      (2 * Real.pi) ^ 7 *
        (∫ z, h3SchwartzTriadShellKernel u z ∂volume.prod volume).im :=
  h3SchwartzFirstMonomialAggregate_twice_re_eq_shell_im u
    (h3SchwartzTriadPolarization_divergence_zero u hDiv)

end
end PrimeTensor.Bridge.Euclidean
