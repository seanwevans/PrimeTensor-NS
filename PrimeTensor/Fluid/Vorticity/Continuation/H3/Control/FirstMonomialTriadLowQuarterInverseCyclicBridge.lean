import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPhysicalPhaseIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Inverse-Fourier realization and full cyclic-shell sign of the quarter packet

The preceding theorem gives a strictly negative full integral for the physical
seven-derivative phase of a concrete compactly supported, Hermitian,
solenoidal Schwartz Fourier vector. Two bridges are established here:

1. Coordinate projection of that vector is Schwartz, and taking inverse
   Fourier transforms produces a genuine *complex-valued spatial Schwartz
   vector field* with precisely the prescribed Fourier transform. Its
   Fourier components obey the proved incompressibility and Hermitian laws.
2. The physically phased six-order coefficient is exactly the physically
   phased sum of its three cyclic outer-shell coefficients. Their FULL
   six-dimensional real integral is strictly negative for some width.

The inverse-Fourier field is not yet proved real valued in this module.
Nor is it identified with the canonical `Point3` physical energy pairing;
the needed reality and coordinate-carrier identification remain separate.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory
open scoped Topology SchwartzMap FourierTransform

noncomputable section

private abbrev InverseV := Fin 3 → ℝ
private abbrev InverseA := Fin 3 → ℂ
private abbrev InversePair := InverseV × InverseV
private abbrev InverseE := EuclideanSpace ℝ (Fin 3)

/-- A coordinate of the already constructed vector-valued Schwartz Fourier
packet is itself a complex-valued Schwartz function. -/
noncomputable def lowNormalQuarterWindowedFourierComponent
    (ρ : ℝ) (hρ : 0 < ρ) (j : Fin 3) : 𝓢(InverseV, ℂ) :=
  (SchwartzMap.postcompCLM (𝕜 := ℝ)
    (ContinuousLinearMap.proj j : InverseA →L[ℝ] ℂ))
      (lowNormalQuarterWindowedSchwartz ρ hρ)

@[simp] theorem lowNormalQuarterWindowedFourierComponent_apply
    (ρ : ℝ) (hρ : 0 < ρ) (j : Fin 3) (ξ : InverseV) :
    lowNormalQuarterWindowedFourierComponent ρ hρ j ξ =
      lowNormalQuarterWeightedFourier
        (lowNormalQuarterEvenWindow ρ hρ) ξ j := rfl

/-- Transport the original frequency-coordinate Schwartz component to
`EuclideanSpace`: the Hilbert carrier on which mathlib defines Schwartz
Fourier inversion. The conversion does NOT change the underlying frequency
coordinates or Fourier data. -/
noncomputable def lowNormalQuarterHilbertFourierComponent
    (ρ : ℝ) (hρ : 0 < ρ) (j : Fin 3) : 𝓢(InverseE, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ))
    (lowNormalQuarterWindowedFourierComponent ρ hρ j)

@[simp] theorem lowNormalQuarterHilbertFourierComponent_apply
    (ρ : ℝ) (hρ : 0 < ρ) (j : Fin 3) (ξ : InverseE) :
    lowNormalQuarterHilbertFourierComponent ρ hρ j ξ =
      lowNormalQuarterWeightedFourier
        (lowNormalQuarterEvenWindow ρ hρ) (WithLp.ofLp ξ) j := by
  change lowNormalQuarterWindowedFourierComponent ρ hρ j (WithLp.ofLp ξ) = _
  exact lowNormalQuarterWindowedFourierComponent_apply ρ hρ j (WithLp.ofLp ξ)

/-- A genuine complex spatial Schwartz velocity component, defined by
inverse Fourier transform on a Euclidean inner-product space. -/
noncomputable def lowNormalQuarterInverseSchwartzComponent
    (ρ : ℝ) (hρ : 0 < ρ) (j : Fin 3) : 𝓢(InverseE, ℂ) :=
  𝓕⁻ (lowNormalQuarterHilbertFourierComponent ρ hρ j)

/-- Exact Schwartz Fourier recovery on the genuine Hilbert carrier. -/
theorem lowNormalQuarterInverseSchwartz_fourier_component
    (ρ : ℝ) (hρ : 0 < ρ) (j : Fin 3) :
    𝓕 (lowNormalQuarterInverseSchwartzComponent ρ hρ j) =
      lowNormalQuarterHilbertFourierComponent ρ hρ j :=
  FourierTransform.fourier_fourierInv_eq _

/-- The recovered Fourier vector equals the original packet after applying
the explicit Euclidean-to-coordinate equivalence. -/
theorem lowNormalQuarterInverseSchwartz_fourier_vector
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : InverseE) :
    (fun j : Fin 3 => 𝓕 (lowNormalQuarterInverseSchwartzComponent ρ hρ j) ξ) =
      lowNormalQuarterWeightedFourier
        (lowNormalQuarterEvenWindow ρ hρ) (WithLp.ofLp ξ) := by
  funext j
  rw [lowNormalQuarterInverseSchwartz_fourier_component]
  exact lowNormalQuarterHilbertFourierComponent_apply ρ hρ j ξ

/-- The spatial inverse field has Fourier divergence zero at each
Euclidean frequency, with no unverified scalar Fourier instance. -/
theorem lowNormalQuarterInverseSchwartz_fourier_divergence
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : InverseE) :
    mixedDot (WithLp.ofLp ξ)
      (fun j : Fin 3 => 𝓕 (lowNormalQuarterInverseSchwartzComponent ρ hρ j) ξ) = 0 := by
  rw [lowNormalQuarterInverseSchwartz_fourier_vector]
  exact lowNormalQuarterWindowedFourier_divergence ρ hρ (WithLp.ofLp ξ)

/-- The Fourier spectrum of the reconstructed field is Hermitian.
The remaining converse (realness of the spatial field) is not claimed. -/
theorem lowNormalQuarterInverseSchwartz_fourier_hermitian
    (ρ : ℝ) (hρ : 0 < ρ) (ξ : InverseE) :
    (fun j : Fin 3 =>
      𝓕 (lowNormalQuarterInverseSchwartzComponent ρ hρ j) (-ξ)) =
    (fun j : Fin 3 =>
      star (𝓕 (lowNormalQuarterInverseSchwartzComponent ρ hρ j) ξ)) := by
  funext j
  simp only [lowNormalQuarterInverseSchwartz_fourier_component,
    lowNormalQuarterHilbertFourierComponent_apply, WithLp.ofLp_neg]
  exact congrFun
    (lowNormalQuarterWindowedFourier_reality ρ hρ (WithLp.ofLp ξ)) j

/-- Three explicitly ordered shell terms of the SAME Fourier field,
with the physical seven-derivative phase and no normalization dropped. -/
def lowNormalQuarterPhysicalCyclicShellKernel
    (ρ : ℝ) (hρ : 0 < ρ) (z : InversePair) : ℝ :=
  let U := lowNormalQuarterWeightedFourier (lowNormalQuarterEvenWindow ρ hρ)
  (((2 * (Real.pi : ℂ) * Complex.I) ^ 7) *
    (shellKernel U (z.1, z.2) +
      shellKernel U (z.1, middleFrequency z.1 z.2) +
        shellKernel U (middleFrequency z.1 z.2, z.2))).re

/-- All three cyclic orderings equal the existing six-permutation kernel
pointwise, BEFORE integrating or discarding complex phases. -/
theorem lowNormalQuarterPhysicalCyclicShellKernel_eq
    (ρ : ℝ) (hρ : 0 < ρ) (p r : InverseV) :
    lowNormalQuarterPhysicalCyclicShellKernel ρ hρ (p, r) =
      lowNormalQuarterPhysicalPhaseKernel
        (lowNormalQuarterEvenWindow ρ hρ) (p, r) := by
  have h := lowNormalQuarterEvenWindow_sixOrder_eq_three_cyclic_shell
    ρ hρ p r
  dsimp only at h
  exact congrArg (fun c : ℂ =>
    (((2 * (Real.pi : ℂ) * Complex.I) ^ 7) * c).re) h

/-- Compact support of the actual packet gives integrability of the
complete physically phased cyclic-shell sum on the momentum plane. -/
theorem lowNormalQuarterPhysicalCyclicShellKernel_integrable
    (ρ : ℝ) (hρ : 0 < ρ) :
    Integrable (lowNormalQuarterPhysicalCyclicShellKernel ρ hρ)
      (volume.prod volume) := by
  exact (lowNormalQuarterPhysicalPhaseKernel_integrable ρ hρ).congr
    (Filter.Eventually.of_forall (fun z => by
      rcases z with ⟨p, r⟩
      exact (lowNormalQuarterPhysicalCyclicShellKernel_eq ρ hρ p r).symm))

/-- The full integral of the THREE physically phased cyclic shell terms
is identically the full integral of the six-order physical-phase symbol. -/
theorem lowNormalQuarterPhysicalCyclicShellKernel_integral_eq
    (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ z : InversePair, lowNormalQuarterPhysicalCyclicShellKernel ρ hρ z
      ∂(volume.prod volume)) =
      ∫ z : InversePair,
        lowNormalQuarterPhysicalPhaseKernel (lowNormalQuarterEvenWindow ρ hρ) z
          ∂(volume.prod volume) := by
  apply integral_congr_ae
  filter_upwards with z
  rcases z with ⟨p, r⟩
  exact lowNormalQuarterPhysicalCyclicShellKernel_eq ρ hρ p r

/-- The previously proved negative six-order integral transfers, with no
loss of orderings or signs, to the physical-phase three-cyclic-shell sum. -/
theorem lowNormalQuarterEvenWindow_exists_negative_full_cyclicShell_integral :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      ρ ≤ lowNormalSixCenterSeparationRadius (1 / 4 : ℝ) ∧
      (∫ z : InversePair,
        lowNormalQuarterPhysicalCyclicShellKernel ρ hρ z
          ∂(volume.prod volume)) < 0 := by
  obtain ⟨ρ, hρ, hSmall, hNeg⟩ :=
    lowNormalQuarterEvenWindow_exists_negative_physicalPhase_integral
  refine ⟨ρ, hρ, hSmall, ?_⟩
  rw [lowNormalQuarterPhysicalCyclicShellKernel_integral_eq]
  exact hNeg

end
end PrimeTensor.FirstMonomialTriad
