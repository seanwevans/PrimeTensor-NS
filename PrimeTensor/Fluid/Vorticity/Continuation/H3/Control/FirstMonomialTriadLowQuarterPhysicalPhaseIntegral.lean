import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterGlobalIntegral
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowPhysicalPhase

/-!
# Exact physical seven-derivative phase of the noncancelling six-order triad

The preceding module constructs a real-compatible, divergence-free Schwartz
Fourier field for which the FULL six-dimensional integral of Re (I * C₆)
is strictly positive. Here we insert the project's actual physical Fourier
multiplier, (2πi)^7. The existing first-monomial Fourier theorem shows that
this equals -(2π)^7 i, so the physically phased six-order integral is
strictly NEGATIVE, with no invented Jacobian or normalization factor.

We also connect the same actual weighted polarization field to the already
proved pointwise cyclic three-shell identity. The physically phased
SIX-ORDER integral must still be connected to the actual real-space H3
aggregate; neither Fourier inversion of the constructed vector field nor an
identification of this six-order integral with the physical aggregate is
claimed here. In particular this file is NOT a Navier--Stokes blowup theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory
open scoped Topology SchwartzMap

noncomputable section

private abbrev PhaseV := Fin 3 → ℝ
private abbrev PhasePair := PhaseV × PhaseV

/-- The full six-order symbol, with the actual multiplier from seven
physical derivatives. This retains all six permutations, not a single slot. -/
def lowNormalQuarterPhysicalPhaseKernel
    (w : PhaseV → ℝ) (z : PhasePair) : ℝ :=
  (((2 * (Real.pi : ℂ) * Complex.I) ^ 7) *
    sixOrderTriadCoefficient z.1 (middleFrequency z.1 z.2) z.2
      (lowNormalQuarterWeightedFourier w z.1)
      (lowNormalQuarterWeightedFourier w (middleFrequency z.1 z.2))
      (lowNormalQuarterWeightedFourier w z.2)).re

/-- The seven-derivative Fourier phase is exactly MINUS the positive-I
symbol audit, multiplied by the positive real scale (2π)^7. -/
private theorem lowNormalQuarter_physical_phase_re (c : ℂ) :
    (((2 * (Real.pi : ℂ) * Complex.I) ^ 7) * c).re =
      -((2 * Real.pi) ^ 7) * (Complex.I * c).re := by
  rw [PrimeTensor.Bridge.Euclidean.h3FirstMonomial_fourier_phase]
  have hMul :
      (-(Complex.I * (((2 * Real.pi) ^ 7 : ℝ) : ℂ))) * c =
        -((((2 * Real.pi) ^ 7 : ℝ) : ℂ) * (Complex.I * c)) := by
    ring
  rw [hMul, Complex.neg_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] <;> ring

/-- Exact sign and normalization for one Fourier momentum pair. -/
theorem lowNormalQuarterPhysicalPhaseKernel_eq
    (w : PhaseV → ℝ) (p r : PhaseV) :
    lowNormalQuarterPhysicalPhaseKernel w (p, r) =
      -((2 * Real.pi) ^ 7) * lowNormalQuarterWeightedSignedKernel w (p, r) := by
  unfold lowNormalQuarterPhysicalPhaseKernel lowNormalQuarterWeightedSignedKernel
  exact lowNormalQuarter_physical_phase_re _

/-- No new polynomial-symbol computation is needed: the SAME actual weighted
field satisfies the complete three-cyclic-shell identity pointwise. -/
theorem lowNormalQuarterEvenWindow_sixOrder_eq_three_cyclic_shell
    (ρ : ℝ) (hρ : 0 < ρ) (p r : PhaseV) :
    let U := lowNormalQuarterWeightedFourier (lowNormalQuarterEvenWindow ρ hρ)
    shellKernel U (p, r) +
      shellKernel U (p, middleFrequency p r) +
        shellKernel U (middleFrequency p r, r) =
      sixOrderTriadCoefficient p (middleFrequency p r) r
        (U p) (U (middleFrequency p r)) (U r) := by
  exact shellKernel_three_cyclic_eq_sixOrder
    (lowNormalQuarterWeightedFourier (lowNormalQuarterEvenWindow ρ hρ))
    p (middleFrequency p r) r (middleFrequency_momentum p r)
    (fun ξ => lowNormalQuarterWindowedFourier_divergence ρ hρ ξ)

/-- Compact support and continuity of the weighted kernel also establish
integrability after insertion of the genuine physical Fourier phase. -/
theorem lowNormalQuarterPhysicalPhaseKernel_integrable
    (ρ : ℝ) (hρ : 0 < ρ) :
    Integrable (lowNormalQuarterPhysicalPhaseKernel
      (lowNormalQuarterEvenWindow ρ hρ)) (volume.prod volume) := by
  let w : PhaseV → ℝ := lowNormalQuarterEvenWindow ρ hρ
  have hEq : lowNormalQuarterPhysicalPhaseKernel w =
      (fun z : PhasePair =>
        -((2 * Real.pi) ^ 7) * lowNormalQuarterWeightedSignedKernel w z) := by
    funext z
    rcases z with ⟨p, r⟩
    exact lowNormalQuarterPhysicalPhaseKernel_eq w p r
  change Integrable (lowNormalQuarterPhysicalPhaseKernel w) (volume.prod volume)
  rw [hEq]
  exact (lowNormalQuarterWindowedSignedKernel_integrable ρ hρ).const_mul _

/-- Insert the true Fourier phase under the FULL six-dimensional integral.
The prefactor is exactly -(2π)^7, with no additional measure constant. -/
theorem lowNormalQuarterPhysicalPhaseKernel_integral_eq
    (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ z : PhasePair,
      lowNormalQuarterPhysicalPhaseKernel (lowNormalQuarterEvenWindow ρ hρ) z
        ∂(volume.prod volume)) =
      -((2 * Real.pi) ^ 7) *
        (∫ z : PhasePair,
          lowNormalQuarterWeightedSignedKernel (lowNormalQuarterEvenWindow ρ hρ) z
            ∂(volume.prod volume)) := by
  let w : PhaseV → ℝ := lowNormalQuarterEvenWindow ρ hρ
  have hEq : lowNormalQuarterPhysicalPhaseKernel w =
      (fun z : PhasePair =>
        -((2 * Real.pi) ^ 7) * lowNormalQuarterWeightedSignedKernel w z) := by
    funext z
    rcases z with ⟨p, r⟩
    exact lowNormalQuarterPhysicalPhaseKernel_eq w p r
  change (∫ z : PhasePair, lowNormalQuarterPhysicalPhaseKernel w z
      ∂(volume.prod volume)) =
    -((2 * Real.pi) ^ 7) *
      (∫ z : PhasePair, lowNormalQuarterWeightedSignedKernel w z
        ∂(volume.prod volume))
  rw [hEq]
  exact integral_const_mul _ _

/-- The constructed divergence-free Hermitian Schwartz Fourier field has a
strictly NEGATIVE full six-order coefficient after the ACTUAL seven-derivative
phase is inserted. This is a statement about the Fourier symbol integral,
not yet a real-space first-monomial energy pairing. -/
theorem lowNormalQuarterEvenWindow_exists_negative_physicalPhase_integral :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      ρ ≤ lowNormalSixCenterSeparationRadius (1 / 4 : ℝ) ∧
      (∫ z : PhasePair,
        lowNormalQuarterPhysicalPhaseKernel (lowNormalQuarterEvenWindow ρ hρ) z
          ∂(volume.prod volume)) < 0 := by
  obtain ⟨ρ, hρ, hSmall, hPositive⟩ :=
    lowNormalQuarterEvenWindow_exists_positive_full_sixOrder_integral
  refine ⟨ρ, hρ, hSmall, ?_⟩
  rw [lowNormalQuarterPhysicalPhaseKernel_integral_eq]
  have hScale : 0 < (2 * Real.pi) ^ 7 := by positivity
  have hProduct := mul_pos hScale hPositive
  nlinarith

/-- In particular the full physically phased Fourier integral is nonzero. -/
theorem lowNormalQuarterEvenWindow_exists_nonzero_physicalPhase_integral :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      (∫ z : PhasePair,
        lowNormalQuarterPhysicalPhaseKernel (lowNormalQuarterEvenWindow ρ hρ) z
          ∂(volume.prod volume)) ≠ 0 := by
  obtain ⟨ρ, hρ, _, hNeg⟩ :=
    lowNormalQuarterEvenWindow_exists_negative_physicalPhase_integral
  exact ⟨ρ, hρ, ne_of_lt hNeg⟩

end
end PrimeTensor.FirstMonomialTriad
