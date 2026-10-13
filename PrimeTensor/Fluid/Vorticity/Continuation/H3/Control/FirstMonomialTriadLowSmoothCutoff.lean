import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowPacketAlgebra
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Actual smooth frequency cutoffs for the sharp low-normal six-packet family

The prior packet algebra accepted arbitrary real scalar weights. This file
constructs bona fide smooth compactly supported weights on its exact carrier
`Fin 3 → ℝ`, using the positive radius `min 1 |t| / 4` established by the
quantitative nonresonance theorem.

Each cutoff equals one at its assigned center and vanishes outside the open
radius-`δ(t)` ball. Nonzero cutoffs imply membership in the earlier
coordinatewise frequency neighborhoods. Consequently a momentum-zero triple
from the six packet supports must have coherent labels.

We also instantiate the Hermitian, divergence-free six-packet field with these
specific smooth cutoffs. The scalar cutoffs are packaged as Schwartz maps.
Packaging the full vector-valued polynomially weighted field as a Schwartz
map, and proving a nonvanishing integrated cubic functional, are later steps.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set
open scoped Topology ContDiff SchwartzMap

noncomputable section

/-- Smooth bump with inner radius `ρ/2`, outer radius `ρ` on the exact
frequency carrier used by the first-monomial triad algebra. -/
noncomputable def lowNormalCenteredFrequencyBump
    (η : Fin 3 → ℝ) (ρ : ℝ) (hρ : 0 < ρ) : ContDiffBump η where
  rIn := ρ / 2
  rOut := ρ
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The actual scalar frequency weight attached to a signed sharp center. -/
noncomputable def lowNormalSmoothCenterCutoff
    (t : ℝ) (ht : t ≠ 0) (i : Fin 6) : (Fin 3 → ℝ) → ℝ :=
  lowNormalCenteredFrequencyBump
    (lowNormalSixCenter t i)
    (lowNormalSixCenterSeparationRadius t)
    (lowNormalSixCenterSeparationRadius_pos t ht)

/-- The cutoff takes the value one at its own frequency center. -/
theorem lowNormalSmoothCenterCutoff_at_center
    (t : ℝ) (ht : t ≠ 0) (i : Fin 6) :
    lowNormalSmoothCenterCutoff t ht i (lowNormalSixCenter t i) = 1 := by
  unfold lowNormalSmoothCenterCutoff
  apply (lowNormalCenteredFrequencyBump
    (lowNormalSixCenter t i)
    (lowNormalSixCenterSeparationRadius t)
    (lowNormalSixCenterSeparationRadius_pos t ht)).one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_self]
  dsimp [lowNormalCenteredFrequencyBump]
  have h := lowNormalSixCenterSeparationRadius_pos t ht
  linarith

/-- Its values are bounded between zero and one. -/
theorem lowNormalSmoothCenterCutoff_nonneg
    (t : ℝ) (ht : t ≠ 0) (i : Fin 6) (ξ : Fin 3 → ℝ) :
    0 ≤ lowNormalSmoothCenterCutoff t ht i ξ := by
  exact (lowNormalCenteredFrequencyBump
    (lowNormalSixCenter t i)
    (lowNormalSixCenterSeparationRadius t)
    (lowNormalSixCenterSeparationRadius_pos t ht)).nonneg

theorem lowNormalSmoothCenterCutoff_le_one
    (t : ℝ) (ht : t ≠ 0) (i : Fin 6) (ξ : Fin 3 → ℝ) :
    lowNormalSmoothCenterCutoff t ht i ξ ≤ 1 := by
  exact (lowNormalCenteredFrequencyBump
    (lowNormalSixCenter t i)
    (lowNormalSixCenterSeparationRadius t)
    (lowNormalSixCenterSeparationRadius_pos t ht)).le_one

/-- The frequency cutoff is genuinely smooth, not an indicator function. -/
theorem lowNormalSmoothCenterCutoff_contDiff
    (t : ℝ) (ht : t ≠ 0) (i : Fin 6) :
    ContDiff ℝ ∞ (lowNormalSmoothCenterCutoff t ht i) := by
  exact (lowNormalCenteredFrequencyBump
    (lowNormalSixCenter t i)
    (lowNormalSixCenterSeparationRadius t)
    (lowNormalSixCenterSeparationRadius_pos t ht)).contDiff

/-- Its frequency support is compact. -/
theorem lowNormalSmoothCenterCutoff_hasCompactSupport
    (t : ℝ) (ht : t ≠ 0) (i : Fin 6) :
    HasCompactSupport (lowNormalSmoothCenterCutoff t ht i) := by
  exact (lowNormalCenteredFrequencyBump
    (lowNormalSixCenter t i)
    (lowNormalSixCenterSeparationRadius t)
    (lowNormalSixCenterSeparationRadius_pos t ht)).hasCompactSupport

/-- Every frequency cutoff is itself a real Schwartz function. -/
noncomputable def lowNormalSmoothCenterCutoffSchwartz
    (t : ℝ) (ht : t ≠ 0) (i : Fin 6) :
    𝓢(Fin 3 → ℝ, ℝ) :=
  (lowNormalSmoothCenterCutoff_hasCompactSupport t ht i).toSchwartzMap
    (lowNormalSmoothCenterCutoff_contDiff t ht i)

@[simp] theorem lowNormalSmoothCenterCutoffSchwartz_apply
    (t : ℝ) (ht : t ≠ 0) (i : Fin 6) (ξ : Fin 3 → ℝ) :
    lowNormalSmoothCenterCutoffSchwartz t ht i ξ =
      lowNormalSmoothCenterCutoff t ht i ξ := rfl

/-- Nonzero cutoff weight forces pointwise membership in the quantitative
coordinatewise ball proved in `FirstMonomialTriadLowSeparation`. -/
theorem lowNormalSmoothCenterCutoff_nonzero_coordinateBall
    (t : ℝ) (ht : t ≠ 0) (i : Fin 6) (ξ : Fin 3 → ℝ)
    (hχ : lowNormalSmoothCenterCutoff t ht i ξ ≠ 0) :
    lowNormalSixCenterCoordinateBall t i ξ := by
  let b := lowNormalCenteredFrequencyBump
    (lowNormalSixCenter t i)
    (lowNormalSixCenterSeparationRadius t)
    (lowNormalSixCenterSeparationRadius_pos t ht)
  have hSupport : ξ ∈ Function.support (b : (Fin 3 → ℝ) → ℝ) := by
    change b ξ ≠ 0
    exact hχ
  rw [b.support_eq] at hSupport
  change ξ ∈ Metric.ball (lowNormalSixCenter t i)
    (lowNormalSixCenterSeparationRadius t) at hSupport
  have hNorm : ‖ξ - lowNormalSixCenter t i‖ <
      lowNormalSixCenterSeparationRadius t := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hSupport
  intro d
  have hCoordinate : |ξ d - lowNormalSixCenter t i d| ≤
      ‖ξ - lowNormalSixCenter t i‖ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (norm_le_pi_norm (ξ - lowNormalSixCenter t i) d)
  exact lt_of_le_of_lt hCoordinate hNorm

/-- A precise resonance-support theorem for the *constructed* smooth weights:
no extra zero-momentum triple can be created by the Fourier bumps. -/
theorem lowNormalSmoothCenterCutoff_zero_sum_coherent
    (t : ℝ) (ht : t ≠ 0) (i j k : Fin 6)
    (x y z : Fin 3 → ℝ)
    (hx : lowNormalSmoothCenterCutoff t ht i x ≠ 0)
    (hy : lowNormalSmoothCenterCutoff t ht j y ≠ 0)
    (hz : lowNormalSmoothCenterCutoff t ht k z ≠ 0)
    (hSum : ∀ d : Fin 3, x d + y d + z d = 0) :
    lowNormalCoherentCenters i j k := by
  exact lowNormalSixCenterCoordinateBall_zero_sum_coherent t ht i j k x y z
    (lowNormalSmoothCenterCutoff_nonzero_coordinateBall t ht i x hx)
    (lowNormalSmoothCenterCutoff_nonzero_coordinateBall t ht j y hy)
    (lowNormalSmoothCenterCutoff_nonzero_coordinateBall t ht k z hz)
    hSum

/-- The actual six-packet Fourier field with smooth compact scalar cutoffs. -/
noncomputable def lowNormalSmoothSixPacketFourier
    (t : ℝ) (ht : t ≠ 0) (ξ : Fin 3 → ℝ) : Fin 3 → ℂ :=
  lowNormalSixPacketFourier t
    (lowNormalSmoothCenterCutoff t ht 0)
    (lowNormalSmoothCenterCutoff t ht 1)
    (lowNormalSmoothCenterCutoff t ht 2) ξ

/-- Exact Fourier incompressibility of the smooth-cutoff packet assembly. -/
theorem lowNormalSmoothSixPacketFourier_divergence
    (t : ℝ) (ht : t ≠ 0) (ξ : Fin 3 → ℝ) :
    mixedDot ξ (lowNormalSmoothSixPacketFourier t ht ξ) = 0 :=
  lowNormalSixPacketFourier_divergence t _ _ _ ξ

/-- Exact conjugate reflection of the smooth-cutoff packet assembly. -/
theorem lowNormalSmoothSixPacketFourier_reality
    (t : ℝ) (ht : t ≠ 0) (ξ : Fin 3 → ℝ) :
    lowNormalSmoothSixPacketFourier t ht (fun d => -ξ d) =
      fun d => star (lowNormalSmoothSixPacketFourier t ht ξ d) :=
  lowNormalSixPacketFourier_reality t _ _ _ ξ

end
end PrimeTensor.FirstMonomialTriad
