import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdProjectedHermitianGerm244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowSmoothCutoff
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic

/-!
# Noncoherent support exclusion on the actual full-third axis carrier

The corrected full-third symbol is carried by `Axis Depth.three -> ℝ`, not
by the `Fin 3 -> ℝ` carrier of the original low-normal Schwartz packets.
The explicit -192 center is nevertheless the old sharp center family at
parameter t=1: p=(1,0,0), q=(1,1,0), r=(-2,-1,0).

We transfer the already proved quantitative six-center separation lemma to
this axis carrier. Small smooth windows around the six frequencies may
contribute to a momentum-conserving triple only when the three center labels
are a permutation of (p,q,r) or of their reflected partners.

This solves the support-exclusion step, NOT the remaining phase bookkeeping,
full Schwartz-packet Fourier identification, or global noncancellation.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Metric PrimeTensor.Bridge.Euclidean
open scoped Topology ContDiff

noncomputable section
set_option maxHeartbeats 1200000

private abbrev A3 := PrimeTensor.Axis Depth.three

noncomputable local instance axisFintypeFullThirdAxisWindow244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Coordinate readback from the actual positive-depth axis carrier. -/
def thirdFullAxisToFin244 (ξ : A3 → ℝ) : Fin 3 → ℝ :=
  ![ξ xAxis, ξ yAxis, ξ zAxis]

/-- The six sharp centers at t=1, written on the ACTUAL full-third carrier.
The labels 0,1,2 are p,q,r; 3,4,5 are their negatives. -/
def thirdFullAxisSixCenter244 (i : Fin 6) : A3 → ℝ :=
  fun d =>
    if axisRank d = 0 then lowNormalSixCenter (1 : ℝ) i 0
    else if axisRank d = 1 then lowNormalSixCenter (1 : ℝ) i 1
    else lowNormalSixCenter (1 : ℝ) i 2

/-- The axis centers are literally the old six sharp centers, after
reading back the three physical axis coordinates. -/
theorem thirdFullAxisSixCenter_toFin244 (i : Fin 6) :
    thirdFullAxisToFin244 (thirdFullAxisSixCenter244 i) =
      lowNormalSixCenter (1 : ℝ) i := by
  funext d
  fin_cases d <;>
    norm_num [thirdFullAxisToFin244, thirdFullAxisSixCenter244,
      axisRank, xAxis, yAxis, zAxis] <;>
    -- After numeral normalization, the last index is a literal Fin subtype.
    -- Both sides reduce to the same Fin index; unfolding the lattice
    -- embedding gives a fallback for this last coordinate.
    first
    | rfl
    | simp [lowNormalSixCenter, lowNormalLatticeEmbedding]

/-- Coordinatewise bounds on `Axis Depth.three` imply the corresponding
bounds on the original `Fin 3` frequency carrier. -/
theorem thirdFullAxis_coordinateBall_transfer244
    (i : Fin 6) (ξ : A3 → ℝ)
    (h : ∀ a : A3,
      |ξ a - thirdFullAxisSixCenter244 i a| <
        lowNormalSixCenterSeparationRadius (1 : ℝ)) :
    lowNormalSixCenterCoordinateBall (1 : ℝ) i (thirdFullAxisToFin244 ξ) := by
  intro d
  have hh : ∀ d : Fin 3,
      |thirdFullAxisToFin244 ξ d -
        thirdFullAxisToFin244 (thirdFullAxisSixCenter244 i) d| <
          lowNormalSixCenterSeparationRadius (1 : ℝ) := by
    intro e
    fin_cases e
    · simpa [thirdFullAxisToFin244] using h xAxis
    · simpa [thirdFullAxisToFin244] using h yAxis
    · simpa [thirdFullAxisToFin244] using h zAxis
  simpa only [thirdFullAxisSixCenter_toFin244] using hh d

/-- The previously established 12-sector resonance classification applies
unchanged to the actual axis carrier of the seven-derivative symbol. -/
theorem thirdFullAxisSixCenter_coordinateBall_zero_sum_coherent244
    (i j k : Fin 6) (p q r : A3 → ℝ)
    (hp : ∀ a : A3,
      |p a - thirdFullAxisSixCenter244 i a| <
        lowNormalSixCenterSeparationRadius (1 : ℝ))
    (hq : ∀ a : A3,
      |q a - thirdFullAxisSixCenter244 j a| <
        lowNormalSixCenterSeparationRadius (1 : ℝ))
    (hr : ∀ a : A3,
      |r a - thirdFullAxisSixCenter244 k a| <
        lowNormalSixCenterSeparationRadius (1 : ℝ))
    (hm : ∀ a : A3, p a + q a + r a = 0) :
    lowNormalCoherentCenters i j k := by
  apply lowNormalSixCenterCoordinateBall_zero_sum_coherent
    (1 : ℝ) (by norm_num) i j k
      (thirdFullAxisToFin244 p)
      (thirdFullAxisToFin244 q)
      (thirdFullAxisToFin244 r)
      (thirdFullAxis_coordinateBall_transfer244 i p hp)
      (thirdFullAxis_coordinateBall_transfer244 j q hq)
      (thirdFullAxis_coordinateBall_transfer244 k r hr)
  intro d
  fin_cases d
  · simpa [thirdFullAxisToFin244] using hm xAxis
  · simpa [thirdFullAxisToFin244] using hm yAxis
  · simpa [thirdFullAxisToFin244] using hm zAxis

/-- Smooth compact center cutoff on `Axis Depth.three`, with adjustable
strictly positive width. The inner ball has radius ρ/2. -/
noncomputable def thirdFullAxisWindowBump244
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6) :
    ContDiffBump (thirdFullAxisSixCenter244 i) where
  rIn := ρ / 2
  rOut := ρ
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- Every window is smooth to all orders. -/
theorem thirdFullAxisWindowBump_contDiff244
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6) :
    ContDiff ℝ ∞ (thirdFullAxisWindowBump244 ρ hρ i : (A3 → ℝ) → ℝ) :=
  (thirdFullAxisWindowBump244 ρ hρ i).contDiff

/-- Every window has compact support. -/
theorem thirdFullAxisWindowBump_hasCompactSupport244
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6) :
    HasCompactSupport (thirdFullAxisWindowBump244 ρ hρ i : (A3 → ℝ) → ℝ) :=
  (thirdFullAxisWindowBump244 ρ hρ i).hasCompactSupport

/-- The window equals one at its assigned sharp center. -/
theorem thirdFullAxisWindowBump_at_center244
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6) :
    (thirdFullAxisWindowBump244 ρ hρ i : (A3 → ℝ) → ℝ)
      (thirdFullAxisSixCenter244 i) = 1 := by
  apply (thirdFullAxisWindowBump244 ρ hρ i).one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_self]
  dsimp [thirdFullAxisWindowBump244]
  linarith

/-- Nonzero window amplitude forces the frequency to lie strictly within
its selected center ball. -/
theorem thirdFullAxisWindowBump_nonzero_ball244
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin 6) (ξ : A3 → ℝ)
    (hw : (thirdFullAxisWindowBump244 ρ hρ i : (A3 → ℝ) → ℝ) ξ ≠ 0) :
    dist ξ (thirdFullAxisSixCenter244 i) < ρ := by
  let b := thirdFullAxisWindowBump244 ρ hρ i
  have hs : ξ ∈ Function.support (b : (A3 → ℝ) → ℝ) := by
    change b ξ ≠ 0
    exact hw
  rw [b.support_eq] at hs
  change ξ ∈ Metric.ball (thirdFullAxisSixCenter244 i) ρ at hs
  exact hs

/-- Nonzero smooth cutoff implies the quantitative coordinate bounds
needed to apply the twelve-sector nonresonance theorem. -/
theorem thirdFullAxisWindowBump_coordinateBall244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (i : Fin 6) (ξ : A3 → ℝ)
    (hw : (thirdFullAxisWindowBump244 ρ hρ i : (A3 → ℝ) → ℝ) ξ ≠ 0) :
    ∀ a : A3,
      |ξ a - thirdFullAxisSixCenter244 i a| <
        lowNormalSixCenterSeparationRadius (1 : ℝ) := by
  intro a
  have hCoord : |ξ a - thirdFullAxisSixCenter244 i a| ≤
      dist ξ (thirdFullAxisSixCenter244 i) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply, dist_eq_norm] using
      (norm_le_pi_norm (ξ - thirdFullAxisSixCenter244 i) a)
  exact lt_of_le_of_lt hCoord
    (lt_of_lt_of_le
      (thirdFullAxisWindowBump_nonzero_ball244 ρ hρ i ξ hw) hSmall)

/-- The actual compact smooth Fourier windows cannot introduce any
noncoherent zero-momentum triad. Unlike the earlier Fin 3 theorem, these
windows live on precisely the full-third physical Axis carrier. -/
theorem thirdFullAxisWindowBump_zero_sum_coherent244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (i j k : Fin 6) (p q r : A3 → ℝ)
    (hp : (thirdFullAxisWindowBump244 ρ hρ i : (A3 → ℝ) → ℝ) p ≠ 0)
    (hq : (thirdFullAxisWindowBump244 ρ hρ j : (A3 → ℝ) → ℝ) q ≠ 0)
    (hr : (thirdFullAxisWindowBump244 ρ hρ k : (A3 → ℝ) → ℝ) r ≠ 0)
    (hm : ∀ a : A3, p a + q a + r a = 0) :
    lowNormalCoherentCenters i j k := by
  exact thirdFullAxisSixCenter_coordinateBall_zero_sum_coherent244
    i j k p q r
    (thirdFullAxisWindowBump_coordinateBall244 ρ hρ hSmall i p hp)
    (thirdFullAxisWindowBump_coordinateBall244 ρ hρ hSmall j q hq)
    (thirdFullAxisWindowBump_coordinateBall244 ρ hρ hSmall k r hr)
    hm


/-- Exact support exclusion in the two-free-momentum representation
`q=-p-r` used by the corrected full-third Hermitian coefficient. -/
theorem thirdFullAxisWindowBump_pair_coherent244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (i j k : Fin 6) (z : (A3 → ℝ) × (A3 → ℝ))
    (hp : (thirdFullAxisWindowBump244 ρ hρ i : (A3 → ℝ) → ℝ) z.1 ≠ 0)
    (hq : (thirdFullAxisWindowBump244 ρ hρ j : (A3 → ℝ) → ℝ)
      (thirdFullMiddleFrequency244 z) ≠ 0)
    (hr : (thirdFullAxisWindowBump244 ρ hρ k : (A3 → ℝ) → ℝ) z.2 ≠ 0) :
    lowNormalCoherentCenters i j k := by
  apply thirdFullAxisWindowBump_zero_sum_coherent244
    ρ hρ hSmall i j k z.1 (thirdFullMiddleFrequency244 z) z.2 hp hq hr
  intro a
  dsimp [thirdFullMiddleFrequency244]
  ring

/-- The literal three-window Fourier factor vanishes identically in every
noncoherent label sector. This is the form needed to remove spurious
momentum sectors from the eventual full-third integral. -/
theorem thirdFullAxisWindowBump_noncoherent_product_zero244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (i j k : Fin 6) (hNon : ¬ lowNormalCoherentCenters i j k)
    (z : (A3 → ℝ) × (A3 → ℝ)) :
    (thirdFullAxisWindowBump244 ρ hρ i : (A3 → ℝ) → ℝ) z.1 *
      (thirdFullAxisWindowBump244 ρ hρ j : (A3 → ℝ) → ℝ)
        (thirdFullMiddleFrequency244 z) *
      (thirdFullAxisWindowBump244 ρ hρ k : (A3 → ℝ) → ℝ) z.2 = 0 := by
  by_cases hp :
      (thirdFullAxisWindowBump244 ρ hρ i : (A3 → ℝ) → ℝ) z.1 = 0
  · rw [hp]
    ring
  by_cases hq :
      (thirdFullAxisWindowBump244 ρ hρ j : (A3 → ℝ) → ℝ)
        (thirdFullMiddleFrequency244 z) = 0
  · rw [hq]
    ring
  by_cases hr :
      (thirdFullAxisWindowBump244 ρ hρ k : (A3 → ℝ) → ℝ) z.2 = 0
  · rw [hr]
    ring
  exact (hNon (thirdFullAxisWindowBump_pair_coherent244
    ρ hρ hSmall i j k z hp hq hr)).elim

end
end PrimeTensor.FirstMonomialTriad
