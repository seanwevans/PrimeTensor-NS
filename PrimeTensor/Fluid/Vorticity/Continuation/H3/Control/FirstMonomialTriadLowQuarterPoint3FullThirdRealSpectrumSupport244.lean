import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdAxisRealSchwartz244
import Mathlib.Tactic

/-!
# Coherent support of the actual real full-third Schwartz velocity spectrum

The earlier support theorem classifies nonzero TRIPLES of individual scalar
windows. This module transfers that geometry to the already constructed,
real-valued, divergence-free Schwartz velocity itself. Every nonzero Fourier
vector must occur in one of the six balls, and any nonzero momentum-conserving
triple belongs to one of the twelve coherent sectors.

The final result is a genuine support exclusion for the three-frequency
amplitude of the recovered physical velocity. It does not assume or prove
that the signed global seven-derivative integral is nonzero.
-/

namespace PrimeTensor.FirstMonomialTriad

open Metric PrimeTensor.Bridge.Euclidean
open scoped SchwartzMap FourierTransform Topology

noncomputable section
set_option maxHeartbeats 1200000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev Pair244 := Freq244 × Freq244

noncomputable local instance axisFintypeActualSupport244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The axis-coordinate transfer preserves the negative mates of the
three sharp lattice centers; no unitary or measure change is involved. -/
private theorem thirdFullAxisSixCenter_neg_of_fin244
    (i j : Fin 6)
    (h : lowNormalSixCenter (1 : ℝ) j =
      (fun d => -lowNormalSixCenter (1 : ℝ) i d)) :
    thirdFullAxisSixCenter244 j = -thirdFullAxisSixCenter244 i := by
  funext a
  by_cases h0 : axisRank a = 0
  · simpa [thirdFullAxisSixCenter244, h0, Pi.neg_apply] using congrFun h 0
  by_cases h1 : axisRank a = 1
  · simpa [thirdFullAxisSixCenter244, h0, h1, Pi.neg_apply] using congrFun h 1
  · simpa [thirdFullAxisSixCenter244, h0, h1, Pi.neg_apply] using congrFun h 2

/-- Each reflected axis center is precisely the opposite of its positive mate. -/
theorem thirdFullAxisSixCenter_reflect_zero244 :
    thirdFullAxisSixCenter244 3 = -thirdFullAxisSixCenter244 0 := by
  apply thirdFullAxisSixCenter_neg_of_fin244
  simpa only [(lowNormalSixCenter_primary (1 : ℝ)).1] using
    (lowNormalSixCenter_reflected (1 : ℝ)).1

theorem thirdFullAxisSixCenter_reflect_one244 :
    thirdFullAxisSixCenter244 4 = -thirdFullAxisSixCenter244 1 := by
  apply thirdFullAxisSixCenter_neg_of_fin244
  simpa only [(lowNormalSixCenter_primary (1 : ℝ)).2.1] using
    (lowNormalSixCenter_reflected (1 : ℝ)).2.1

theorem thirdFullAxisSixCenter_reflect_two244 :
    thirdFullAxisSixCenter244 5 = -thirdFullAxisSixCenter244 2 := by
  apply thirdFullAxisSixCenter_neg_of_fin244
  simpa only [(lowNormalSixCenter_primary (1 : ℝ)).2.2] using
    (lowNormalSixCenter_reflected (1 : ℝ)).2.2

/-- Vanishing of all three positive window amplitudes at both frequencies
kills the entire Hermitianized vector, including all reflected terms. -/
theorem thirdFullAxisSixFourierPacket_zero_of_windows244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (ξ : Freq244)
    (h0 : (thirdFullAxisWindowBump244 ρ hρ 0 : Freq244 → ℝ) ξ = 0)
    (h1 : (thirdFullAxisWindowBump244 ρ hρ 1 : Freq244 → ℝ) ξ = 0)
    (h2 : (thirdFullAxisWindowBump244 ρ hρ 2 : Freq244 → ℝ) ξ = 0)
    (hn0 : (thirdFullAxisWindowBump244 ρ hρ 0 : Freq244 → ℝ) (-ξ) = 0)
    (hn1 : (thirdFullAxisWindowBump244 ρ hρ 1 : Freq244 → ℝ) (-ξ) = 0)
    (hn2 : (thirdFullAxisWindowBump244 ρ hρ 2 : Freq244 → ℝ) (-ξ) = 0) :
    thirdFullAxisSixFourierPacket244 ρ hρ A B C ξ = 0 := by
  funext d
  simp [thirdFullAxisSixFourierPacket244, thirdFullAxisHermitianize244,
    thirdFullAxisPositiveThreePacket244, thirdFullAxisComplexWindowPacket244,
    h0, h1, h2, hn0, hn1, hn2]

/-- The ACTUAL six-frequency Fourier field is zero outside the union of
six radius-ρ axis balls. Its phases and transverse germs do not enlarge
support beyond the scalar compact windows. -/
theorem thirdFullAxisSixFourierPacket_nonzero_center244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (ξ : Freq244)
    (hU : thirdFullAxisSixFourierPacket244 ρ hρ A B C ξ ≠ 0) :
    ∃ i : Fin 6, dist ξ (thirdFullAxisSixCenter244 i) < ρ := by
  by_contra hn
  push Not at hn
  have hZero (i : Fin 6) (x : Freq244)
      (hd : ρ ≤ dist x (thirdFullAxisSixCenter244 i)) :
      (thirdFullAxisWindowBump244 ρ hρ i : Freq244 → ℝ) x = 0 := by
    by_contra hw
    exact (not_lt.mpr hd)
      (thirdFullAxisWindowBump_nonzero_ball244 ρ hρ i x hw)
  have hp0 := hZero 0 ξ (hn 0)
  have hp1 := hZero 1 ξ (hn 1)
  have hp2 := hZero 2 ξ (hn 2)
  have hNegDist (i j : Fin 6)
      (hj : thirdFullAxisSixCenter244 j = -thirdFullAxisSixCenter244 i) :
      ρ ≤ dist (-ξ) (thirdFullAxisSixCenter244 i) := by
    have heq : dist (-ξ) (thirdFullAxisSixCenter244 i) =
        dist ξ (thirdFullAxisSixCenter244 j) := by
      rw [hj]
      simpa only [neg_neg] using
        (dist_neg_neg ξ (-thirdFullAxisSixCenter244 i))
    rw [heq]
    exact hn j
  have hn0 := hZero 0 (-ξ)
    (hNegDist 0 3 thirdFullAxisSixCenter_reflect_zero244)
  have hn1 := hZero 1 (-ξ)
    (hNegDist 1 4 thirdFullAxisSixCenter_reflect_one244)
  have hn2 := hZero 2 (-ξ)
    (hNegDist 2 5 thirdFullAxisSixCenter_reflect_two244)
  exact hU (thirdFullAxisSixFourierPacket_zero_of_windows244
    ρ hρ A B C ξ hp0 hp1 hp2 hn0 hn1 hn2)

/-- Three nonzero FULL-vector frequency amplitudes on the conserving
momentum plane must belong to one of the twelve coherent labeled sectors.
The two free momenta also lie in the corresponding product ball. -/
theorem thirdFullAxisSixFourierPacket_coherent_pair244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (A B C : Freq244) (z : Pair244)
    (hp : thirdFullAxisSixFourierPacket244 ρ hρ A B C z.1 ≠ 0)
    (hq : thirdFullAxisSixFourierPacket244 ρ hρ A B C
      (thirdFullMiddleFrequency244 z) ≠ 0)
    (hr : thirdFullAxisSixFourierPacket244 ρ hρ A B C z.2 ≠ 0) :
    ∃ i j k : Fin 6, lowNormalCoherentCenters i j k ∧
      dist z (thirdFullAxisSixCenter244 i, thirdFullAxisSixCenter244 k) < ρ := by
  obtain ⟨i, hi⟩ := thirdFullAxisSixFourierPacket_nonzero_center244
    ρ hρ A B C z.1 hp
  obtain ⟨j, hj⟩ := thirdFullAxisSixFourierPacket_nonzero_center244
    ρ hρ A B C (thirdFullMiddleFrequency244 z) hq
  obtain ⟨k, hk⟩ := thirdFullAxisSixFourierPacket_nonzero_center244
    ρ hρ A B C z.2 hr
  have hBall (l : Fin 6) (x : Freq244)
      (hd : dist x (thirdFullAxisSixCenter244 l) < ρ) :
      ∀ a : A3, |x a - thirdFullAxisSixCenter244 l a| <
        lowNormalSixCenterSeparationRadius (1 : ℝ) := by
    intro a
    have hc : |x a - thirdFullAxisSixCenter244 l a| ≤
        dist x (thirdFullAxisSixCenter244 l) := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply, dist_eq_norm] using
        (norm_le_pi_norm (x - thirdFullAxisSixCenter244 l) a)
    exact lt_of_le_of_lt hc (lt_of_lt_of_le hd hSmall)
  have hm : ∀ a : A3,
      z.1 a + thirdFullMiddleFrequency244 z a + z.2 a = 0 := by
    intro a
    dsimp [thirdFullMiddleFrequency244]
    ring
  have hCoherent : lowNormalCoherentCenters i j k :=
    thirdFullAxisSixCenter_coordinateBall_zero_sum_coherent244
      i j k z.1 (thirdFullMiddleFrequency244 z) z.2
      (hBall i z.1 hi)
      (hBall j (thirdFullMiddleFrequency244 z) hj)
      (hBall k z.2 hk) hm
  refine ⟨i, j, k, hCoherent, ?_⟩
  simpa only [Prod.dist_eq, max_lt_iff] using And.intro hi hk

/-- Exact Fourier spectrum of the REAL constructed velocity on the
coordinate carrier. The Hilbert-space conversion is not left implicit. -/
noncomputable def thirdFullAxisRealSchwartzSpectrum244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (ξ : Freq244) : A3 → ℂ :=
  fun j => 𝓕 (h3SchwartzComplexify
    (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C j)) (WithLp.toLp 2 ξ)

/-- The real physical velocity's Fourier spectrum agrees with the complete
six-window packet, so the support geometry applies directly to the velocity. -/
theorem thirdFullAxisRealSchwartzSpectrum_eq_packet244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (ξ : Freq244) :
    thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C ξ =
      thirdFullAxisSixFourierPacket244 ρ hρ A B C ξ := by
  -- Expose the definitional spectrum lambda before applying Fourier recovery.
  -- `simpa` alone does not unfold the locally defined spectrum on its target.
  change (fun j : A3 =>
    𝓕 (h3SchwartzComplexify
      (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C j))
        (WithLp.toLp 2 ξ)) =
      thirdFullAxisSixFourierPacket244 ρ hρ A B C ξ
  simpa only [WithLp.ofLp_toLp] using
    (thirdFullAxisRealSchwartz_fourier_vector244 ρ hρ A B C
      (WithLp.toLp 2 ξ))

/-- The nonlinear three-frequency support theorem now holds for the
ACTUAL REAL divergence-free Schwartz velocity, not an auxiliary symbol. -/
theorem thirdFullAxisRealSchwartzSpectrum_coherent_pair244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (A B C : Freq244) (z : Pair244)
    (hp : thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C z.1 ≠ 0)
    (hq : thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
      (thirdFullMiddleFrequency244 z) ≠ 0)
    (hr : thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C z.2 ≠ 0) :
    ∃ i j k : Fin 6, lowNormalCoherentCenters i j k ∧
      dist z (thirdFullAxisSixCenter244 i, thirdFullAxisSixCenter244 k) < ρ := by
  simp only [thirdFullAxisRealSchwartzSpectrum_eq_packet244] at hp hq hr
  exact thirdFullAxisSixFourierPacket_coherent_pair244
    ρ hρ hSmall A B C z hp hq hr

/-- Every product of three spectral norms is zero away from all twelve
coherent-sector pair balls. This gives a concrete nonnegative majorant whose
support captures the complete real velocity's cubic Fourier interactions. -/
noncomputable def thirdFullAxisRealSchwartzTripleMass244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) (z : Pair244) : ℝ :=
  ‖thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C z.1‖ *
    ‖thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
      (thirdFullMiddleFrequency244 z)‖ *
    ‖thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C z.2‖

theorem thirdFullAxisRealSchwartzTripleMass_zero_off_coherent244
    (ρ : ℝ) (hρ : 0 < ρ)
    (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ))
    (A B C : Freq244) (z : Pair244)
    (hAway : ∀ i j k : Fin 6, lowNormalCoherentCenters i j k →
      ρ ≤ dist z (thirdFullAxisSixCenter244 i, thirdFullAxisSixCenter244 k)) :
    thirdFullAxisRealSchwartzTripleMass244 ρ hρ A B C z = 0 := by
  by_cases hp : thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C z.1 = 0
  · simp [thirdFullAxisRealSchwartzTripleMass244, hp]
  by_cases hq : thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C
      (thirdFullMiddleFrequency244 z) = 0
  · simp [thirdFullAxisRealSchwartzTripleMass244, hq]
  by_cases hr : thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C z.2 = 0
  · simp [thirdFullAxisRealSchwartzTripleMass244, hr]
  obtain ⟨i, j, k, hcoh, hdist⟩ :=
    thirdFullAxisRealSchwartzSpectrum_coherent_pair244
      ρ hρ hSmall A B C z hp hq hr
  exact ((not_lt.mpr (hAway i j k hcoh)) hdist).elim

/-- The exact physical commutator/Fourier identity, now specialized to the
constructed REAL velocity. A nonzero global integral remains to be proved. -/
theorem thirdFullAxisRealSchwartz_commutator_eq_fourier244
    (ρ : ℝ) (hρ : 0 < ρ) (A B C : Freq244) :
    fullSchwartzThirdCommutator244
        (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C) =
      (fullThirdSchwartzFourierCoefficient244
        (thirdFullAxisRealSchwartzVelocity244 ρ hρ A B C)).re :=
  fullSchwartzThirdCommutator_eq_fullFourierRe244 _

end
end PrimeTensor.FirstMonomialTriad
