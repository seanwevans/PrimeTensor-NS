import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdRealGlobalSixSectors244
import Mathlib.Tactic

/-!
# Exact one-window isolation for the actual full-third real Schwartz Fourier field

The global physical H3 third commutator has now been reduced to six disjoint
positive-orientation signed Fourier integrals. To analyze their sign we must
identify the *actual* Fourier vector in each frequency neighborhood, rather
than substituting the sharp-center polarization into an integral.

The existing unit separation of the six actual Axis centers guarantees that,
for 2ρ ≤ 1, at most one of the six scalar windows is nonzero at any frequency.
In particular, near a positive-frequency center the three negative-frequency
Hermitian windows all vanish, and the positive three-window sum reduces to
its unique labeled polynomial transverse germ. We transfer that identity to
the exact Fourier spectrum of the constructed real Schwartz velocity.

This proves no sign by itself. It is the required algebraic localization step
for the true six-sector trilinear kernel, with its exact Fourier phases.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 1600000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ

noncomputable local instance axisFintypeFullThirdSingleWindow244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The established nonresonance radius at t=1 is at most one quarter;
therefore it always implies the stronger-than-needed window separation. -/
theorem thirdFullAxisWindowBump_width_sep_of_nonresonance244
    (ρ : ℝ) (hSmall : ρ ≤ lowNormalSixCenterSeparationRadius (1 : ℝ)) :
    2 * ρ ≤ 1 := by
  norm_num [lowNormalSixCenterSeparationRadius] at hSmall
  linarith

/-- Under twice-width unit separation, any OTHER scalar Fourier window
vanishes throughout the open radius-ρ ball of the selected center. -/
theorem thirdFullAxisWindowBump_zero_near_distinct_center244
    (ρ : ℝ) (hρ : 0 < ρ) (hSep : 2 * ρ ≤ 1)
    (i j : Fin 6) (hij : i ≠ j) (ξ : Freq244)
    (hNear : dist ξ (thirdFullAxisSixCenter244 i) < ρ) :
    (thirdFullAxisWindowBump244 ρ hρ j : Freq244 → ℝ) ξ = 0 := by
  by_contra hw
  have hj := thirdFullAxisWindowBump_nonzero_ball244 ρ hρ j ξ hw
  have hGap := thirdFullSixAxisCenters_dist_gap244 i j hij
  have hTri := dist_triangle
    (thirdFullAxisSixCenter244 i) ξ (thirdFullAxisSixCenter244 j)
  have hNear' : dist (thirdFullAxisSixCenter244 i) ξ < ρ := by
    simpa only [dist_comm] using hNear
  linarith

/-- Two nonzero scalar windows of this physical Fourier construction must
carry the SAME label whenever 2ρ ≤ 1. -/
theorem thirdFullAxisWindowBump_nonzero_labels_eq244
    (ρ : ℝ) (hρ : 0 < ρ) (hSep : 2 * ρ ≤ 1)
    (i j : Fin 6) (ξ : Freq244)
    (hi : (thirdFullAxisWindowBump244 ρ hρ i : Freq244 → ℝ) ξ ≠ 0)
    (hj : (thirdFullAxisWindowBump244 ρ hρ j : Freq244 → ℝ) ξ ≠ 0) :
    i = j := by
  by_contra hij
  have hNear := thirdFullAxisWindowBump_nonzero_ball244 ρ hρ i ξ hi
  exact hj (thirdFullAxisWindowBump_zero_near_distinct_center244
    ρ hρ hSep i j hij ξ hNear)

/-- At a frequency close to a distinct center, the entire off-label
complex transverse packet vanishes, not only its scalar cutoff. -/
theorem thirdFullAxisComplexWindowPacket_zero_near_distinct_center244
    (ρ : ℝ) (hρ : 0 < ρ) (hSep : 2 * ρ ≤ 1)
    (i j : Fin 6) (hij : i ≠ j) (ξ : Freq244)
    (hNear : dist ξ (thirdFullAxisSixCenter244 i) < ρ)
    (a : Freq244) (phase : ℂ) :
    thirdFullAxisComplexWindowPacket244 ρ hρ j a phase ξ = 0 := by
  have hZero := thirdFullAxisWindowBump_zero_near_distinct_center244
    ρ hρ hSep i j hij ξ hNear
  funext d
  simp [thirdFullAxisComplexWindowPacket244, hZero]

/-- Reflection of a positive window cannot overlap a selected *other*
center's radius-ρ neighborhood: opposite centers are among the six labels. -/
theorem thirdFullAxisWindowBump_reflected_zero_near_distinct_center244
    (ρ : ℝ) (hρ : 0 < ρ) (hSep : 2 * ρ ≤ 1)
    (i j k : Fin 6)
    (hjk : thirdFullAxisSixCenter244 k = -thirdFullAxisSixCenter244 j)
    (hik : i ≠ k) (ξ : Freq244)
    (hNear : dist ξ (thirdFullAxisSixCenter244 i) < ρ) :
    (thirdFullAxisWindowBump244 ρ hρ j : Freq244 → ℝ) (-ξ) = 0 := by
  by_contra hw
  have hj := thirdFullAxisWindowBump_nonzero_ball244 ρ hρ j (-ξ) hw
  have hReflectDist :
      dist ξ (-thirdFullAxisSixCenter244 j) =
        dist (-ξ) (thirdFullAxisSixCenter244 j) := by
    simpa only [neg_neg] using
      (dist_neg_neg ξ (-thirdFullAxisSixCenter244 j)).symm
  have hk : dist ξ (thirdFullAxisSixCenter244 k) < ρ := by
    rw [hjk, hReflectDist]
    exact hj
  have hGap := thirdFullSixAxisCenters_dist_gap244 i k hik
  have hTri := dist_triangle
    (thirdFullAxisSixCenter244 i) ξ (thirdFullAxisSixCenter244 k)
  have hNear' : dist (thirdFullAxisSixCenter244 i) ξ < ρ := by
    simpa only [dist_comm] using hNear
  linarith

/-- On each of the three positive center balls, the Hermitian-reflected
positive packet is exactly ZERO at -ξ. No reality partner survives there. -/
theorem thirdFullAxisPositiveThreePacket_zero_at_reflected_frequency244
    (ρ : ℝ) (hρ : 0 < ρ) (hSep : 2 * ρ ≤ 1)
    (i : Fin 6) (hi : i = 0 ∨ i = 1 ∨ i = 2)
    (A B C : Freq244) (ξ : Freq244)
    (hNear : dist ξ (thirdFullAxisSixCenter244 i) < ρ) :
    thirdFullAxisPositiveThreePacket244 ρ hρ A B C 1 1 Complex.I (-ξ) = 0 := by
  have hi3 : i ≠ 3 := by
    rcases hi with h | h | h <;> rw [h] <;> decide
  have hi4 : i ≠ 4 := by
    rcases hi with h | h | h <;> rw [h] <;> decide
  have hi5 : i ≠ 5 := by
    rcases hi with h | h | h <;> rw [h] <;> decide
  have h0 := thirdFullAxisWindowBump_reflected_zero_near_distinct_center244
    ρ hρ hSep i 0 3 thirdFullAxisSixCenter_reflect_zero244 hi3 ξ hNear
  have h1 := thirdFullAxisWindowBump_reflected_zero_near_distinct_center244
    ρ hρ hSep i 1 4 thirdFullAxisSixCenter_reflect_one244 hi4 ξ hNear
  have h2 := thirdFullAxisWindowBump_reflected_zero_near_distinct_center244
    ρ hρ hSep i 2 5 thirdFullAxisSixCenter_reflect_two244 hi5 ξ hNear
  funext d
  simp [thirdFullAxisPositiveThreePacket244,
    thirdFullAxisComplexWindowPacket244, h0, h1, h2]

/-- The actual Hermitian six-window spectrum equals precisely the zeroth
positive transverse-germ packet near p, with phase one. -/
theorem thirdFullAxisSixFourierPacket_isolated_zero244
    (ρ : ℝ) (hρ : 0 < ρ) (hSep : 2 * ρ ≤ 1)
    (A B C : Freq244) (ξ : Freq244)
    (hNear : dist ξ (thirdFullAxisSixCenter244 0) < ρ) :
    thirdFullAxisSixFourierPacket244 ρ hρ A B C ξ =
      thirdFullAxisComplexWindowPacket244 ρ hρ 0 A 1 ξ := by
  have h1 := thirdFullAxisComplexWindowPacket_zero_near_distinct_center244
    ρ hρ hSep 0 1 (by decide) ξ hNear B (1 : ℂ)
  have h2 := thirdFullAxisComplexWindowPacket_zero_near_distinct_center244
    ρ hρ hSep 0 2 (by decide) ξ hNear C Complex.I
  have hn := thirdFullAxisPositiveThreePacket_zero_at_reflected_frequency244
    ρ hρ hSep 0 (Or.inl rfl) A B C ξ hNear
  funext d
  change thirdFullAxisPositiveThreePacket244 ρ hρ A B C 1 1 Complex.I ξ d +
      star (thirdFullAxisPositiveThreePacket244 ρ hρ A B C 1 1 Complex.I (-ξ) d) =
    thirdFullAxisComplexWindowPacket244 ρ hρ 0 A 1 ξ d
  rw [hn]
  simp only [Pi.zero_apply, star_zero, add_zero]
  simp [thirdFullAxisPositiveThreePacket244, h1, h2]

/-- Exact isolation near q, with phase one. -/
theorem thirdFullAxisSixFourierPacket_isolated_one244
    (ρ : ℝ) (hρ : 0 < ρ) (hSep : 2 * ρ ≤ 1)
    (A B C : Freq244) (ξ : Freq244)
    (hNear : dist ξ (thirdFullAxisSixCenter244 1) < ρ) :
    thirdFullAxisSixFourierPacket244 ρ hρ A B C ξ =
      thirdFullAxisComplexWindowPacket244 ρ hρ 1 B 1 ξ := by
  have h0 := thirdFullAxisComplexWindowPacket_zero_near_distinct_center244
    ρ hρ hSep 1 0 (by decide) ξ hNear A (1 : ℂ)
  have h2 := thirdFullAxisComplexWindowPacket_zero_near_distinct_center244
    ρ hρ hSep 1 2 (by decide) ξ hNear C Complex.I
  have hn := thirdFullAxisPositiveThreePacket_zero_at_reflected_frequency244
    ρ hρ hSep 1 (Or.inr (Or.inl rfl)) A B C ξ hNear
  funext d
  change thirdFullAxisPositiveThreePacket244 ρ hρ A B C 1 1 Complex.I ξ d +
      star (thirdFullAxisPositiveThreePacket244 ρ hρ A B C 1 1 Complex.I (-ξ) d) =
    thirdFullAxisComplexWindowPacket244 ρ hρ 1 B 1 ξ d
  rw [hn]
  simp only [Pi.zero_apply, star_zero, add_zero]
  simp [thirdFullAxisPositiveThreePacket244, h0, h2]

/-- Exact isolation near r, retaining its essential complex phase I. -/
theorem thirdFullAxisSixFourierPacket_isolated_two244
    (ρ : ℝ) (hρ : 0 < ρ) (hSep : 2 * ρ ≤ 1)
    (A B C : Freq244) (ξ : Freq244)
    (hNear : dist ξ (thirdFullAxisSixCenter244 2) < ρ) :
    thirdFullAxisSixFourierPacket244 ρ hρ A B C ξ =
      thirdFullAxisComplexWindowPacket244 ρ hρ 2 C Complex.I ξ := by
  have h0 := thirdFullAxisComplexWindowPacket_zero_near_distinct_center244
    ρ hρ hSep 2 0 (by decide) ξ hNear A (1 : ℂ)
  have h1 := thirdFullAxisComplexWindowPacket_zero_near_distinct_center244
    ρ hρ hSep 2 1 (by decide) ξ hNear B (1 : ℂ)
  have hn := thirdFullAxisPositiveThreePacket_zero_at_reflected_frequency244
    ρ hρ hSep 2 (Or.inr (Or.inr rfl)) A B C ξ hNear
  funext d
  change thirdFullAxisPositiveThreePacket244 ρ hρ A B C 1 1 Complex.I ξ d +
      star (thirdFullAxisPositiveThreePacket244 ρ hρ A B C 1 1 Complex.I (-ξ) d) =
    thirdFullAxisComplexWindowPacket244 ρ hρ 2 C Complex.I ξ d
  rw [hn]
  simp only [Pi.zero_apply, star_zero, add_zero]
  simp [thirdFullAxisPositiveThreePacket244, h0, h1]

/-- The frequency-local calculation applies directly to the Fourier
transform of the recovered REAL Schwartz velocity at the primary p window. -/
theorem thirdFullAxisRealSchwartzSpectrum_isolated_zero244
    (ρ : ℝ) (hρ : 0 < ρ) (hSep : 2 * ρ ≤ 1)
    (A B C : Freq244) (ξ : Freq244)
    (hNear : dist ξ (thirdFullAxisSixCenter244 0) < ρ) :
    thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C ξ =
      thirdFullAxisComplexWindowPacket244 ρ hρ 0 A 1 ξ := by
  rw [thirdFullAxisRealSchwartzSpectrum_eq_packet244]
  exact thirdFullAxisSixFourierPacket_isolated_zero244 ρ hρ hSep A B C ξ hNear

/-- Same exact physical Fourier identification at the second q window. -/
theorem thirdFullAxisRealSchwartzSpectrum_isolated_one244
    (ρ : ℝ) (hρ : 0 < ρ) (hSep : 2 * ρ ≤ 1)
    (A B C : Freq244) (ξ : Freq244)
    (hNear : dist ξ (thirdFullAxisSixCenter244 1) < ρ) :
    thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C ξ =
      thirdFullAxisComplexWindowPacket244 ρ hρ 1 B 1 ξ := by
  rw [thirdFullAxisRealSchwartzSpectrum_eq_packet244]
  exact thirdFullAxisSixFourierPacket_isolated_one244 ρ hρ hSep A B C ξ hNear

/-- Same exact physical Fourier identification at the third r window,
including the prescribed phase I needed for the signed center value. -/
theorem thirdFullAxisRealSchwartzSpectrum_isolated_two244
    (ρ : ℝ) (hρ : 0 < ρ) (hSep : 2 * ρ ≤ 1)
    (A B C : Freq244) (ξ : Freq244)
    (hNear : dist ξ (thirdFullAxisSixCenter244 2) < ρ) :
    thirdFullAxisRealSchwartzSpectrum244 ρ hρ A B C ξ =
      thirdFullAxisComplexWindowPacket244 ρ hρ 2 C Complex.I ξ := by
  rw [thirdFullAxisRealSchwartzSpectrum_eq_packet244]
  exact thirdFullAxisSixFourierPacket_isolated_two244 ρ hρ hSep A B C ξ hNear

end
end PrimeTensor.FirstMonomialTriad
