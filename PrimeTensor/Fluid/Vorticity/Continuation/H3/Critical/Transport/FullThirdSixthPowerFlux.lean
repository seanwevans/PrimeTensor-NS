import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdProjectedRadialIntegral
import Mathlib.Tactic

/-!
# Complete physical H³ six-orbit as differences of sixth-power Fourier radii

For an exact momentum-conserving, solenoidal triad, the divided-difference
multipliers of the previously proved full-third radial-defect identity are
NOT independent angular coefficients. The three momenta satisfy

  (p·q)+(p·r) = -|p|²,
  (p·q)+(q·r) = -|q|²,
  (p·r)+(q·r) = -|r|².

Consequently the three quadratic multipliers become sums of pairwise products
of the SQUARED radii, and each radial-defect product is EXACTLY a difference
of CUBES of squared radii (i.e. sixth powers of frequency lengths).

The result retains all four physical gradient pieces and all three
interpolation pieces through the previously verified corrected six-orbit.
It also applies, without frozen polarizations, to the actual moving
transverse Leray-germ kernel and its compact six-dimensional integral.

This is a symbol/compact-kernel identity, not an unconditional estimate for
the arbitrary-Schwartz full Fourier coefficient or a PDE-time H³ bound.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Metric Set
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 1800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Pair244 := (A3 → ℝ) × (A3 → ℝ)

noncomputable local instance axisFintypeFullThirdSixthPowerFlux
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance frequencyMeasureFullThirdSixthPowerFlux :
    MeasureSpace (A3 → ℝ) :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The apparent angular cubic divided difference is the elementary
quadratic form in the shifted arguments. -/
theorem thirdFullRadialDefectMultiplier_shiftedSquares244 (x y z : ℝ) :
    thirdFullRadialDefectMultiplier244 x y z =
      (x + z) ^ 2 + (x + z) * (y + z) + (y + z) ^ 2 := by
  unfold thirdFullRadialDefectMultiplier244
  ring

/-- The multiplier itself is always nonnegative. This is an algebraic
property, not a global sign condition on the full cubic transport. -/
theorem thirdFullRadialDefectMultiplier_nonneg244 (x y z : ℝ) :
    0 ≤ thirdFullRadialDefectMultiplier244 x y z := by
  have h : 4 * thirdFullRadialDefectMultiplier244 x y z =
      (x - y) ^ 2 + 3 * (x + y + 2 * z) ^ 2 := by
    unfold thirdFullRadialDefectMultiplier244
    ring
  nlinarith only [h, sq_nonneg (x - y), sq_nonneg (x + y + 2 * z)]

/-- The COMPLETE corrected physical third-order six-permutation symbol
is an oriented sum of three *differences of sixth powers of frequencies*.
No term of the underlying physical gradient or interpolation polynomial
has been discarded; all angular structure now resides in the three genuine
polarization contractions. -/
theorem thirdFullPhysicalSix_sixthPowerFlux244
    (p q r A B C : A3 → ℝ)
    (hMomentum : ∀ i, p i + q i + r i = 0)
    (hA : thirdTriadAxisDot244 A p = 0)
    (hB : thirdTriadAxisDot244 B q = 0)
    (hC : thirdTriadAxisDot244 C r = 0) :
    thirdFullPhysicalSixSymbol244 p q r A B C =
      (thirdTriadAxisDot244 A C * thirdTriadAxisDot244 B r) *
        ((thirdTriadAxisDot244 r r) ^ 3 - (thirdTriadAxisDot244 p p) ^ 3) +
      (thirdTriadAxisDot244 A B * thirdTriadAxisDot244 C q) *
        ((thirdTriadAxisDot244 q q) ^ 3 - (thirdTriadAxisDot244 p p) ^ 3) +
      (thirdTriadAxisDot244 B C * thirdTriadAxisDot244 A r) *
        ((thirdTriadAxisDot244 r r) ^ 3 - (thirdTriadAxisDot244 q q) ^ 3) := by
  let P : ℝ := thirdTriadAxisDot244 p p
  let Q : ℝ := thirdTriadAxisDot244 q q
  let R : ℝ := thirdTriadAxisDot244 r r
  let a : ℝ := thirdTriadAxisDot244 p q
  let b : ℝ := thirdTriadAxisDot244 p r
  let c : ℝ := thirdTriadAxisDot244 q r
  have hpRaw := momentum_dot p q r p hMomentum
  have hqRaw := momentum_dot p q r q hMomentum
  have hrRaw := momentum_dot p q r r hMomentum
  have hp : P + a + b = 0 := by
    change thirdTriadAxisDot244 p p + thirdTriadAxisDot244 q p +
      thirdTriadAxisDot244 r p = 0 at hpRaw
    rw [thirdFullAxisDot_comm244 q p, thirdFullAxisDot_comm244 r p] at hpRaw
    exact hpRaw
  have hq : a + Q + c = 0 := by
    change thirdTriadAxisDot244 p q + thirdTriadAxisDot244 q q +
      thirdTriadAxisDot244 r q = 0 at hqRaw
    rw [thirdFullAxisDot_comm244 r q] at hqRaw
    exact hqRaw
  have hr : b + c + R = 0 := by
    change thirdTriadAxisDot244 p r + thirdTriadAxisDot244 q r +
      thirdTriadAxisDot244 r r = 0 at hrRaw
    exact hrRaw
  have hAP : a + b = -P := by linarith only [hp]
  have hBP : b + a = -P := by linarith only [hp]
  have hAQ : a + c = -Q := by linarith only [hq]
  have hCQ : c + a = -Q := by linarith only [hq]
  have hCR : c + b = -R := by linarith only [hr]
  have hBR : b + c = -R := by linarith only [hr]
  have hG1 : thirdFullRadialDefectMultiplier244 a c b =
      P ^ 2 + P * R + R ^ 2 := by
    rw [thirdFullRadialDefectMultiplier_shiftedSquares244, hAP, hCR]
    ring
  have hG2 : thirdFullRadialDefectMultiplier244 b c a =
      P ^ 2 + P * Q + Q ^ 2 := by
    rw [thirdFullRadialDefectMultiplier_shiftedSquares244, hBP, hCQ]
    ring
  have hG3 : thirdFullRadialDefectMultiplier244 a b c =
      Q ^ 2 + Q * R + R ^ 2 := by
    rw [thirdFullRadialDefectMultiplier_shiftedSquares244, hAQ, hBR]
    ring
  rw [thirdFullPhysicalSix_radialDefect_factorization244
    p q r A B C hMomentum hA hB hC]
  change
    (thirdTriadAxisDot244 A C * thirdTriadAxisDot244 B r) *
      (R - P) * thirdFullRadialDefectMultiplier244 a c b +
    (thirdTriadAxisDot244 A B * thirdTriadAxisDot244 C q) *
      (Q - P) * thirdFullRadialDefectMultiplier244 b c a +
    (thirdTriadAxisDot244 B C * thirdTriadAxisDot244 A r) *
      (R - Q) * thirdFullRadialDefectMultiplier244 a b c =
    (thirdTriadAxisDot244 A C * thirdTriadAxisDot244 B r) *
      (R ^ 3 - P ^ 3) +
    (thirdTriadAxisDot244 A B * thirdTriadAxisDot244 C q) *
      (Q ^ 3 - P ^ 3) +
    (thirdTriadAxisDot244 B C * thirdTriadAxisDot244 A r) *
      (R ^ 3 - Q ^ 3)
  rw [hG1, hG2, hG3]
  ring

/-- When TWO squared radii coincide, the full third-order symbol is
exactly the remaining two-shell transfer, rather than necessarily zero. -/
theorem thirdFullPhysicalSix_twoEqualRadii_flux244
    (p q r A B C : A3 → ℝ)
    (hMomentum : ∀ i, p i + q i + r i = 0)
    (hA : thirdTriadAxisDot244 A p = 0)
    (hB : thirdTriadAxisDot244 B q = 0)
    (hC : thirdTriadAxisDot244 C r = 0)
    (hPQ : thirdTriadAxisDot244 p p = thirdTriadAxisDot244 q q) :
    thirdFullPhysicalSixSymbol244 p q r A B C =
      ((thirdTriadAxisDot244 r r) ^ 3 - (thirdTriadAxisDot244 p p) ^ 3) *
        (thirdTriadAxisDot244 A C * thirdTriadAxisDot244 B r +
          thirdTriadAxisDot244 B C * thirdTriadAxisDot244 A r) := by
  rw [thirdFullPhysicalSix_sixthPowerFlux244 p q r A B C
    hMomentum hA hB hC]
  rw [← hPQ]
  ring

/-- The actual frequency-dependent solenoidal Fourier germ, now written
as an exact three-term SIXTH-POWER radial flux density. -/
noncomputable def thirdFullProjectedSixthPowerFluxDensity244
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z : Pair244) : ℝ :=
  let p := z.1
  let q := thirdFullMiddleFrequency244 z
  let r := z.2
  let U := thirdFullFixedCenterTransverseGerm244 p₀ p A
  let V := thirdFullFixedCenterTransverseGerm244 q₀ q B
  let W := thirdFullFixedCenterTransverseGerm244 r₀ r C
  2 * (
    (thirdTriadAxisDot244 U W * thirdTriadAxisDot244 V r) *
      ((thirdTriadAxisDot244 r r) ^ 3 - (thirdTriadAxisDot244 p p) ^ 3) +
    (thirdTriadAxisDot244 U V * thirdTriadAxisDot244 W q) *
      ((thirdTriadAxisDot244 q q) ^ 3 - (thirdTriadAxisDot244 p p) ^ 3) +
    (thirdTriadAxisDot244 V W * thirdTriadAxisDot244 U r) *
      ((thirdTriadAxisDot244 r r) ^ 3 - (thirdTriadAxisDot244 q q) ^ 3))

/-- The projected, phase-correct Hermitian kernel is pointwise EXACTLY its
oriented sixth-power flux density, without a new cutoff or positivity input. -/
theorem thirdFullProjectedHermitian_eq_sixthPowerFlux244
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z : Pair244) :
    thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C z =
      thirdFullProjectedSixthPowerFluxDensity244 p₀ q₀ r₀ A B C z := by
  let q := thirdFullMiddleFrequency244 z
  let U := thirdFullFixedCenterTransverseGerm244 p₀ z.1 A
  let V := thirdFullFixedCenterTransverseGerm244 q₀ q B
  let W := thirdFullFixedCenterTransverseGerm244 r₀ z.2 C
  have hm : ∀ i : A3, z.1 i + q i + z.2 i = 0 := by
    intro i
    dsimp [q, thirdFullMiddleFrequency244]
    ring
  have ht := thirdFullProjectedHermitianKernel_transverse244
    p₀ q₀ r₀ A B C z
  have hU : thirdTriadAxisDot244 U z.1 = 0 := by
    rw [thirdFullAxisDot_comm244]
    exact ht.1
  have hV : thirdTriadAxisDot244 V q = 0 := by
    rw [thirdFullAxisDot_comm244]
    exact ht.2.1
  have hW : thirdTriadAxisDot244 W z.2 = 0 := by
    rw [thirdFullAxisDot_comm244]
    exact ht.2.2
  have hSix := thirdFullPhysicalSix_sixthPowerFlux244
    z.1 q z.2 U V W hm hU hV hW
  have hKernel :
      thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C z =
        2 * thirdFullPhysicalSixSymbol244 z.1 q z.2 U V W := by
    unfold thirdFullProjectedHermitianKernel244
    rw [thirdFullHermitianMomentumKernel_eq244]
  rw [hKernel, hSix]
  rfl

/-- On ANY compact momentum-pair ball the sixth-power flux density is
absolutely integrable, as a consequence of the existing actual moving
polarization continuity and the exact pointwise identity. -/
theorem thirdFullProjectedSixthPowerFlux_integrableOn_ball244
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z₀ : Pair244) (σ : ℝ) :
    IntegrableOn (thirdFullProjectedSixthPowerFluxDensity244 p₀ q₀ r₀ A B C)
      (Metric.closedBall z₀ σ) (volume.prod volume) := by
  have hK : IntegrableOn
      (thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C)
      (Metric.closedBall z₀ σ) (volume.prod volume) :=
    (thirdFullProjectedHermitianKernel_continuous244 p₀ q₀ r₀ A B C).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)
  exact hK.congr (Filter.Eventually.of_forall (fun z =>
    thirdFullProjectedHermitian_eq_sixthPowerFlux244 p₀ q₀ r₀ A B C z))

/-- The genuine six-dimensional compact Fourier integral is EXACTLY the
integral of three radial-sixth-power flux differences, with no radial
smallness assumption and no loss from taking absolute values. -/
theorem thirdFullProjectedHermitian_compact_sixthPowerFlux_integral244
    (p₀ q₀ r₀ A B C : A3 → ℝ) (z₀ : Pair244) (σ : ℝ) :
    (∫ z in Metric.closedBall z₀ σ,
      thirdFullProjectedHermitianKernel244 p₀ q₀ r₀ A B C z
        ∂(volume.prod volume)) =
      ∫ z in Metric.closedBall z₀ σ,
        thirdFullProjectedSixthPowerFluxDensity244 p₀ q₀ r₀ A B C z
          ∂(volume.prod volume) := by
  apply integral_congr_ae
  filter_upwards with z
  exact thirdFullProjectedHermitian_eq_sixthPowerFlux244 p₀ q₀ r₀ A B C z

end
end PrimeTensor.FirstMonomialTriad
