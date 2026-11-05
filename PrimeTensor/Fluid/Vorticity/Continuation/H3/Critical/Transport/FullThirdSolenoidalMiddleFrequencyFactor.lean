import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalPhysicalOffshellPersistence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalRadialShellFluxGain
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadNormalFrequency
import Mathlib.Tactic

/-!
# A genuine middle-frequency factor in the solenoidal H³ complex flux

The radial-spread bound controls balanced triads but loses the low-frequency
factor when q is small and p,r are large. Here we use p+q+r=0 before
estimating the complex six-transfer symbol. The exact identity

  |r|² - |p|² = |q|² + 2 p·q

places q in the first cubic gap. The third contraction originally contains
r·A; physical solenoidality p·A=0 replaces it by -q·A. The second
contraction already contains q·C. Thus ALL THREE complex channels have a
middle-frequency factor, with no Hermitian replacement or division by |q|.

The existing shell-gap lemma also gives

  ||r|^6 - |p|^6| <= 3 S² (|p|+|r|) |q|,
  S=max(|p|²,|q|²,|r|²).

These are exact algebraic and pointwise estimates. No claim that the
resulting seventh-order trilinear majorant is globally H³-integrable, nor
that it absorbs the physical signed transport, is made here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeMiddleFrequencyFactor244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact momentum substitutions for all three squared-radius differences.
No inverse-frequency factors occur, including at q=0. -/
theorem thirdFullTriadSquareRadius_middleFrequencyIdentities244
    (p q r : A3 → ℝ)
    (hm : ∀ i, p i + q i + r i = 0) :
    (thirdTriadAxisDot244 r r - thirdTriadAxisDot244 p p =
        thirdTriadAxisDot244 q q + 2 * thirdTriadAxisDot244 p q) ∧
    (thirdTriadAxisDot244 q q - thirdTriadAxisDot244 p p =
        -(thirdTriadAxisDot244 r r + 2 * thirdTriadAxisDot244 q r)) ∧
    (thirdTriadAxisDot244 r r - thirdTriadAxisDot244 q q =
        thirdTriadAxisDot244 p p + 2 * thirdTriadAxisDot244 p q) := by
  have hp := momentum_dot p q r p hm
  change thirdTriadAxisDot244 p p + thirdTriadAxisDot244 q p +
    thirdTriadAxisDot244 r p = 0 at hp
  rw [thirdFullAxisDot_comm244 q p, thirdFullAxisDot_comm244 r p] at hp
  have hq := momentum_dot p q r q hm
  change thirdTriadAxisDot244 p q + thirdTriadAxisDot244 q q +
    thirdTriadAxisDot244 r q = 0 at hq
  rw [thirdFullAxisDot_comm244 r q] at hq
  have hr := momentum_dot p q r r hm
  change thirdTriadAxisDot244 p r + thirdTriadAxisDot244 q r +
    thirdTriadAxisDot244 r r = 0 at hr
  constructor
  · linarith only [hp, hq, hr]
  constructor
  · linarith only [hp, hq, hr]
  · linarith only [hp, hq, hr]

/-- The true complex cubic gap contains the *middle* Fourier frequency.
The factorization is valid for arbitrary real momenta satisfying conservation. -/
theorem thirdFullComplexCubeGap_middleFrequencyFactor244
    (p q r : A3 → ℝ)
    (hm : ∀ i, p i + q i + r i = 0) :
    ((thirdTriadAxisDot244 r r : ℂ) ^ 3 -
      (thirdTriadAxisDot244 p p : ℂ) ^ 3) =
    ((thirdTriadAxisDot244 q q + 2 * thirdTriadAxisDot244 p q : ℝ) : ℂ) *
      ((thirdTriadAxisDot244 r r : ℂ) ^ 2 +
        (thirdTriadAxisDot244 r r : ℂ) *
          (thirdTriadAxisDot244 p p : ℂ) +
        (thirdTriadAxisDot244 p p : ℂ) ^ 2) := by
  have hRP := (thirdFullTriadSquareRadius_middleFrequencyIdentities244
    p q r hm).1
  calc
    _ = ((thirdTriadAxisDot244 r r - thirdTriadAxisDot244 p p : ℝ) : ℂ) *
      ((thirdTriadAxisDot244 r r : ℂ) ^ 2 +
        (thirdTriadAxisDot244 r r : ℂ) *
          (thirdTriadAxisDot244 p p : ℂ) +
        (thirdTriadAxisDot244 p p : ℂ) ^ 2) := by
          push_cast
          ring
    _ = _ := by rw [hRP]

/-- Signed radial gap gains one full middle-frequency power, before any
Fourier integration. The q factor comes from the existing exact gap lemma. -/
theorem thirdFullComplexCubeGap_middleFrequencyBound244
    (p q r : A3 → ℝ)
    (hm : ∀ i, p i + q i + r i = 0) :
    ‖((thirdTriadAxisDot244 r r : ℂ) ^ 3 -
      (thirdTriadAxisDot244 p p : ℂ) ^ 3)‖ ≤
      (3 * (thirdFullTriadSquareRadiusMax244 p q r) ^ 2) *
        ((frequencyNorm p + frequencyNorm r) * frequencyNorm q) := by
  let P : ℝ := thirdTriadAxisDot244 p p
  let R : ℝ := thirdTriadAxisDot244 r r
  let S : ℝ := thirdFullTriadSquareRadiusMax244 p q r
  have hp0 : 0 ≤ P := thirdFull_axisSquareRadius_nonneg244 p
  have hr0 : 0 ≤ R := thirdFull_axisSquareRadius_nonneg244 r
  have hpS : P ≤ S := by
    dsimp only [S, thirdFullTriadSquareRadiusMax244]
    exact le_max_left _ _
  have hrS : R ≤ S := by
    dsimp only [S, thirdFullTriadSquareRadiusMax244]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hGap : |R - P| ≤
      (frequencyNorm p + frequencyNorm r) * frequencyNorm q := by
    simpa only [R, P, thirdTriadAxisDot244, dot] using
      (shell_gap_le_frequencyNorm p q r hm)
  rw [thirdFull_complexCubeGap_norm244]
  calc
    |R ^ 3 - P ^ 3| ≤ (3 * S ^ 2) * |R - P| :=
      thirdFull_realCubeGap_le_radiusSquare244 R P S hr0 hp0 hrS hpS
    _ ≤ (3 * S ^ 2) *
        ((frequencyNorm p + frequencyNorm r) * frequencyNorm q) :=
      mul_le_mul_of_nonneg_left hGap (by positivity)

/-- Solenoidality transfers the third channel's derivative from the outer
frequency r onto the middle frequency q. All three terms now contain q. -/
theorem thirdFullComplexSixthPowerFlux_middleFrequencyFactorization244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ)
    (hm : ∀ i, p i + q i + r i = 0)
    (hA : mixedDot p A = 0) :
    thirdFullComplexSixthPowerFlux244 p q r A B C =
      (thirdFullComplexPolarizationDot244 A C * mixedDot r B) *
        (((thirdTriadAxisDot244 q q + 2 * thirdTriadAxisDot244 p q : ℝ) : ℂ) *
          ((thirdTriadAxisDot244 r r : ℂ) ^ 2 +
            (thirdTriadAxisDot244 r r : ℂ) *
              (thirdTriadAxisDot244 p p : ℂ) +
            (thirdTriadAxisDot244 p p : ℂ) ^ 2)) +
      (thirdFullComplexPolarizationDot244 A B * mixedDot q C) *
        ((thirdTriadAxisDot244 q q : ℂ) ^ 3 -
          (thirdTriadAxisDot244 p p : ℂ) ^ 3) -
      (thirdFullComplexPolarizationDot244 B C * mixedDot q A) *
        ((thirdTriadAxisDot244 r r : ℂ) ^ 3 -
          (thirdTriadAxisDot244 q q : ℂ) ^ 3) := by
  have hmA := thirdFullComplex_momentum_dot244 p q r A hm
  have hrA : mixedDot r A = -mixedDot q A := by
    calc
      mixedDot r A =
        (mixedDot p A + mixedDot q A + mixedDot r A) -
          mixedDot p A - mixedDot q A := by ring
      _ = -mixedDot q A := by rw [hmA, hA]; ring
  have hGap := thirdFullComplexCubeGap_middleFrequencyFactor244 p q r hm
  unfold thirdFullComplexSixthPowerFlux244
  rw [hGap, hrA]
  ring

/-- The exact sixth-power flux has no nonzero middle-frequency-zero channel.
The conclusion uses momentum conservation and just the p-polarization
solenoidal equation, without an assumption on complex phases. -/
theorem thirdFullComplexSixthPowerFlux_zeroMiddle244
    (p r : A3 → ℝ) (A B C : A3 → ℂ)
    (hm : ∀ i, p i + r i = 0)
    (hA : mixedDot p A = 0) :
    thirdFullComplexSixthPowerFlux244 p (fun _ : A3 => (0 : ℝ)) r A B C = 0 := by
  have hm0 : ∀ i,
      p i + (fun _ : A3 => (0 : ℝ)) i + r i = 0 := by
    intro i
    simpa only [add_zero] using hm i
  rw [thirdFullComplexSixthPowerFlux_middleFrequencyFactorization244
    p (fun _ : A3 => (0 : ℝ)) r A B C hm0 hA]
  simp [thirdTriadAxisDot244, mixedDot]

/-- Apply the exact q-factorization to the complex Fourier polarization of a
GENUINE solenoidal Schwartz velocity and the actual triad (p,-p-r,r).
No auxiliary real-amplitude replacement or density limit is used. -/
theorem thirdFullSchwartzSixthPowerFlux_middleFrequencyFactorization244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (z : V3 × V3) :
    let p : A3 → ℝ := WithLp.ofLp z.1
    let q : A3 → ℝ := WithLp.ofLp (-(z.1 + z.2))
    let r : A3 → ℝ := WithLp.ofLp z.2
    let U := h3SchwartzTriadPolarization v
    thirdFullSchwartzComplexSixthPowerFlux244 v z =
      (thirdFullComplexPolarizationDot244 (U p) (U r) * mixedDot r (U q)) *
        (((thirdTriadAxisDot244 q q + 2 * thirdTriadAxisDot244 p q : ℝ) : ℂ) *
          ((thirdTriadAxisDot244 r r : ℂ) ^ 2 +
            (thirdTriadAxisDot244 r r : ℂ) *
              (thirdTriadAxisDot244 p p : ℂ) +
            (thirdTriadAxisDot244 p p : ℂ) ^ 2)) +
      (thirdFullComplexPolarizationDot244 (U p) (U q) * mixedDot q (U r)) *
        ((thirdTriadAxisDot244 q q : ℂ) ^ 3 -
          (thirdTriadAxisDot244 p p : ℂ) ^ 3) -
      (thirdFullComplexPolarizationDot244 (U q) (U r) * mixedDot q (U p)) *
        ((thirdTriadAxisDot244 r r : ℂ) ^ 3 -
          (thirdTriadAxisDot244 q q : ℂ) ^ 3) := by
  let p : A3 → ℝ := WithLp.ofLp z.1
  let q : A3 → ℝ := WithLp.ofLp (-(z.1 + z.2))
  let r : A3 → ℝ := WithLp.ofLp z.2
  let U := h3SchwartzTriadPolarization v
  have hm : ∀ i, p i + q i + r i = 0 := by
    intro i
    change (WithLp.ofLp z.1) i +
      (WithLp.ofLp (-(z.1 + z.2))) i + (WithLp.ofLp z.2) i = 0
    simp only [WithLp.ofLp_neg, WithLp.ofLp_add, Pi.neg_apply, Pi.add_apply]
    abel
  have hA : mixedDot p (U p) = 0 :=
    h3SchwartzTriadPolarization_divergence_zero v hDiv p
  change thirdFullComplexSixthPowerFlux244 p q r (U p) (U q) (U r) = _
  exact thirdFullComplexSixthPowerFlux_middleFrequencyFactorization244
    p q r (U p) (U q) (U r) hm hA

end
end PrimeTensor.FirstMonomialTriad
