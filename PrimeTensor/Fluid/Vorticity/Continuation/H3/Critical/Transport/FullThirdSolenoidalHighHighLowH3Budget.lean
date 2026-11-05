import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalMiddleFrequencyFactor
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadSchwartzMoments
import Mathlib.Tactic

/-!
# High-high-low H³ budget from the genuine solenoidal complex flux

Let p+q+r=0, |q| <= min(|p|,|r|), and let A,B,C be complex Fourier
polarizations. The exact cubic-radius flux and solenoidality imply

  |F₆(p,q,r;A,B,C)| <= 52 |p|³ |r|³ |q| |A| |B| |C|.

No high-frequency cutoff occurs: momentum makes the two outer radii
comparable. Integrating over an arbitrary measurable high-high-low sector
using the existing measure-preserving middle-frequency map yields

  |integral_sector F₆| <= 72 (integral |ξ|⁶ F(ξ)²)
                                (integral |ξ| F(ξ)).

The constant 72 absorbs 52 to use the existing exact L²-L²-L¹ theorem
with F_outer=6 |ξ|³ F(ξ). Unlike a generic unsigned budget, the first
frequency moment sits at the *middle* frequency q. This is a genuine
three-derivative allocation onto each outer Fourier factor; it is not a
sign, coercivity, or endpoint H³ estimate.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev PairV := V3 × V3

noncomputable local instance axisFintypeHighHighLowBudget244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The low middle frequency forces both outer norms to be comparable.
In particular the largest *squared* radius is at most twice the product
of the two outer norms, without division by a possibly zero radius. -/
theorem thirdFull_lowMiddle_maxSquare_le_outerProduct244
    (p q r : A3 → ℝ)
    (hm : ∀ i, p i + q i + r i = 0)
    (hLow : frequencyNorm q ≤ min (frequencyNorm p) (frequencyNorm r)) :
    thirdFullTriadSquareRadiusMax244 p q r ≤
      2 * frequencyNorm p * frequencyNorm r ∧
    (frequencyNorm p + frequencyNorm r) * frequencyNorm r ≤
      3 * frequencyNorm p * frequencyNorm r := by
  let P : EuclideanSpace ℝ A3 := WithLp.toLp 2 p
  let Q : EuclideanSpace ℝ A3 := WithLp.toLp 2 q
  let R : EuclideanSpace ℝ A3 := WithLp.toLp 2 r
  have hmVec : P + Q + R = 0 := by
    ext i
    change p i + q i + r i = 0
    exact hm i
  have hpVec : P = -(Q + R) := by
    calc
      P = P + Q + R - (Q + R) := by abel
      _ = -(Q + R) := by rw [hmVec]; abel
  have hrVec : R = -(P + Q) := by
    calc
      R = P + Q + R - (P + Q) := by abel
      _ = -(P + Q) := by rw [hmVec]; abel
  have hpTriangle : frequencyNorm p ≤ frequencyNorm q + frequencyNorm r := by
    change ‖P‖ ≤ ‖Q‖ + ‖R‖
    rw [hpVec, norm_neg]
    exact norm_add_le Q R
  have hrTriangle : frequencyNorm r ≤ frequencyNorm p + frequencyNorm q := by
    change ‖R‖ ≤ ‖P‖ + ‖Q‖
    rw [hrVec, norm_neg]
    exact norm_add_le P Q
  have hqP : frequencyNorm q ≤ frequencyNorm p := (le_min_iff.mp hLow).1
  have hqR : frequencyNorm q ≤ frequencyNorm r := (le_min_iff.mp hLow).2
  have hpR : frequencyNorm p ≤ 2 * frequencyNorm r := by linarith
  have hrP : frequencyNorm r ≤ 2 * frequencyNorm p := by linarith
  have hp0 : 0 ≤ frequencyNorm p := norm_nonneg _
  have hq0 : 0 ≤ frequencyNorm q := norm_nonneg _
  have hr0 : 0 ≤ frequencyNorm r := norm_nonneg _
  have hpSq : frequencyNorm p ^ 2 ≤
      2 * frequencyNorm p * frequencyNorm r := by
    have h := mul_le_mul_of_nonneg_left hpR hp0
    nlinarith only [h]
  have hrSq : frequencyNorm r ^ 2 ≤
      2 * frequencyNorm p * frequencyNorm r := by
    have h := mul_le_mul_of_nonneg_left hrP hr0
    nlinarith only [h]
  have hqSq : frequencyNorm q ^ 2 ≤
      2 * frequencyNorm p * frequencyNorm r :=
    (pow_le_pow_left₀ hq0 hqP 2).trans hpSq
  have hpp : thirdTriadAxisDot244 p p = frequencyNorm p ^ 2 := by
    simpa only [thirdTriadAxisDot244, dot] using
      (dot_self_eq_frequencyNorm_sq p)
  have hqq : thirdTriadAxisDot244 q q = frequencyNorm q ^ 2 := by
    simpa only [thirdTriadAxisDot244, dot] using
      (dot_self_eq_frequencyNorm_sq q)
  have hrr : thirdTriadAxisDot244 r r = frequencyNorm r ^ 2 := by
    simpa only [thirdTriadAxisDot244, dot] using
      (dot_self_eq_frequencyNorm_sq r)
  constructor
  · unfold thirdFullTriadSquareRadiusMax244
    rw [hpp, hqq, hrr]
    exact max_le hpSq (max_le hqSq hrSq)
  · have h := mul_le_mul_of_nonneg_right hrP hr0
    nlinarith only [h]

/-- The remaining two complex cubic gaps cannot exceed the cube of the
largest squared radius. This is sharper than the elementary 2S³ bound. -/
theorem thirdFullComplexCubeGap_le_maxCube244
    (p q r : A3 → ℝ) :
    ‖((thirdTriadAxisDot244 q q : ℂ) ^ 3 -
      (thirdTriadAxisDot244 p p : ℂ) ^ 3)‖ ≤
        thirdFullTriadSquareRadiusMax244 p q r ^ 3 ∧
    ‖((thirdTriadAxisDot244 r r : ℂ) ^ 3 -
      (thirdTriadAxisDot244 q q : ℂ) ^ 3)‖ ≤
        thirdFullTriadSquareRadiusMax244 p q r ^ 3 := by
  let P : ℝ := thirdTriadAxisDot244 p p
  let Q : ℝ := thirdTriadAxisDot244 q q
  let R : ℝ := thirdTriadAxisDot244 r r
  let S : ℝ := thirdFullTriadSquareRadiusMax244 p q r
  have hp0 : 0 ≤ P := thirdFull_axisSquareRadius_nonneg244 p
  have hq0 : 0 ≤ Q := thirdFull_axisSquareRadius_nonneg244 q
  have hr0 : 0 ≤ R := thirdFull_axisSquareRadius_nonneg244 r
  have hpS : P ≤ S := by
    dsimp only [S, thirdFullTriadSquareRadiusMax244]
    exact le_max_left _ _
  have hqS : Q ≤ S := by
    dsimp only [S, thirdFullTriadSquareRadiusMax244]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hrS : R ≤ S := by
    dsimp only [S, thirdFullTriadSquareRadiusMax244]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hpCube : P ^ 3 ≤ S ^ 3 := pow_le_pow_left₀ hp0 hpS 3
  have hqCube : Q ^ 3 ≤ S ^ 3 := pow_le_pow_left₀ hq0 hqS 3
  have hrCube : R ^ 3 ≤ S ^ 3 := pow_le_pow_left₀ hr0 hrS 3
  constructor
  · rw [thirdFull_complexCubeGap_norm244]
    apply abs_le.mpr
    constructor
    · nlinarith only [hpCube, pow_nonneg hq0 3]
    · nlinarith only [hqCube, pow_nonneg hp0 3]
  · rw [thirdFull_complexCubeGap_norm244]
    apply abs_le.mpr
    constructor
    · nlinarith only [hqCube, pow_nonneg hr0 3]
    · nlinarith only [hrCube, pow_nonneg hq0 3]

/-- The genuine complex sixth-power flux, before taking a Fourier integral,
places one entire Fourier derivative on the middle input q. -/
theorem thirdFullComplexSixthPowerFlux_middleAmplitudeBound244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ)
    (hm : ∀ i, p i + q i + r i = 0)
    (hA : mixedDot p A = 0) :
    ‖thirdFullComplexSixthPowerFlux244 p q r A B C‖ ≤
      (3 * thirdFullTriadSquareRadiusMax244 p q r ^ 2 *
        ((frequencyNorm p + frequencyNorm r) * frequencyNorm r) +
        2 * thirdFullTriadSquareRadiusMax244 p q r ^ 3) *
      frequencyNorm q *
        (h3TriadPolarizationNorm A * h3TriadPolarizationNorm B *
          h3TriadPolarizationNorm C) := by
  let S : ℝ := thirdFullTriadSquareRadiusMax244 p q r
  let a : ℝ := h3TriadPolarizationNorm A
  let b : ℝ := h3TriadPolarizationNorm B
  let c : ℝ := h3TriadPolarizationNorm C
  let X : ℂ := thirdFullComplexPolarizationDot244 A C * mixedDot r B
  let Y : ℂ := thirdFullComplexPolarizationDot244 A B * mixedDot q C
  let Z : ℂ := thirdFullComplexPolarizationDot244 B C * mixedDot q A
  let RP : ℂ := ((thirdTriadAxisDot244 r r : ℂ) ^ 3 -
    (thirdTriadAxisDot244 p p : ℂ) ^ 3)
  let QP : ℂ := ((thirdTriadAxisDot244 q q : ℂ) ^ 3 -
    (thirdTriadAxisDot244 p p : ℂ) ^ 3)
  let RQ : ℂ := ((thirdTriadAxisDot244 r r : ℂ) ^ 3 -
    (thirdTriadAxisDot244 q q : ℂ) ^ 3)
  have hmA := thirdFullComplex_momentum_dot244 p q r A hm
  have hrA : mixedDot r A = -mixedDot q A := by
    calc
      mixedDot r A = (mixedDot p A + mixedDot q A + mixedDot r A) -
          mixedDot p A - mixedDot q A := by ring
      _ = -mixedDot q A := by rw [hmA, hA]; ring
  have hFlux : thirdFullComplexSixthPowerFlux244 p q r A B C =
      X * RP + Y * QP - Z * RQ := by
    unfold thirdFullComplexSixthPowerFlux244
    rw [hrA]
    dsimp only [X, Y, Z, RP, QP, RQ]
    ring
  have hAC : ‖thirdFullComplexPolarizationDot244 A C‖ ≤ a * c := by
    simpa only [thirdFullComplexPolarizationDot244, amplitudeDot,
      a, c, h3TriadPolarizationNorm] using
      h3Triad_amplitudeDot_norm_le A C
  have hAB : ‖thirdFullComplexPolarizationDot244 A B‖ ≤ a * b := by
    simpa only [thirdFullComplexPolarizationDot244, amplitudeDot,
      a, b, h3TriadPolarizationNorm] using
      h3Triad_amplitudeDot_norm_le A B
  have hBC : ‖thirdFullComplexPolarizationDot244 B C‖ ≤ b * c := by
    simpa only [thirdFullComplexPolarizationDot244, amplitudeDot,
      b, c, h3TriadPolarizationNorm] using
      h3Triad_amplitudeDot_norm_le B C
  have hrB : ‖mixedDot r B‖ ≤ frequencyNorm r * b := by
    simpa only [b, h3TriadPolarizationNorm, polarizationNorm] using
      (mixedDot_norm_le_euclidean r B)
  have hqC : ‖mixedDot q C‖ ≤ frequencyNorm q * c := by
    simpa only [c, h3TriadPolarizationNorm, polarizationNorm] using
      (mixedDot_norm_le_euclidean q C)
  have hqA : ‖mixedDot q A‖ ≤ frequencyNorm q * a := by
    simpa only [a, h3TriadPolarizationNorm, polarizationNorm] using
      (mixedDot_norm_le_euclidean q A)
  have hX : ‖X‖ ≤ (a * c) * (frequencyNorm r * b) := by
    rw [show ‖X‖ = ‖thirdFullComplexPolarizationDot244 A C‖ *
        ‖mixedDot r B‖ from norm_mul _ _]
    exact mul_le_mul hAC hrB (norm_nonneg _)
      (mul_nonneg (h3TriadPolarizationNorm_nonneg A)
        (h3TriadPolarizationNorm_nonneg C))
  have hY : ‖Y‖ ≤ (a * b) * (frequencyNorm q * c) := by
    rw [show ‖Y‖ = ‖thirdFullComplexPolarizationDot244 A B‖ *
        ‖mixedDot q C‖ from norm_mul _ _]
    exact mul_le_mul hAB hqC (norm_nonneg _)
      (mul_nonneg (h3TriadPolarizationNorm_nonneg A)
        (h3TriadPolarizationNorm_nonneg B))
  have hZ : ‖Z‖ ≤ (b * c) * (frequencyNorm q * a) := by
    rw [show ‖Z‖ = ‖thirdFullComplexPolarizationDot244 B C‖ *
        ‖mixedDot q A‖ from norm_mul _ _]
    exact mul_le_mul hBC hqA (norm_nonneg _)
      (mul_nonneg (h3TriadPolarizationNorm_nonneg B)
        (h3TriadPolarizationNorm_nonneg C))
  have hRP : ‖RP‖ ≤ (3 * S ^ 2) *
      ((frequencyNorm p + frequencyNorm r) * frequencyNorm q) :=
    thirdFullComplexCubeGap_middleFrequencyBound244 p q r hm
  obtain ⟨hQP, hRQ⟩ := thirdFullComplexCubeGap_le_maxCube244 p q r
  have ha0 : 0 ≤ a := h3TriadPolarizationNorm_nonneg A
  have hb0 : 0 ≤ b := h3TriadPolarizationNorm_nonneg B
  have hc0 : 0 ≤ c := h3TriadPolarizationNorm_nonneg C
  have hr0 : 0 ≤ frequencyNorm r := norm_nonneg _
  have hXUpper0 : 0 ≤ (a * c) * (frequencyNorm r * b) :=
    mul_nonneg (mul_nonneg ha0 hc0) (mul_nonneg hr0 hb0)
  have hYUpper0 : 0 ≤ (a * b) * (frequencyNorm q * c) :=
    mul_nonneg (mul_nonneg ha0 hb0)
      (mul_nonneg (norm_nonneg _) hc0)
  have hZUpper0 : 0 ≤ (b * c) * (frequencyNorm q * a) :=
    mul_nonneg (mul_nonneg hb0 hc0)
      (mul_nonneg (norm_nonneg _) ha0)
  have hXRP : ‖X * RP‖ ≤
      ((a * c) * (frequencyNorm r * b)) *
        ((3 * S ^ 2) * ((frequencyNorm p + frequencyNorm r) * frequencyNorm q)) := by
    rw [norm_mul]
    exact mul_le_mul hX hRP (norm_nonneg _) hXUpper0
  have hYQP : ‖Y * QP‖ ≤ ((a * b) * (frequencyNorm q * c)) * S ^ 3 := by
    rw [norm_mul]
    exact mul_le_mul hY hQP (norm_nonneg _) hYUpper0
  have hZRQ : ‖Z * RQ‖ ≤ ((b * c) * (frequencyNorm q * a)) * S ^ 3 := by
    rw [norm_mul]
    exact mul_le_mul hZ hRQ (norm_nonneg _) hZUpper0
  rw [hFlux]
  calc
    ‖X * RP + Y * QP - Z * RQ‖ ≤
      ‖X * RP‖ + ‖Y * QP‖ + ‖Z * RQ‖ := by
        have h1 := norm_add_le (X * RP) (Y * QP)
        have h2 := norm_sub_le (X * RP + Y * QP) (Z * RQ)
        linarith only [h1, h2]
    _ ≤ ((a * c) * (frequencyNorm r * b)) *
          ((3 * S ^ 2) * ((frequencyNorm p + frequencyNorm r) * frequencyNorm q)) +
        ((a * b) * (frequencyNorm q * c)) * S ^ 3 +
        ((b * c) * (frequencyNorm q * a)) * S ^ 3 := by
          exact add_le_add (add_le_add hXRP hYQP) hZRQ
    _ = (3 * S ^ 2 * ((frequencyNorm p + frequencyNorm r) * frequencyNorm r) +
          2 * S ^ 3) * frequencyNorm q * (a * b * c) := by ring

/-- High-high-low gain with no cutoff: all six outer derivatives are paid
by |p|³ and |r|³, while one frequency power remains on |q|. -/
theorem thirdFullComplexSixthPowerFlux_lowMiddleH3Bound244
    (p q r : A3 → ℝ) (A B C : A3 → ℂ)
    (hm : ∀ i, p i + q i + r i = 0)
    (hA : mixedDot p A = 0)
    (hLow : frequencyNorm q ≤ min (frequencyNorm p) (frequencyNorm r)) :
    ‖thirdFullComplexSixthPowerFlux244 p q r A B C‖ ≤
      52 * (frequencyNorm p ^ 3 * h3TriadPolarizationNorm A) *
        (frequencyNorm r ^ 3 * h3TriadPolarizationNorm C) *
        (frequencyNorm q * h3TriadPolarizationNorm B) := by
  let S : ℝ := thirdFullTriadSquareRadiusMax244 p q r
  let P : ℝ := frequencyNorm p
  let Q : ℝ := frequencyNorm q
  let R : ℝ := frequencyNorm r
  let a : ℝ := h3TriadPolarizationNorm A
  let b : ℝ := h3TriadPolarizationNorm B
  let c : ℝ := h3TriadPolarizationNorm C
  obtain ⟨hS, hOuter⟩ :=
    thirdFull_lowMiddle_maxSquare_le_outerProduct244 p q r hm hLow
  have hS0 : 0 ≤ S := by
    dsimp only [S, thirdFullTriadSquareRadiusMax244]
    exact (thirdFull_axisSquareRadius_nonneg244 p).trans (le_max_left _ _)
  have hp0 : 0 ≤ P := norm_nonneg _
  have hr0 : 0 ≤ R := norm_nonneg _
  have hSsq : S ^ 2 ≤ (2 * P * R) ^ 2 :=
    pow_le_pow_left₀ hS0 hS 2
  have hScube : S ^ 3 ≤ (2 * P * R) ^ 3 :=
    pow_le_pow_left₀ hS0 hS 3
  have hOut0 : 0 ≤ (P + R) * R :=
    mul_nonneg (add_nonneg hp0 hr0) hr0
  have hFirst :
      S ^ 2 * ((P + R) * R) ≤ (2 * P * R) ^ 2 * (3 * P * R) :=
    mul_le_mul hSsq hOuter hOut0 (sq_nonneg _)
  have hCoeff :
      3 * S ^ 2 * ((P + R) * R) + 2 * S ^ 3 ≤
        52 * P ^ 3 * R ^ 3 := by
    calc
      _ ≤ 3 * ((2 * P * R) ^ 2 * (3 * P * R)) +
          2 * (2 * P * R) ^ 3 := by
            nlinarith only [hFirst, hScube]
      _ = _ := by ring
  have hAmp : 0 ≤ Q * (a * b * c) := by
    dsimp only [Q, a, b, c, h3TriadPolarizationNorm, frequencyNorm]
    positivity
  calc
    ‖thirdFullComplexSixthPowerFlux244 p q r A B C‖ ≤
        (3 * S ^ 2 * ((P + R) * R) + 2 * S ^ 3) *
          Q * (a * b * c) :=
            thirdFullComplexSixthPowerFlux_middleAmplitudeBound244 p q r A B C hm hA
    _ ≤ (52 * P ^ 3 * R ^ 3) * Q * (a * b * c) := by
      calc
        _ = (3 * S ^ 2 * ((P + R) * R) + 2 * S ^ 3) *
            (Q * (a * b * c)) := by ring
        _ ≤ (52 * P ^ 3 * R ^ 3) * (Q * (a * b * c)) :=
          mul_le_mul_of_nonneg_right hCoeff hAmp
        _ = _ := by ring
    _ = 52 * (P ^ 3 * a) * (R ^ 3 * c) * (Q * b) := by ring

/-- Any measurable high-high-low Fourier sector obeys a genuine global
L²-L²-L¹ estimate. All integral norms are finite for Schwartz data,
without a fixed upper frequency radius or an assumed L∞ Fourier bound. -/
theorem thirdFullSchwartzSixthPowerFlux_lowMiddleIntegral_le_H3Moments244
    (v : A3 → SchwartzMap V3 ℂ)
    (hDiv : ∀ x : V3,
      ∑ j : A3, fderiv ℝ (v j) x (h3FourierAxisDirection j) = 0)
    (s : Set PairV) (hs : MeasurableSet s)
    (hLow : ∀ z ∈ s,
      ‖-(z.1 + z.2)‖ ≤ min ‖z.1‖ ‖z.2‖) :
    ‖∫ z in s, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume‖ ≤
      72 * (∫ ξ : V3, ‖ξ‖ ^ 6 * (h3TriadSpectralAmplitude v ξ) ^ 2
        ∂volume) *
      (∫ ξ : V3, ‖ξ‖ * h3TriadSpectralAmplitude v ξ ∂volume) := by
  let F : V3 → ℝ := fun ξ => 6 * (‖ξ‖ ^ 3 * h3TriadSpectralAmplitude v ξ)
  let H : V3 → ℝ := fun ξ => ‖ξ‖ * h3TriadSpectralAmplitude v ξ
  let K : PairV → ℂ := (s.indicator (thirdFullSchwartzComplexSixthPowerFlux244 v))
  have hFlux : Integrable (thirdFullSchwartzComplexSixthPowerFlux244 v)
      (volume.prod volume) :=
    thirdFullSchwartzSixthPowerFlux_integrable_of_complexDivergence244 v hDiv
  have hK : Integrable K (volume.prod volume) := hFlux.indicator hs
  have hF : Integrable (fun ξ : V3 => F ξ ^ 2) volume := by
    have h := (h3TriadSpectralAmplitude_integrable_pow_mul_sq v 6).const_mul 36
    apply h.congr
    filter_upwards with ξ
    dsimp only [F]
    ring
  have hH : Integrable H volume := by
    simpa only [H, pow_one] using
      (h3TriadSpectralAmplitude_integrable_pow_mul v 1)
  have hH0 : ∀ ξ, 0 ≤ H ξ := by
    intro ξ
    exact mul_nonneg (norm_nonneg ξ) (h3TriadSpectralAmplitude_nonneg v ξ)
  have hBound : ∀ z : PairV,
      ‖K z‖ ≤ 2 * F z.1 * F z.2 * H (-(z.1 + z.2)) := by
    intro z
    have hRHS : 0 ≤ 2 * F z.1 * F z.2 * H (-(z.1 + z.2)) := by
      dsimp only [F]
      have hp : 0 ≤ h3TriadSpectralAmplitude v z.1 :=
        h3TriadSpectralAmplitude_nonneg v z.1
      have hr : 0 ≤ h3TriadSpectralAmplitude v z.2 :=
        h3TriadSpectralAmplitude_nonneg v z.2
      have hq := hH0 (-(z.1 + z.2))
      positivity
    by_cases hz : z ∈ s
    · rw [show K z = thirdFullSchwartzComplexSixthPowerFlux244 v z by
        simp only [K, Set.indicator_of_mem hz]]
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
      have hLowP : frequencyNorm q ≤ min (frequencyNorm p) (frequencyNorm r) := by
        simpa only [frequencyNorm, p, q, r, WithLp.toLp_ofLp]
          using (hLow z hz)
      have hPoint := thirdFullComplexSixthPowerFlux_lowMiddleH3Bound244
        p q r (U p) (U q) (U r) hm hA hLowP
      have hPoint' :
          ‖thirdFullSchwartzComplexSixthPowerFlux244 v z‖ ≤
            52 * (‖z.1‖ ^ 3 * h3TriadSpectralAmplitude v z.1) *
              (‖z.2‖ ^ 3 * h3TriadSpectralAmplitude v z.2) *
              (‖-(z.1 + z.2)‖ *
                h3TriadSpectralAmplitude v (-(z.1 + z.2))) := by
        simpa only [thirdFullSchwartzComplexSixthPowerFlux244,
          h3TriadSpectralAmplitude, h3TriadPolarizationNorm,
          frequencyNorm, WithLp.toLp_ofLp, p, q, r, U] using hPoint
      calc
        _ ≤ 52 * (‖z.1‖ ^ 3 * h3TriadSpectralAmplitude v z.1) *
          (‖z.2‖ ^ 3 * h3TriadSpectralAmplitude v z.2) *
          (‖-(z.1 + z.2)‖ *
            h3TriadSpectralAmplitude v (-(z.1 + z.2))) := hPoint'
        _ ≤ 2 * F z.1 * F z.2 * H (-(z.1 + z.2)) := by
          have hp : 0 ≤ ‖z.1‖ ^ 3 * h3TriadSpectralAmplitude v z.1 :=
            mul_nonneg (pow_nonneg (norm_nonneg _) _)
              (h3TriadSpectralAmplitude_nonneg v z.1)
          have hr : 0 ≤ ‖z.2‖ ^ 3 * h3TriadSpectralAmplitude v z.2 :=
            mul_nonneg (pow_nonneg (norm_nonneg _) _)
              (h3TriadSpectralAmplitude_nonneg v z.2)
          have hq : 0 ≤ H (-(z.1 + z.2)) := hH0 _
          dsimp only [F, H]
          nlinarith only [mul_nonneg hp (mul_nonneg hr hq)]
    · rw [show K z = (0 : ℂ) by
        simp only [K, Set.indicator_of_notMem hz]]
      simp only [norm_zero]
      exact hRHS
  have hEstimate := h3Triad_integral_norm_le_L2_L1
    K F H hK hF hH hH0 hBound
  have hFIntegral : (∫ ξ : V3, F ξ ^ 2 ∂volume) =
      36 * (∫ ξ : V3, ‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2 ∂volume) := by
    have hEq : (fun ξ : V3 => F ξ ^ 2) =
        (fun ξ : V3 => 36 * (‖ξ‖ ^ 6 * h3TriadSpectralAmplitude v ξ ^ 2)) := by
      funext ξ
      dsimp only [F]
      ring
    rw [hEq, integral_const_mul]
  have hHIntegral : (∫ ξ : V3, H ξ ∂volume) =
      ∫ ξ : V3, ‖ξ‖ * h3TriadSpectralAmplitude v ξ ∂volume := rfl
  have hKIntegral : (∫ z : PairV, K z ∂volume.prod volume) =
      ∫ z in s, thirdFullSchwartzComplexSixthPowerFlux244 v z
        ∂volume.prod volume := by
    exact integral_indicator hs
  rw [← hKIntegral]
  calc
    ‖∫ z : PairV, K z ∂volume.prod volume‖ ≤
        2 * (∫ ξ : V3, F ξ ^ 2 ∂volume) *
          (∫ ξ : V3, H ξ ∂volume) := hEstimate
    _ = _ := by rw [hFIntegral, hHIntegral]; ring

end
end PrimeTensor.FirstMonomialTriad
