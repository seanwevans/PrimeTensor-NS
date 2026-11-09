import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxIndexRateBernsteinGate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxRadialTenthPowerEscape
import Mathlib.Tactic

/-!
# Signed sixth flux: collapse the exact kinetic index rate to one Fourier ball

The previous index-k gate retained the sum of all kinetic-band PDE rates.
The present argument compares each constituent natural-radius Fourier ball
with the *single* outer ball at k+1. The exact source ceiling is monotone in
natural radius at nonnegative kinetic energy, even though no monotonicity of
the full nonlinear Fourier source is postulated. The accepted cubic finite-
band Bernstein bound then dominates every low-band rate by one explicit
radius-k factor. Summing this majorant produces a scalar single-radius
upper bound on the entire index-rate payment.

The Fourier-ball volume remains explicit. No unproved polynomial bound on
product-measure volume, no regularity of the full H3 trace, and no decay of
the rate-weighted dissipation are assumed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

-- Match the canonical three-axis Lebesgue product measure used by the
-- imported physical kinetic/source ceilings; do not infer a new measure.
noncomputable local instance axisFintypeOneRadiusSource244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceOneRadiusSource244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The actual physical Fourier-gradient ball volume is monotone along
natural radii. Its finite measure is the established Leray-ball result. -/
theorem thirdFullKinetic_signedLowMax_fourierBallVolume_mono244
    (j k : ℕ) (hjk : j ≤ k) :
    (volume : Measure H3FourierPoint3).real
        (h3TerminalRadialFrequencyBelow ((j : ℝ) + 1)) ≤
      (volume : Measure H3FourierPoint3).real
        (h3TerminalRadialFrequencyBelow ((k : ℝ) + 1)) := by
  have hRadius : (j : ℝ) + 1 ≤ (k : ℝ) + 1 := by
    have hCast : (j : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hjk
    linarith only [hCast]
  have hSub :
      h3TerminalRadialFrequencyBelow ((j : ℝ) + 1) ⊆
        h3TerminalRadialFrequencyBelow ((k : ℝ) + 1) := by
    intro ξ hξ
    change h3FourierGradientMagnitude ξ < (j : ℝ) + 1 at hξ
    change h3FourierGradientMagnitude ξ < (k : ℝ) + 1
    exact lt_of_lt_of_le hξ hRadius
  have hFinite := h3Critical_lowRadial_fourierBall_finiteVolume ((k : ℝ) + 1)
  rw [Measure.real_def, Measure.real_def]
  exact ENNReal.toReal_mono hFinite.ne (measure_mono hSub)

/-- The exact low-radial physical projected-source ceiling is monotone in
natural cutoff at any nonnegative earlier kinetic anchor. Both its Laplacian
and its Leray Fourier-ball contributions are compared explicitly. -/
theorem thirdFullKinetic_signedLowMax_kineticSourceCeiling_mono244
    (j k : ℕ) (E0 : ℝ) (hE : 0 ≤ E0) (hjk : j ≤ k) :
    thirdFullPhysicalKineticLowBandSourceCeiling244 ((j : ℝ) + 1) E0 ≤
      thirdFullPhysicalKineticLowBandSourceCeiling244 ((k : ℝ) + 1) E0 := by
  let r : ℝ := (j : ℝ) + 1
  let s : ℝ := (k : ℝ) + 1
  let Vj : ℝ := (volume : Measure H3FourierPoint3).real
    (h3TerminalRadialFrequencyBelow r)
  let Vk : ℝ := (volume : Measure H3FourierPoint3).real
    (h3TerminalRadialFrequencyBelow s)
  have hRadius : r ≤ s := by
    dsimp only [r, s]
    have hCast : (j : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hjk
    linarith only [hCast]
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hVolume : Vj ≤ Vk := by
    simpa only [Vj, Vk, r, s] using
      (thirdFullKinetic_signedLowMax_fourierBallVolume_mono244 j k hjk)
  have hVk : 0 ≤ Vk := measureReal_nonneg
  have hRadiusSq : r ^ 2 ≤ s ^ 2 :=
    pow_le_pow_left₀ hr hRadius 2
  have hSourceCoeff : 18 * (r * E0) ≤ 18 * (s * E0) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hRadius hE) (by norm_num)
  have hSourceCoeffNonneg : 0 ≤ 18 * (r * E0) := by positivity
  have hSourceSq : (18 * (r * E0)) ^ 2 ≤ (18 * (s * E0)) ^ 2 :=
    pow_le_pow_left₀ hSourceCoeffNonneg hSourceCoeff 2
  have hInside : Vj * (18 * (r * E0)) ^ 2 ≤
      Vk * (18 * (s * E0)) ^ 2 := by
    calc
      Vj * (18 * (r * E0)) ^ 2 ≤
          Vk * (18 * (r * E0)) ^ 2 :=
        mul_le_mul_of_nonneg_right hVolume (sq_nonneg _)
      _ ≤ Vk * (18 * (s * E0)) ^ 2 :=
        mul_le_mul_of_nonneg_left hSourceSq hVk
  change r ^ 2 * Real.sqrt E0 +
      Real.sqrt (Vj * (18 * (r * E0)) ^ 2) ≤
    s ^ 2 * Real.sqrt E0 +
      Real.sqrt (Vk * (18 * (s * E0)) ^ 2)
  exact add_le_add
    (mul_le_mul_of_nonneg_right hRadiusSq (Real.sqrt_nonneg E0))
    (Real.sqrt_le_sqrt hInside)

/-- Single-radius Bernstein/source envelope for all j ≤ k. Its polynomial
prefactor is explicit; the genuine Fourier-ball volume remains in S(k+1,E). -/
noncomputable def thirdFullKineticSignedLowMaxOneRadiusBandRate244
    (k : ℕ) (E0 : ℝ) : ℝ :=
  24 * ((k : ℝ) + 2) ^ 2 * ((k : ℝ) + 1) ^ 6 *
    Real.sqrt E0 *
    thirdFullPhysicalKineticLowBandSourceCeiling244 ((k : ℝ) + 1) E0

/-- Every physical low-band kinetic dissipation rate up to k is bounded
by one polynomial Bernstein factor at k and the actual source ball at k+1. -/
theorem thirdFullKinetic_signedLowMax_bandRate_le_oneRadius244
    (j k : ℕ) (E0 : ℝ) (hE : 0 ≤ E0) (hjk : j ≤ k) :
    thirdFullPhysicalKineticLowBandDissipationRate244 j E0 ≤
      thirdFullKineticSignedLowMaxOneRadiusBandRate244 k E0 := by
  let Wj : ℝ := thirdFullFiniteBandH3WeightCeiling244 j
  let B : ℝ := 2 * ((k : ℝ) + 1) ^ 3
  let Sj : ℝ := thirdFullPhysicalKineticLowBandSourceCeiling244
    ((j : ℝ) + 1) E0
  let Sk : ℝ := thirdFullPhysicalKineticLowBandSourceCeiling244
    ((k : ℝ) + 1) E0
  have hRadius : (j : ℝ) + 1 ≤ (k : ℝ) + 1 := by
    have hCast : (j : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hjk
    linarith only [hCast]
  have hRadiusTwo : (j : ℝ) + 2 ≤ (k : ℝ) + 2 := by
    linarith only [hRadius]
  have hA : ((j : ℝ) + 2) ^ 2 ≤ ((k : ℝ) + 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hRadiusTwo 2
  have hWcap : Wj ≤ B := by
    calc
      Wj ≤ 2 * ((j : ℝ) + 1) ^ 3 :=
        thirdFullFiniteBandH3WeightCeiling_le_radialCubic244 j
      _ ≤ B := by
        dsimp only [B]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hRadius 3) (by norm_num)
  have hWSq : Wj ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (thirdFullFiniteBandH3WeightCeiling_nonneg244 j) hWcap 2
  have hS : Sj ≤ Sk :=
    thirdFullKinetic_signedLowMax_kineticSourceCeiling_mono244 j k E0 hE hjk
  have hSj0 : 0 ≤ Sj := thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244 _ _
  have hLeftFactor : 0 ≤ Real.sqrt E0 * Sj :=
    mul_nonneg (Real.sqrt_nonneg E0) hSj0
  have hRightFactor : 0 ≤ 6 * ((k : ℝ) + 2) ^ 2 * B ^ 2 := by
    positivity
  have hFirst : 6 * ((j : ℝ) + 2) ^ 2 * Wj ^ 2 ≤
      6 * ((k : ℝ) + 2) ^ 2 * B ^ 2 := by
    calc
      6 * ((j : ℝ) + 2) ^ 2 * Wj ^ 2 ≤
          6 * ((k : ℝ) + 2) ^ 2 * Wj ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA (by norm_num)) (sq_nonneg _)
      _ ≤ 6 * ((k : ℝ) + 2) ^ 2 * B ^ 2 :=
        mul_le_mul_of_nonneg_left hWSq (by positivity)
  have hSecond : Real.sqrt E0 * Sj ≤ Real.sqrt E0 * Sk :=
    mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg E0)
  calc
    thirdFullPhysicalKineticLowBandDissipationRate244 j E0 =
        (6 * ((j : ℝ) + 2) ^ 2 * Wj ^ 2) *
          (Real.sqrt E0 * Sj) := by
      rw [thirdFullKinetic_signedLowMax_bandRate_eq_BernsteinSource244]
      ring
    _ ≤ (6 * ((k : ℝ) + 2) ^ 2 * B ^ 2) *
        (Real.sqrt E0 * Sj) :=
      mul_le_mul_of_nonneg_right hFirst hLeftFactor
    _ ≤ (6 * ((k : ℝ) + 2) ^ 2 * B ^ 2) *
        (Real.sqrt E0 * Sk) :=
      mul_le_mul_of_nonneg_left hSecond hRightFactor
    _ = thirdFullKineticSignedLowMaxOneRadiusBandRate244 k E0 := by
      unfold thirdFullKineticSignedLowMaxOneRadiusBandRate244
      dsimp only [B, Sk]
      ring

/-- One explicit natural radius dominates the entire original index-rate
budget. The only remaining nonpolynomial factor is the known finite volume
of the genuine Fourier-gradient ball at k+1. -/
noncomputable def thirdFullKineticSignedLowMaxOneRadiusIndexRate244
    (k : ℕ) (E0 : ℝ) : ℝ :=
  1 + 2 * ((k : ℝ) + 1) *
    thirdFullKineticSignedLowMaxOneRadiusBandRate244 k E0

/-- The exact sum C_k is no larger than the single-radius source envelope. -/
theorem thirdFullKinetic_signedLowMax_indexRate_le_oneRadius244
    (k : ℕ) (E0 : ℝ) (hE : 0 ≤ E0) :
    thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 k E0 ≤
      thirdFullKineticSignedLowMaxOneRadiusIndexRate244 k E0 := by
  let L : ℕ → ℝ := fun j => thirdFullPhysicalKineticLowBandDissipationRate244 j E0
  let B : ℝ := thirdFullKineticSignedLowMaxOneRadiusBandRate244 k E0
  have hSum : (∑ j ∈ Finset.range (k + 1), L j) ≤
      (∑ _j ∈ Finset.range (k + 1), B) := by
    apply Finset.sum_le_sum
    intro j hj
    exact thirdFullKinetic_signedLowMax_bandRate_le_oneRadius244
      j k E0 hE (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hConst : (∑ _j ∈ Finset.range (k + 1), B) =
      ((k : ℝ) + 1) * B := by
    simp [nsmul_eq_mul, Nat.cast_add, mul_comm]
  have hBound : (∑ j ∈ Finset.range (k + 1), L j) ≤
      ((k : ℝ) + 1) * B := by
    calc
      (∑ j ∈ Finset.range (k + 1), L j) ≤
          (∑ _j ∈ Finset.range (k + 1), B) := hSum
      _ = ((k : ℝ) + 1) * B := hConst
  change 2 * (∑ j ∈ Finset.range (k + 1), L j) + 1 ≤
    1 + 2 * ((k : ℝ) + 1) * B
  calc
    2 * (∑ j ∈ Finset.range (k + 1), L j) + 1 ≤
        2 * (((k : ℝ) + 1) * B) + 1 := by
      have hTwice : 2 * (∑ j ∈ Finset.range (k + 1), L j) ≤
          2 * (((k : ℝ) + 1) * B) :=
        mul_le_mul_of_nonneg_left hBound (by norm_num : (0 : ℝ) ≤ 2)
      linarith only [hTwice]
    _ = 1 + 2 * ((k : ℝ) + 1) * B := by ring

/-- The single-radius index-rate coefficient is strictly positive even at
zero kinetic energy. -/
theorem thirdFullKinetic_signedLowMax_oneRadiusIndexRate_pos244
    (k : ℕ) (E0 : ℝ) (hE : 0 ≤ E0) :
    0 < thirdFullKineticSignedLowMaxOneRadiusIndexRate244 k E0 := by
  have hSource := thirdFullPhysicalKineticLowBandSourceCeiling_nonneg244
    ((k : ℝ) + 1) E0
  have hBand : 0 ≤ thirdFullKineticSignedLowMaxOneRadiusBandRate244 k E0 := by
    unfold thirdFullKineticSignedLowMaxOneRadiusBandRate244
    positivity
  unfold thirdFullKineticSignedLowMaxOneRadiusIndexRate244
  have hk : 0 ≤ (k : ℝ) + 1 := by positivity
  have hProduct : 0 ≤ 2 * ((k : ℝ) + 1) *
      thirdFullKineticSignedLowMaxOneRadiusBandRate244 k E0 := by
    positivity
  linarith only [hProduct]

/-- A paid exact physical index-rate budget yields a genuine lower bound
on original gap dissipation with one cutoff, not a sum over all lower bands. -/
theorem thirdFullKinetic_signedLowMax_oneRadius_inverseGapCharge244
    (k : ℕ) (E0 h D : ℝ) (hE : 0 ≤ E0) (hh : 0 < h)
    (hRate : h ^ 2 ≤
      32 * thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 k E0 * D)
    (hD : 0 ≤ D) :
    h ^ 2 / (32 * thirdFullKineticSignedLowMaxOneRadiusIndexRate244 k E0) ≤ D := by
  have hC := thirdFullKinetic_signedLowMax_indexRate_le_oneRadius244 k E0 hE
  have hW : 0 < thirdFullKineticSignedLowMaxOneRadiusIndexRate244 k E0 :=
    thirdFullKinetic_signedLowMax_oneRadiusIndexRate_pos244 k E0 hE
  have hScaled : h ^ 2 ≤
      32 * thirdFullKineticSignedLowMaxOneRadiusIndexRate244 k E0 * D := by
    calc
      h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244 k E0 * D := hRate
      _ ≤ 32 * thirdFullKineticSignedLowMaxOneRadiusIndexRate244 k E0 * D := by
        have hMul := mul_le_mul_of_nonneg_right hC hD
        nlinarith only [hMul]
  have hDen : 0 < 32 * thirdFullKineticSignedLowMaxOneRadiusIndexRate244 k E0 :=
    mul_pos (by norm_num) hW
  apply (div_le_iff₀ hDen).mpr
  calc
    h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxOneRadiusIndexRate244 k E0 * D := hScaled
    _ = D * (32 * thirdFullKineticSignedLowMaxOneRadiusIndexRate244 k E0) := by ring

/-- The original cofinal signed-sixth-flux index gate, now with every
finite-band kinetic PDE rate on 0..k dominated by the SAME outer Fourier ball
at k+1. The explicit polynomial Bernstein factor is kept together with the
real physical source volume; neither the earlier tenth-power residual nor
the positive-density branch is discarded. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_tenthResidual_oneRadiusGate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (tau : ℕ → ℝ) (N : ℕ → ℕ)
    (delta : ℕ → ℝ) (v : ℕ → ℕ)
    (hLimit : Tendsto (fun k => tau (v k)) atTop (𝓝 T))
    (hSeparated : ∀ k l : ℕ, k < l →
      tau (v k) + delta (v k) < tau (v l))
    (hWindows : ∀ k : ℕ,
      tau (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (tau (v k)) (v k) (N (v k))
        (M (v k)) (delta (v k)))
    (eta : ℝ) (hEta : 0 < eta)
    (J : ℕ) (E epsilon : ℝ) (hE : 0 ≤ E) (hEpsilon : 0 < epsilon) :
    let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
    let D : ℕ → ℝ := fun k =>
      ∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
        velocityH3DissipationAt u r ∂volume
    let G : ℕ → ℕ := thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244
      (velocityH3Energy0At u b) h D
    Tendsto G atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        ∀ (R : ℕ) (t : ℝ),
          t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
          eta < -velocityH3TransportDerivative3At u t →
          ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
            hH3 R J E eta epsilon
              (tau (v k) + delta (v k)) (tau (v (k + 1))) t →
          ((tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤
              16 * D k) ∨
          (h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxOneRadiusIndexRate244
              k (velocityH3Energy0At u b) * D k) ∨
          (∃ Q : ℕ, R ≤ Q ∧ k < Q)) := by
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let D : ℕ → ℝ := fun k =>
    ∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
      velocityH3DissipationAt u r ∂volume
  let G : ℕ → ℕ := thirdFullKineticSignedLowMaxPhysicalAdaptiveGauge244
    (velocityH3Energy0At u b) h D
  change Tendsto G atTop atTop ∧
    (∀ᶠ k : ℕ in atTop, ∀ (R : ℕ) (t : ℝ),
      t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
      eta < -velocityH3TransportDerivative3At u t →
      ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
        hH3 R J E eta epsilon
          (tau (v k) + delta (v k)) (tau (v (k + 1))) t →
      ((tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤ 16 * D k) ∨
      (h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxOneRadiusIndexRate244
        k (velocityH3Energy0At u b) * D k) ∨
      (∃ Q : ℕ, R ≤ Q ∧ k < Q))
  have hOld :=
    thirdFullPhysical_kineticGaps_signedLowMax_tenthResidual_indexRateGate244
      hH3 hClass hDInt b hb M tau N delta v
      hLimit hSeparated hWindows eta hEta J E epsilon hE hEpsilon
  change Tendsto G atTop atTop ∧
    (∀ᶠ k : ℕ in atTop, ∀ (R : ℕ) (t : ℝ),
      t ∈ Set.Icc (tau (v k) + delta (v k)) (tau (v (k + 1))) →
      eta < -velocityH3TransportDerivative3At u t →
      ¬ ThirdFullKineticSignedLowMaxTenthPowerResidual244
        hH3 R J E eta epsilon
          (tau (v k) + delta (v k)) (tau (v (k + 1))) t →
      ((tau (v (k + 1)) - (tau (v k) + delta (v k))) * h ≤ 16 * D k) ∨
      (h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
        k (velocityH3Energy0At u b) * D k) ∨
      (∃ Q : ℕ, R ≤ Q ∧ k < Q)) at hOld
  refine ⟨hOld.1, ?_⟩
  filter_upwards [hOld.2] with k hk
  intro R t ht hAdverse hNoResidual
  rcases hk R t ht hAdverse hNoResidual with hClock | hRest
  · exact Or.inl hClock
  rcases hRest with hRate | hOuter
  · right; left
    have hCap :
        thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
            k (velocityH3Energy0At u b) ≤
          thirdFullKineticSignedLowMaxOneRadiusIndexRate244
            k (velocityH3Energy0At u b) :=
      thirdFullKinetic_signedLowMax_indexRate_le_oneRadius244
        k (velocityH3Energy0At u b) (velocityH3Energy0At_nonneg u b)
    have hxy : tau (v k) + delta (v k) < tau (v (k + 1)) :=
      hSeparated k (k + 1) (Nat.lt_succ_self k)
    have hD : 0 ≤ D k := by
      change 0 ≤ ∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
        velocityH3DissipationAt u r ∂volume
      exact intervalIntegral.integral_nonneg hxy.le
        (fun r _hr => velocityH3DissipationAt_nonneg u r)
    have hBound := mul_le_mul_of_nonneg_right hCap hD
    calc
      h ^ 2 ≤ 32 * thirdFullKineticSignedLowMaxFiniteGaugeRateCeiling244
          k (velocityH3Energy0At u b) * D k := hRate
      _ ≤ 32 * thirdFullKineticSignedLowMaxOneRadiusIndexRate244
          k (velocityH3Energy0At u b) * D k := by
        nlinarith only [hBound]
  · exact Or.inr (Or.inr hOuter)

end
end PrimeTensor.FirstMonomialTriad
