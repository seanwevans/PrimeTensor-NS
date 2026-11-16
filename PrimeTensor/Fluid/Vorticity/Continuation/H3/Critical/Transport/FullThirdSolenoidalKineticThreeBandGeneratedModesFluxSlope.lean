import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandViscousFirstVariation
import Mathlib.Tactic

/-!
# Immediate mode creation and signed three-band flux slopes

The existing six-mode solenoidal Leray example is not an invariant six-mode
truncation of the actual unforced Navier--Stokes equation. The full ordered
quadratic convolution creates the frequency pairs b-a, a+c and b+c at time
zero. We compute the solenoidal source amplitudes and their squared norms.

The accompanying exact Gaussian-rational audit independently differentiates
both complete cutoff flux sums, INCLUDING the initially empty generated modes.
Its evaluated first derivatives for common scale k and amplitude A are:

  lower cutoff 3k/2: -46/5*k^2*A^4 - 32*nu*k^3*A^3
  upper cutoff 3k:    36/5*k^2*A^4 - 64*nu*k^3*A^3

The Lean lemmas below prove the new-mode source geometry and the exact scalar
implications of these independently audited coefficients. They do NOT claim
to derive a Fourier PDE solution or an unproved time-uniform flux inequality.
All ordinary additive Fourier arithmetic lives in the established real bridge;
the intrinsic nonempty prime-multiset structure is untouched.
-/

namespace PrimeTensor.FirstMonomialTriad

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private abbrev BandV244 := PrimeTensor.Tensor.Vector ℝ PrimeTensor.Depth.three

/-- Negative of a Fourier wavevector, only in the real bridge. -/
def thirdFullThreeBandWaveNeg244 (v : BandV244) : BandV244 :=
  ⟨fun j => -v.component j⟩

/-- The previously empty frequency b-a, of squared radius two. -/
def thirdFullThreeBandNewDifferenceWave244 : BandV244 :=
  thirdFullThreeBandAdd244 thirdFullThreeBandWaveMid244
    (thirdFullThreeBandWaveNeg244 thirdFullThreeBandWaveLow244)

/-- The previously empty frequency a+c, of squared radius seventeen. -/
def thirdFullThreeBandNewOuterLeftWave244 : BandV244 :=
  thirdFullThreeBandAdd244 thirdFullThreeBandWaveLow244
    thirdFullThreeBandWaveHigh244

/-- The previously empty frequency b+c, of squared radius twenty-nine. -/
def thirdFullThreeBandNewOuterRightWave244 : BandV244 :=
  thirdFullThreeBandAdd244 thirdFullThreeBandWaveMid244
    thirdFullThreeBandWaveHigh244

/-- Imaginary coefficient of the full ordered (-a,b) + (b,-a)
interaction at b-a, before the actual Leray projection. -/
def thirdFullThreeBandNewDifferenceSourceIm244 : BandV244 :=
  ⟨fun j =>
    thirdFullThreeBandDot244 thirdFullThreeBandPolarMid244
      thirdFullThreeBandWaveLow244 *
        (thirdFullThreeBandPolarLow244.component j) -
    thirdFullThreeBandDot244 thirdFullThreeBandPolarLow244
      thirdFullThreeBandWaveMid244 *
        (thirdFullThreeBandPolarMid244.component j)⟩

/-- Real coefficient of the two ordered (a,c),(c,a) interactions. -/
def thirdFullThreeBandNewOuterLeftSource244 : BandV244 :=
  ⟨fun j =>
    thirdFullThreeBandDot244 thirdFullThreeBandPolarLow244
      thirdFullThreeBandWaveHigh244 *
        (thirdFullThreeBandPolarHigh244.component j) +
    thirdFullThreeBandDot244 thirdFullThreeBandPolarHigh244
      thirdFullThreeBandWaveLow244 *
        (thirdFullThreeBandPolarLow244.component j)⟩

/-- Real coefficient of the two ordered (b,c),(c,b) interactions. -/
def thirdFullThreeBandNewOuterRightSource244 : BandV244 :=
  ⟨fun j =>
    thirdFullThreeBandDot244 thirdFullThreeBandPolarMid244
      thirdFullThreeBandWaveHigh244 *
        (thirdFullThreeBandPolarHigh244.component j) +
    thirdFullThreeBandDot244 thirdFullThreeBandPolarHigh244
      thirdFullThreeBandWaveMid244 *
        (thirdFullThreeBandPolarMid244.component j)⟩

/-- Exact Leray-projected imaginary coefficient at b-a. -/
def thirdFullThreeBandNewDifferenceProjectedIm244 : BandV244 :=
  thirdFullThreeBandLeray244 thirdFullThreeBandNewDifferenceWave244
    thirdFullThreeBandNewDifferenceSourceIm244

/-- Exact Leray-projected real coefficient at a+c. -/
def thirdFullThreeBandNewOuterLeftProjected244 : BandV244 :=
  thirdFullThreeBandLeray244 thirdFullThreeBandNewOuterLeftWave244
    thirdFullThreeBandNewOuterLeftSource244

/-- Exact Leray-projected real coefficient at b+c. -/
def thirdFullThreeBandNewOuterRightProjected244 : BandV244 :=
  thirdFullThreeBandLeray244 thirdFullThreeBandNewOuterRightWave244
    thirdFullThreeBandNewOuterRightSource244

/-- Exact new frequency radii: the difference lies below the first
cutoff 3/2, while both sum modes lie above the second cutoff 3. -/
theorem thirdFullThreeBand_newWaveSquares244 :
    thirdFullThreeBandDot244 thirdFullThreeBandNewDifferenceWave244
      thirdFullThreeBandNewDifferenceWave244 = 2 ∧
    thirdFullThreeBandDot244 thirdFullThreeBandNewOuterLeftWave244
      thirdFullThreeBandNewOuterLeftWave244 = 17 ∧
    thirdFullThreeBandDot244 thirdFullThreeBandNewOuterRightWave244
      thirdFullThreeBandNewOuterRightWave244 = 29 := by
  constructor
  · norm_num [thirdFullThreeBandDot244, thirdFullThreeBandNewDifferenceWave244,
      thirdFullThreeBandWaveNeg244, thirdFullThreeBandAdd244,
      thirdFullThreeBandWaveLow244, thirdFullThreeBandWaveMid244,
      PrimeTensor.Bridge.Euclidean.axis_fold_three]
  constructor
  · norm_num [thirdFullThreeBandDot244, thirdFullThreeBandNewOuterLeftWave244,
      thirdFullThreeBandAdd244, thirdFullThreeBandWaveHigh244,
      thirdFullThreeBandWaveLow244, thirdFullThreeBandWaveMid244,
      PrimeTensor.Bridge.Euclidean.axis_fold_three]
  · norm_num [thirdFullThreeBandDot244, thirdFullThreeBandNewOuterRightWave244,
      thirdFullThreeBandAdd244, thirdFullThreeBandWaveHigh244,
      thirdFullThreeBandWaveLow244, thirdFullThreeBandWaveMid244,
      PrimeTensor.Bridge.Euclidean.axis_fold_three]

/-- The actual Leray coefficients have squared amplitudes 8, 1, 1.
No six-mode closure assumption is used to evaluate these interactions. -/
theorem thirdFullThreeBand_newProjectedSquares244 :
    thirdFullThreeBandDot244 thirdFullThreeBandNewDifferenceProjectedIm244
      thirdFullThreeBandNewDifferenceProjectedIm244 = 8 ∧
    thirdFullThreeBandDot244 thirdFullThreeBandNewOuterLeftProjected244
      thirdFullThreeBandNewOuterLeftProjected244 = 1 ∧
    thirdFullThreeBandDot244 thirdFullThreeBandNewOuterRightProjected244
      thirdFullThreeBandNewOuterRightProjected244 = 1 := by
  constructor
  · norm_num [thirdFullThreeBandDot244,
      thirdFullThreeBandNewDifferenceProjectedIm244,
      thirdFullThreeBandNewDifferenceSourceIm244,
      thirdFullThreeBandNewDifferenceWave244, thirdFullThreeBandWaveNeg244,
      thirdFullThreeBandLeray244, thirdFullThreeBandAdd244,
      thirdFullThreeBandWaveLow244, thirdFullThreeBandWaveMid244,
      thirdFullThreeBandPolarLow244, thirdFullThreeBandPolarMid244,
      PrimeTensor.Bridge.Euclidean.axis_fold_three]
  constructor
  · norm_num [thirdFullThreeBandDot244,
      thirdFullThreeBandNewOuterLeftProjected244,
      thirdFullThreeBandNewOuterLeftSource244,
      thirdFullThreeBandNewOuterLeftWave244, thirdFullThreeBandLeray244,
      thirdFullThreeBandAdd244, thirdFullThreeBandWaveHigh244,
      thirdFullThreeBandWaveLow244, thirdFullThreeBandWaveMid244,
      thirdFullThreeBandPolarLow244, thirdFullThreeBandPolarHigh244,
      PrimeTensor.Bridge.Euclidean.axis_fold_three]
  · norm_num [thirdFullThreeBandDot244,
      thirdFullThreeBandNewOuterRightProjected244,
      thirdFullThreeBandNewOuterRightSource244,
      thirdFullThreeBandNewOuterRightWave244, thirdFullThreeBandLeray244,
      thirdFullThreeBandAdd244, thirdFullThreeBandWaveHigh244,
      thirdFullThreeBandWaveLow244, thirdFullThreeBandWaveMid244,
      thirdFullThreeBandPolarMid244, thirdFullThreeBandPolarHigh244,
      PrimeTensor.Bridge.Euclidean.axis_fold_three]

/-- First nonvanishing (quadratic-time) coefficient of the total kinetic
energy in the three newly generated conjugate frequency pairs. -/
def thirdFullThreeBandNewPairLeakCoefficient244 (k A : ℝ) : ℝ :=
  k ^ 2 * A ^ 4 *
    (thirdFullThreeBandDot244 thirdFullThreeBandNewDifferenceProjectedIm244
        thirdFullThreeBandNewDifferenceProjectedIm244 +
     thirdFullThreeBandDot244 thirdFullThreeBandNewOuterLeftProjected244
        thirdFullThreeBandNewOuterLeftProjected244 +
     thirdFullThreeBandDot244 thirdFullThreeBandNewOuterRightProjected244
        thirdFullThreeBandNewOuterRightProjected244)

/-- Quadratic-time coefficient from the TWO new pairs outside radius 3k. -/
def thirdFullThreeBandNewOuterLeakCoefficient244 (k A : ℝ) : ℝ :=
  k ^ 2 * A ^ 4 *
    (thirdFullThreeBandDot244 thirdFullThreeBandNewOuterLeftProjected244
        thirdFullThreeBandNewOuterLeftProjected244 +
     thirdFullThreeBandDot244 thirdFullThreeBandNewOuterRightProjected244
        thirdFullThreeBandNewOuterRightProjected244)

theorem thirdFullThreeBand_newLeakCoefficients244 (k A : ℝ) :
    thirdFullThreeBandNewPairLeakCoefficient244 k A =
        10 * k ^ 2 * A ^ 4 ∧
    thirdFullThreeBandNewOuterLeakCoefficient244 k A =
        2 * k ^ 2 * A ^ 4 := by
  obtain ⟨hD, hL, hR⟩ := thirdFullThreeBand_newProjectedSquares244
  constructor
  · unfold thirdFullThreeBandNewPairLeakCoefficient244
    rw [hD, hL, hR]
    ring
  · unfold thirdFullThreeBandNewOuterLeakCoefficient244
    rw [hL, hR]
    ring

/-- Exact scalar polynomial returned by the independent full ordered
convolution audit for the lower-cutoff initial flux derivative. -/
def thirdFullThreeBandLowerFluxSlope244 (nu k A : ℝ) : ℝ :=
  -(46 / 5) * k ^ 2 * A ^ 4 - 32 * nu * k ^ 3 * A ^ 3

/-- Exact scalar polynomial returned by the independent full ordered
convolution audit for the upper-cutoff initial flux derivative. -/
def thirdFullThreeBandUpperFluxSlope244 (nu k A : ℝ) : ℝ :=
  (36 / 5) * k ^ 2 * A ^ 4 - 64 * nu * k ^ 3 * A ^ 3

/-- The scalar upper-slope coefficient factors into the exact independent
threshold 80/9. The PDE interpretation is audited, not asserted here. -/
theorem thirdFullThreeBand_upperFluxSlope_factor244 (nu k A : ℝ) :
    thirdFullThreeBandUpperFluxSlope244 nu k A =
      (4 / 5) * k ^ 2 * A ^ 3 * (9 * A - 80 * nu * k) := by
  unfold thirdFullThreeBandUpperFluxSlope244
  ring

theorem thirdFullThreeBand_upperFluxSlope_positive_iff244
    (nu k A : ℝ) (hk : 0 < k) (hA : 0 < A) :
    0 < thirdFullThreeBandUpperFluxSlope244 nu k A ↔
      (80 / 9) * nu * k < A := by
  rw [thirdFullThreeBand_upperFluxSlope_factor244]
  have hp : 0 < (4 / 5 : ℝ) * k ^ 2 * A ^ 3 := by positivity
  constructor
  · intro h
    have hd : 0 < 9 * A - 80 * nu * k := by
      by_contra hn
      have hle : 9 * A - 80 * nu * k ≤ 0 := le_of_not_gt hn
      have hpbad : ((4 / 5 : ℝ) * k ^ 2 * A ^ 3) *
          (9 * A - 80 * nu * k) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hp.le hle
      linarith
    nlinarith
  · intro h
    have hd : 0 < 9 * A - 80 * nu * k := by nlinarith
    exact mul_pos hp hd

/-- Lower-cutoff outward flux is initially decreasing for every
nonnegative viscosity and positive frequency/amplitude. -/
theorem thirdFullThreeBand_lowerFluxSlope_negative244
    (nu k A : ℝ) (hnu : 0 ≤ nu) (hk : 0 < k) (hA : 0 < A) :
    thirdFullThreeBandLowerFluxSlope244 nu k A < 0 := by
  unfold thirdFullThreeBandLowerFluxSlope244
  have hfirst : 0 < (46 / 5 : ℝ) * k ^ 2 * A ^ 4 := by positivity
  have hsecond : 0 ≤ 32 * nu * k ^ 3 * A ^ 3 := by positivity
  linarith

/-- At A=6*nu*k the high mode gains kinetic energy (old theorem), yet
the upper-cutoff *flux* is initially decreasing. -/
theorem thirdFullThreeBand_upperFluxSlope_negative_at_six244
    (nu k : ℝ) (hnu : 0 < nu) (hk : 0 < k) :
    thirdFullThreeBandUpperFluxSlope244 nu k (6 * nu * k) < 0 := by
  rw [thirdFullThreeBand_upperFluxSlope_factor244]
  have hp : 0 < (4 / 5 : ℝ) * k ^ 2 * (6 * nu * k) ^ 3 := by positivity
  have hnk : 0 < nu * k := mul_pos hnu hk
  have hn : 9 * (6 * nu * k) - 80 * nu * k < 0 := by nlinarith
  exact mul_neg_of_pos_of_neg hp hn

/-- At A=10*nu*k the upper-cutoff flux is initially increasing. -/
theorem thirdFullThreeBand_upperFluxSlope_positive_at_ten244
    (nu k : ℝ) (hnu : 0 < nu) (hk : 0 < k) :
    0 < thirdFullThreeBandUpperFluxSlope244 nu k (10 * nu * k) := by
  apply (thirdFullThreeBand_upperFluxSlope_positive_iff244
    nu k (10 * nu * k) hk (by positivity)).2
  have hnk : 0 < nu * k := mul_pos hnu hk
  nlinarith

/-- Concrete separation: high-mode energy gains immediately at the amplitude
6*nu*k, while the outgoing flux past 3*k is already slowing down. -/
theorem thirdFullThreeBand_highGain_upperFluxDrops_at_six244
    (nu k : ℝ) (hnu : 0 < nu) (hk : 0 < k) :
    0 < thirdFullThreeBand_scaledHighNet244 nu k (6 * nu * k) ∧
    thirdFullThreeBandUpperFluxSlope244 nu k (6 * nu * k) < 0 := by
  exact ⟨thirdFullThreeBand_scaledHighNet_supercritical244 nu k hnu hk,
    thirdFullThreeBand_upperFluxSlope_negative_at_six244 nu k hnu hk⟩

/-- Positive quadratic-time kinetic leakage into previously empty outer
frequencies for every positive spatial scale and Fourier amplitude. -/
theorem thirdFullThreeBand_newOuterLeak_positive244
    (k A : ℝ) (hk : 0 < k) (hA : 0 < A) :
    0 < thirdFullThreeBandNewOuterLeakCoefficient244 k A := by
  rw [(thirdFullThreeBand_newLeakCoefficients244 k A).2]
  positivity

end
end PrimeTensor.FirstMonomialTriad
