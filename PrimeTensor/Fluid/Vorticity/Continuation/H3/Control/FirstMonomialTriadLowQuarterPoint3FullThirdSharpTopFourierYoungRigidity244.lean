import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSharpTopFourierYoung244
import Mathlib.Tactic

/-!
# The exact defect and rigidity of sharp top-order Fourier Young absorption

The optimal constant `27/256` is not just a one-sided estimate. For
`x = K E₃`, `d = D₃`, `b = K⁴ E₀`, the *whole* gap between the sharp Young
ceiling and actual top dissipation is the sum of two nonnegative defects:

  256 d³ [d + (27/256)b - x]
    = 27 [b d³ - x⁴]
      + (3x - 4d)² [3x² + 8xd + 16d²].

The first term is the actual Fourier moment interpolation defect. The
second is a **frequency-scale mismatch**: equality in the optimal Young
bound requires `3 K E₃ = 4 D₃`. If `d>0`, saturation also requires exact
saturation of the Fourier interpolation inequality.

This identity yields quantitative near-saturation control, without asserting
that a physical Navier–Stokes state can attain equality. In particular it
is NOT a new unconditional H³ continuation theorem. The nontrivial next
analytic question is whether the actual Fourier moment inequality is
strict/quantitatively stable for relevant physical spectral distributions.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1200000

/-- Exact decomposition of the optimal fourth-power Young gap into
moment-defect and scale-mismatch contributions. No inequality is used. -/
theorem h3_sharpTopYoung_exactDefect244 (x b d : ℝ) :
    256 * d ^ 3 * (d + (27 / 256 : ℝ) * b - x) =
      27 * (b * d ^ 3 - x ^ 4) +
        (3 * x - 4 * d) ^ 2 *
          (3 * x ^ 2 + 8 * x * d + 16 * d ^ 2) := by
  ring

/-- The moment inequality bounds the entire mismatch contribution by
`256 d³` times the sharp Young gap, an effective stability estimate. -/
theorem h3_sharpTopYoung_mismatch_le_gap244
    {x b d : ℝ}
    (hPower : x ^ 4 ≤ b * d ^ 3) :
    (3 * x - 4 * d) ^ 2 *
        (3 * x ^ 2 + 8 * x * d + 16 * d ^ 2) ≤
      256 * d ^ 3 * (d + (27 / 256 : ℝ) * b - x) := by
  have hMoment : 0 ≤ 27 * (b * d ^ 3 - x ^ 4) := by
    apply mul_nonneg (by norm_num)
    exact sub_nonneg.mpr hPower
  have hExact := h3_sharpTopYoung_exactDefect244 x b d
  linarith only [hExact, hMoment]

/-- An upper bound on the Young gap forces a quantitative bound on the
scale-mismatch square, provided actual top dissipation is nonnegative. -/
theorem h3_sharpTopYoung_mismatch_le_nearSaturation244
    {x b d δ : ℝ}
    (hd : 0 ≤ d)
    (hPower : x ^ 4 ≤ b * d ^ 3)
    (hNear : d + (27 / 256 : ℝ) * b - x ≤ δ) :
    (3 * x - 4 * d) ^ 2 *
        (3 * x ^ 2 + 8 * x * d + 16 * d ^ 2) ≤
      256 * δ * d ^ 3 := by
  have hMismatch := h3_sharpTopYoung_mismatch_le_gap244 hPower
  have hFactor : 0 ≤ (256 : ℝ) * d ^ 3 :=
    mul_nonneg (by norm_num) (pow_nonneg hd 3)
  have hScaled := mul_le_mul_of_nonneg_left hNear hFactor
  nlinarith only [hMismatch, hScaled]

/-- Saturation of the optimal Young bound with positive dissipation
forces BOTH equality in the Fourier moment estimate and the critical
`3x=4d` frequency ratio. -/
theorem h3_sharpTopYoung_equalityRigidity244
    {x b d : ℝ}
    (hx : 0 ≤ x) (hd : 0 < d)
    (hPower : x ^ 4 ≤ b * d ^ 3)
    (hSat : x = d + (27 / 256 : ℝ) * b) :
    x ^ 4 = b * d ^ 3 ∧ 3 * x = 4 * d := by
  have hGap : d + (27 / 256 : ℝ) * b - x = 0 := by
    linarith only [hSat]
  have hExact := h3_sharpTopYoung_exactDefect244 x b d
  rw [hGap, mul_zero] at hExact
  have hMomentNonneg : 0 ≤ b * d ^ 3 - x ^ 4 :=
    sub_nonneg.mpr hPower
  have hProd : 0 ≤ x * d := mul_nonneg hx hd.le
  have hD2 : 0 < d ^ 2 := pow_pos hd 2
  have hQuadratic : 0 < 3 * x ^ 2 + 8 * x * d + 16 * d ^ 2 := by
    nlinarith only [sq_nonneg x, hProd, hD2]
  have hMismatchNonneg : 0 ≤
      (3 * x - 4 * d) ^ 2 *
        (3 * x ^ 2 + 8 * x * d + 16 * d ^ 2) :=
    mul_nonneg (sq_nonneg _) hQuadratic.le
  have hMomentZero : b * d ^ 3 - x ^ 4 = 0 := by
    linarith only [hExact, hMomentNonneg, hMismatchNonneg]
  have hMismatchZero :
      (3 * x - 4 * d) ^ 2 *
        (3 * x ^ 2 + 8 * x * d + 16 * d ^ 2) = 0 := by
    linarith only [hExact, hMomentZero]
  have hSquareZero : (3 * x - 4 * d) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hMismatchZero with hSq | hQ
    · exact hSq
    · exact False.elim ((ne_of_gt hQuadratic) hQ)
  constructor
  · linarith only [hMomentZero]
  · nlinarith only [hSquareZero]

/-- The full defect budget is an EXACT identity for arbitrary physical
Fourier blocks; using the Navier–Stokes moment inequality makes its two
right-hand contributions nonnegative. -/
theorem h3Path_sharpTopFourierYoung_exactDefect244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t K : ℝ) :
    256 * velocityH3Dissipation3At u t ^ 3 *
        (velocityH3Dissipation3At u t +
          (27 / 256 : ℝ) * (K ^ 4 * velocityH3Energy0At u t) -
          K * velocityH3Energy3At u t) =
      27 * ((K ^ 4 * velocityH3Energy0At u t) *
          velocityH3Dissipation3At u t ^ 3 -
          (K * velocityH3Energy3At u t) ^ 4) +
        (3 * (K * velocityH3Energy3At u t) -
          4 * velocityH3Dissipation3At u t) ^ 2 *
        (3 * (K * velocityH3Energy3At u t) ^ 2 +
          8 * (K * velocityH3Energy3At u t) * velocityH3Dissipation3At u t +
          16 * velocityH3Dissipation3At u t ^ 2) := by
  exact h3_sharpTopYoung_exactDefect244
    (K * velocityH3Energy3At u t)
    (K ^ 4 * velocityH3Energy0At u t)
    (velocityH3Dissipation3At u t)

/-- The *actual* H³ Fourier moment inequality supplies the quantitative
mismatch budget for arbitrary nonnegative Landau coefficient `K`. -/
theorem h3Path_sharpTopFourierYoung_physicalMismatchBound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (hK : 0 ≤ K) :
    (3 * (K * velocityH3Energy3At u t) -
        4 * velocityH3Dissipation3At u t) ^ 2 *
      (3 * (K * velocityH3Energy3At u t) ^ 2 +
        8 * (K * velocityH3Energy3At u t) * velocityH3Dissipation3At u t +
        16 * velocityH3Dissipation3At u t ^ 2) ≤
      256 * velocityH3Dissipation3At u t ^ 3 *
        (velocityH3Dissipation3At u t +
          (27 / 256 : ℝ) * (K ^ 4 * velocityH3Energy0At u t) -
          K * velocityH3Energy3At u t) := by
  have hMoment :=
    velocityH3Energy3At_pow_four_le_energy0_mul_dissipation3_pow_three
      hH3 hClass ht
  have hScaled :
      (K * velocityH3Energy3At u t) ^ 4 ≤
        (K ^ 4 * velocityH3Energy0At u t) *
          velocityH3Dissipation3At u t ^ 3 := by
    calc
      _ = K ^ 4 * velocityH3Energy3At u t ^ 4 := by ring
      _ ≤ K ^ 4 * (velocityH3Energy0At u t *
          velocityH3Dissipation3At u t ^ 3) :=
        mul_le_mul_of_nonneg_left hMoment (pow_nonneg hK 4)
      _ = _ := by ring
  exact h3_sharpTopYoung_mismatch_le_gap244 hScaled

/-- If a physical H³ top-order Young estimate saturates exactly at a
nonzero dissipative time, its top-frequency blocks must satisfy the
precise scale ratio and must saturate the Fourier fourth-moment bound. -/
theorem h3Path_sharpTopFourierYoung_physicalEqualityRigidity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (hK : 0 ≤ K)
    (hD : 0 < velocityH3Dissipation3At u t)
    (hSat : K * velocityH3Energy3At u t =
      velocityH3Dissipation3At u t +
        (27 / 256 : ℝ) * (K ^ 4 * velocityH3Energy0At u t)) :
    (K * velocityH3Energy3At u t) ^ 4 =
        (K ^ 4 * velocityH3Energy0At u t) *
          velocityH3Dissipation3At u t ^ 3 ∧
      3 * (K * velocityH3Energy3At u t) =
        4 * velocityH3Dissipation3At u t := by
  have hx : 0 ≤ K * velocityH3Energy3At u t :=
    mul_nonneg hK (velocityH3Energy3At_nonneg u t)
  have hMoment :=
    velocityH3Energy3At_pow_four_le_energy0_mul_dissipation3_pow_three
      hH3 hClass ht
  have hScaled :
      (K * velocityH3Energy3At u t) ^ 4 ≤
        (K ^ 4 * velocityH3Energy0At u t) *
          velocityH3Dissipation3At u t ^ 3 := by
    calc
      _ = K ^ 4 * velocityH3Energy3At u t ^ 4 := by ring
      _ ≤ K ^ 4 * (velocityH3Energy0At u t *
          velocityH3Dissipation3At u t ^ 3) :=
        mul_le_mul_of_nonneg_left hMoment (pow_nonneg hK 4)
      _ = _ := by ring
  exact h3_sharpTopYoung_equalityRigidity244 hx hD hScaled hSat

end
end PrimeTensor.FirstMonomialTriad
