import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedTwoSnapshotFlux
import Mathlib.Tactic

/-!
# Finite-radius Lipschitz continuity of the genuine signed sixth-flux integral

The previous two-snapshot theorem retains a reciprocal Young scale for each of
three genuinely mixed Fourier contractions. We eliminate those scales WITHOUT
asserting a false global L2-L2-L2 convolution estimate.

For spectral distance d = ‖V-W‖, choose a positive regularization τ=d+ε.
The first mixed term uses scale 1/sqrt τ, the middle term uses scale 1,
and the third uses scale sqrt τ. The two outer terms then contribute at most
O(τ), while the middle term contributes O(d). A purely real algebra lemma
makes the estimate uniform even when d=0. Letting ε approach zero proves
an actual Lipschitz bound for the complex signed integral on LowMax(R).

This theorem is FOR EACH FIXED R. It does not assert uniformity as R tends
to infinity, terminal-time H3 bounds, or a Navier-Stokes continuation claim.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev LA3 := PrimeTensor.Axis Depth.three
private abbrev LV3 := H3FourierPoint3

-- The finite axis structure supplies the normed Fourier point and
-- volume-measure instances for the concrete three-dimensional carrier.
noncomputable local instance axisFintypeKineticLowMaxLipschitz244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Real reciprocal-scale optimization -/

/-- Quantitative real arithmetic for the three mixed contractions.
The denominator τ is strictly positive; the estimate works also at d=0. -/
private theorem thirdFullKinetic_twoSnapshot_sqrtScale_algebra244
    (D a b d τ : ℝ)
    (hD : 0 ≤ D) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hdt : d ≤ τ) (hτ : 0 < τ) :
    (((τ⁻¹ * (3 * d ^ 2) + τ * (3 * a ^ 2)) / 2) * (D * a) +
      ((3 * b ^ 2 + 3 * a ^ 2) / 2) * (D * d)) +
      ((τ * (3 * b ^ 2) + τ⁻¹ * (3 * d ^ 2)) / 2) * (D * b) ≤
    9 * D * τ * (1 + a + b) ^ 3 := by
  let M : ℝ := 1 + a + b
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have haM : a ≤ M := by dsimp [M]; linarith
  have hbM : b ≤ M := by dsimp [M]; linarith
  have hM2 : 1 ≤ M ^ 2 := by nlinarith [sq_nonneg (M - 1)]
  have hM2M3 : M ^ 2 ≤ M ^ 3 := by
    calc
      M ^ 2 = 1 * M ^ 2 := by ring
      _ ≤ M * M ^ 2 := mul_le_mul_of_nonneg_right hM (sq_nonneg M)
      _ = M ^ 3 := by ring
  have hτM : τ ≤ τ * M ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hM2 hτ.le
    nlinarith only [h]
  have ha2 : a ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ ha haM 2
  have hb2 : b ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hb hbM 2
  have hd2 : d ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ hd hdt 2
  have hRatio : d ^ 2 * τ⁻¹ ≤ τ := by
    calc
      d ^ 2 * τ⁻¹ ≤ τ ^ 2 * τ⁻¹ :=
        mul_le_mul_of_nonneg_right hd2 (inv_nonneg.mpr hτ.le)
      _ = τ := by field_simp [ne_of_gt hτ]
  have hRatioM : τ⁻¹ * d ^ 2 ≤ τ * M ^ 2 := by
    calc
      _ = d ^ 2 * τ⁻¹ := by ring
      _ ≤ τ := hRatio
      _ ≤ τ * M ^ 2 := hτM
  have hτa : τ * a ^ 2 ≤ τ * M ^ 2 :=
    mul_le_mul_of_nonneg_left ha2 hτ.le
  have hτb : τ * b ^ 2 ≤ τ * M ^ 2 :=
    mul_le_mul_of_nonneg_left hb2 hτ.le
  have hN1 :
      (τ⁻¹ * (3 * d ^ 2) + τ * (3 * a ^ 2)) / 2 ≤
        3 * τ * M ^ 2 := by
    nlinarith only [hRatioM, hτa]
  have hN2 :
      (3 * b ^ 2 + 3 * a ^ 2) / 2 ≤ 3 * M ^ 2 := by
    nlinarith only [ha2, hb2]
  have hN3 :
      (τ * (3 * b ^ 2) + τ⁻¹ * (3 * d ^ 2)) / 2 ≤
        3 * τ * M ^ 2 := by
    nlinarith only [hRatioM, hτb]
  have hDa : D * a ≤ D * M := mul_le_mul_of_nonneg_left haM hD
  have hDb : D * b ≤ D * M := mul_le_mul_of_nonneg_left hbM hD
  have hDd : D * d ≤ D * τ := mul_le_mul_of_nonneg_left hdt hD
  have hFirst :
      ((τ⁻¹ * (3 * d ^ 2) + τ * (3 * a ^ 2)) / 2) * (D * a) ≤
        3 * D * τ * M ^ 3 := by
    calc
      _ ≤ (3 * τ * M ^ 2) * (D * a) :=
        mul_le_mul_of_nonneg_right hN1 (mul_nonneg hD ha)
      _ ≤ (3 * τ * M ^ 2) * (D * M) :=
        mul_le_mul_of_nonneg_left hDa (by positivity)
      _ = 3 * D * τ * M ^ 3 := by ring
  have hMiddle :
      ((3 * b ^ 2 + 3 * a ^ 2) / 2) * (D * d) ≤
        3 * D * τ * M ^ 3 := by
    calc
      _ ≤ (3 * M ^ 2) * (D * d) :=
        mul_le_mul_of_nonneg_right hN2 (mul_nonneg hD hd)
      _ ≤ (3 * M ^ 2) * (D * τ) :=
        mul_le_mul_of_nonneg_left hDd (by positivity)
      _ ≤ (3 * M ^ 3) * (D * τ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hM2M3 (by norm_num))
          (mul_nonneg hD hτ.le)
      _ = 3 * D * τ * M ^ 3 := by ring
  have hLast :
      ((τ * (3 * b ^ 2) + τ⁻¹ * (3 * d ^ 2)) / 2) * (D * b) ≤
        3 * D * τ * M ^ 3 := by
    calc
      _ ≤ (3 * τ * M ^ 2) * (D * b) :=
        mul_le_mul_of_nonneg_right hN3 (mul_nonneg hD hb)
      _ ≤ (3 * τ * M ^ 2) * (D * M) :=
        mul_le_mul_of_nonneg_left hDb (by positivity)
      _ = 3 * D * τ * M ^ 3 := by ring
  change _ ≤ 9 * D * τ * M ^ 3
  calc
    _ ≤ (3 * D * τ * M ^ 3 + 3 * D * τ * M ^ 3) +
          3 * D * τ * M ^ 3 :=
      add_le_add (add_le_add hFirst hMiddle) hLast
    _ = _ := by ring

/-- Remove an arbitrary positive additive regularization from a
nonnegative multiple, without dividing by the spectral distance. -/
private theorem thirdFullKinetic_le_of_all_regularizations244
    (x y A : ℝ) (hA : 0 ≤ A)
    (h : ∀ ε : ℝ, 0 < ε → x ≤ A * (y + ε)) :
    x ≤ A * y := by
  apply le_of_forall_pos_le_add
  intro η hη
  let ε : ℝ := η / (A + 1)
  have hDen : 0 < A + 1 := by linarith
  have hε : 0 < ε := div_pos hη hDen
  have hRatio : A / (A + 1) ≤ 1 :=
    (div_le_iff₀ hDen).mpr (by linarith)
  have hEpsilonCost : A * ε ≤ η := by
    calc
      A * ε = (A / (A + 1)) * η := by dsimp [ε]; ring
      _ ≤ 1 * η := mul_le_mul_of_nonneg_right hRatio hη.le
      _ = η := one_mul η
  calc
    x ≤ A * (y + ε) := h ε hε
    _ = A * y + A * ε := by ring
    _ ≤ A * y + η := add_le_add_right hEpsilonCost (A * y)

/-! ## Exact phase-bearing spectral flux Lipschitz theorem -/

/-- With ε>0, the reciprocal Young scales can be selected without any
case split on the weighted-H3 distance. This is the algebraic precursor
of the exact Lipschitz bound. -/
theorem thirdFullKinetic_lowMax_twoSnapshot_signedFlux_regularized244
    (R : ℕ)
    (v w : LA3 → SchwartzMap LV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : LA3,
      (V (h3ClassicalizationFinOfAxis j) : LV3 → ℂ) =ᵐ[volume]
        (fun ξ : LV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : LA3,
      (W (h3ClassicalizationFinOfAxis j) : LV3 → ℂ) =ᵐ[volume]
        (fun ξ : LV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ))
    (ε : ℝ) (hε : 0 < ε) :
    ‖thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v -
      thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w‖ ≤
      (243 * (2 * ((R : ℝ) + 1)) ^ 7 * h3SobolevDeweightingConstant) *
        (‖V - W‖ + ε) * (1 + ‖V‖ + ‖W‖) ^ 3 := by
  let d : ℝ := ‖V - W‖
  let a : ℝ := ‖V‖
  let b : ℝ := ‖W‖
  let τ : ℝ := d + ε
  let s : ℝ := Real.sqrt τ
  let C : ℝ := 9 * (2 * ((R : ℝ) + 1)) ^ 7
  let D : ℝ := 3 * h3SobolevDeweightingConstant
  have hd : 0 ≤ d := norm_nonneg _
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hτ : 0 < τ := by dsimp only [τ]; linarith
  have hdt : d ≤ τ := by dsimp only [τ]; linarith
  have hs : 0 < s := Real.sqrt_pos.2 hτ
  have his : 0 < s⁻¹ := inv_pos.mpr hs
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (by norm_num) h3SobolevDeweightingConstant_nonneg
  have hSq : s ^ 2 = τ := Real.sq_sqrt hτ.le
  have hInvSq : (s⁻¹) ^ 2 = τ⁻¹ := by rw [inv_pow, hSq]
  have hInvInvSq : ((s⁻¹)⁻¹) ^ 2 = τ := by rw [inv_inv, hSq]
  have hScaled := thirdFullKinetic_lowMax_twoSnapshot_signedFlux_scaled244
    R v w V W hv hw (s⁻¹) 1 s his (by norm_num) hs
  have hAlgebra := thirdFullKinetic_twoSnapshot_sqrtScale_algebra244
    D a b d τ hD ha hb hd hdt hτ
  calc
    ‖thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v -
        thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w‖ ≤
      (thirdFullKineticTwoSnapshotMixedBound244 R (s⁻¹) d a a +
        thirdFullKineticTwoSnapshotMixedBound244 R 1 b d a) +
        thirdFullKineticTwoSnapshotMixedBound244 R s b b d := hScaled
    _ = C *
          ((((τ⁻¹ * (3 * d ^ 2) + τ * (3 * a ^ 2)) / 2) * (D * a) +
            ((3 * b ^ 2 + 3 * a ^ 2) / 2) * (D * d)) +
            ((τ * (3 * b ^ 2) + τ⁻¹ * (3 * d ^ 2)) / 2) * (D * b)) := by
      dsimp only [thirdFullKineticTwoSnapshotMixedBound244]
      rw [hInvSq, hInvInvSq, hSq]
      simp only [one_pow, inv_one, one_mul]
      dsimp only [C, D]
      ring
    _ ≤ C * (9 * D * τ * (1 + a + b) ^ 3) :=
      mul_le_mul_of_nonneg_left hAlgebra hC
    _ = (243 * (2 * ((R : ℝ) + 1)) ^ 7 *
          h3SobolevDeweightingConstant) *
          (‖V - W‖ + ε) * (1 + ‖V‖ + ‖W‖) ^ 3 := by
      dsimp only [C, D, τ, d, a, b]
      ring

/-- The TRUE signed complex sixth-flux integral is locally Lipschitz in
its actual weighted-H3 spectral state on each literal LowMax(R) sector.
No extra mixed-integrability assumptions, no solenoidal approximation
hypotheses, and no globally uniform frequency bound are needed. -/
theorem thirdFullKinetic_lowMax_twoSnapshot_signedFlux_lipschitz244
    (R : ℕ)
    (v w : LA3 → SchwartzMap LV3 ℂ)
    (V W : H3SpectralVelocityState)
    (hv : ∀ j : LA3,
      (V (h3ClassicalizationFinOfAxis j) : LV3 → ℂ) =ᵐ[volume]
        (fun ξ : LV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : LA3,
      (W (h3ClassicalizationFinOfAxis j) : LV3 → ℂ) =ᵐ[volume]
        (fun ξ : LV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ)) :
    ‖thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v -
      thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w‖ ≤
      (243 * (2 * ((R : ℝ) + 1)) ^ 7 * h3SobolevDeweightingConstant) *
        ‖V - W‖ * (1 + ‖V‖ + ‖W‖) ^ 3 := by
  let A : ℝ :=
    (243 * (2 * ((R : ℝ) + 1)) ^ 7 * h3SobolevDeweightingConstant) *
      (1 + ‖V‖ + ‖W‖) ^ 3
  have hA : 0 ≤ A := by
    dsimp only [A]
    have hC : 0 ≤ h3SobolevDeweightingConstant :=
      h3SobolevDeweightingConstant_nonneg
    positivity
  have hNear (ε : ℝ) (hε : 0 < ε) :
      ‖thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v -
        thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w‖ ≤
        A * (‖V - W‖ + ε) := by
    have h := thirdFullKinetic_lowMax_twoSnapshot_signedFlux_regularized244
      R v w V W hv hw ε hε
    simpa only [A, mul_assoc, mul_left_comm, mul_comm] using h
  have hLimit := thirdFullKinetic_le_of_all_regularizations244
    (‖thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R v -
      thirdFullKineticSchwartzSignedLowMaxFluxIntegral244 R w‖)
    ‖V - W‖ A hA hNear
  convert hLimit using 1 <;> dsimp only [A] <;> ring

end
end PrimeTensor.FirstMonomialTriad
