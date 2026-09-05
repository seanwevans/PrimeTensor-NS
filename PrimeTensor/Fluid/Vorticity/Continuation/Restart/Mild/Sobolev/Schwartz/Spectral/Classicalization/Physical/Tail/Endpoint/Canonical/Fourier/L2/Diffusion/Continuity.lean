import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.L2.Evolution
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Raw.L2.Shift

/-!
# Classicalization: strong Fourier `L²` continuity of endpoint diffusion

The reduced endpoint hypothesis gives strong continuity of the weighted H³
spectral path without assuming time continuity of the concrete second-order
jet slots.

The Laplacian should therefore be obtained directly from the weighted spectral
state.  If

    G(ξ) = W₃(ξ) f̂(ξ),

then

    Δf ̂(ξ) = -q(ξ) f̂(ξ)
             = -(q(ξ) / W₃(ξ)) G(ξ),

with

    q(ξ) = (2π)² ‖ξ‖²
    W₃(ξ)² = 1 + q + q² + q³.

Since `q² ≤ W₃²`, we have `q / W₃ ≤ 1`.  Thus the deweighted Laplacian
multiplier is a contraction from the weighted H³ scalar state to raw Fourier
`L²`.

This file packages that contraction and identifies it with the already-defined
endpoint Fourier `L²` Laplacian.  Consequently the endpoint diffusion path is
strongly continuous in Fourier `L²`, using only continuity of the weighted H³
path.

No second-jet time-continuity assumption is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalFourierL2DiffusionContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The deweighted Fourier Laplacian multiplier on a weighted H³ state. -/
def h3SpectralScalarLaplacianRawMultiplier
    (ξ : H3FourierPoint3) : ℂ :=
  ((-(h3FourierGradientSquare ξ *
        h3SobolevFrequencyWeightInv ξ) : ℝ) : ℂ)

/-- The scalar coefficient `q / W₃` is bounded by one. -/
theorem h3FourierGradientSquare_mul_weightInv_le_one
    (ξ : H3FourierPoint3) :
    h3FourierGradientSquare ξ *
        h3SobolevFrequencyWeightInv ξ
      ≤ 1 := by
  let q : ℝ := h3FourierGradientSquare ξ
  let W : ℝ := h3SobolevFrequencyWeight ξ

  have hq : 0 ≤ q := by
    dsimp only [q]
    exact h3FourierGradientSquare_nonneg ξ

  have hWpos : 0 < W := by
    dsimp only [W]
    exact h3SobolevFrequencyWeight_pos ξ

  have hq2le :
      q ^ 2 ≤ h3SobolevFrequencyWeightSq ξ := by
    dsimp only [q]
    unfold h3SobolevFrequencyWeightSq
    have hq0 := h3FourierGradientSquare_nonneg ξ
    have hq3 : 0 ≤ h3FourierGradientSquare ξ ^ 3 := by positivity
    linarith

  have hqleW : q ≤ W := by
    calc
      q = Real.sqrt (q ^ 2) := by
        rw [Real.sqrt_sq hq]
      _ ≤ Real.sqrt (h3SobolevFrequencyWeightSq ξ) :=
        Real.sqrt_le_sqrt hq2le
      _ = W := by
        rfl

  unfold h3SobolevFrequencyWeightInv
  change q * W⁻¹ ≤ 1

  calc
    q * W⁻¹ ≤ W * W⁻¹ :=
      mul_le_mul_of_nonneg_right
        hqleW
        (inv_nonneg.mpr hWpos.le)
    _ = 1 :=
      mul_inv_cancel₀ (ne_of_gt hWpos)

/-- The complex Laplacian multiplier has norm at most one. -/
theorem norm_h3SpectralScalarLaplacianRawMultiplier_le_one
    (ξ : H3FourierPoint3) :
    ‖h3SpectralScalarLaplacianRawMultiplier ξ‖ ≤ 1 := by
  unfold h3SpectralScalarLaplacianRawMultiplier
  rw [Complex.norm_real, Real.norm_eq_abs, abs_neg]
  have hnonneg :
      0 ≤ h3FourierGradientSquare ξ *
        h3SobolevFrequencyWeightInv ξ := by
    exact
      mul_nonneg
        (h3FourierGradientSquare_nonneg ξ)
        (inv_nonneg.mpr
          (h3SobolevFrequencyWeight_pos ξ).le)
  rw [abs_of_nonneg hnonneg]
  exact h3FourierGradientSquare_mul_weightInv_le_one ξ

/-- Raw Fourier Laplacian of a weighted scalar H³ state, bundled in `L²`. -/
noncomputable def h3SpectralScalarLaplacianRawFourierL2
    (G : H3SpectralScalarState) :
    H3FourierComplexL2 := by
  let f : H3FourierPoint3 → ℂ :=
    fun ξ => h3SpectralScalarLaplacianRawMultiplier ξ * G ξ

  have hfMeas :
      AEStronglyMeasurable
        f
        (volume : Measure H3FourierPoint3) := by
    apply AEStronglyMeasurable.mul
    · apply Continuous.aestronglyMeasurable
      have hq :
          Continuous h3FourierGradientSquare := by
        unfold h3FourierGradientSquare
        fun_prop

      have hReal :
          Continuous
            (fun ξ : H3FourierPoint3 =>
              -(h3FourierGradientSquare ξ *
                h3SobolevFrequencyWeightInv ξ)) :=
        (hq.mul continuous_h3SobolevFrequencyWeightInv).neg

      unfold h3SpectralScalarLaplacianRawMultiplier
      exact Complex.continuous_ofReal.comp hReal
    · exact (MeasureTheory.Lp.memLp G).1

  have hf :
      MemLp
        f
        2
        (volume : Measure H3FourierPoint3) := by
    apply (MeasureTheory.Lp.memLp G).of_le hfMeas
    filter_upwards with ξ
    rw [norm_mul]
    calc
      ‖h3SpectralScalarLaplacianRawMultiplier ξ‖ * ‖G ξ‖
          ≤ 1 * ‖G ξ‖ :=
        mul_le_mul_of_nonneg_right
          (norm_h3SpectralScalarLaplacianRawMultiplier_le_one ξ)
          (norm_nonneg (G ξ))
      _ = ‖G ξ‖ := one_mul _

  exact hf.toLp f

/-- The bundled Laplacian has its defining multiplier representative a.e. -/
theorem h3SpectralScalarLaplacianRawFourierL2_ae
    (G : H3SpectralScalarState) :
    ((h3SpectralScalarLaplacianRawFourierL2 G :
        H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ =>
      h3SpectralScalarLaplacianRawMultiplier ξ * G ξ) := by
  unfold h3SpectralScalarLaplacianRawFourierL2
  dsimp only
  exact MemLp.coeFn_toLp _

/-- The weighted-H³-to-raw-Laplacian map is contractive. -/
theorem norm_h3SpectralScalarLaplacianRawFourierL2_le
    (G : H3SpectralScalarState) :
    ‖h3SpectralScalarLaplacianRawFourierL2 G‖ ≤ ‖G‖ := by
  unfold h3SpectralScalarLaplacianRawFourierL2
  dsimp only

  rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_def]

  refine
    ENNReal.toReal_mono
      (MeasureTheory.Lp.eLpNorm_ne_top G)
      ?_

  apply eLpNorm_mono_ae
  filter_upwards with ξ
  rw [norm_mul]
  exact
    (mul_le_mul_of_nonneg_right
      (norm_h3SpectralScalarLaplacianRawMultiplier_le_one ξ)
      (norm_nonneg (G ξ))).trans_eq
      (one_mul ‖G ξ‖)

/-- The raw Fourier Laplacian respects subtraction. -/
theorem h3SpectralScalarLaplacianRawFourierL2_sub
    (G H : H3SpectralScalarState) :
    h3SpectralScalarLaplacianRawFourierL2 (G - H)
      =
    h3SpectralScalarLaplacianRawFourierL2 G
      -
    h3SpectralScalarLaplacianRawFourierL2 H := by
  apply MeasureTheory.Lp.ext

  have hGH :=
    h3SpectralScalarLaplacianRawFourierL2_ae (G - H)
  have hG :=
    h3SpectralScalarLaplacianRawFourierL2_ae G
  have hH :=
    h3SpectralScalarLaplacianRawFourierL2_ae H
  have hSub :=
    MeasureTheory.Lp.coeFn_sub G H
  have hOutSub :=
    MeasureTheory.Lp.coeFn_sub
      (h3SpectralScalarLaplacianRawFourierL2 G)
      (h3SpectralScalarLaplacianRawFourierL2 H)

  filter_upwards [hGH, hG, hH, hSub, hOutSub] with ξ hGHξ hGξ hHξ hSubξ hOutξ

  rw [hGHξ, hOutξ]
  simp only [Pi.sub_apply]
  rw [hGξ, hHξ, hSubξ]
  simp only [Pi.sub_apply]
  ring

/-- The raw Fourier Laplacian map is one-Lipschitz. -/
theorem norm_h3SpectralScalarLaplacianRawFourierL2_sub_le
    (G H : H3SpectralScalarState) :
    ‖h3SpectralScalarLaplacianRawFourierL2 G
        -
      h3SpectralScalarLaplacianRawFourierL2 H‖
      ≤
    ‖G - H‖ := by
  rw [
    ← h3SpectralScalarLaplacianRawFourierL2_sub
  ]
  exact
    norm_h3SpectralScalarLaplacianRawFourierL2_le
      (G - H)

/-- Hence the raw Fourier Laplacian is strongly continuous as a function of the
weighted H³ state. -/
theorem continuous_h3SpectralScalarLaplacianRawFourierL2 :
    Continuous h3SpectralScalarLaplacianRawFourierL2 := by
  rw [continuous_iff_continuousAt]
  intro G

  unfold ContinuousAt
  rw [tendsto_iff_norm_sub_tendsto_zero]

  apply squeeze_zero
  · intro H
    exact norm_nonneg _
  · intro H
    exact
      norm_h3SpectralScalarLaplacianRawFourierL2_sub_le H G
  · exact
      tendsto_iff_norm_sub_tendsto_zero.1
        continuousAt_id

/-- The generic weighted-state Laplacian representative is the familiar
`-q * raw(G)` expression. -/
theorem h3SpectralScalarLaplacianRawFourierL2_ae_eq_gradientSquare_mul_raw
    (G : H3SpectralScalarState) :
    ((h3SpectralScalarLaplacianRawFourierL2 G :
        H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ =>
      -(h3FourierGradientSquare ξ : ℂ) *
        h3SpectralScalarRawFourierL2 G ξ) := by
  have hLap :=
    h3SpectralScalarLaplacianRawFourierL2_ae G
  have hRaw :=
    h3SpectralScalarRawFourierL2_ae G

  filter_upwards [hLap, hRaw] with ξ hLapξ hRawξ

  rw [hLapξ, hRawξ]
  unfold
    h3SpectralScalarLaplacianRawMultiplier
    h3SpectralScalarRawFourier
    h3SobolevFrequencyWeightInvComplex
  push_cast
  ring

/-- The already-packaged endpoint Fourier `L²` Laplacian is exactly the
contractive weighted-state Laplacian map. -/
theorem h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_eq_spectralLaplacian
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau)
    (j : Fin 3) :
    h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
        hNS ht hEnd hTail q j
      =
    h3SpectralScalarLaplacianRawFourierL2
      ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
        (q : ℝ)) j) := by
  apply MeasureTheory.Lp.ext

  have hOld :=
    h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_ae_eq_normalizedRealPath
      hNS ht htau hEnd hE hTail hEndpoint
      (q : ℝ) q.property j

  have hNew :=
    h3SpectralScalarLaplacianRawFourierL2_ae_eq_gradientSquare_mul_raw
      ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint
        (q : ℝ)) j)

  filter_upwards [hOld, hNew] with ξ hOldξ hNewξ
  rw [hOldξ, hNewξ]

/-- Strong continuity of the quotient-safe endpoint Fourier `L²` diffusion
coordinate on the entire closed elapsed interval. -/
theorem continuous_h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (j : Fin 3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
          hNS ht hEnd hTail q j) := by
  have hW :
      Continuous
        (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint) :=
    continuous_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  have hCoord :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau.le hEnd hE hTail hEndpoint
            (q : ℝ)) j) :=
    (continuous_apply j).comp
      (hW.comp continuous_subtype_val)

  have hNew :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          h3SpectralScalarLaplacianRawFourierL2
            ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
              hNS ht htau.le hEnd hE hTail hEndpoint
              (q : ℝ)) j)) :=
    continuous_h3SpectralScalarLaplacianRawFourierL2.comp
      hCoord

  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
          hNS ht hEnd hTail q j)
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3SpectralScalarLaplacianRawFourierL2
          ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau.le hEnd hE hTail hEndpoint
            (q : ℝ)) j)) := by
    funext q
    exact
      h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_eq_spectralLaplacian
        hNS ht htau hEnd hE hTail hEndpoint q j

  rw [hEq]
  exact hNew

end

end Euclidean
end Bridge
end PrimeTensor
