import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedHighFrechetComplexL2Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spatial.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Reconstruction.Compatibility
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Reduce selected high Fréchet L² to Fourier-coordinate multiplier L²

The remaining diffusion frontier asks for complex fourth/fifth Fréchet
coordinate fields of the selected positive-time restart to belong to physical
`L²`.

For a selected scalar state `H`, each ordered coordinate derivative is exactly
the ordinary inverse Fourier transform of Mathlib's order-generic coordinate
multiplier

    fourierPowSMulRight (-(innerSL ℝ)) (raw H) ξ n m.

The selected all-orders moment theorem already gives the `L¹` integrability
required to differentiate the ordinary inverse Fourier integral.  Therefore
the only additional datum needed here is `L²` membership of those exact
order-four and order-five multiplier amplitudes.

The generic `L¹ ∩ L²` inverse-Fourier compatibility theorem then identifies
the ordinary inverse Fourier integral with Mathlib's unitary `L²` inverse
transform almost everywhere.  Finally the volume-preserving
`Point3 ↔ H3FourierPoint3` transport converts this into the physical complex
`L²` Fréchet-coordinate frontier.

After this file, the high-diffusion branch is a purely spectral `MemLp 2`
problem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedHighFourierCoordinateL2Frontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathSelectedHighFourierCoordinateL2Frontier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Exact selected raw coordinate multipliers -/

noncomputable def h3SelectedFourthFrechetRawCoordinateMultiplier
    (H : H3SpectralScalarState)
    (a b c d : PrimeTensor.Axis Depth.three)
    (ξ : H3FourierPoint3) : ℂ :=
  let m : Fin 4 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection a,
      h3FourierAxisDirection b,
      h3FourierAxisDirection c,
      h3FourierAxisDirection d
    ]
  (VectorFourier.fourierPowSMulRight
      (-(innerSL ℝ :
        H3FourierPoint3 →L[ℝ]
          H3FourierPoint3 →L[ℝ] ℝ))
      (h3SpectralScalarRawFourier H)
      ξ
      4)
    m

noncomputable def h3SelectedFifthFrechetRawCoordinateMultiplier
    (H : H3SpectralScalarState)
    (a b c d e : PrimeTensor.Axis Depth.three)
    (ξ : H3FourierPoint3) : ℂ :=
  let m : Fin 5 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection a,
      h3FourierAxisDirection b,
      h3FourierAxisDirection c,
      h3FourierAxisDirection d,
      h3FourierAxisDirection e
    ]
  (VectorFourier.fourierPowSMulRight
      (-(innerSL ℝ :
        H3FourierPoint3 →L[ℝ]
          H3FourierPoint3 →L[ℝ] ℝ))
      (h3SpectralScalarRawFourier H)
      ξ
      5)
    m

/-! ## Positive selected time automatically supplies multiplier L¹ -/

private theorem h3SelectedFourthFrechetRawCoordinateMultiplier_integrable
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (j : Fin 3)
    (a b c d : PrimeTensor.Axis Depth.three) :
    Integrable
      (h3SelectedFourthFrechetRawCoordinateMultiplier
        ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀) q j)
        a b c d)
      (volume : Measure H3FourierPoint3) := by

  let H : H3SpectralScalarState :=
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀) q j

  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier H

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  let m : Fin 4 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection a,
      h3FourierAxisDirection b,
      h3FourierAxisDirection c,
      h3FourierAxisDirection d
    ]

  have hRawInt :
      Integrable f
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f, H]
    exact
      MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1
          ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀) q j))

  have hFourth :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f, H]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        4 hν U₀ hA hU₀ hq hqR j

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 4)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L hFourth hRawInt.aestronglyMeasurable

  have hEvalInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (VectorFourier.fourierPowSMulRight
            L f ξ 4) m)
        (volume : Measure H3FourierPoint3) :=
    ContinuousLinearMap.integrable_comp
      (ContinuousMultilinearMap.apply
        ℝ
        (fun _ : Fin 4 => H3FourierPoint3)
        ℂ
        m)
      hPowInt

  dsimp only [
    h3SelectedFourthFrechetRawCoordinateMultiplier,
    H, f, L, m
  ] at hEvalInt ⊢

  exact hEvalInt

private theorem h3SelectedFifthFrechetRawCoordinateMultiplier_integrable
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (j : Fin 3)
    (a b c d e : PrimeTensor.Axis Depth.three) :
    Integrable
      (h3SelectedFifthFrechetRawCoordinateMultiplier
        ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀) q j)
        a b c d e)
      (volume : Measure H3FourierPoint3) := by

  let H : H3SpectralScalarState :=
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀) q j

  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier H

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  let m : Fin 5 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection a,
      h3FourierAxisDirection b,
      h3FourierAxisDirection c,
      h3FourierAxisDirection d,
      h3FourierAxisDirection e
    ]

  have hRawInt :
      Integrable f
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f, H]
    exact
      MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1
          ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀) q j))

  have hFifth :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f, H]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        5 hν U₀ hA hU₀ hq hqR j

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 5)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L hFifth hRawInt.aestronglyMeasurable

  have hEvalInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (VectorFourier.fourierPowSMulRight
            L f ξ 5) m)
        (volume : Measure H3FourierPoint3) :=
    ContinuousLinearMap.integrable_comp
      (ContinuousMultilinearMap.apply
        ℝ
        (fun _ : Fin 5 => H3FourierPoint3)
        ℂ
        m)
      hPowInt

  dsimp only [
    h3SelectedFifthFrechetRawCoordinateMultiplier,
    H, f, L, m
  ] at hEvalInt ⊢

  exact hEvalInt

/-! ## Exact inverse-Fourier / Fréchet identities -/

private theorem h3SelectedFourthFrechetRawCoordinateMultiplier_fourierInv_eq
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (j : Fin 3)
    (a b c d : PrimeTensor.Axis Depth.three)
    (x : H3FourierPoint3) :
    let H : H3SpectralScalarState :=
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀) q j
    FourierTransformInv.fourierInv
        (h3SelectedFourthFrechetRawCoordinateMultiplier
          H a b c d)
        x
      =
    iteratedFDeriv ℝ 4
      (h3SpectralScalarC1Representative H)
      x
      ![
        h3FourierAxisDirection a,
        h3FourierAxisDirection b,
        h3FourierAxisDirection c,
        h3FourierAxisDirection d
      ] := by
  dsimp only

  let H : H3SpectralScalarState :=
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀) q j

  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier H

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  let m : Fin 4 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection a,
      h3FourierAxisDirection b,
      h3FourierAxisDirection c,
      h3FourierAxisDirection d
    ]

  have hRawInt :
      Integrable f
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f, H]
    exact
      MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1
          ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀) q j))

  have hMom :
      ∀ (n : ℕ), n ≤ (4 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n _hn
    dsimp only [f, H]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        n hν U₀ hA hU₀ hq hqR j

  have hDeriv :=
    VectorFourier.iteratedFDeriv_fourierIntegral
      (L := L)
      (f := f)
      (μ := (volume : Measure H3FourierPoint3))
      hMom
      hRawInt.aestronglyMeasurable
      (n := 4)
      (by norm_num)

  have hEval :=
    congrArg
      (fun F => F x m)
      hDeriv

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 4)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L
      (hMom 4 (by norm_num))
      hRawInt.aestronglyMeasurable

  rw [
    Real.fourierIntegral_continuousMultilinearMap_apply'
      hPowInt
  ] at hEval

  have hInner :
      ContinuousLinearMap.toLinearMap₁₂
          (-(innerSL ℝ :
            H3FourierPoint3 →L[ℝ]
              H3FourierPoint3 →L[ℝ] ℝ))
        =
      -(innerₗ H3FourierPoint3) := by
    ext v w
    simp only [
      ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
      neg_apply,
      innerSL_apply_apply,
      LinearMap.neg_apply,
      innerₗ_apply_apply
    ]

  dsimp only [L] at hEval
  rw [hInner] at hEval

  unfold h3SelectedFourthFrechetRawCoordinateMultiplier
  unfold h3SpectralScalarC1Representative

  change
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        (fun ξ : H3FourierPoint3 =>
          (VectorFourier.fourierPowSMulRight
            (-(innerSL ℝ :
              H3FourierPoint3 →L[ℝ]
                H3FourierPoint3 →L[ℝ] ℝ))
            f ξ 4)
            m)
        x
      =
    iteratedFDeriv ℝ 4
      (VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        f)
      x
      m

  exact hEval.symm

private theorem h3SelectedFifthFrechetRawCoordinateMultiplier_fourierInv_eq
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (j : Fin 3)
    (a b c d e : PrimeTensor.Axis Depth.three)
    (x : H3FourierPoint3) :
    let H : H3SpectralScalarState :=
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀) q j
    FourierTransformInv.fourierInv
        (h3SelectedFifthFrechetRawCoordinateMultiplier
          H a b c d e)
        x
      =
    iteratedFDeriv ℝ 5
      (h3SpectralScalarC1Representative H)
      x
      ![
        h3FourierAxisDirection a,
        h3FourierAxisDirection b,
        h3FourierAxisDirection c,
        h3FourierAxisDirection d,
        h3FourierAxisDirection e
      ] := by
  dsimp only

  let H : H3SpectralScalarState :=
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀) q j

  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier H

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  let m : Fin 5 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection a,
      h3FourierAxisDirection b,
      h3FourierAxisDirection c,
      h3FourierAxisDirection d,
      h3FourierAxisDirection e
    ]

  have hRawInt :
      Integrable f
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f, H]
    exact
      MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1
          ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀) q j))

  have hMom :
      ∀ (n : ℕ), n ≤ (5 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n _hn
    dsimp only [f, H]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        n hν U₀ hA hU₀ hq hqR j

  have hDeriv :=
    VectorFourier.iteratedFDeriv_fourierIntegral
      (L := L)
      (f := f)
      (μ := (volume : Measure H3FourierPoint3))
      hMom
      hRawInt.aestronglyMeasurable
      (n := 5)
      (by norm_num)

  have hEval :=
    congrArg
      (fun F => F x m)
      hDeriv

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 5)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L
      (hMom 5 (by norm_num))
      hRawInt.aestronglyMeasurable

  rw [
    Real.fourierIntegral_continuousMultilinearMap_apply'
      hPowInt
  ] at hEval

  have hInner :
      ContinuousLinearMap.toLinearMap₁₂
          (-(innerSL ℝ :
            H3FourierPoint3 →L[ℝ]
              H3FourierPoint3 →L[ℝ] ℝ))
        =
      -(innerₗ H3FourierPoint3) := by
    ext v w
    simp only [
      ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
      neg_apply,
      innerSL_apply_apply,
      LinearMap.neg_apply,
      innerₗ_apply_apply
    ]

  dsimp only [L] at hEval
  rw [hInner] at hEval

  unfold h3SelectedFifthFrechetRawCoordinateMultiplier
  unfold h3SpectralScalarC1Representative

  change
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        (fun ξ : H3FourierPoint3 =>
          (VectorFourier.fourierPowSMulRight
            (-(innerSL ℝ :
              H3FourierPoint3 →L[ℝ]
                H3FourierPoint3 →L[ℝ] ℝ))
            f ξ 5)
            m)
        x
      =
    iteratedFDeriv ℝ 5
      (VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        f)
      x
      m

  exact hEval.symm

/-! ## Pure spectral high-coordinate L² frontier -/

/--
The only remaining high-diffusion data are `L²` membership of the exact
ordered fourth/fifth raw Fourier coordinate multipliers.
-/
def H3CanonicalSelectedFourthFifthRawCoordinateMultiplierMemLp2OnRestartRadius : Prop :=
  ∀
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t₀ : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E),
      ∀ q : ℝ,
        q ∈
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        let U₀ : H3SpectralVelocityState :=
          h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail
        let hA : 0 < E :=
          lt_of_lt_of_le zero_lt_one hE
        let hU₀ : ‖U₀‖ ≤ E :=
          norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            (one_pos : (0 : ℝ) < 1)
            U₀ hA hU₀
        (
          ∀
            (a b c d : PrimeTensor.Axis Depth.three)
            (j : Fin 3),
              MemLp
                (h3SelectedFourthFrechetRawCoordinateMultiplier
                  (W q j) a b c d)
                2
                (volume : Measure H3FourierPoint3)
        )
          ∧
        (
          ∀
            (a b c d e : PrimeTensor.Axis Depth.three)
            (j : Fin 3),
              MemLp
                (h3SelectedFifthFrechetRawCoordinateMultiplier
                  (W q j) a b c d e)
                2
                (volume : Measure H3FourierPoint3)
        )

/-! ## Plancherel closes the complex physical Fréchet frontier -/

private theorem memLp_point3_fourierInv_of_integrable_memLp2_h3SelectedHighFourier
    {f : H3FourierPoint3 → ℂ}
    (hf1 :
      Integrable
        f
        (volume : Measure H3FourierPoint3))
    (hf2 :
      MemLp
        f
        2
        (volume : Measure H3FourierPoint3)) :
    MemLp
      (fun x : Point3 =>
        FourierTransformInv.fourierInv
          f
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x))
      2
      (volume : Measure Point3) := by

  let f2 : H3FourierComplexL2 :=
    hf2.toLp f

  let u2 : H3FourierComplexL2 :=
    (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).symm f2

  let p2 :
      MeasureTheory.Lp
        ℂ
        2
        (volume : Measure Point3) :=
    MeasureTheory.Lp.compMeasurePreserving
      (WithLp.toLp 2 : Point3 → H3FourierPoint3)
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three))
      u2

  have hCompat :
      FourierTransformInv.fourierInv f
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((u2 : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) := by
    dsimp only [u2, f2]
    exact
      h3FourierInv_integrable_memLp2_ae_eq_L2
        hf1 hf2

  have hComp :
      (fun x : Point3 =>
        FourierTransformInv.fourierInv
          f
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((u2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)) := by
    exact
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hCompat

  have hFrom :
      ((p2 :
          MeasureTheory.Lp
            ℂ
            2
            (volume : Measure Point3)) :
        Point3 → ℂ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((u2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)) := by
    dsimp only [p2]
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        u2
        (PiLp.volume_preserving_toLp
          (PrimeTensor.Axis Depth.three))

  have hAE :
      (fun x : Point3 =>
        FourierTransformInv.fourierInv
          f
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      ((p2 :
          MeasureTheory.Lp
            ℂ
            2
            (volume : Measure Point3)) :
        Point3 → ℂ) :=
    hComp.trans hFrom.symm

  have hp2 :
      MemLp
        ((p2 :
            MeasureTheory.Lp
              ℂ
              2
              (volume : Measure Point3)) :
          Point3 → ℂ)
        2
        (volume : Measure Point3) :=
    MeasureTheory.Lp.memLp p2

  exact
    (memLp_congr_ae hAE).2 hp2

theorem h3CanonicalSelectedFourthFifthFrechetComplexMemLp2OnRestartRadius_of_rawCoordinateMultiplier
    (hMultiplier :
      H3CanonicalSelectedFourthFifthRawCoordinateMultiplierMemLp2OnRestartRadius) :
    H3CanonicalSelectedFourthFifthFrechetComplexMemLp2OnRestartRadius := by

  intro E u T t₀ hNS ht₀ hE hTail q hq

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  have hM :=
    hMultiplier E u T t₀ hNS ht₀ hE hTail q hq

  dsimp only at hM ⊢

  constructor

  · intro a b c d j

    let H : H3SpectralScalarState :=
      W q j

    let f : H3FourierPoint3 → ℂ :=
      h3SelectedFourthFrechetRawCoordinateMultiplier
        H a b c d

    have hf1 :
        Integrable
          f
          (volume : Measure H3FourierPoint3) := by
      dsimp only [f, H, W, U₀, hA, hU₀]
      exact
        h3SelectedFourthFrechetRawCoordinateMultiplier_integrable
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          hq.1
          hq.2.le
          j a b c d

    have hf2 :
        MemLp
          f
          2
          (volume : Measure H3FourierPoint3) := by
      dsimp only [f, H, W, U₀, hA, hU₀]
      exact hM.1 a b c d j

    have hInv :
        MemLp
          (fun x : Point3 =>
            FourierTransformInv.fourierInv
              f
              ((WithLp.toLp 2 :
                Point3 → H3FourierPoint3) x))
          2
          (volume : Measure Point3) :=
      memLp_point3_fourierInv_of_integrable_memLp2_h3SelectedHighFourier
        hf1 hf2

    have hEq :
        (fun x : Point3 =>
          iteratedFDeriv ℝ 4
            (h3SpectralScalarC1Representative
              (W q j))
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)
            ![
              h3FourierAxisDirection a,
              h3FourierAxisDirection b,
              h3FourierAxisDirection c,
              h3FourierAxisDirection d
            ])
          =
        (fun x : Point3 =>
          FourierTransformInv.fourierInv
            f
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)) := by
      funext x
      dsimp only [f, H, W, U₀, hA, hU₀]
      exact
        (h3SelectedFourthFrechetRawCoordinateMultiplier_fourierInv_eq
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          hq.1
          hq.2.le
          j a b c d
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)).symm

    rw [hEq]
    exact hInv

  · intro a b c d e j

    let H : H3SpectralScalarState :=
      W q j

    let f : H3FourierPoint3 → ℂ :=
      h3SelectedFifthFrechetRawCoordinateMultiplier
        H a b c d e

    have hf1 :
        Integrable
          f
          (volume : Measure H3FourierPoint3) := by
      dsimp only [f, H, W, U₀, hA, hU₀]
      exact
        h3SelectedFifthFrechetRawCoordinateMultiplier_integrable
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          hq.1
          hq.2.le
          j a b c d e

    have hf2 :
        MemLp
          f
          2
          (volume : Measure H3FourierPoint3) := by
      dsimp only [f, H, W, U₀, hA, hU₀]
      exact hM.2 a b c d e j

    have hInv :
        MemLp
          (fun x : Point3 =>
            FourierTransformInv.fourierInv
              f
              ((WithLp.toLp 2 :
                Point3 → H3FourierPoint3) x))
          2
          (volume : Measure Point3) :=
      memLp_point3_fourierInv_of_integrable_memLp2_h3SelectedHighFourier
        hf1 hf2

    have hEq :
        (fun x : Point3 =>
          iteratedFDeriv ℝ 5
            (h3SpectralScalarC1Representative
              (W q j))
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)
            ![
              h3FourierAxisDirection a,
              h3FourierAxisDirection b,
              h3FourierAxisDirection c,
              h3FourierAxisDirection d,
              h3FourierAxisDirection e
            ])
          =
        (fun x : Point3 =>
          FourierTransformInv.fourierInv
            f
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)) := by
      funext x
      dsimp only [f, H, W, U₀, hA, hU₀]
      exact
        (h3SelectedFifthFrechetRawCoordinateMultiplier_fourierInv_eq
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          hq.1
          hq.2.le
          j a b c d e
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)).symm

    rw [hEq]
    exact hInv

/-! ## BKM closure at the pure Fourier-coordinate L² frontier -/

theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_selectedRawCoordinateMultiplier_of_transportPressure_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hMultiplier :
      H3CanonicalSelectedFourthFifthRawCoordinateMultiplierMemLp2OnRestartRadius)
    (hTP :
      H3PathEnergyClassProducesTransportPressureMemLp2)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_selectedFourthFifthFrechetComplex_of_transportPressure_of_fullScalarEnergy
      hLow
      hDerivative
      (h3CanonicalSelectedFourthFifthFrechetComplexMemLp2OnRestartRadius_of_rawCoordinateMultiplier
        hMultiplier)
      hTP
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
