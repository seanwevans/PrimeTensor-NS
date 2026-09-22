import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedForcingUniformRadialL2

/-!
# Order-generic uniform radial Fourier L² bounds for selected forcing

The fourth/fifth checkpoint proved the square estimate twice.  This file
extracts the repeated argument at arbitrary natural radial order `m ≥ 1`.

For the unheated selected nonlinear forcing `N_s` on a positive terminal slab,

    (|ξ|^m |N_s(ξ)|)^2
      ≤ L∞ * |ξ|^(2m) |N_s(ξ)|.

The state moment slab of order `2m+1` supplies a forcing moment of order
`2m`, uniformly in source time.  The global Fourier `L∞` ceiling supplies the
other factor.  Hence one numerical constant bounds the squared weighted `L²`
integral uniformly for every source time in `[q/2,q]`.

The theorem immediately provides the additional order-six bound needed to
interpolate the fifth weighted `L²` source path from ordinary Fourier `L²`
continuity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedForcingUniformRadialL2Generic
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Pointwise square estimate from a frequency-independent ceiling. -/
private theorem radialWeight_sq_le_linf_mul_doubleWeight
    (m : ℕ)
    (N : H3FourierPoint3 → ℂ)
    (L : ℝ)
    (hLinf : ∀ ξ, ‖N ξ‖ ≤ L)
    (ξ : H3FourierPoint3) :
    ‖((‖ξ‖ ^ m : ℝ) : ℂ) * N ξ‖ ^ 2
      ≤
    L * (‖ξ‖ ^ (2 * m) * ‖N ξ‖) := by

  have hr0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have hrm0 : 0 ≤ ‖ξ‖ ^ m := pow_nonneg hr0 m
  have hN0 : 0 ≤ ‖N ξ‖ := norm_nonneg _

  have hPow :
      (‖ξ‖ ^ m) ^ 2 = ‖ξ‖ ^ (2 * m) := by
    rw [pow_two, ← pow_add]
    congr 1
    omega

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hrm0,
    mul_pow,
    hPow
  ]

  calc
    ‖ξ‖ ^ (2 * m) * ‖N ξ‖ ^ 2
        =
      ‖ξ‖ ^ (2 * m) * (‖N ξ‖ * ‖N ξ‖) := by
      rw [pow_two]
    _ ≤
      ‖ξ‖ ^ (2 * m) * (L * ‖N ξ‖) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (hLinf ξ)
            hN0)
          (pow_nonneg hr0 (2 * m))
    _ =
      L * (‖ξ‖ ^ (2 * m) * ‖N ξ‖) := by
      ring

/-- Integrating the pointwise square estimate gives the quantitative weighted
`L²` bound. -/
private theorem integral_sq_radialWeight_le_linf_mul_momentMass_generic
    (m : ℕ)
    (N : H3FourierPoint3 → ℂ)
    (hN2 :
      MemLp N 2 (volume : Measure H3FourierPoint3))
    (L M : ℝ)
    (hL0 : 0 ≤ L)
    (hLinf : ∀ ξ, ‖N ξ‖ ≤ L)
    (hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ (2 * m) * ‖N ξ‖)
        (volume : Measure H3FourierPoint3))
    (hMass :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ (2 * m) * ‖N ξ‖)
        ≤ M) :
    (∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ m : ℝ) : ℂ) * N ξ‖ ^ 2)
      ≤
    L * M := by

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          L * (‖ξ‖ ^ (2 * m) * ‖N ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul L

  have hWeightedMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ m : ℝ) : ℂ) * N ξ)
        (volume : Measure H3FourierPoint3) :=
    (Complex.continuous_ofReal.comp
      (continuous_norm.pow m)).aestronglyMeasurable.mul
      hN2.1

  have hLeftMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ m : ℝ) : ℂ) * N ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    (hWeightedMeas.norm.aemeasurable.pow_const 2).aestronglyMeasurable

  have hLeftInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ m : ℝ) : ℂ) * N ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) := by
    refine hMajor.mono' hLeftMeas ?_
    filter_upwards with ξ
    have hPoint :=
      radialWeight_sq_le_linf_mul_doubleWeight
        m N L hLinf ξ
    rw [
      Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)
    ]
    exact hPoint

  calc
    (∫ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ m : ℝ) : ℂ) * N ξ‖ ^ 2)
        ≤
      ∫ ξ : H3FourierPoint3,
        L * (‖ξ‖ ^ (2 * m) * ‖N ξ‖) := by
      apply integral_mono hLeftInt hMajor
      intro ξ
      exact
        radialWeight_sq_le_linf_mul_doubleWeight
          m N L hLinf ξ
    _ =
      L *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ (2 * m) * ‖N ξ‖) := by
      rw [integral_const_mul]
    _ ≤
      L * M :=
      mul_le_mul_of_nonneg_left hMass hL0

/--
Order-generic uniform radial Fourier `L²` control for the selected unheated
nonlinear forcing on a positive terminal half.
-/
theorem exists_selectedRestart_forcing_radialL2_uniform_nat
    {ν A q : ℝ}
    (m : ℕ)
    (hm : 1 ≤ m)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A) :
    ∃ Bm : ℝ,
      0 ≤ Bm ∧
      ∀ s ∈ Set.Icc (q / 2) q, ∀ i : Fin 3,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ m : ℝ) : ℂ) *
              h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ)
          2
          (volume : Measure H3FourierPoint3)
        ∧
        (∫ ξ : H3FourierPoint3,
            ‖((‖ξ‖ ^ m : ℝ) : ℂ) *
              h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖ ^ 2)
          ≤ Bm := by

  have hHalf : 0 < q / 2 := by
    positivity

  have hHalfQ : q / 2 ≤ q := by
    linarith

  let pNat : ℕ := 2 * m + 1

  have hpNat : 3 ≤ pNat := by
    dsimp only [pNat]
    omega

  obtain ⟨BState, BDuhamel, B0, hSlab⟩ :=
    h3SelectedMomentSlab_nat_ge_three
      (a := q / 2)
      (t := q)
      pNat
      hpNat
      hν U₀ hA hU₀
      hHalf hHalfQ hqR

  unfold H3SelectedMomentSlab at hSlab
  rcases hSlab with ⟨hBS0, hBD0, hB00, hData⟩

  let L : ℝ :=
    h3SelectedForcingFourierLinfEnvelope A

  let M : ℝ :=
    h3SelectedMomentSlabForcingEnvelope
      (pNat : ℝ) BState B0

  let Bm : ℝ := L * M

  have hL0 : 0 ≤ L := by
    dsimp only [L]
    exact
      h3SelectedForcingFourierLinfEnvelope_nonneg
        hA.le

  have hM0 : 0 ≤ M := by
    dsimp only [M]
    exact
      h3SelectedMomentSlabForcingEnvelope_nonneg
        hBS0 hB00

  refine ⟨Bm, mul_nonneg hL0 hM0, ?_⟩

  intro s hs i
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  have hsPos : 0 < s := by
    linarith [hs.1, hHalf]

  have hsR :
      s ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hs.2 hqR

  have hN2 :
      MemLp N 2 (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3RawFinLerayOuterProductDivergence_memLp2
        (W s) (W s) i

  have hWeighted :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ m : ℝ) : ℂ) * N ξ)
        2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_radialWeight_memLp2
        m hν U₀ hA hU₀ hsPos hsR i

  have hLinf :
      ∀ ξ : H3FourierPoint3, ‖N ξ‖ ≤ L := by
    intro ξ
    dsimp only [N, L, W]
    exact
      norm_h3RawFinLerayOuterProductDivergence_selectedRestart_le_uniformLinf
        hν U₀ hA hU₀ i ξ

  have hpReal : 1 ≤ (pNat : ℝ) := by
    exact_mod_cast (show 1 ≤ pNat by omega)

  have hSlabPacked :
      H3SelectedMomentSlab
        (pNat : ℝ) ν A (q / 2) q
        BState BDuhamel B0
        hν U₀ hA hU₀ := by
    unfold H3SelectedMomentSlab
    exact ⟨hBS0, hBD0, hB00, hData⟩

  have hMomentGeneric :=
    h3RawFinLerayOuterProductDivergence_selectedMomentSlab_subOneMoment_integrable
      (p := (pNat : ℝ))
      hpReal
      hν U₀ hA hU₀
      hSlabPacked
      s hs i

  have hMassGeneric :=
    h3RawFinLerayOuterProductDivergence_selectedMomentSlab_subOneMass_le
      (p := (pNat : ℝ))
      hpReal
      hν U₀ hA hU₀
      hSlabPacked
      s hs i

  have hpSub :
      (pNat : ℝ) - 1 = (2 * m : ℕ) := by
    dsimp only [pNat]
    norm_num

  have hWeight :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight ((2 * m : ℕ) : ℝ) ξ
          =
        ‖ξ‖ ^ (2 * m) := by
    intro ξ
    exact
      h3FourierMomentWeight_natCast (2 * m) ξ

  have hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ (2 * m) * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    rw [hpSub] at hMomentGeneric
    simpa only [hWeight] using hMomentGeneric

  have hMass :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ (2 * m) * ‖N ξ‖)
        ≤ M := by
    dsimp only [N, W, M]
    rw [hpSub] at hMassGeneric
    simpa only [
      hWeight,
      h3RawFinLerayOuterProductDivergenceMomentMass
    ] using hMassGeneric

  constructor
  · exact hWeighted
  · dsimp only [Bm]
    exact
      integral_sq_radialWeight_le_linf_mul_momentMass_generic
        m N hN2 L M hL0 hLinf hMoment hMass

/-- The sixth radial Fourier `L²` forcing bound needed for fifth-order
weighted-source continuity. -/
theorem exists_selectedRestart_forcing_sixth_radialL2_uniform
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A) :
    ∃ B6 : ℝ,
      0 ≤ B6 ∧
      ∀ s ∈ Set.Icc (q / 2) q, ∀ i : Fin 3,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ 6 : ℝ) : ℂ) *
              h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ)
          2
          (volume : Measure H3FourierPoint3)
        ∧
        (∫ ξ : H3FourierPoint3,
            ‖((‖ξ‖ ^ 6 : ℝ) : ℂ) *
              h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖ ^ 2)
          ≤ B6 := by
  simpa using
    exists_selectedRestart_forcing_radialL2_uniform_nat
      6 (by norm_num)
      hν U₀ hA hU₀ hq hqR

end

end Euclidean
end Bridge
end PrimeTensor
