import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Derivative.Pairing

/-!
# Strict-time weighted PDE factors for the physical fourth-radial pairing

The preceding checkpoint identified the exact combined Hilbert-pairing
integrand

    -2 q^5 |û_j|^2
      -
    2 q^4 Re ⟪û_j, F_j(U,U)⟫.

To split that integral safely, we first record the two strict-time Fourier
`L²` factors which positive-time restart smoothing already supplies:

    q^3 û_j ∈ L²,
    q^2 F_j(U,U) ∈ L².

The proof uses the same local selected restart germ and the same selected/old
spectral-state identification as the physical derivative representative.
The selected sixth-radial velocity package and fourth-radial forcing package
are then rescaled by the exact `(2π)` constants and transported to the
canonical terminal spectral state.

No integral is split in this file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedOldDerivativeFactors
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 3000000

/--
At every strict physical time and for every velocity coordinate, the canonical
terminal state admits genuine Fourier `L²` representatives of

    `q³ û_j`
and
    `q² F_j(U,U)`.

These are exactly the two factors needed to justify the separate diffusion and
nonlinear-transfer integrals in the terminal fourth-radial Hilbert pairing.
-/
theorem exists_h3TerminalPhysicalTopDissipationStrictTimeWeightedPDEFactors
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ∃ V3 F2 : H3FourierComplexL2,
      (
        ((V3 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
            *
          h3SpectralScalarRawFourierL2
            (U j) ξ)
      )
        ∧
      (
        ((F2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
            *
          h3RawFinLerayOuterProductDivergence
            U U j ξ)
      ) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let Uterm : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  rcases
    hH3.exists_localCanonicalRestartWindowAt htAbs
  with
    ⟨
      t₀,
      S,
      E,
      ht₀,
      hST,
      hE,
      hTail,
      hGap0,
      hGapR,
      hTarget,
      htS
    ⟩

  have hS :
      0 < S :=
    lt_trans ht₀.1 ht₀.2

  have hNSShort :
      LoggedPreterminalNavierStokesAdmissible u S :=
    loggedPreterminalNavierStokesAdmissible_mono_terminal
      hH3.navier_stokes
      hS
      (le_of_lt hST)

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  have hR :
      0 < R := by
    dsimp only [R]
    exact
      h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
        (one_pos : (0 : ℝ) < 1)
        hE

  let δ : ℝ :=
    min
      (R / 2)
      ((t - t₀) / 2)

  have hGapHalf :
      0 < (t - t₀) / 2 := by
    linarith [hGap0]

  have hRHalf :
      0 < R / 2 := by
    linarith

  have hδ0 :
      0 < δ := by
    dsimp only [δ]
    exact
      lt_min
        hRHalf
        hGapHalf

  have hδRHalf :
      δ ≤ R / 2 := by
    dsimp only [δ]
    exact min_le_left _ _

  have hδGapHalf :
      δ ≤ (t - t₀) / 2 := by
    dsimp only [δ]
    exact min_le_right _ _

  let t₁ : ℝ :=
    t - δ

  have ht₀t₁ :
      t₀ ≤ t₁ := by
    dsimp only [t₁]
    linarith [hδGapHalf]

  have ht₁t :
      t₁ < t := by
    dsimp only [t₁]
    linarith [hδ0]

  have ht₁S :
      t₁ < S :=
    lt_trans ht₁t htS

  have ht₁0 :
      0 < t₁ :=
    lt_of_lt_of_le
      ht₀.1
      ht₀t₁

  have ht₁ :
      t₁ ∈ Set.Ioo (0 : ℝ) S :=
    ⟨ht₁0, ht₁S⟩

  have hTail₁ :
      CanonicalH3TailDataFrom u t₁ S E :=
    canonicalH3TailDataFrom_mono_start
      ht₀t₁
      ht₁S
      hTail

  let q : ℝ :=
    t - t₁

  have hqδ :
      q = δ := by
    dsimp only [q, t₁]
    ring

  have hq0 :
      0 < q := by
    rw [hqδ]
    exact hδ0

  have hqRHalf :
      q ≤ R / 2 := by
    rw [hqδ]
    exact hδRHalf

  have hqR :
      q ≤ R := by
    exact
      hqRHalf.trans
        (by linarith [hR])

  have htq :
      t₁ + q = t := by
    dsimp only [q]
    ring

  have hEnd :
      t₁ + q < S := by
    rw [htq]
    exact htS

  let Q : ℝ :=
    3 * q / 2

  have hQ :
      0 < Q := by
    dsimp only [Q]
    linarith [hq0]

  have hqLower :
      Q / 2 < q := by
    dsimp only [Q]
    linarith [hq0]

  have hqUpper :
      q < Q := by
    dsimp only [Q]
    linarith [hq0]

  have hQR :
      Q < R := by
    have hThreeQuarter :
        3 * R / 4 < R := by
      linarith [hR]

    have hQLe :
        Q ≤ 3 * R / 4 := by
      dsimp only [Q]
      linarith [hqRHalf]

    exact
      lt_of_le_of_lt
        hQLe
        hThreeQuarter

  have hWeakFTC :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
        E u S t₁ hNSShort ht₁ hE hTail₁ :=
    H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_tailH3_curl
      E hE u S t₁ hNSShort ht₁ hTail₁

  have hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u S t₁ hNSShort ht₁ hE hTail₁ :=
    h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_projectedRHSWeakFTC
      hNSShort
      ht₁
      hE
      hTail₁
      hWeakFTC

  let qClosed :
      Set.Icc (0 : ℝ) q :=
    ⟨q, hq0.le, le_rfl⟩

  have hStateOld :=
    h3PreterminalSelectedUnitSpectralStateOnRadius_eq_tailCanonical_of_restartRadiusAgreement
      hNSShort
      ht₁
      hEnd
      hE
      hTail₁
      hqR
      hPhysical
      qClosed
      hq0

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNSShort ht₁ hTail₁

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNSShort ht₁ hE hTail₁

  let Usel : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀
      hA
      hU₀
      q

  let Uold : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNSShort ht₁ hEnd hTail₁ qClosed

  have hSelOld :
      Usel = Uold := by
    dsimp only [Usel, Uold, U₀, hA, hU₀]
    simpa only [
      h3PreterminalSelectedUnitSpectralStateOnRadius,
      h3PreterminalElapsedToSelectedUnitRadius_coe,
      qClosed
    ] using hStateOld

  have hOldTerm :
      Uold = Uterm := by

    dsimp only [Uold, Uterm]

    unfold
      h3PreterminalTailCanonicalSpectralStateOnElapsed
      h3TerminalVelocitySpectralStateAt

    apply
      velocityH3SpectralStateAt_eq_of_time_eq
        u
        htq

  have hSelTerm :
      Usel = Uterm :=
    hSelOld.trans hOldTerm

  let qSlab :
      Set.Icc (Q / 2) Q :=
    ⟨q, hqLower.le, hqUpper.le⟩

  have hhalf :
      0 < Q / 2 := by
    positivity

  let V6 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hhalf hQR
      qSlab
      j

  let F4 : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      4
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hQ hQR.le
      j qSlab

  let c6 : ℝ :=
    (2 * Real.pi) ^ 6

  let c4 : ℝ :=
    (2 * Real.pi) ^ 4

  let V3 : H3FourierComplexL2 :=
    c6 • V6

  let F2 : H3FourierComplexL2 :=
    c4 • F4

  have hV6 :=
    h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact_ae
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hhalf hQR
      qSlab
      j

  have hF4 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      4
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hQ hQR.le
      j qSlab

  have hV3Smul :=
    MeasureTheory.Lp.coeFn_smul
      c6
      V6

  have hF2Smul :=
    MeasureTheory.Lp.coeFn_smul
      c4
      F4

  have hRaw :
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
          (one_pos : (0 : ℝ) < 1)
          U₀
          hA
          hU₀
          q
          j
        =
      h3SpectralScalarRawFourierL2
        (Uterm j) := by

    unfold
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2

    rw [← hSelTerm]

    rfl

  have hV3 :
      ((V3 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
          *
        h3SpectralScalarRawFourierL2
          (Uterm j) ξ) := by

    filter_upwards [
      hV6,
      hV3Smul
    ] with ξ hV6ξ hSmulξ

    dsimp only [V3]

    rw [hSmulξ]
    simp only [Pi.smul_apply]
    rw [hV6ξ, hRaw]

    have hQ3 :=
      h3FourierGradientSquare_cube_eq_two_pi_six_mul_norm_six
        ξ

    dsimp only [c6]

    rw [hQ3]

    simp only [
      Complex.real_smul,
      Complex.ofReal_mul,
      Complex.ofReal_pow,
      Complex.ofReal_ofNat
    ]

    ring

  have hF2 :
      ((F2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        h3RawFinLerayOuterProductDivergence
          Uterm Uterm j ξ) := by

    filter_upwards [
      hF4,
      hF2Smul
    ] with ξ hF4ξ hSmulξ

    dsimp only [F2]

    rw [hSmulξ]
    simp only [Pi.smul_apply]
    rw [hF4ξ]

    change
      ((c4 : ℝ) : ℂ)
            *
          (
            ((‖ξ‖ ^ 4 : ℝ) : ℂ)
              *
            h3RawFinLerayOuterProductDivergence
              Usel Usel j ξ
          )
        =
      ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
            *
          h3RawFinLerayOuterProductDivergence
            Uterm Uterm j ξ

    rw [hSelTerm]

    have hQ2 :=
      h3FourierGradientSquare_sq_eq_two_pi_four_mul_norm_four
        ξ

    dsimp only [c4]

    rw [hQ2]

    simp only [
      Complex.ofReal_mul,
      Complex.ofReal_pow,
      Complex.ofReal_ofNat
    ]

    ring

  refine
    ⟨
      V3,
      F2,
      ?_,
      ?_
    ⟩

  · simpa only [Uterm] using hV3
  · simpa only [Uterm] using hF2

end

end Euclidean
end Bridge
end PrimeTensor
