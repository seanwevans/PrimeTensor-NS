import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Derivative.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.RHS.Continuity

/-!
# Separate physical weighted PDE terms in Fourier L²

At every strict physical time, positive-time smoothing gives two actual
Fourier `L²` states for each coordinate:

    A_j = q³ û_j,
    B_j = q² F_j(U,U).

The derivative representative proved in the preceding checkpoint is their
negative sum.  Here we package the two terms separately.

This is the exact integrability input needed to split the restricted pairing
integral into the physical diffusion and nonlinear-transfer integrals.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailSeparatedPDETerms
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2500000

/--
At every strict physical time and for each velocity coordinate there exist
global Fourier `L²` states representing the separated weighted diffusion and
forcing terms `q³ û_j` and `q² F_j(U,U)`.
-/
theorem exists_h3TerminalPhysicalTopTailSeparatedWeightedPDETerms
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
    ∃ A B : H3FourierComplexL2,
      (
        ((A : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ)
          =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
            *
          (
            h3SpectralScalarRawFourierL2
              (U j)
          ) ξ)
      )
        ∧
      (
        ((B : H3FourierComplexL2) :
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
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

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

  have hS : 0 < S :=
    lt_trans ht₀.1 ht₀.2

  have hNSShort :
      LoggedPreterminalNavierStokesAdmissible u S :=
    loggedPreterminalNavierStokesAdmissible_mono_terminal
      hH3.navier_stokes hS (le_of_lt hST)

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  have hR : 0 < R := by
    dsimp only [R]
    exact
      h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
        (one_pos : (0 : ℝ) < 1) hE

  let δ : ℝ :=
    min (R / 2) ((t - t₀) / 2)

  have hGapHalf : 0 < (t - t₀) / 2 := by
    linarith [hGap0]

  have hRHalf : 0 < R / 2 := by
    linarith

  have hδ0 : 0 < δ := by
    dsimp only [δ]
    exact lt_min hRHalf hGapHalf

  have hδRHalf : δ ≤ R / 2 := by
    dsimp only [δ]
    exact min_le_left _ _

  have hδGapHalf : δ ≤ (t - t₀) / 2 := by
    dsimp only [δ]
    exact min_le_right _ _

  let t₁ : ℝ :=
    t - δ

  have ht₀t₁ : t₀ ≤ t₁ := by
    dsimp only [t₁]
    linarith [hδGapHalf]

  have ht₁t : t₁ < t := by
    dsimp only [t₁]
    linarith [hδ0]

  have ht₁S : t₁ < S :=
    lt_trans ht₁t htS

  have ht₁0 : 0 < t₁ :=
    lt_of_lt_of_le ht₀.1 ht₀t₁

  have ht₁ : t₁ ∈ Set.Ioo (0 : ℝ) S :=
    ⟨ht₁0, ht₁S⟩

  have hTail₁ :
      CanonicalH3TailDataFrom u t₁ S E :=
    canonicalH3TailDataFrom_mono_start
      ht₀t₁ ht₁S hTail

  let τ : ℝ :=
    t - t₁

  have hτδ : τ = δ := by
    dsimp only [τ, t₁]
    ring

  have hτ0 : 0 < τ := by
    rw [hτδ]
    exact hδ0

  have hτRHalf : τ ≤ R / 2 := by
    rw [hτδ]
    exact hδRHalf

  have hτR : τ ≤ R :=
    hτRHalf.trans (by linarith [hR])

  have htτ : t₁ + τ = t := by
    dsimp only [τ]
    ring

  have hEnd : t₁ + τ < S := by
    rw [htτ]
    exact htS

  let Q : ℝ :=
    3 * τ / 2

  have hQ : 0 < Q := by
    dsimp only [Q]
    linarith [hτ0]

  have hτLower : Q / 2 < τ := by
    dsimp only [Q]
    linarith [hτ0]

  have hτUpper : τ < Q := by
    dsimp only [Q]
    linarith [hτ0]

  have hQR : Q < R := by
    have hThreeQuarter : 3 * R / 4 < R := by
      linarith [hR]
    have hQLe : Q ≤ 3 * R / 4 := by
      dsimp only [Q]
      linarith [hτRHalf]
    exact hQLe.trans_lt hThreeQuarter

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
      hNSShort ht₁ hE hTail₁ hWeakFTC

  let τClosed : Set.Icc (0 : ℝ) τ :=
    ⟨τ, hτ0.le, le_rfl⟩

  have hStateOld :=
    h3PreterminalSelectedUnitSpectralStateOnRadius_eq_tailCanonical_of_restartRadiusAgreement
      hNSShort ht₁ hEnd hE hTail₁ hτR hPhysical τClosed hτ0

  let Usel : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState hNSShort ht₁ hTail₁)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNSShort ht₁ hE hTail₁)
      τ

  let Uold : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNSShort ht₁ hEnd hTail₁ τClosed

  have hSelOld : Usel = Uold := by
    dsimp only [Usel, Uold]
    simpa only [
      h3PreterminalSelectedUnitSpectralStateOnRadius,
      h3PreterminalElapsedToSelectedUnitRadius_coe,
      τClosed
    ] using hStateOld

  have hOldTerm : Uold = Uterm := by
    dsimp only [Uold, Uterm]
    unfold
      h3PreterminalTailCanonicalSpectralStateOnElapsed
      h3TerminalVelocitySpectralStateAt
    apply velocityH3SpectralStateAt_eq_of_time_eq u htτ

  have hSelTerm : Usel = Uterm :=
    hSelOld.trans hOldTerm

  let τSlab : Set.Icc (Q / 2) Q :=
    ⟨τ, hτLower.le, hτUpper.le⟩

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNSShort ht₁ hTail₁

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNSShort ht₁ hE hTail₁

  let V6 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      (by positivity : 0 < Q / 2)
      hQR
      τSlab
      j

  let F4 : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      4
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      Q hQR.le
      j
      τSlab

  let A : H3FourierComplexL2 :=
    ((2 * Real.pi) ^ 6 : ℝ) • V6

  let B : H3FourierComplexL2 :=
    ((2 * Real.pi) ^ 4 : ℝ) • F4

  refine ⟨A, B, ?_, ?_⟩

  · have hV6 :=
      h3PreterminalSelectedVelocitySixthRadialFourierL2OnCompact_ae
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        (by positivity : 0 < Q / 2)
        hQR
        τSlab
        j

    have hSmul :=
      MeasureTheory.Lp.coeFn_smul
        ((2 * Real.pi) ^ 6 : ℝ)
        V6

    have hRaw :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_rawFourier
        (t := (τ : ℝ))
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ j

    have hDeweighted :=
      h3SpectralScalarRawFourierL2_ae
        (Usel j)

    filter_upwards [hV6, hSmul, hRaw, hDeweighted]
      with ξ hV6ξ hSmulξ hRawξ hDeweightedξ

    rw [hSmulξ, hV6ξ, hRawξ, ← hDeweightedξ]

    rw [h3FourierGradientSquare_cube_eq_two_pi_six_mul_norm_six]

    dsimp only [A, V6, Usel, U₀, hA, hU₀, τSlab] at *

    rw [hSelTerm]

    simp only [
      Complex.real_smul,
      Complex.ofReal_mul,
      Complex.ofReal_pow,
      Complex.ofReal_ofNat
    ]

    ring

  · have hF4 :=
      h3SelectedRestartForcingRadialFourierL2OnSlab_ae
        4
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        Q hQR.le
        j
        τSlab

    have hSmul :=
      MeasureTheory.Lp.coeFn_smul
        ((2 * Real.pi) ^ 4 : ℝ)
        F4

    filter_upwards [hF4, hSmul]
      with ξ hF4ξ hSmulξ

    rw [hSmulξ, hF4ξ]

    rw [h3FourierGradientSquare_sq_eq_two_pi_four_mul_norm_four]

    dsimp only [B, F4, U₀, hA, hU₀, τSlab] at *

    change
      ((2 * Real.pi) ^ 4 : ℝ) •
          (((‖ξ‖ ^ 4 : ℝ) : ℂ) *
            h3RawFinLerayOuterProductDivergence
              Usel Usel j ξ)
        =
      (((2 * Real.pi) ^ 4 * ‖ξ‖ ^ 4 : ℝ) : ℂ)
          *
        h3RawFinLerayOuterProductDivergence
          Uterm Uterm j ξ

    rw [hSelTerm]

    simp only [
      Complex.real_smul,
      Complex.ofReal_mul,
      Complex.ofReal_pow,
      Complex.ofReal_ofNat
    ]

    ring

end

end Euclidean
end Bridge
end PrimeTensor
