import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Factorization.Overlap

/-!
# Raw terminal representatives of the sixth-diffusion factors

The previous checkpoint identified the algebraically canonical terminal
fourth-q velocity with the selected eighth-radial velocity on every admissible
restart overlap.  This file removes the restart chart completely.

At every strict physical time,

    V₄,j(ξ) = q(ξ)^4 û_j(ξ)

almost everywhere, where `q(ξ) = (2π)^2 |ξ|^2`.

Together with the already-canonical forcing representative

    F₃,j(ξ) = q(ξ)^3 F_j(ξ),

this yields exact norm-square integral formulas for both terminal factors.

Thus the sixth-diffusion factor alternative is now phrased in intrinsic raw
Fourier masses, not in restart coordinates.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2200000

noncomputable local instance axisFintypeH3TerminalFourthQRaw
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
The canonical terminal fourth-q velocity has the literal raw Fourier
representative `q(ξ)^4 û_j(ξ)` almost everywhere.
-/
theorem h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At_ae
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
    ((
      h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At
        hH3 hClass ht j :
      H3FourierComplexL2
    ) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((h3FourierGradientSquare ξ ^ 4 : ℝ) : ℂ) *
        h3SpectralScalarRawFourierL2 (U j) ξ) := by

  dsimp only

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  rcases
    hH3.exists_localCanonicalRestartWindowAt htAbs
  with
    ⟨t₀, S, E, ht₀, hST, hE, hTail, hGap0, hGapR, hTarget, htS⟩

  have hS : 0 < S :=
    lt_trans ht₀.1 ht₀.2

  have hNSShort :
      LoggedPreterminalNavierStokesAdmissible u S :=
    loggedPreterminalNavierStokesAdmissible_mono_terminal
      hH3.navier_stokes hS hST.le

  have hWeakFTC :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
        E u S t₀ hNSShort ht₀ hE hTail :=
    H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_tailH3_curl
      E hE u S t₀ hNSShort ht₀ hTail

  have hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u S t₀ hNSShort ht₀ hE hTail :=
    h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_projectedRHSWeakFTC
      hNSShort ht₀ hE hTail hWeakFTC

  let q : ℝ := t - t₀
  let R : ℝ := h3FinHeatLerayRestartRadius (1 : ℝ) E
  let B : ℝ := min (2 * q) R
  let Q : ℝ := (q + B) / 2

  have hq0 : 0 < q := by
    dsimp only [q]
    exact hGap0

  have hqR : q < R := by
    dsimp only [q, R]
    exact hGapR

  have hqB : q < B := by
    dsimp only [B]
    exact lt_min (by linarith [hq0]) hqR

  have hB_le_twoq : B ≤ 2 * q := by
    dsimp only [B]
    exact min_le_left _ _

  have hB_le_R : B ≤ R := by
    dsimp only [B]
    exact min_le_right _ _

  have hQ : 0 < Q := by
    dsimp only [Q]
    linarith [hq0, hqB]

  have hqUpper : q < Q := by
    dsimp only [Q]
    linarith [hqB]

  have hqLower : Q / 2 < q := by
    dsimp only [Q]
    linarith [hB_le_twoq, hq0]

  have hQR : Q < R := by
    dsimp only [Q]
    linarith [hqR, hB_le_R]

  let qSlab : Set.Icc (Q / 2) Q :=
    ⟨q, hqLower.le, hqUpper.le⟩

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNSShort ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNSShort ht₀ hE hTail

  let Usel : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1) U₀ hA hU₀ q

  let Uterm : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  have hState :
      Usel = Uterm := by

    dsimp only [Usel, Uterm, U₀, hA, hU₀]

    simpa only [q] using
      h3PreterminalSelectedSpectralStateOnOverlap_eq_terminalVelocitySpectralStateAt
        hH3 hClass hNSShort ht₀ hE hTail hPhysical
        hQ hQR ht htS
        ⟨
          by simpa only [q] using hqLower.le,
          by simpa only [q] using hqUpper.le
        ⟩

  let hhalf : 0 < Q / 2 := by
    positivity

  let V8 : H3FourierComplexL2 :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
      8 (by norm_num)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hhalf hQR qSlab j

  have hOverlap :
      ((2 * Real.pi) ^ 8 : ℝ) • V8
        =
      h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At
        hH3 hClass ht j := by

    dsimp only [V8, U₀, hA, hU₀, hhalf, qSlab]

    exact
      h3SelectedVelocityEighthRadialFourierL2OnSlab_eq_terminalVelocityFourthQ
        hH3 hClass hNSShort ht₀ hE hTail hPhysical
        hQ hQR ht htS
        ⟨
          by simpa only [q] using hqLower,
          by simpa only [q] using hqUpper
        ⟩
        j

  have hV8AE :=
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact_ae
      8 (by norm_num)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hhalf hQR qSlab j

  have hSmulAE :=
    MeasureTheory.Lp.coeFn_smul
      (((2 * Real.pi) ^ 8 : ℝ))
      V8

  have hRaw :
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀ q j
        =
      h3SpectralScalarRawFourierL2
        (Uterm j) := by

    rw [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_eq_scalarRawFourierL2
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀ j
    ]

    change
      h3SpectralScalarRawFourierL2
          (Usel j)
        =
      h3SpectralScalarRawFourierL2
          (Uterm j)

    rw [hState]

  rw [← hOverlap]

  filter_upwards [hSmulAE, hV8AE]
    with ξ hSmulξ hV8ξ

  rw [hSmulξ]
  simp only [Pi.smul_apply, Complex.real_smul]
  rw [hV8ξ]

  change
    (((2 * Real.pi) ^ 8 : ℝ) : ℂ) *
        (
          ((‖ξ‖ ^ 8 : ℝ) : ℂ) *
            (
              (
                h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
                  (one_pos : (0 : ℝ) < 1)
                  U₀ hA hU₀ q j :
                H3FourierComplexL2
              ) ξ
            )
        )
      =
    ((h3FourierGradientSquare ξ ^ 4 : ℝ) : ℂ) *
      h3SpectralScalarRawFourierL2
        (Uterm j) ξ

  rw [hRaw]

  unfold h3FourierGradientSquare
  push_cast
  ring

/--
Exact terminal fourth-q velocity norm-square as an intrinsic raw Fourier mass.
-/
theorem norm_sq_h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At
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
    ‖h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At
        hH3 hClass ht j‖ ^ 2
      =
    ∫ ξ : H3FourierPoint3,
      ‖((h3FourierGradientSquare ξ ^ 4 : ℝ) : ℂ) *
        h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 := by

  dsimp only

  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]

  apply integral_congr_ae

  filter_upwards [
    h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At_ae
      hH3 hClass ht j
  ] with ξ hξ

  rw [hξ]

/--
Exact terminal third-q forcing norm-square as an intrinsic raw Fourier mass.
-/
theorem norm_sq_h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
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
    ‖h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
        hH3 hClass ht j‖ ^ 2
      =
    ∫ ξ : H3FourierPoint3,
      ‖((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence U U j ξ‖ ^ 2 := by

  dsimp only

  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]

  apply integral_congr_ae

  filter_upwards [
    h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At_ae
      hH3 hClass ht j
  ] with ξ hξ

  rw [hξ]

end

end Euclidean
end Bridge
end PrimeTensor
