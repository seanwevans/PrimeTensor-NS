import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude.Sixth

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2200000

noncomputable local instance axisFintypeH3TerminalSixthFactors
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Canonical terminal q³ forcing factor -/

theorem h3TerminalPhysicalTopDissipationForcingThirdQ_memLp2
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
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence U U j ξ)
      2
      (volume : Measure H3FourierPoint3) := by

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

  have hState :=
    h3PreterminalSelectedSpectralStateOnOverlap_eq_terminalVelocitySpectralStateAt
      hH3 hClass hNSShort ht₀ hE hTail hPhysical
      hQ hQR ht htS
      (by
        exact
          ⟨
            by simpa only [q] using hqLower.le,
            by simpa only [q] using hqUpper.le
          ⟩)

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

  have hState' : Usel = Uterm := by
    dsimp only [Usel, Uterm, U₀, hA, hU₀]
    simpa only [q] using hState

  let F6 : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      6
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hQ hQR.le j qSlab

  let F3 : H3FourierComplexL2 :=
    ((2 * Real.pi) ^ 6 : ℝ) • F6

  have hF3Mem :
      MemLp
        ((F3 : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        2
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.Lp.memLp F3

  have hSelectedAE :=
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      6
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hQ hQR.le j qSlab

  have hSmulAE :=
    MeasureTheory.Lp.coeFn_smul
      (((2 * Real.pi) ^ 6 : ℝ))
      F6

  have hAE :
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence Uterm Uterm j ξ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((F3 : H3FourierComplexL2) : H3FourierPoint3 → ℂ) := by

    filter_upwards [hSelectedAE, hSmulAE]
      with ξ hSelectedξ hSmulξ

    rw [hSmulξ]
    simp only [Pi.smul_apply, Complex.real_smul]
    rw [hSelectedξ]

    change
      ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence
            Uterm Uterm j ξ
        =
      (((2 * Real.pi) ^ 6 : ℝ) : ℂ) *
        (
          ((‖ξ‖ ^ 6 : ℝ) : ℂ) *
            h3RawFinLerayOuterProductDivergence
              Usel Usel j ξ
        )

    rw [hState']

    unfold h3FourierGradientSquare
    push_cast
    ring

  exact
    (memLp_congr_ae hAE).2
      hF3Mem

noncomputable def h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    H3FourierComplexL2 :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  (
    h3TerminalPhysicalTopDissipationForcingThirdQ_memLp2
      hH3 hClass ht j
  ).toLp
    (fun ξ : H3FourierPoint3 =>
      ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence U U j ξ)

theorem h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At_ae
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
      h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
        hH3 hClass ht j :
      H3FourierComplexL2
    ) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence U U j ξ) := by

  dsimp only

  unfold
    h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At

  exact
    MemLp.coeFn_toLp
      (
        h3TerminalPhysicalTopDissipationForcingThirdQ_memLp2
          hH3 hClass ht j
      )

/-! ## Canonical terminal q⁴ velocity factor -/

noncomputable def h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    H3FourierComplexL2 :=
  -
    h3TerminalResolvedSixthDiffusionPDERHS
      hH3 hClass j t
  -
    h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
      hH3 hClass ht j

theorem h3TerminalResolvedSixthDiffusionPDERHS_eq_neg_velocityFourthQ_sub_forcingThirdQ
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalResolvedSixthDiffusionPDERHS
        hH3 hClass j t
      =
    -
      h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At
        hH3 hClass ht j
      -
      h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
        hH3 hClass ht j := by

  unfold
    h3TerminalPhysicalTopDissipationVelocityFourthQFourierL2At

  abel

/--
Every local selected sixth-order forcing factor agrees with the canonical
terminal `q³ F_j` state.
-/
theorem h3SelectedForcingSixthQFourierL2OnSlab_eq_terminalForcingThirdQ
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S a t₀ Q r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNS : LoggedPreterminalNavierStokesAdmissible u S)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) S)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ S E)
    (hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u S t₀ hNS ht₀ hE hTail)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hrClass : r ∈ Set.Ioo a T)
    (hrS : r < S)
    (hrSlab : r - t₀ ∈ Set.Icc (Q / 2) Q)
    (j : Fin 3) :
    ((2 * Real.pi) ^ 6 : ℝ) •
        h3SelectedRestartForcingRadialFourierL2OnSlab
          6
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          hQ hQR.le j
          ⟨r - t₀, hrSlab⟩
      =
    h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
      hH3 hClass hrClass j := by

  let q : ℝ := r - t₀
  let qSlab : Set.Icc (Q / 2) Q :=
    ⟨q, by simpa only [q] using hrSlab⟩

  have hrAbs :
      r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hrClass.1, hrClass.2⟩

  let Usel : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le hNS ht₀ hE hTail)
      q

  let Uterm : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 r hrAbs

  have hState : Usel = Uterm := by
    dsimp only [Usel, Uterm]
    simpa only [q] using
      h3PreterminalSelectedSpectralStateOnOverlap_eq_terminalVelocitySpectralStateAt
        hH3 hClass hNS ht₀ hE hTail hPhysical
        hQ hQR hrClass hrS hrSlab

  let Fsel : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      6
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le hNS ht₀ hE hTail)
      hQ hQR.le j qSlab

  have hSelectedAE :=
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      6
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le hNS ht₀ hE hTail)
      hQ hQR.le j qSlab

  have hSmulAE :=
    MeasureTheory.Lp.coeFn_smul
      (((2 * Real.pi) ^ 6 : ℝ))
      Fsel

  have hTerminalAE :=
    h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At_ae
      hH3 hClass hrClass j

  change
    (((2 * Real.pi) ^ 6 : ℝ) • Fsel)
      =
    h3TerminalPhysicalTopDissipationForcingThirdQFourierL2At
      hH3 hClass hrClass j

  apply MeasureTheory.Lp.ext

  filter_upwards [hSmulAE, hSelectedAE, hTerminalAE]
    with ξ hSmulξ hSelectedξ hTerminalξ

  rw [hSmulξ]
  simp only [Pi.smul_apply, Complex.real_smul]
  rw [hSelectedξ, hTerminalξ]

  change
    (((2 * Real.pi) ^ 6 : ℝ) : ℂ) *
        (
          ((‖ξ‖ ^ 6 : ℝ) : ℂ) *
            h3RawFinLerayOuterProductDivergence
              Usel Usel j ξ
        )
      =
    ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ) *
      h3RawFinLerayOuterProductDivergence
        Uterm Uterm j ξ

  rw [hState]
  unfold h3FourierGradientSquare
  push_cast
  ring

end

end Euclidean
end Bridge
end PrimeTensor
