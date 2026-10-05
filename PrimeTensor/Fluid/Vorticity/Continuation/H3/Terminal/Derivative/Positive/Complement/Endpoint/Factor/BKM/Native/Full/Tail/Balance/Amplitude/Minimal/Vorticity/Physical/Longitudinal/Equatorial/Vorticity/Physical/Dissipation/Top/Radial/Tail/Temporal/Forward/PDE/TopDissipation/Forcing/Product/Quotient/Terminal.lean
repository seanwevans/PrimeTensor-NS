import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights

/-!
# Identify selected intrinsic forcing weights with terminal forcing states

The selected `q F_j` and `q² F_j` paths now have genuine strong derivatives.
To use those derivatives in the terminal Hilbert obstruction, we identify their
values with the canonical terminal forcing states on every local
selected/physical overlap.

The only input is the already-proved selected/old physical agreement.  It first
identifies the selected spectral velocity state with the terminal spectral
velocity state at the same physical time.  The forcing identities then follow
from the literal raw Fourier representatives and

    q(ξ) = (2π)² |ξ|².
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedTerminalForcingWeights
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2400000

/-! ## Common spectral-state overlap -/

/--
On a selected/physical overlap, the selected spectral state at elapsed time
`r - t₀` is exactly the canonical terminal spectral state at physical time `r`.
-/
theorem h3PreterminalSelectedSpectralStateOnOverlap_eq_terminalVelocitySpectralStateAt
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
    (hrSlab : r - t₀ ∈ Set.Icc (Q / 2) Q) :
    let hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
      ⟨
        lt_trans hClass.terminal_start.1 hrClass.1,
        hrClass.2
      ⟩
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht₀ hE hTail)
        (r - t₀)
      =
    h3TerminalVelocitySpectralStateAt
      hH3 r hrAbs := by

  dsimp only

  let q : ℝ :=
    r - t₀

  have hq0 :
      0 < q := by
    dsimp only [q]
    have hHalfPos : 0 < Q / 2 := by
      positivity
    exact
      lt_of_lt_of_le
        hHalfPos
        hrSlab.1

  have hqR :
      q ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    dsimp only [q]
    exact
      hrSlab.2.trans
        hQR.le

  have hEnd :
      t₀ + q < S := by
    dsimp only [q]
    linarith

  let qClosed :
      Set.Icc (0 : ℝ) q :=
    ⟨q, hq0.le, le_rfl⟩

  let qIoc :
      Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨q, hq0, hqR⟩

  have hAgreement :
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1)
        q
        hNS ht₀ hE hTail := by
    have hAt :=
      hPhysical qIoc hEnd
    simpa only [qIoc] using hAt

  have hStateRaw :=
    h3PreterminalSelectedUnitSpectralStateOnRadius_eq_tailCanonical_of_physicalAgreement
      hNS ht₀ hEnd hE hTail hqR
      qClosed hq0 hAgreement

  let Usel : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
      q

  let Uold : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht₀ hEnd hTail qClosed

  have hSelOld :
      Usel = Uold := by
    dsimp only [Usel, Uold]
    simpa only [
      h3PreterminalSelectedUnitSpectralStateOnRadius,
      h3PreterminalElapsedToSelectedUnitRadius_coe,
      qClosed
    ] using hStateRaw

  have hrAbs :
      r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 hrClass.1,
      hrClass.2
    ⟩

  let Uterm : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 r hrAbs

  have hOldTerm :
      Uold = Uterm := by

    dsimp only [Uold, Uterm]

    unfold
      h3PreterminalTailCanonicalSpectralStateOnElapsed
      h3TerminalVelocitySpectralStateAt

    apply
      velocityH3SpectralStateAt_eq_of_time_eq
        u

    dsimp only [q]
    ring

  have hSelTerm :
      Usel = Uterm :=
    hSelOld.trans hOldTerm

  dsimp only [Usel, Uterm, q] at hSelTerm ⊢
  exact hSelTerm

/-! ## q F overlap -/

/--
On every strict selected/terminal overlap, the selected intrinsic `q F_j`
state equals the canonical terminal `q F_j` state.
-/
theorem h3PreterminalSelectedForcingSecondQFourierL2OnSlabExtension_eq_terminalPhysicalForcingSecondQFourierL2At
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
    h3PreterminalSelectedForcingSecondQFourierL2OnSlabExtension
        hNS ht₀ hE hTail hQ hQR j
        (r - t₀)
      =
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
      hH3 hClass hrClass j := by

  let q : ℝ :=
    r - t₀

  let qSlab :
      Set.Icc (Q / 2) Q :=
    ⟨q, by simpa only [q] using hrSlab⟩

  have hrAbs :
      r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 hrClass.1,
      hrClass.2
    ⟩

  let Usel : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
      q

  let Uterm : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 r hrAbs

  have hState :
      Usel = Uterm := by
    dsimp only [Usel, Uterm]
    simpa only [q] using
      h3PreterminalSelectedSpectralStateOnOverlap_eq_terminalVelocitySpectralStateAt
        hH3 hClass hNS ht₀ hE hTail hPhysical
        hQ hQR hrClass hrS hrSlab

  let Fsel : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      2
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
      hQ hQR.le j qSlab

  have hSelectedAE :=
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      2
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
      hQ hQR.le j qSlab

  have hSmulAE :=
    MeasureTheory.Lp.coeFn_smul
      (((2 * Real.pi) ^ 2 : ℝ))
      Fsel

  have hTerminalAE :=
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At_ae
      hH3 hClass hrClass j

  unfold
    h3PreterminalSelectedForcingSecondQFourierL2OnSlabExtension
    h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension

  rw [
    Set.IccExtend_of_mem
      (by linarith : Q / 2 ≤ Q)
      (fun s : Set.Icc (Q / 2) Q =>
        h3SelectedRestartForcingRadialFourierL2OnSlab
          2
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          hQ hQR.le j s)
      hrSlab
  ]

  change
    (((2 * Real.pi) ^ 2 : ℝ) • Fsel)
      =
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
      hH3 hClass hrClass j

  apply MeasureTheory.Lp.ext

  filter_upwards [
    hSmulAE,
    hSelectedAE,
    hTerminalAE
  ] with ξ hSmulξ hSelectedξ hTerminalξ

  rw [hSmulξ]
  simp only [Pi.smul_apply, Complex.real_smul]
  rw [hSelectedξ, hTerminalξ]

  change
    (((2 * Real.pi) ^ 2 : ℝ) : ℂ) *
        (
          ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
            h3RawFinLerayOuterProductDivergence
              Usel Usel j ξ
        )
      =
    ((h3FourierGradientSquare ξ : ℝ) : ℂ) *
      h3RawFinLerayOuterProductDivergence
        Uterm Uterm j ξ

  rw [hState]
  unfold h3FourierGradientSquare
  push_cast
  ring

/-! ## q² F overlap -/

/--
On every strict selected/terminal overlap, the selected intrinsic `q² F_j`
state equals the canonical terminal `q² F_j` state.
-/
theorem h3PreterminalSelectedForcingFourthQFourierL2OnSlabExtension_eq_terminalPhysicalForcingFourthQFourierL2At
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
    h3PreterminalSelectedForcingFourthQFourierL2OnSlabExtension
        hNS ht₀ hE hTail hQ hQR j
        (r - t₀)
      =
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
      hH3 hClass hrClass j := by

  let q : ℝ :=
    r - t₀

  let qSlab :
      Set.Icc (Q / 2) Q :=
    ⟨q, by simpa only [q] using hrSlab⟩

  have hrAbs :
      r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 hrClass.1,
      hrClass.2
    ⟩

  let Usel : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
      q

  let Uterm : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 r hrAbs

  have hState :
      Usel = Uterm := by
    dsimp only [Usel, Uterm]
    simpa only [q] using
      h3PreterminalSelectedSpectralStateOnOverlap_eq_terminalVelocitySpectralStateAt
        hH3 hClass hNS ht₀ hE hTail hPhysical
        hQ hQR hrClass hrS hrSlab

  let Fsel : H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      4
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
      hQ hQR.le j qSlab

  have hSelectedAE :=
    h3SelectedRestartForcingRadialFourierL2OnSlab_ae
      4
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
      hQ hQR.le j qSlab

  have hSmulAE :=
    MeasureTheory.Lp.coeFn_smul
      (((2 * Real.pi) ^ 4 : ℝ))
      Fsel

  have hTerminalAE :=
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At_ae
      hH3 hClass hrClass j

  unfold
    h3PreterminalSelectedForcingFourthQFourierL2OnSlabExtension
    h3PreterminalSelectedForcingRadialFourierL2OnSlabExtension

  rw [
    Set.IccExtend_of_mem
      (by linarith : Q / 2 ≤ Q)
      (fun s : Set.Icc (Q / 2) Q =>
        h3SelectedRestartForcingRadialFourierL2OnSlab
          4
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          hQ hQR.le j s)
      hrSlab
  ]

  change
    (((2 * Real.pi) ^ 4 : ℝ) • Fsel)
      =
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
      hH3 hClass hrClass j

  apply MeasureTheory.Lp.ext

  filter_upwards [
    hSmulAE,
    hSelectedAE,
    hTerminalAE
  ] with ξ hSmulξ hSelectedξ hTerminalξ

  rw [hSmulξ]
  simp only [Pi.smul_apply, Complex.real_smul]
  rw [hSelectedξ, hTerminalξ]

  change
    (((2 * Real.pi) ^ 4 : ℝ) : ℂ) *
        (
          ((‖ξ‖ ^ 4 : ℝ) : ℂ) *
            h3RawFinLerayOuterProductDivergence
              Usel Usel j ξ
        )
      =
    ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ) *
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
