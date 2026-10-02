import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Restriction
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Spectral.State.Old.Bridge

/-!
# Identify the selected weighted state with the old physical weighted state

The selected restart argument now gives a genuine strong Fourier `L²`
derivative of

    q² û_selected.

To transport that derivative back to the terminal physical top-dissipation
path, the only missing state-level fact is equality on the selected/old
overlap.

At a positive overlap time, radius-wide physical agreement already upgrades
to exact equality of the selected weighted H³ spectral state and the canonical
old spectral state.  Deweighting that equality gives equality of the raw
Fourier `L²` velocity coordinates.  Multiplying their almost-everywhere
representatives by the same intrinsic `q²` weight then identifies the two
weighted Hilbert states exactly.

No derivative is transported in this file; it closes only the state
identification seam.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedOldBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/--
On a strict selected/old overlap, the selected intrinsic `q² û_j` state is
exactly the terminal physical fourth-radial `L²` coordinate at the same
physical time.
-/
theorem h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_eq_terminalPhysicalFourthRadialL2At
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
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
        hNS ht₀ hE hTail hQ hQR j
        ⟨r - t₀, hrSlab⟩
      =
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
      hH3 hClass hrClass j := by

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

  have hState :
      Usel = Uold := by
    dsimp only [Usel, Uold]
    simpa only [
      h3PreterminalSelectedUnitSpectralStateOnRadius,
      h3PreterminalElapsedToSelectedUnitRadius_coe,
      qClosed
    ] using hStateRaw

  have hrAbs :
      r ∈ Set.Ioo (0 : ℝ) T := by
    exact
      ⟨
        lt_trans
          hClass.terminal_start.1
          hrClass.1,
        hrClass.2
      ⟩

  let hInt :
      VelocityH3IntegrableAt u r :=
    hH3.velocity_h3_integrable r hrAbs

  let hMeas :
      VelocityH3MeasurableAt u r :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes hrAbs

  have hRawOld :
      h3SpectralScalarRawFourierL2 (Uold j)
        =
      velocityH3BaseFourierAt
        u r hInt hMeas j := by

    have hRound :=
      h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
        (h3PreterminalTailFourierCompatibleOnElapsed
          hNS ht₀ hEnd hTail qClosed)
        j

    dsimp only [Uold]

    unfold
      h3PreterminalTailCanonicalSpectralStateOnElapsed
      velocityH3SpectralStateAt

    dsimp only [qClosed, q, hInt, hMeas] at *

    simpa using hRound

  have hRaw :
      h3SpectralScalarRawFourierL2 (Usel j)
        =
      velocityH3BaseFourierAt
        u r hInt hMeas j := by
    rw [hState]
    exact hRawOld

  have hRawAE :=
    h3SpectralScalarRawFourierL2_ae
      (Usel j)

  rw [hRaw] at hRawAE

  have hSelectedAE :=
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_ae
      hNS ht₀ hE hTail hQ hQR j
      ⟨r - t₀, hrSlab⟩

  have hOldAE :=
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2At_ae
      hH3 hClass hrClass j

  apply MeasureTheory.Lp.ext

  filter_upwards [
    hSelectedAE,
    hOldAE,
    hRawAE
  ] with ξ hSelectedξ hOldξ hRawξ

  rw [hSelectedξ, hOldξ]

  unfold
    h3TerminalPhysicalTopDissipationFourthRadialComponent

  dsimp only [Usel, q, hInt, hMeas] at hRawξ ⊢

  rw [← hRawξ]

end

end Euclidean
end Bridge
end PrimeTensor
