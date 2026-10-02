import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.State
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Radial.L2.Continuity

/-!
# Continuity of the physical third-radial forcing state

The cubic forcing obstruction is now exactly a fixed multiple of the sum of
squared norms of the canonical physical third-radial forcing states.

The selected restart library already proves strong Fourier `L²` continuity of
the radial forcing state at every finite order.  Around an arbitrary strict
physical time, choose the same local canonical restart used throughout the
terminal Hilbert argument.  On a positive selected slab:

* selected/old physical agreement identifies the complete spectral states;
* therefore the selected order-three radial forcing state has exactly the same
  raw Fourier representative as the canonical physical state;
* `Lp.ext` upgrades that a.e. representative equality to equality of the
  quotient-safe Hilbert states.

The selected continuous germ then transports to the physical path.

No terminal bound is introduced here.  This is purely a topology/identification
checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailCubicForcingContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 3000000

/-! ## Global physical path -/

/--
The canonical physical third-radial forcing state, extended by zero outside
the strict energy-class interval.
-/
noncomputable def h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    H3FourierComplexL2 :=
  if ht : t ∈ Set.Ioo a T then
    h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
      hH3 hClass ht j
  else
    0

theorem h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
        hH3 hClass j t
      =
    h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
      hH3 hClass ht j := by

  simp [
    h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path,
    ht
  ]

/-! ## Local transport of selected continuity -/

/--
At every strict physical time, one canonical physical third-radial forcing
coordinate is strongly continuous in Fourier `L²`.
-/
theorem h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path_continuousAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ContinuousAt
      (h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
        hH3 hClass j)
      t := by

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

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
      q ≤ R :=
    hqRHalf.trans
      (by linarith [hR])

  have htq :
      t₁ + q = t := by
    dsimp only [q]
    ring

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
      hQLe.trans_lt
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

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNSShort ht₁ hTail₁

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNSShort ht₁ hE hTail₁

  let Fclosed :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3SelectedRestartForcingRadialFourierL2OnSlab
      3
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hQ hQR.le
      j

  have hFclosed :
      Continuous Fclosed := by

    dsimp only [Fclosed]

    exact
      continuous_h3SelectedRestartForcingRadialFourierL2OnSlab
        3
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        hQ hQR.le
        j

  let Frelative :
      ℝ → H3FourierComplexL2 :=
    Set.IccExtend
      (by linarith : Q / 2 ≤ Q)
      Fclosed

  have hFrelative :
      Continuous Frelative := by

    dsimp only [Frelative]

    exact
      hFclosed.Icc_extend'

  let shift : ℝ → ℝ :=
    fun r : ℝ => r - t₁

  have hShift :
      Continuous shift := by

    dsimp only [shift]

    exact
      continuous_id.sub
        continuous_const

  let Fselected :
      ℝ → H3FourierComplexL2 :=
    Frelative ∘ shift

  have hSelected :
      Continuous Fselected := by

    dsimp only [Fselected]

    exact
      hFrelative.comp hShift

  let Fphysical :
      ℝ → H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
      hH3 hClass j

  have hClassNeighborhood :
      Set.Ioo a T ∈ 𝓝 t :=
    Ioo_mem_nhds
      ht.1
      ht.2

  have hSlabLeft :
      t₁ + Q / 2 < t := by
    linarith [htq, hqLower]

  have hSlabRight :
      t < t₁ + Q := by
    linarith [htq, hqUpper]

  have hSlabNeighborhood :
      Set.Ioo
          (t₁ + Q / 2)
          (t₁ + Q)
        ∈
      𝓝 t :=
    Ioo_mem_nhds
      hSlabLeft
      hSlabRight

  have hSNeighborhood :
      Set.Iio S ∈ 𝓝 t :=
    Iio_mem_nhds htS

  have hEventuallyEq :
      Fphysical =ᶠ[𝓝 t] Fselected := by

    filter_upwards [
      hClassNeighborhood,
      hSlabNeighborhood,
      hSNeighborhood
    ] with r hrClass hrSlabAbs hrS

    have hrAbs :
        r ∈ Set.Ioo (0 : ℝ) T :=
      ⟨
        lt_trans
          hClass.terminal_start.1
          hrClass.1,
        hrClass.2
      ⟩

    have hrSlab :
        r - t₁ ∈ Set.Icc (Q / 2) Q := by
      constructor
      · linarith [hrSlabAbs.1]
      · linarith [hrSlabAbs.2]

    let rSlab :
        Set.Icc (Q / 2) Q :=
      ⟨r - t₁, hrSlab⟩

    let qr : ℝ :=
      r - t₁

    have hqr0 :
        0 < qr := by
      dsimp only [qr]
      have hHalf :
          0 < Q / 2 := by
        linarith [hQ]
      linarith [hrSlab.1]

    have hqrR :
        qr ≤ R := by
      dsimp only [qr]
      exact
        hrSlab.2.trans
          hQR.le

    have htqr :
        t₁ + qr = r := by
      dsimp only [qr]
      ring

    have hEndr :
        t₁ + qr < S := by
      rw [htqr]
      exact hrS

    let qClosed :
        Set.Icc (0 : ℝ) qr :=
      ⟨qr, hqr0.le, le_rfl⟩

    have hStateOld :=
      h3PreterminalSelectedUnitSpectralStateOnRadius_eq_tailCanonical_of_restartRadiusAgreement
        hNSShort
        ht₁
        hEndr
        hE
        hTail₁
        hqrR
        hPhysical
        qClosed
        hqr0

    let Usel : H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        qr

    let Uold : H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNSShort ht₁ hEndr hTail₁ qClosed

    have hSelOld :
        Usel = Uold := by

      dsimp only [Usel, Uold]

      simpa only [
        U₀,
        hA,
        hU₀,
        h3PreterminalSelectedUnitSpectralStateOnRadius,
        h3PreterminalElapsedToSelectedUnitRadius_coe,
        qClosed
      ] using
        hStateOld

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
          htqr

    have hSelTerm :
        Usel = Uterm :=
      hSelOld.trans
        hOldTerm

    have hSelectedRep :=
      h3SelectedRestartForcingRadialFourierL2OnSlab_ae
        3
        (one_pos : (0 : ℝ) < 1)
        U₀ hA hU₀
        hQ hQR.le
        j
        rSlab

    have hPhysicalRep :=
      h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At_ae
        hH3 hClass hrClass j

    have hBridge :
        Fclosed rSlab
          =
        h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
          hH3 hClass hrClass j := by

      apply
        MeasureTheory.Lp.ext

      filter_upwards [
        hSelectedRep,
        hPhysicalRep
      ] with ξ hSelectedξ hPhysicalξ

      rw [
        hSelectedξ,
        hPhysicalξ
      ]

      change
        ((‖ξ‖ ^ 3 : ℝ) : ℂ)
              *
            h3RawFinLerayOuterProductDivergence
              Usel Usel j ξ
          =
        ((‖ξ‖ ^ 3 : ℝ) : ℂ)
              *
            h3RawFinLerayOuterProductDivergence
              Uterm Uterm j ξ

      rw [hSelTerm]

    have hPhysicalAt :
        Fphysical r
          =
        h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
          hH3 hClass hrClass j := by

      dsimp only [Fphysical]

      exact
        h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path_eq
          hH3 hClass hrClass j

    have hSelectedAt :
        Fselected r
          =
        Fclosed rSlab := by

      dsimp only [
        Fselected,
        Function.comp_apply,
        Frelative,
        shift,
        qr,
        rSlab
      ]

      rw [
        Set.IccExtend_of_mem
          (by linarith : Q / 2 ≤ Q)
          Fclosed
          hrSlab
      ]

    calc
      Fphysical r
          =
        h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At
          hH3 hClass hrClass j :=
        hPhysicalAt
      _ =
        Fclosed rSlab :=
        hBridge.symm
      _ =
        Fselected r :=
        hSelectedAt.symm

  have hPhysicalContinuous :
      ContinuousAt Fphysical t :=
    hSelected.continuousAt.congr_of_eventuallyEq
      hEventuallyEq

  simpa only [Fphysical] using
    hPhysicalContinuous

/--
Each canonical physical third-radial forcing coordinate is strongly continuous
on the complete strict energy-class interval.
-/
theorem h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path_continuousOn
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3) :
    ContinuousOn
      (h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
        hH3 hClass j)
      (Set.Ioo a T) := by

  intro t ht

  exact
    (
      h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path_continuousAt
        hH3 hClass ht j
    ).continuousWithinAt

end

end Euclidean
end Bridge
end PrimeTensor
