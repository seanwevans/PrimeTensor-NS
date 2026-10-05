import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.LowerDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Raw.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Projected.RHS.Old.Bridge

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalRawFourierDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2600000

noncomputable def h3TerminalPhysicalRawVelocityFourierL2At
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    H3FourierComplexL2 :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  h3SpectralScalarRawFourierL2
    ((h3TerminalVelocitySpectralStateAt hH3 t htAbs) j)

noncomputable def h3TerminalPhysicalRawVelocityFourierL2Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    H3FourierComplexL2 :=
  if ht : t ∈ Set.Ioo a T then
    h3TerminalPhysicalRawVelocityFourierL2At
      hH3 hClass ht j
  else
    0

theorem h3TerminalPhysicalRawVelocityFourierL2Path_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalRawVelocityFourierL2Path
        hH3 hClass j t
      =
    h3TerminalPhysicalRawVelocityFourierL2At
      hH3 hClass ht j := by
  simp [
    h3TerminalPhysicalRawVelocityFourierL2Path,
    ht
  ]

noncomputable def h3TerminalPhysicalRawPDERHSFourierL2At
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
  h3SpectralScalarLaplacianRawFourierL2 (U j)
    -
  h3RawFinLerayOuterProductDivergenceFourierL2
    U U j

theorem h3TerminalPhysicalRawVelocityFourierL2Path_hasDerivAt_unitPDE
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    HasDerivAt
      (h3TerminalPhysicalRawVelocityFourierL2Path
        hH3 hClass j)
      (h3TerminalPhysicalRawPDERHSFourierL2At
        hH3 hClass ht j)
      t := by

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  rcases hH3.exists_localCanonicalRestartWindowAt htAbs with
    ⟨t₀, S, E, ht₀, hST, hE, hTail,
      hGap0, hGapR, hTarget, htS⟩

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

  let t₁ : ℝ := t - δ

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

  let q : ℝ := t - t₁

  have hqδ : q = δ := by
    dsimp only [q, t₁]
    ring

  have hq0 : 0 < q := by
    rw [hqδ]
    exact hδ0

  have hqRHalf : q ≤ R / 2 := by
    rw [hqδ]
    exact hδRHalf

  have hqR : q ≤ R := by
    exact hqRHalf.trans (by linarith [hR])

  have htq : t₁ + q = t := by
    dsimp only [q]
    ring

  have hEnd : t₁ + q < S := by
    rw [htq]
    exact htS

  let Q : ℝ := 3 * q / 2

  have hQ : 0 < Q := by
    dsimp only [Q]
    linarith [hq0]

  have hqQ : q < Q := by
    dsimp only [Q]
    linarith [hq0]

  have hQR : Q < R := by
    have hQLe : Q ≤ 3 * R / 4 := by
      dsimp only [Q]
      linarith [hqRHalf]
    have hThreeQuarter : 3 * R / 4 < R := by
      linarith [hR]
    exact lt_of_le_of_lt hQLe hThreeQuarter

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

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNSShort ht₁ hTail₁

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNSShort ht₁ hE hTail₁

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  let Vselected : ℝ → H3FourierComplexL2 :=
    fun r =>
      h3SpectralScalarRawFourierL2
        (W (r - t₁) j)

  let Vphysical : ℝ → H3FourierComplexL2 :=
    h3TerminalPhysicalRawVelocityFourierL2Path
      hH3 hClass j

  let qClosedQ : Set.Icc (0 : ℝ) Q :=
    ⟨q, hq0.le, hqQ.le⟩

  let qRadius :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    h3PreterminalElapsedToSelectedUnitRadius
      hQR.le qClosedQ

  let RHSselected : H3FourierComplexL2 :=
    h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      hNSShort ht₁ hE hTail₁ qRadius j

  have hRelative :=
    h3SelectedRestartVelocityRawFourierL2_hasDerivAt_unit
      hNSShort ht₁ hQ hE hTail₁ hQR.le
      ⟨hq0, hqQ⟩ j

  have hShift :
      HasDerivAt
        (fun r : ℝ => r - t₁)
        1 t := by
    simpa using
      (hasDerivAt_id t).sub_const t₁

  have hSelectedAbsolute :
      HasDerivAt Vselected RHSselected t := by
    have hComp := hRelative.scomp t hShift
    dsimp only [
      Vselected, RHSselected, W, U₀, hA, hU₀,
      qRadius, qClosedQ, q
    ] at hComp ⊢
    simpa only [Function.comp_def, one_smul] using hComp

  have hClassNeighborhood :
      Set.Ioo a T ∈ 𝓝 t :=
    Ioo_mem_nhds ht.1 ht.2

  have hElapsedNeighborhood :
      Set.Ioo t₁ (t₁ + Q) ∈ 𝓝 t := by
    apply Ioo_mem_nhds
    · exact ht₁t
    · rw [← htq]
      linarith [hqQ]

  have hSNeighborhood :
      Set.Iio S ∈ 𝓝 t :=
    Iio_mem_nhds htS

  have hEventuallyEq :
      Vphysical =ᶠ[𝓝 t] Vselected := by
    filter_upwards [
      hClassNeighborhood,
      hElapsedNeighborhood,
      hSNeighborhood
    ] with r hrClass hrElapsed hrS

    let qr : ℝ := r - t₁

    have hqr0 : 0 < qr := by
      dsimp only [qr]
      linarith [hrElapsed.1]

    have hqrQ : qr < Q := by
      dsimp only [qr]
      linarith [hrElapsed.2]

    have hqrR : qr ≤ R :=
      (hqrQ.trans hQR).le

    have hTimeR :
        t₁ + qr = r := by
      dsimp only [qr]
      ring

    have hEndr :
        t₁ + qr < S := by
      rw [hTimeR]
      exact hrS

    let qrClosed : Set.Icc (0 : ℝ) qr :=
      ⟨qr, hqr0.le, le_rfl⟩

    have hStateOld :=
      h3PreterminalSelectedUnitSpectralStateOnRadius_eq_tailCanonical_of_restartRadiusAgreement
        hNSShort ht₁ hEndr hE hTail₁ hqrR
        hPhysical qrClosed hqr0

    let Usel : H3SpectralFinVectorState := W qr

    let Uold : H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNSShort ht₁ hEndr hTail₁ qrClosed

    have hSelOld : Usel = Uold := by
      dsimp only [Usel, Uold, W, U₀, hA, hU₀]
      simpa only [
        h3PreterminalSelectedUnitSpectralStateOnRadius,
        h3PreterminalElapsedToSelectedUnitRadius_coe,
        qrClosed
      ] using hStateOld

    have hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
      ⟨
        lt_trans hClass.terminal_start.1 hrClass.1,
        hrClass.2
      ⟩

    let Uterm : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt
        hH3 r hrAbs

    have hTime : t₁ + qr = r := by
      dsimp only [qr]
      ring

    have hOldTerm : Uold = Uterm := by
      dsimp only [Uold, Uterm]
      unfold
        h3PreterminalTailCanonicalSpectralStateOnElapsed
        h3TerminalVelocitySpectralStateAt
      apply velocityH3SpectralStateAt_eq_of_time_eq u hTime

    have hSelTerm : Usel = Uterm :=
      hSelOld.trans hOldTerm

    have hPhysicalAt :
        Vphysical r
          =
        h3SpectralScalarRawFourierL2
          (Uterm j) := by
      dsimp only [Vphysical]
      rw [
        h3TerminalPhysicalRawVelocityFourierL2Path_eq
          hH3 hClass hrClass j
      ]
      rfl

    have hSelectedAt :
        Vselected r
          =
        h3SpectralScalarRawFourierL2
          (Usel j) := by
      dsimp only [Vselected, Usel, qr]

    calc
      Vphysical r
          =
        h3SpectralScalarRawFourierL2
          (Uterm j) := hPhysicalAt
      _ =
        h3SpectralScalarRawFourierL2
          (Usel j) := by
        rw [hSelTerm]
      _ =
        Vselected r := hSelectedAt.symm

  have hPhysicalDerivative :
      HasDerivAt Vphysical RHSselected t :=
    hSelectedAbsolute.congr_of_eventuallyEq
      hEventuallyEq

  let qClosed : Set.Icc (0 : ℝ) q :=
    ⟨q, hq0.le, le_rfl⟩

  have hStateOld :=
    h3PreterminalSelectedUnitSpectralStateOnRadius_eq_tailCanonical_of_restartRadiusAgreement
      hNSShort ht₁ hEnd hE hTail₁ hqR
      hPhysical qClosed hq0

  let Usel : H3SpectralFinVectorState := W q

  let Uold : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNSShort ht₁ hEnd hTail₁ qClosed

  have hSelOld : Usel = Uold := by
    dsimp only [Usel, Uold, W, U₀, hA, hU₀]
    simpa only [
      h3PreterminalSelectedUnitSpectralStateOnRadius,
      h3PreterminalElapsedToSelectedUnitRadius_coe,
      qClosed
    ] using hStateOld

  let Uterm : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  have hOldTerm : Uold = Uterm := by
    dsimp only [Uold, Uterm]
    unfold
      h3PreterminalTailCanonicalSpectralStateOnElapsed
      h3TerminalVelocitySpectralStateAt
    apply velocityH3SpectralStateAt_eq_of_time_eq u htq

  have hSelTerm : Usel = Uterm :=
    hSelOld.trans hOldTerm

  have hRHSValue :
      RHSselected
        =
      h3TerminalPhysicalRawPDERHSFourierL2At
        hH3 hClass ht j := by
    dsimp only [RHSselected]
    unfold
      h3PreterminalSelectedUnitProjectedRHSFourierL2OnRadius
      h3PreterminalSelectedUnitLaplacianFourierL2OnRadius
      h3PreterminalSelectedUnitLerayForcingFourierL2OnRadius
      h3TerminalPhysicalRawPDERHSFourierL2At
    dsimp only
    change
      h3SpectralScalarLaplacianRawFourierL2 (Usel j)
        -
      h3RawFinLerayOuterProductDivergenceFourierL2
        Usel Usel j
        =
      h3SpectralScalarLaplacianRawFourierL2 (Uterm j)
        -
      h3RawFinLerayOuterProductDivergenceFourierL2
        Uterm Uterm j
    rw [hSelTerm]

  dsimp only [Vphysical] at hPhysicalDerivative ⊢
  exact
    hPhysicalDerivative.congr_deriv
      hRHSValue

theorem h3TerminalPhysicalRawVelocityFourierL2Derivative_closed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ (t : ℝ),
      ∀ (ht : t ∈ Set.Ioo a T),
        ∀ j : Fin 3,
          HasDerivAt
            (h3TerminalPhysicalRawVelocityFourierL2Path
              hH3 hClass j)
            (h3TerminalPhysicalRawPDERHSFourierL2At
              hH3 hClass ht j)
            t := by
  intro t ht j
  exact
    h3TerminalPhysicalRawVelocityFourierL2Path_hasDerivAt_unitPDE
      hH3 hClass ht j

end
end Euclidean
end Bridge
end PrimeTensor
