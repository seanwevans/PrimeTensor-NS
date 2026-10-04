import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Evolution
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Derivative.Closure

/-!
# Close the sixth-diffusion terminal derivative branch

The selected restart analysis now gives a genuine strong derivative

    d/dt (q³ û_j) = -q⁴ û_j - q³ F_j

on every positive compact restart slab.

This file transports that derivative back to the canonical terminal physical
state used by the fixed-channel obstruction.

The transport has the same architecture as the already-closed `q²` physical
fourth-radial derivative:

1. identify the selected `q³ û_j` state with the terminal canonical
   `q³ û_j` state on every strict selected/old overlap;
2. around an arbitrary strict physical time, choose a local canonical restart
   and slide the anchor so the target elapsed time lies strictly inside one
   positive compact slab;
3. compose the selected derivative with the physical-time shift;
4. use eventual selected/terminal equality to transport the derivative to the
   terminal `q³ û_j` path.

Consequently the terminal sixth-diffusion Hilbert state is differentiable at
every strict preterminal time.  Its Hilbert norm-square derivative obstruction
therefore has no nondifferentiability side: under hypothetical nonextension,
the sixth-diffusion branch can only survive through a cofinally unbounded
pairing

    2 ⟪q³ û_j, d/dt(q³ û_j)⟫_ℝ.

Together with the previously closed top-dissipation branch, this leaves only
the lower-temporal and fourth-temporal one-more-derivative frontiers.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalSixthDiffusionClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 3500000

/-! ## Selected q³ state equals terminal q³ state -/

/--
On a strict selected/old overlap, the selected intrinsic `q³ û_j` state is
exactly the canonical terminal sixth-diffusion Hilbert state at the same
physical time.
-/
theorem h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab_eq_terminalPhysicalVelocityThirdQFourierL2At
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
    h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
        hNS ht₀ hE hTail hQ hQR j
        ⟨r - t₀, hrSlab⟩
      =
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At
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

  have hSelOld :
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

  have hRaw :
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          q
          j
        =
      h3SpectralScalarRawFourierL2
        (Uterm j) := by

    unfold
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2

    rw [← hSelTerm]

    rfl

  have hSelectedAE :=
    h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab_ae
      hNS ht₀ hE hTail hQ hQR j
      ⟨r - t₀, hrSlab⟩

  have hTerminalAE :=
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At_ae
      hH3 hClass hrClass j

  apply MeasureTheory.Lp.ext

  filter_upwards [
    hSelectedAE,
    hTerminalAE
  ] with ξ hSelectedξ hTerminalξ

  rw [hSelectedξ, hTerminalξ]

  dsimp only [q, Uterm] at hRaw ⊢

  rw [hRaw]

/-! ## Global strict-time terminal q³ differentiability -/

/--
At every strict physical time, the canonical terminal `q³ û_j` path has a
strong Fourier `L²` derivative.
-/
theorem h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path_differentiableAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    DifferentiableAt ℝ
      (h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
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

  let qSlab :
      Set.Icc (Q / 2) Q :=
    ⟨q, hqLower.le, hqUpper.le⟩

  let W : H3FourierComplexL2 :=
    h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
      hNSShort ht₁ hE hTail₁ hQ hQR j qSlab

  let Vclosed :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
      hNSShort ht₁ hE hTail₁ hQ hQR j

  let Vselected :
      ℝ → H3FourierComplexL2 :=
    fun r =>
      Set.IccExtend
        (by linarith : Q / 2 ≤ Q)
        Vclosed
        (r - t₁)

  let Vphysical :
      ℝ → H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
      hH3 hClass j

  have hRelative :=
    h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab_hasDerivAt
      hNSShort
      ht₁
      hE
      hTail₁
      hQ
      hQR
      j
      ⟨hqLower, hqUpper⟩

  have hShift :
      HasDerivAt
        (fun r : ℝ => r - t₁)
        1
        t := by
    simpa using
      (hasDerivAt_id t).sub_const t₁

  have hSelectedAbsolute :
      HasDerivAt
        Vselected
        W
        t := by

    have hComp :=
      hRelative.scomp
        t
        hShift

    dsimp only [
      Vselected,
      Vclosed,
      W,
      qSlab,
      q
    ] at hComp ⊢

    simpa only [
      Function.comp_def,
      one_smul
    ] using hComp

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
      Vphysical =ᶠ[𝓝 t] Vselected := by

    filter_upwards [
      hClassNeighborhood,
      hSlabNeighborhood,
      hSNeighborhood
    ] with r hrClass hrSlabAbs hrS

    have hrSlab :
        r - t₁ ∈ Set.Icc (Q / 2) Q := by
      constructor
      · linarith [hrSlabAbs.1]
      · linarith [hrSlabAbs.2]

    let rSlab :
        Set.Icc (Q / 2) Q :=
      ⟨r - t₁, hrSlab⟩

    have hBridge :=
      h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab_eq_terminalPhysicalVelocityThirdQFourierL2At
        hH3
        hClass
        hNSShort
        ht₁
        hE
        hTail₁
        hPhysical
        hQ
        hQR
        hrClass
        hrS
        hrSlab
        j

    have hPhysicalAt :
        Vphysical r
          =
        h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At
          hH3 hClass hrClass j := by
      dsimp only [Vphysical]
      exact
        h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path_eq
          hH3 hClass hrClass j

    have hSelectedAt :
        Vselected r
          =
        Vclosed rSlab := by

      dsimp only [Vselected]

      rw [
        Set.IccExtend_of_mem
          (by linarith : Q / 2 ≤ Q)
          Vclosed
          hrSlab
      ]

    calc
      Vphysical r
          =
        h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At
          hH3 hClass hrClass j :=
        hPhysicalAt
      _ =
        h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
          hNSShort ht₁ hE hTail₁ hQ hQR j rSlab := by
        exact hBridge.symm
      _ =
        Vselected r := by
        exact hSelectedAt.symm

  have hPhysicalDerivative :
      HasDerivAt
        Vphysical
        W
        t :=
    hSelectedAbsolute.congr_of_eventuallyEq
      hEventuallyEq

  exact
    hPhysicalDerivative.differentiableAt

/--
The abstract resolved sixth-diffusion Hilbert state is differentiable at every
strict preterminal time.
-/
theorem h3TerminalResolvedSixthDiffusionHilbertState_differentiableAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    DifferentiableAt ℝ
      (h3TerminalResolvedSixthDiffusionHilbertState
        hH3 hClass j)
      t := by

  change
    DifferentiableAt ℝ
      (h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
        hH3 hClass j)
      t

  exact
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path_differentiableAt
      hH3 hClass ht j

/-! ## Collapse the sixth-diffusion Hilbert obstruction -/

/--
Once terminal `q³ û_j` differentiability is known, the sixth-diffusion
Hilbert obstruction can only occupy its unbounded-pairing branch.
-/
theorem sixthDiffusion_pairing_cofinallyUnbounded_of_hilbertDerivativeObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (hObstruction :
      H3TerminalHilbertNormSqDerivativeObstruction
        (a := a) (T := T)
        (h3TerminalResolvedSixthDiffusionHilbertState
          hH3 hClass j)) :
    ∀ c : ℝ,
      c ∈ Set.Ioo a T →
      ∀ M : ℝ,
        ∃ r : ℝ,
          r ∈ Set.Ioo c T
            ∧
          M
            <
          abs
            (
              2 *
                inner ℝ
                  (h3TerminalResolvedSixthDiffusionHilbertState
                    hH3 hClass j r)
                  (
                    deriv
                      (h3TerminalResolvedSixthDiffusionHilbertState
                        hH3 hClass j)
                      r
                  )
            ) := by

  intro c hc

  rcases
    hObstruction c hc
  with hFail | hLarge

  · obtain
      ⟨t, htTail, hNotDiff⟩ :=
      hFail

    have ht :
        t ∈ Set.Ioo a T :=
      ⟨
        lt_trans hc.1 htTail.1,
        htTail.2
      ⟩

    have hDiff :=
      h3TerminalResolvedSixthDiffusionHilbertState_differentiableAt
        hH3 hClass ht j

    exact
      False.elim
        (
          hNotDiff hDiff
        )

  · exact hLarge

/-! ## Refine the fixed-channel alternative -/

/--
Under hypothetical nonextension, both the top-dissipation and sixth-diffusion
branches are now fully concrete Hilbert-pairing escapes.

Only the lower-temporal and fourth-temporal branches retain a possible loss of
one additional strong time derivative.
-/
theorem exists_fixed_resolvedPhysicalPDEChannel_hilbertDerivativeObstruction_topAndSixthClosed_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T) :
    ∃ j₀ : Fin 3,
      (
        H3TerminalHilbertNormSqDerivativeObstruction
          (a := a) (T := T)
          (h3TerminalResolvedLowerTemporalHilbertState
            hH3 hClass j₀)
      )
        ∨
      (
        ∀ c : ℝ,
          c ∈ Set.Ioo a T →
          ∀ M : ℝ,
            ∃ r : ℝ,
              r ∈ Set.Ioo c T
                ∧
              M
                <
              abs
                (
                  ∑ k : Fin 3,
                    2 *
                      inner ℝ
                        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                          hH3 hClass k r)
                        (
                          deriv
                            (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                              hH3 hClass k)
                            r
                        )
                )
      )
        ∨
      (
        H3TerminalHilbertNormSqDerivativeObstruction
          (a := a) (T := T)
          (h3TerminalResolvedFourthTemporalHilbertState
            hH3 hClass j₀)
      )
        ∨
      (
        ∀ c : ℝ,
          c ∈ Set.Ioo a T →
          ∀ M : ℝ,
            ∃ r : ℝ,
              r ∈ Set.Ioo c T
                ∧
              M
                <
              abs
                (
                  2 *
                    inner ℝ
                      (h3TerminalResolvedSixthDiffusionHilbertState
                        hH3 hClass j₀ r)
                      (
                        deriv
                          (h3TerminalResolvedSixthDiffusionHilbertState
                            hH3 hClass j₀)
                          r
                      )
                )
      ) := by

  obtain
    ⟨j₀, hBranch⟩ :=
    exists_fixed_resolvedPhysicalPDEChannel_hilbertDerivativeObstruction_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3 hClass hPhysical hCauchy hNoExtension

  refine
    ⟨
      j₀,
      ?_
    ⟩

  rcases hBranch with hLower | hTop | hFourth | hSixth

  · exact
      Or.inl hLower

  · exact
      Or.inr
        (
          Or.inl hTop
        )

  · exact
      Or.inr
        (
          Or.inr
            (
              Or.inl hFourth
            )
        )

  · exact
      Or.inr
        (
          Or.inr
            (
              Or.inr
                (
                  sixthDiffusion_pairing_cofinallyUnbounded_of_hilbertDerivativeObstruction
                    hH3 hClass j₀ hSixth
                )
            )
        )

/--
Neutral continuation form with the top-dissipation and sixth-diffusion
derivative branches both closed to explicit Hilbert-pairing escapes.
-/
theorem smoothContinuationExtension_or_fixed_resolvedPhysicalPDEChannel_hilbertDerivativeObstruction_topAndSixthClosed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∃ j₀ : Fin 3,
        (
          H3TerminalHilbertNormSqDerivativeObstruction
            (a := a) (T := T)
            (h3TerminalResolvedLowerTemporalHilbertState
              hH3 hClass j₀)
        )
          ∨
        (
          ∀ c : ℝ,
            c ∈ Set.Ioo a T →
            ∀ M : ℝ,
              ∃ r : ℝ,
                r ∈ Set.Ioo c T
                  ∧
                M
                  <
                abs
                  (
                    ∑ k : Fin 3,
                      2 *
                        inner ℝ
                          (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                            hH3 hClass k r)
                          (
                            deriv
                              (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                                hH3 hClass k)
                              r
                          )
                  )
        )
          ∨
        (
          H3TerminalHilbertNormSqDerivativeObstruction
            (a := a) (T := T)
            (h3TerminalResolvedFourthTemporalHilbertState
              hH3 hClass j₀)
        )
          ∨
        (
          ∀ c : ℝ,
            c ∈ Set.Ioo a T →
            ∀ M : ℝ,
              ∃ r : ℝ,
                r ∈ Set.Ioo c T
                  ∧
                M
                  <
                abs
                  (
                    2 *
                      inner ℝ
                        (h3TerminalResolvedSixthDiffusionHilbertState
                          hH3 hClass j₀ r)
                        (
                          deriv
                            (h3TerminalResolvedSixthDiffusionHilbertState
                              hH3 hClass j₀)
                            r
                        )
                  )
        )
    ) := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl hExtension

  · exact
      Or.inr
        (
          exists_fixed_resolvedPhysicalPDEChannel_hilbertDerivativeObstruction_topAndSixthClosed_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3 hClass hPhysical hCauchy hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
