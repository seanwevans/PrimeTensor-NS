import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathClosedHighVelocityJets

/-!
# Recover arbitrary physical fourth velocity L² jets

`H3PathClosedHighVelocityJets` closes the fourth/fifth physical jet package in
exactly the repeated-coordinate shape needed by the differentiated Laplacian.
The transport term needs a slightly stronger presentation: every ordered fourth
spatial derivative of the old velocity.

No new estimate is required.  The closed selected radial Fourier theorem already
passes through the raw-coordinate and Fréchet layers with arbitrary ordered
axes.  This file keeps that full order-four information when returning to
physical space and then transports it from the selected restart to the old H³
path by the existing physical-agreement theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathClosedArbitraryFourthVelocityJets
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathClosedArbitraryFourthVelocityJets :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Every ordered fourth spatial derivative of the old velocity belongs to
physical `L²` at one time. -/
def H3ArbitraryFourthVelocityJetMemLp2At
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : Prop :=
  ∀ a b c d j : PrimeTensor.Axis Depth.three,
    MemLp
      (spatial3.d a
        (spatial3.d b
          (spatial3.d c
            (spatial3.d d
              (loggedVelocityComponent u t j)))))
      2
      (volume : Measure Point3)

/-- Path-level arbitrary fourth-velocity-jet `L²` package. -/
def H3PathEnergyClassProducesArbitraryFourthVelocityJetMemLp2 : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ _hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            t ∈ Set.Ioo a T →
              H3ArbitraryFourthVelocityJetMemLp2At u t

/--
The closed selected terminal-tail radial theorem already gives every ordered
fourth selected physical derivative in `L²`.
-/
theorem h3CanonicalSelectedArbitraryFourthVelocityJetMemLp2OnRestartRadius_closed :
    ∀
      (E : ℝ)
      (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
      (T t₀ : ℝ)
      (hNS : LoggedPreterminalNavierStokesAdmissible u T)
      (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
      (hE : 1 ≤ E)
      (hTail : CanonicalH3TailDataFrom u t₀ T E)
      (q : ℝ),
        q ∈
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        ∀ a b c d j : PrimeTensor.Axis Depth.three,
          MemLp
            (spatial3.d a
              (spatial3.d b
                (spatial3.d c
                  (spatial3.d d
                    (fun y : Point3 =>
                      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                        (one_pos : (0 : ℝ) < 1)
                        (h3PreterminalSelectedDecoderAnchorState
                          hNS ht₀ hTail)
                        (lt_of_lt_of_le zero_lt_one hE)
                        (norm_h3PreterminalSelectedDecoderAnchorState_le
                          hNS ht₀ hE hTail)
                        q
                        y).component j)))))
            2
            (volume : Measure Point3) := by

  intro E u T t₀ hNS ht₀ hE hTail q hq a b c d j

  have hTailL2 :
      H3CanonicalSelectedDuhamelTailFourthFifthRadialRawFourierMemLp2OnRestartRadius :=
    h3CanonicalSelectedDuhamelTailFourthFifthRadialRawFourierMemLp2OnRestartRadius

  have hDuhamel :
      H3CanonicalSelectedDuhamelFourthFifthRadialRawFourierMemLp2OnRestartRadius :=
    h3CanonicalSelectedDuhamelFourthFifthRadialRawFourierMemLp2OnRestartRadius_of_tail
      hTailL2

  have hRadial :
      H3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius :=
    h3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius_of_duhamel
      hDuhamel

  have hMultiplier :
      H3CanonicalSelectedFourthFifthRawCoordinateMultiplierMemLp2OnRestartRadius :=
    h3CanonicalSelectedFourthFifthRawCoordinateMultiplierMemLp2OnRestartRadius_of_radial
      hRadial

  have hComplex :
      H3CanonicalSelectedFourthFifthFrechetComplexMemLp2OnRestartRadius :=
    h3CanonicalSelectedFourthFifthFrechetComplexMemLp2OnRestartRadius_of_rawCoordinateMultiplier
      hMultiplier

  have hReal :
      H3CanonicalSelectedFourthFifthFrechetRealPartMemLp2OnRestartRadius :=
    h3CanonicalSelectedFourthFifthFrechetRealPartMemLp2OnRestartRadius_of_complex
      hComplex

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  have hF :=
    hReal E u T t₀ hNS ht₀ hE hTail q hq

  dsimp only at hF

  let jf : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have hAxisJ :
      h3AxisOfFin3 jf = j := by
    dsimp only [jf]
    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis j

  have hComponent :
      (fun y : Point3 =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          (one_pos : (0 : ℝ) < 1)
          U₀ hA hU₀ q y).component j)
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W q jf) := by
    funext y
    rw [← hAxisJ]
    simp only [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
      h3SpectralVelocityRealC1RepresentativeOnPoint3,
      W
    ]

  rw [hComponent]

  have hPoint :
      spatial3.d a
          (spatial3.d b
            (spatial3.d c
              (spatial3.d d
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W q jf)))))
        =
      fun x : Point3 =>
        (iteratedFDeriv ℝ 4
          (h3SpectralScalarC1Representative
            (W q jf))
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)
          ![
            h3FourierAxisDirection a,
            h3FourierAxisDirection b,
            h3FourierAxisDirection c,
            h3FourierAxisDirection d
          ]).re := by

    funext x

    dsimp only [W, U₀, hA, hU₀, jf]

    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_four_eq_re_fourthFrechet
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNS ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNS ht₀ hE hTail)
        hq.1
        hq.2
        (h3ClassicalizationFinOfAxis j)
        x
        a b c d

  rw [hPoint]

  simpa only [W, U₀, hA, hU₀, jf] using
    hF.1 a b c d
      (h3ClassicalizationFinOfAxis j)

/--
All ordered fourth derivatives transfer from the selected local restart to the
old H³ path.  Hence the arbitrary fourth-jet package is closed outright.
-/
theorem h3PathEnergyClassProducesArbitraryFourthVelocityJetMemLp2_closed :
    H3PathEnergyClassProducesArbitraryFourthVelocityJetMemLp2 := by

  intro u T hH3 a hClass s hs

  have hsAbs :
      s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 hs.1,
      hs.2
    ⟩

  rcases
    hH3.exists_localCanonicalRestartWindowAt hsAbs
  with
    ⟨
      t₀,
      S,
      E,
      ht₀,
      hST,
      hE,
      hTail,
      hq0,
      hqR,
      hts,
      hsS
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

  let q : ℝ :=
    s - t₀

  have hqMem :
      q ∈
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) := by
    constructor
    · dsimp only [q]
      exact hq0
    · dsimp only [q]
      exact hqR

  have hqMemClosed :
      q ∈
        Set.Ioc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨hqMem.1, le_of_lt hqMem.2⟩

  have hWeakFTC :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
        E u S t₀ hNSShort ht₀ hE hTail :=
    H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_tailH3_curl
      E hE u S t₀ hNSShort ht₀ hTail

  have hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E
        (one_pos : (0 : ℝ) < 1)
        u S t₀ hNSShort ht₀ hE hTail :=
    h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_projectedRHSWeakFTC
      hNSShort
      ht₀
      hE
      hTail
      hWeakFTC

  have hEnd :
      t₀ + q < S := by
    dsimp only [q]
    rw [hts]
    exact hsS

  let qSubtype :
      Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨q, hqMemClosed⟩

  have hAgreement :
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1)
        q
        hNSShort ht₀ hE hTail := by
    simpa only [qSubtype] using
      hPhysical qSubtype hEnd

  intro i k l r j

  let selectedSlice : ScalarField3 :=
    fun y : Point3 =>
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalSelectedDecoderAnchorState
          hNSShort ht₀ hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalSelectedDecoderAnchorState_le
          hNSShort ht₀ hE hTail)
        q
        y).component j

  have hSliceEq :
      selectedSlice
        =
      loggedVelocityComponent u s j := by

    funext y

    let jj : Fin 3 :=
      h3ClassicalizationFinOfAxis j

    have hPoint :=
      hAgreement jj y

    dsimp only [jj] at hPoint

    rw [
      h3AxisOfFin3_h3ClassicalizationFinOfAxis j
    ] at hPoint

    dsimp only [selectedSlice]

    have hTime :
        t₀ + q = s := by
      dsimp only [q]
      exact hts

    rw [hTime] at hPoint

    simpa only [
      loggedVelocityComponent
    ] using hPoint

  rw [← hSliceEq]

  dsimp only [selectedSlice]

  exact
    h3CanonicalSelectedArbitraryFourthVelocityJetMemLp2OnRestartRadius_closed
      E
      u
      S
      t₀
      hNSShort
      ht₀
      hE
      hTail
      q
      hqMem
      i k l r j

end

end Euclidean
end Bridge
end PrimeTensor
