import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathHighSpatialJetL2Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrder3SelectedReduction

/-!
# Reduce fourth/fifth old-velocity L² jets to the selected restart

The remaining diffusion frontier from
`H3PathHighSpatialJetL2Frontier` is physical `L²` membership of fourth and
fifth spatial derivatives of the old logged velocity.

At every strict target time, `LoggedPreterminalH3PathAdmissible` already
provides a local canonical selected restart whose positive-time selected
velocity agrees pointwise with the old velocity on the overlap.  Equality of
the entire spatial scalar slice transports all spatial derivatives, exactly as
in the existing selected-to-old `C⁵` transfer.

Hence no old-branch high-order mass estimate is needed.  It is enough to prove
the corresponding fourth/fifth `L²` statement for the canonical selected
restart at every positive elapsed time inside its restart radius.

This file packages that reduction.  The remaining diffusion problem is now
purely selected-side Fourier analysis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedHighSpatialJetL2Frontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathSelectedHighSpatialJetL2Frontier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Pure selected-restart high-jet L² target -/

/--
At every positive elapsed time in a canonical restart radius, every fourth and
fifth spatial derivative needed by the diffusion Laplacian belongs to physical
`L²`.

This is the exact selected-side analytic target left by the diffusion
reduction.
-/
def H3CanonicalSelectedFourthFifthVelocityJetMemLp2OnRestartRadius : Prop :=
  ∀
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t₀ : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E),
      ∀ q : ℝ,
        q ∈
          Set.Ioc
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        (
          ∀ i k r j : PrimeTensor.Axis Depth.three,
            MemLp
              (spatial3.d i
                (spatial3.d k
                  (spatial3.d r
                    (spatial3.d r
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
              (volume : Measure Point3)
        )
          ∧
        (
          ∀ i k l r j : PrimeTensor.Axis Depth.three,
            MemLp
              (spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (spatial3.d r
                      (spatial3.d r
                        (fun y : Point3 =>
                          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                            (one_pos : (0 : ℝ) < 1)
                            (h3PreterminalSelectedDecoderAnchorState
                              hNS ht₀ hTail)
                            (lt_of_lt_of_le zero_lt_one hE)
                            (norm_h3PreterminalSelectedDecoderAnchorState_le
                              hNS ht₀ hE hTail)
                            q
                            y).component j))))))
              2
              (volume : Measure Point3)
        )

/-! ## Transport the selected L² jets to the old H³ path -/

/--
Selected fourth/fifth high-jet `L²` on every canonical restart radius implies
the old-path fourth/fifth velocity-jet frontier.
-/
theorem h3PathEnergyClassProducesFourthFifthVelocityJetMemLp2_of_selected
    (hSelected :
      H3CanonicalSelectedFourthFifthVelocityJetMemLp2OnRestartRadius) :
    H3PathEnergyClassProducesFourthFifthVelocityJetMemLp2 := by

  intro u T hH3 a hClass s hs

  have hsAbs :
      s ∈ Set.Ioo (0 : ℝ) T := by
    exact
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
        Set.Ioc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) := by
    constructor
    · dsimp only [q]
      exact hq0
    · dsimp only [q]
      exact le_of_lt hqR

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
    ⟨q, hqMem⟩

  have hAgreement :
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1)
        q
        hNSShort ht₀ hE hTail := by
    simpa only [qSubtype] using
      hPhysical qSubtype hEnd

  have hSelectedJets :=
    hSelected
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

  constructor

  · intro i k r j

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
      hSelectedJets.1 i k r j

  · intro i k l r j

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
      hSelectedJets.2 i k l r j

/-! ## BKM closure at the pure selected high-jet frontier -/

/--
After the previous reductions, the diffusion side of BKM continuation requires
only the selected restart's positive-time fourth/fifth spatial `L²` jets.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_selectedFourthFifthVelocityJet_of_transportPressure_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hSelected :
      H3CanonicalSelectedFourthFifthVelocityJetMemLp2OnRestartRadius)
    (hTP :
      H3PathEnergyClassProducesTransportPressureMemLp2)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_fourthFifthVelocityJet_of_transportPressure_of_fullScalarEnergy
      hLow
      hDerivative
      (h3PathEnergyClassProducesFourthFifthVelocityJetMemLp2_of_selected
        hSelected)
      hTP
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
