import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedHighSpatialJetL2Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Third.Mixed.Derivative.Candidate.Bridge

/-!
# Reduce selected fourth/fifth physical L² jets to complex Fréchet coordinates

The remaining diffusion frontier has already been localized entirely to the
canonical selected restart at strict positive elapsed times.

The selected classicalization stack also already proves exact pointwise
identities

    ∂ₐ∂ᵦ∂𝑐∂𝑑 u
      = Re(D⁴ U[eₐ,eᵦ,e𝑐,e𝑑]),

    ∂ₐ∂ᵦ∂𝑐∂𝑑∂ₑ u
      = Re(D⁵ U[eₐ,eᵦ,e𝑐,e𝑑,eₑ]),

for the complex selected inverse-Fourier representative.

Therefore the concrete physical-derivative `L²` frontier can be replaced by
`L²` membership of those real Fréchet coordinate evaluations.  This removes
the last spatial-calculus layer before the Fourier multiplier estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedHighFrechetL2Frontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathSelectedHighFrechetL2Frontier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Selected complex Fréchet L² frontier -/

/--
At every strict positive selected-restart time, the real parts of every
ordered fourth and fifth complex Fréchet coordinate belong to physical `L²`.
-/
def H3CanonicalSelectedFourthFifthFrechetRealPartMemLp2OnRestartRadius : Prop :=
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
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
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
        (
          ∀
            (a b c d : PrimeTensor.Axis Depth.three)
            (j : Fin 3),
              MemLp
                (fun x : Point3 =>
                  (iteratedFDeriv ℝ 4
                    (h3SpectralScalarC1Representative
                      (W q j))
                    ((WithLp.toLp 2 :
                      Point3 → H3FourierPoint3) x)
                    ![
                      h3FourierAxisDirection a,
                      h3FourierAxisDirection b,
                      h3FourierAxisDirection c,
                      h3FourierAxisDirection d
                    ]).re)
                2
                (volume : Measure Point3)
        )
          ∧
        (
          ∀
            (a b c d e : PrimeTensor.Axis Depth.three)
            (j : Fin 3),
              MemLp
                (fun x : Point3 =>
                  (iteratedFDeriv ℝ 5
                    (h3SpectralScalarC1Representative
                      (W q j))
                    ((WithLp.toLp 2 :
                      Point3 → H3FourierPoint3) x)
                    ![
                      h3FourierAxisDirection a,
                      h3FourierAxisDirection b,
                      h3FourierAxisDirection c,
                      h3FourierAxisDirection d,
                      h3FourierAxisDirection e
                    ]).re)
                2
                (volume : Measure Point3)
        )

/-! ## Fréchet coordinates imply the concrete selected high jets -/

/--
The compiled fourth/fifth real-complex derivative bridges turn Fréchet
coordinate `L²` membership into the concrete selected physical high-jet
frontier.
-/
theorem h3CanonicalSelectedFourthFifthVelocityJetMemLp2OnRestartRadius_of_frechetRealPart
    (hFrechet :
      H3CanonicalSelectedFourthFifthFrechetRealPartMemLp2OnRestartRadius) :
    H3CanonicalSelectedFourthFifthVelocityJetMemLp2OnRestartRadius := by

  intro E u T t₀ hNS ht₀ hE hTail q hq

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
    hFrechet E u T t₀ hNS ht₀ hE hTail q hq

  dsimp only at hF

  constructor

  · intro i k r j

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
        spatial3.d i
            (spatial3.d k
              (spatial3.d r
                (spatial3.d r
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
              h3FourierAxisDirection i,
              h3FourierAxisDirection k,
              h3FourierAxisDirection r,
              h3FourierAxisDirection r
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
          i k r r

    rw [hPoint]

    simpa only [W, U₀, hA, hU₀, jf] using
      hF.1 i k r r
        (h3ClassicalizationFinOfAxis j)

  · intro i k l r j

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
        spatial3.d i
            (spatial3.d k
              (spatial3.d l
                (spatial3.d r
                  (spatial3.d r
                    (h3SpectralScalarRealC1RepresentativeOnPoint3
                      (W q jf))))))
          =
        fun x : Point3 =>
          (iteratedFDeriv ℝ 5
            (h3SpectralScalarC1Representative
              (W q jf))
            ((WithLp.toLp 2 :
              Point3 → H3FourierPoint3) x)
            ![
              h3FourierAxisDirection i,
              h3FourierAxisDirection k,
              h3FourierAxisDirection l,
              h3FourierAxisDirection r,
              h3FourierAxisDirection r
            ]).re := by

      funext x

      dsimp only [W, U₀, hA, hU₀, jf]

      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_five_eq_re_fifthFrechet
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
          i k l r r

    rw [hPoint]

    simpa only [W, U₀, hA, hU₀, jf] using
      hF.2 i k l r r
        (h3ClassicalizationFinOfAxis j)

/-! ## BKM closure at the selected Fréchet L² frontier -/

/--
The diffusion side of BKM continuation is now reduced to `L²` control of
selected fourth/fifth complex Fréchet coordinate real parts.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_selectedFourthFifthFrechetRealPart_of_transportPressure_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hFrechet :
      H3CanonicalSelectedFourthFifthFrechetRealPartMemLp2OnRestartRadius)
    (hTP :
      H3PathEnergyClassProducesTransportPressureMemLp2)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_selectedFourthFifthVelocityJet_of_transportPressure_of_fullScalarEnergy
      hLow
      hDerivative
      (h3CanonicalSelectedFourthFifthVelocityJetMemLp2OnRestartRadius_of_frechetRealPart
        hFrechet)
      hTP
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
