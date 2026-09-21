import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedHighFrechetL2Frontier

/-!
# Remove the real-part seam from the selected high-Fréchet L² frontier

`H3PathSelectedHighFrechetL2Frontier` reduced the remaining diffusion mass
problem to physical `L²` membership of the real parts of selected fourth and
fifth complex Fréchet coordinate evaluations.

For the Fourier/Plancherel step, the natural target is the complex coordinate
field itself.  Taking real parts is a bounded real-linear operation on complex
`L²`, so no additional estimate is required.

This file therefore replaces

    Re(D⁴ U[...]), Re(D⁵ U[...]) ∈ L²

by the cleaner complex frontier

    D⁴ U[...], D⁵ U[...] ∈ L².

The next checkpoint can work entirely in complex `L²` and Fourier space.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedHighFrechetComplexL2Frontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathSelectedHighFrechetComplexL2Frontier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Bounded real projection preserves physical L² -/

/--
The real part of a complex physical `L²` representative is again in `L²`.
-/
private theorem memLp_re_of_memLp_complex_h3SelectedHighFrechet
    {f : Point3 → ℂ}
    (hf :
      MemLp
        f
        2
        (volume : Measure Point3)) :
    MemLp
      (fun x : Point3 => (f x).re)
      2
      (volume : Measure Point3) := by

  let F :
      MeasureTheory.Lp
        ℂ
        2
        (volume : Measure Point3) :=
    hf.toLp f

  let R :
      MeasureTheory.Lp
        ℝ
        2
        (volume : Measure Point3) :=
    Complex.reCLM.compLp F

  have hF :
      ((F :
          MeasureTheory.Lp
            ℂ
            2
            (volume : Measure Point3)) :
        Point3 → ℂ)
        =ᵐ[(volume : Measure Point3)]
      f := by
    dsimp only [F]
    exact
      MeasureTheory.MemLp.coeFn_toLp hf

  have hR :
      ((R :
          MeasureTheory.Lp
            ℝ
            2
            (volume : Measure Point3)) :
        Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (((F :
            MeasureTheory.Lp
              ℂ
              2
              (volume : Measure Point3)) :
          Point3 → ℂ) x).re) := by
    dsimp only [R]
    exact
      Complex.reCLM.coeFn_compLp F

  have hAE :
      (fun x : Point3 => (f x).re)
        =ᵐ[(volume : Measure Point3)]
      ((R :
          MeasureTheory.Lp
            ℝ
            2
            (volume : Measure Point3)) :
        Point3 → ℝ) := by
    filter_upwards [hF, hR] with x hxF hxR
    calc
      (f x).re
          =
        (((F :
            MeasureTheory.Lp
              ℂ
              2
              (volume : Measure Point3)) :
          Point3 → ℂ) x).re := by
            exact congrArg Complex.re hxF.symm
      _ =
        ((R :
            MeasureTheory.Lp
              ℝ
              2
              (volume : Measure Point3)) :
          Point3 → ℝ) x := hxR.symm

  have hRMem :
      MemLp
        ((R :
            MeasureTheory.Lp
              ℝ
              2
              (volume : Measure Point3)) :
          Point3 → ℝ)
        2
        (volume : Measure Point3) :=
    MeasureTheory.Lp.memLp R

  exact
    (memLp_congr_ae hAE).2 hRMem

/-! ## Complex selected high-Fréchet frontier -/

/--
At every strict positive selected-restart time, every ordered fourth and fifth
complex Fréchet coordinate field belongs to physical complex `L²`.
-/
def H3CanonicalSelectedFourthFifthFrechetComplexMemLp2OnRestartRadius : Prop :=
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
                  iteratedFDeriv ℝ 4
                    (h3SpectralScalarC1Representative
                      (W q j))
                    ((WithLp.toLp 2 :
                      Point3 → H3FourierPoint3) x)
                    ![
                      h3FourierAxisDirection a,
                      h3FourierAxisDirection b,
                      h3FourierAxisDirection c,
                      h3FourierAxisDirection d
                    ])
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
                  iteratedFDeriv ℝ 5
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
                    ])
                2
                (volume : Measure Point3)
        )

/-! ## Complex L² implies the previous real-part frontier -/

/--
Bounded real projection converts the complex selected high-Fréchet frontier
directly into the previously isolated real-part frontier.
-/
theorem h3CanonicalSelectedFourthFifthFrechetRealPartMemLp2OnRestartRadius_of_complex
    (hComplex :
      H3CanonicalSelectedFourthFifthFrechetComplexMemLp2OnRestartRadius) :
    H3CanonicalSelectedFourthFifthFrechetRealPartMemLp2OnRestartRadius := by

  intro E u T t₀ hNS ht₀ hE hTail q hq

  have hC :=
    hComplex E u T t₀ hNS ht₀ hE hTail q hq

  dsimp only at hC ⊢

  constructor

  · intro a b c d j

    exact
      memLp_re_of_memLp_complex_h3SelectedHighFrechet
        (hC.1 a b c d j)

  · intro a b c d e j

    exact
      memLp_re_of_memLp_complex_h3SelectedHighFrechet
        (hC.2 a b c d e j)

/-! ## BKM closure at the complex high-Fréchet frontier -/

/--
The diffusion branch of BKM continuation now accepts complex selected
fourth/fifth Fréchet coordinate `L²` data directly.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_selectedFourthFifthFrechetComplex_of_transportPressure_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hComplex :
      H3CanonicalSelectedFourthFifthFrechetComplexMemLp2OnRestartRadius)
    (hTP :
      H3PathEnergyClassProducesTransportPressureMemLp2)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_selectedFourthFifthFrechetRealPart_of_transportPressure_of_fullScalarEnergy
      hLow
      hDerivative
      (h3CanonicalSelectedFourthFifthFrechetRealPartMemLp2OnRestartRadius_of_complex
        hComplex)
      hTP
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
