import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedFluxBasicData
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Fourier.L2.Forcing.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Reconstruction.Compatibility
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldSlot0RealSchwartzWeakIntegral

/-!
# L² first derivatives of the selected--old weak--strong difference

The generic flux-coordinate argument is now missing only

    ∂ᵢ Dⱼ ∈ L².

This file closes that fact in two layers.

First, for an arbitrary weighted H³ scalar state `G`, the already-proved raw
Fourier derivative multiplier

    dᵢ(ξ) W₃(ξ)⁻¹ G(ξ)

lies in Fourier `L²`.  It is also `L¹`, so the ordinary inverse-Fourier
derivative representative agrees almost everywhere with the unitary `L²`
inverse transform.  Taking real parts and transporting back through
`WithLp.toLp` gives

    ∂ᵢ Rep(G) ∈ L²(Point3).

Second, apply that generic theorem to the selected restart spectral state.
The old branch first derivative is already `L²` from the H³ jet package.
Subtraction therefore gives every coordinate derivative of

    D = S - O

in physical `L²`.

No new PDE estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

attribute [local instance]
  point3MeasureSpaceH3SelectedOldWeakStrongTransportIntegralBound

noncomputable local instance axisFintypeH3SelectedOldWeakStrongDifferenceDerivativeL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every first spatial coordinate derivative of an arbitrary real H³
representative belongs to physical `L²(Point3)`. -/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_memLp_two
    (G : H3SpectralScalarState)
    (i : Fin 3) :
    MemLp
      (spatial3.d
        (h3AxisOfFin3 i)
        (h3SpectralScalarRealC1RepresentativeOnPoint3 G))
      2
      (volume : Measure Point3) := by
  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourierCoordinateDerivative G i

  have hf1 :
      Integrable f
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SpectralScalarRawFourierCoordinateDerivative_integrable
        G i

  have hf2 :
      MemLp f 2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    unfold h3SpectralScalarRawFourierCoordinateDerivative

    exact
      h3SpectralScalarRawDerivative_memLp2 i G

  let f2 : H3FourierComplexL2 :=
    hf2.toLp f

  let u2 : H3FourierComplexL2 :=
    (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).symm f2

  let r2 : H3FourierRealL2 :=
    h3RealPartFourierL2 u2

  let p2 : H3ScalarL2 :=
    h3FromFourierRealL2 r2

  have hCompat :
      FourierTransformInv.fourierInv f
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((u2 : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) := by
    dsimp only [u2, f2]

    exact
      h3FourierInv_integrable_memLp2_ae_eq_L2
        hf1 hf2

  have hRealPart :
      ((r2 : H3FourierRealL2) :
        H3FourierPoint3 → ℝ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun x : H3FourierPoint3 =>
        (((u2 : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) x).re) := by
    dsimp only [r2]

    unfold h3RealPartFourierL2

    exact
      Complex.reCLM.coeFn_compLp u2

  have hFourierReal :
      (fun x : H3FourierPoint3 =>
        (FourierTransformInv.fourierInv f x).re)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      ((r2 : H3FourierRealL2) :
        H3FourierPoint3 → ℝ) := by
    filter_upwards [hCompat, hRealPart] with x hx hRe

    rw [hRe]

    exact congrArg Complex.re hx

  have hComp :
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          f
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)).re)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((r2 : H3FourierRealL2) :
          H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)) := by
    exact
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hFourierReal

  have hFrom :
      ((p2 : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        ((r2 : H3FourierRealL2) :
          H3FourierPoint3 → ℝ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)) := by
    dsimp only [p2]

    unfold h3FromFourierRealL2

    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        r2
        (PiLp.volume_preserving_toLp
          (PrimeTensor.Axis Depth.three))

  have hDerivative :
      spatial3.d
          (h3AxisOfFin3 i)
          (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (FourierTransformInv.fourierInv
          f
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)).re) := by
    exact
      Filter.Eventually.of_forall
        (fun x => by
          dsimp only [f]

          exact
            h3SpectralScalarRealC1RepresentativeOnPoint3_spatialDerivative_fin
              G i x)

  have hAE :
      spatial3.d
          (h3AxisOfFin3 i)
          (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
        =ᵐ[(volume : Measure Point3)]
      ((p2 : H3ScalarL2) : Point3 → ℝ) :=
    hDerivative.trans
      (hComp.trans hFrom.symm)

  have hp2 :
      MemLp
        ((p2 : H3ScalarL2) : Point3 → ℝ)
        2
        (volume : Measure Point3) :=
    MeasureTheory.Lp.memLp p2

  exact
    (memLp_congr_ae hAE).2 hp2

/-- Every selected restart first spatial coordinate derivative belongs to
physical `L²`. -/
theorem h3PreterminalSelectedWeakStrongVelocity_spatial_d_memLp_two
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (s : ℝ)
    (j i : PrimeTensor.Axis Depth.three) :
    MemLp
      (spatial3.d
        i
        (fun x : Point3 =>
          ((h3PreterminalSelectedWeakStrongVelocity
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail)
            s x).component j))
      2
      (volume : Measure Point3) := by
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState hNS ht hTail

  let hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hEpos hU₀

  let k : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  let a : Fin 3 :=
    h3ClassicalizationFinOfAxis i

  have hAxis :
      h3AxisOfFin3 a = i := by
    dsimp only [a]

    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis i

  have hSelectedComponent :
      (fun x : Point3 =>
        ((h3PreterminalSelectedWeakStrongVelocity
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail)
          s x).component j)
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W s k) := by
    funext x

    unfold h3PreterminalSelectedWeakStrongVelocity
    unfold
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity

    rw [h3SpectralRealVelocityOfPath_component]

    rfl

  have hRep :
      MemLp
        (spatial3.d
          i
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (W s k)))
        2
        (volume : Measure Point3) := by
    have h :=
      h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_memLp_two
        (W s k) a

    simpa only [hAxis] using h

  have hDerivativeEq :
      spatial3.d
          i
          (fun x : Point3 =>
            ((h3PreterminalSelectedWeakStrongVelocity
              (one_pos : (0 : ℝ) < 1)
              hNS ht hE hTail)
              s x).component j)
        =
      spatial3.d
        i
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (W s k)) :=
    congrArg
      (spatial3.d i)
      hSelectedComponent

  exact
    (memLp_congr_ae
      (Filter.Eventually.of_forall
        (fun x =>
          congrFun hDerivativeEq x))).2
      hRep

/-- Every first spatial derivative of a concrete selected-minus-old difference
component belongs to physical `L²`. -/
theorem h3PreterminalSelectedOldWeakStrongVelocityDifference_spatial_d_memLp_two
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j i : PrimeTensor.Axis Depth.three) :
    let selected :=
      h3PreterminalSelectedWeakStrongVelocity
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    let old :=
      h3PreterminalOldElapsedWeakStrongVelocity u t
    MemLp
      (spatial3.d
        i
        (selectedOldVelocityDifferenceComponent
          selected old (q : ℝ) j))
      2
      (volume : Measure Point3) := by
  dsimp only

  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity u t

  let k : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  let a : Fin 3 :=
    h3ClassicalizationFinOfAxis i

  have hAxisJ :
      h3AxisOfFin3 k = j := by
    dsimp only [k]

    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis j

  have hAxisI :
      h3AxisOfFin3 a = i := by
    dsimp only [a]

    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis i

  have hSelectedC1 :
      SpatialC1
        (fun x : Point3 =>
          (selected (q : ℝ) x).component j) := by
    dsimp only [selected]

    exact
      h3PreterminalSelectedWeakStrongVelocity_component_spatialC1
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ) j

  have hOldC1 :
      SpatialC1
        (fun x : Point3 =>
          (old (q : ℝ) x).component j) := by
    dsimp only [old]

    exact
      h3PreterminalOldElapsedWeakStrongVelocity_component_spatialC1
        hNS ht hEnd hTail q j

  have hSelected :
      MemLp
        (spatial3.d
          i
          (fun x : Point3 =>
            (selected (q : ℝ) x).component j))
        2
        (volume : Measure Point3) := by
    dsimp only [selected]

    exact
      h3PreterminalSelectedWeakStrongVelocity_spatial_d_memLp_two
        hNS ht hE hTail (q : ℝ) j i

  have hOld :
      MemLp
        (spatial3.d
          i
          (fun x : Point3 =>
            (old (q : ℝ) x).component j))
        2
        (volume : Measure Point3) := by
    have hOldRaw :
        MemLp
          (spatial3.d
            (h3AxisOfFin3 a)
            (loggedVelocityComponent
              u
              (t + (q : ℝ))
              (h3AxisOfFin3 k)))
          2
          (volume : Measure Point3) := by
      simpa [velocityH3JetFieldAt, h3JetSlot1] using
        (velocityH3JetFieldAt_memLp2
          (h3PreterminalTailIntegrableOnElapsed
            hEnd hTail q)
          (h3PreterminalTailMeasurableOnElapsed
            hNS ht hEnd hTail q)
          (h3JetSlot1 k a))

    have hComponent :
        loggedVelocityComponent
            u
            (t + (q : ℝ))
            (h3AxisOfFin3 k)
          =
        (fun x : Point3 =>
          (logSpaceTimeVectorField
            u
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 k)) := by
      rfl

    rw [hComponent] at hOldRaw
    rw [hAxisI, hAxisJ] at hOldRaw

    dsimp only [old, h3PreterminalOldElapsedWeakStrongVelocity]

    exact hOldRaw

  have hSub :
      MemLp
        (fun x : Point3 =>
          spatial3.d
              i
              (fun y : Point3 =>
                (selected (q : ℝ) y).component j)
              x
            -
          spatial3.d
              i
              (fun y : Point3 =>
                (old (q : ℝ) y).component j)
              x)
        2
        (volume : Measure Point3) :=
    hSelected.sub hOld

  have hDerivativeEq :
      spatial3.d
          i
          (selectedOldVelocityDifferenceComponent
            selected old (q : ℝ) j)
        =
      (fun x : Point3 =>
        spatial3.d
            i
            (fun y : Point3 =>
              (selected (q : ℝ) y).component j)
            x
          -
        spatial3.d
            i
            (fun y : Point3 =>
              (old (q : ℝ) y).component j)
            x) := by
    funext x

    unfold selectedOldVelocityDifferenceComponent

    exact
      SpatialC1.spatial3_d_sub
        hSelectedC1
        hOldC1
        x i

  exact
    (memLp_congr_ae
      (Filter.Eventually.of_forall
        (fun x =>
          congrFun hDerivativeEq x))).2
      hSub

end

end Euclidean
end Bridge
end PrimeTensor
