import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldSlot1RealSchwartzWeakIntegral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Pressure-free slot1 real-Schwartz spatial FTC / integration by parts

`OldSlot1RealSchwartzWeakIntegral` supplies the `L¹` inputs required to repeat
the spatial integration-by-parts argument one derivative higher.

For one retained elapsed snapshot and indices `j,i,k`, write

    u₀ = uⱼ(t+q,·),
    f  = ∂ₖ u₀,
    g  = ∂ᵢ f = ∂ᵢ∂ₖ u₀.

The old preterminal regularity gives `SpatialC3 u₀`.  Hence `f` is
`SpatialC2`, in particular `SpatialC1`, so after carrier transport the genuine
line derivative of `F = transport(f)` in the `i`-direction is
`G = transport(g)`.

Mathlib's line-derivative integration-by-parts theorem therefore gives

    ∫ F (∂ᵢ φ) = - ∫ G φ,

equivalently

    ∫ G φ = - ∫ F (∂ᵢ φ).

This is exactly the pressure-free weak derivative identity needed to transfer
real-Schwartz weak continuity from slot `1` to slot `2`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3ZeroOldSlot1RealSchwartzWeakFTC
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ZeroOldSlot1RealSchwartzWeakFTC :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Spatial integration by parts from one old first spatial jet to the
corresponding ordered-second jet. -/
theorem h3PreterminalOldSlot1_transport_realSchwartzLineDeriv_integral_eq_neg_slot2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i k : Fin 3) :
    (∫ x : H3FourierPoint3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        ((h3TransportScalarField
          (spatial3.d
            (h3AxisOfFin3 k)
            (loggedVelocityComponent
              u
              (t + (q : ℝ))
              (h3AxisOfFin3 j)))) x)
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
            𝓢(H3FourierPoint3, ℝ)) x)
      ∂volume)
      =
    -
    ∫ x : H3FourierPoint3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        ((h3TransportScalarField
          (spatial3.d
            (h3AxisOfFin3 i)
            (spatial3.d
              (h3AxisOfFin3 k)
              (loggedVelocityComponent
                u
                (t + (q : ℝ))
                (h3AxisOfFin3 j))))) x)
        (φ x)
      ∂volume := by
  let u₀ : ScalarField3 :=
    loggedVelocityComponent
      u
      (t + (q : ℝ))
      (h3AxisOfFin3 j)

  let f : ScalarField3 :=
    spatial3.d
      (h3AxisOfFin3 k)
      u₀

  let g : ScalarField3 :=
    spatial3.d
      (h3AxisOfFin3 i)
      f

  let F : H3FourierPoint3 → ℝ :=
    h3TransportScalarField f

  let G : H3FourierPoint3 → ℝ :=
    h3TransportScalarField g

  let v : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 i)

  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  have hAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd q

  have huC3 :
      SpatialC3 u₀ := by
    dsimp only [u₀]
    unfold loggedVelocityComponent
    exact
      hPDE.regularity.velocity_spatial_three
        (t + (q : ℝ))
        hAbs
        (h3AxisOfFin3 j)

  have hfC2 :
      SpatialC2 f := by
    change
      SpatialC2
        (fun y =>
          partialDeriv
            (h3AxisOfFin3 k)
            u₀
            y)

    exact
      SpatialC3.partialDeriv_contDiff_two
        huC3
        (h3AxisOfFin3 k)

  have hfC1 :
      SpatialC1 f := by
    exact
      hfC2.of_le
        (by norm_num)

  have hFderiv :
      ∀ x : H3FourierPoint3,
        HasLineDerivAt ℝ
          F
          (G x)
          x
          v := by
    intro x
    dsimp only [F, G, g, v]
    exact
      h3TransportScalarField_hasLineDerivAt
        hfC1
        (h3AxisOfFin3 i)
        x

  have hφderiv :
      ∀ x : H3FourierPoint3,
        HasLineDerivAt ℝ
          (φ : H3FourierPoint3 → ℝ)
          ((∂_{v} φ :
              𝓢(H3FourierPoint3, ℝ)) x)
          x
          v := by
    intro x
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      (φ.hasFDerivAt x).hasLineDerivAt v

  have hGφ :
      Integrable
        (fun x : H3FourierPoint3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (G x)
            (φ x))
        (volume : Measure H3FourierPoint3) := by
    dsimp only [G, g, f, u₀]
    exact
      h3PreterminalOldSlot2_transport_mul_realSchwartz_integrable
        hNS ht hEnd hTail q φ j i k

  have hFDφ :
      Integrable
        (fun x : H3FourierPoint3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (F x)
            ((∂_{v} φ :
                𝓢(H3FourierPoint3, ℝ)) x))
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F, v, f, u₀]
    exact
      h3PreterminalOldSlot1_transport_mul_realSchwartzLineDeriv_integrable
        hNS ht hEnd hTail q φ j i k

  have hFφ :
      Integrable
        (fun x : H3FourierPoint3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (F x)
            (φ x))
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F, f, u₀]
    exact
      h3PreterminalOldSlot1_transport_mul_realSchwartz_integrable
        hNS ht hEnd hTail q φ j k

  have hIBP :
      (∫ x : H3FourierPoint3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (F x)
          ((∂_{v} φ :
              𝓢(H3FourierPoint3, ℝ)) x)
        ∂volume)
        =
      -
      ∫ x : H3FourierPoint3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (G x)
          (φ x)
        ∂volume := by
    exact
      integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
        (B := ContinuousLinearMap.lsmul ℝ ℝ)
        hGφ
        hFDφ
        hFφ
        (fun x _ => hFderiv x)
        (fun x _ => hφderiv x)

  simpa only [F, G, f, g, u₀, v] using hIBP

/-- The same spatial integration-by-parts identity oriented with the ordered
second old spatial jet on the left. -/
theorem h3PreterminalOldSlot2_transport_realSchwartz_integral_eq_neg_slot1LineDeriv
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i k : Fin 3) :
    (∫ x : H3FourierPoint3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        ((h3TransportScalarField
          (spatial3.d
            (h3AxisOfFin3 i)
            (spatial3.d
              (h3AxisOfFin3 k)
              (loggedVelocityComponent
                u
                (t + (q : ℝ))
                (h3AxisOfFin3 j))))) x)
        (φ x)
      ∂volume)
      =
    -
    ∫ x : H3FourierPoint3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        ((h3TransportScalarField
          (spatial3.d
            (h3AxisOfFin3 k)
            (loggedVelocityComponent
              u
              (t + (q : ℝ))
              (h3AxisOfFin3 j)))) x)
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
            𝓢(H3FourierPoint3, ℝ)) x)
      ∂volume := by
  have h :=
    h3PreterminalOldSlot1_transport_realSchwartzLineDeriv_integral_eq_neg_slot2
      hNS ht hEnd hTail q φ j i k

  linarith

end

end Euclidean
end Bridge
end PrimeTensor
