import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldSlot0RealSchwartzWeakIntegral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Pressure-free slot0 real-Schwartz spatial FTC / integration by parts

`OldSlot0RealSchwartzWeakIntegral` isolated the three `L¹` products required by
Mathlib's line-derivative integration-by-parts theorem.

At one retained elapsed snapshot, let

    f(x) = u_j(t+q,x)

and let `g = ∂ᵢ f`.  The old preterminal regularity gives spatial `C³`, hence
spatial `C¹`, so after transport to the Euclidean Fourier carrier we have the
genuine coordinate line derivative

    D_{e_i} F = G.

For every real Schwartz test `φ`, Mathlib's integration-by-parts theorem then
gives

    ∫ F (∂ᵢ φ) = - ∫ G φ,

equivalently

    ∫ G φ = - ∫ F (∂ᵢ φ).

This is the pressure-free spatial weak-derivative identity needed to transfer
the already-proved slot0 Schwartz continuity to the first spatial jet.  No
pressure, temporal derivative, endpoint continuity, or mild equation enters.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3ZeroOldSlot0RealSchwartzWeakFTC
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ZeroOldSlot0RealSchwartzWeakFTC :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Spatial integration by parts on the Euclidean carrier for one retained old
velocity coordinate and one real Schwartz test. -/
theorem h3PreterminalOldSlot0_transport_realSchwartzLineDeriv_integral_eq_neg_slot1
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i : Fin 3) :
    (∫ x : H3FourierPoint3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        ((h3TransportScalarField
          (loggedVelocityComponent
            u
            (t + (q : ℝ))
            (h3AxisOfFin3 j))) x)
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
            (loggedVelocityComponent
              u
              (t + (q : ℝ))
              (h3AxisOfFin3 j)))) x)
        (φ x)
      ∂volume := by
  let f : ScalarField3 :=
    loggedVelocityComponent
      u
      (t + (q : ℝ))
      (h3AxisOfFin3 j)

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

  have hfC3 :
      SpatialC3 f := by
    dsimp only [f]
    unfold loggedVelocityComponent
    exact
      hPDE.regularity.velocity_spatial_three
        (t + (q : ℝ))
        hAbs
        (h3AxisOfFin3 j)

  have hfC1 :
      SpatialC1 f :=
    SpatialC3.toSpatialC1 hfC3

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
    dsimp only [G, g, f]
    exact
      h3PreterminalOldSlot1_transport_mul_realSchwartz_integrable
        hNS ht hEnd hTail q φ j i

  have hFDφ :
      Integrable
        (fun x : H3FourierPoint3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (F x)
            ((∂_{v} φ :
                𝓢(H3FourierPoint3, ℝ)) x))
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F, v, f]
    exact
      h3PreterminalOldSlot0_transport_mul_realSchwartzLineDeriv_integrable
        hNS ht hEnd hTail q φ j i

  have hFφ :
      Integrable
        (fun x : H3FourierPoint3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (F x)
            (φ x))
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F, f]
    exact
      h3PreterminalOldSlot0_transport_mul_realSchwartz_integrable
        hNS ht hEnd hTail q φ j

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

  simpa only [F, G, f, g, v] using hIBP

/-- The same spatial integration-by-parts identity oriented with the first old
spatial jet on the left. -/
theorem h3PreterminalOldSlot1_transport_realSchwartz_integral_eq_neg_slot0LineDeriv
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j i : Fin 3) :
    (∫ x : H3FourierPoint3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        ((h3TransportScalarField
          (spatial3.d
            (h3AxisOfFin3 i)
            (loggedVelocityComponent
              u
              (t + (q : ℝ))
              (h3AxisOfFin3 j)))) x)
        (φ x)
      ∂volume)
      =
    -
    ∫ x : H3FourierPoint3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        ((h3TransportScalarField
          (loggedVelocityComponent
            u
            (t + (q : ℝ))
            (h3AxisOfFin3 j))) x)
        ((∂_{h3FourierAxisDirection (h3AxisOfFin3 i)} φ :
            𝓢(H3FourierPoint3, ℝ)) x)
      ∂volume := by
  have h :=
    h3PreterminalOldSlot0_transport_realSchwartzLineDeriv_integral_eq_neg_slot1
      hNS ht hEnd hTail q φ j i

  linarith

end

end Euclidean
end Bridge
end PrimeTensor
