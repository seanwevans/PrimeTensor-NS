import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Snapshot

/-!
# Zeroth-order endpoint continuity: old snapshot nonlinear reconstruction

Each old preterminal elapsed slice is now known to be:

* the canonical weighted H³ spectral encoding of the old velocity;
* physically realizable;
* raw-Fourier divergence-free;
* pointwise equal, after canonical real reconstruction, to the old logged
  velocity.

The generic nonlinear reconstruction theorem therefore applies snapshot by
snapshot.  This file records the endpoint-independent identity

    Re F⁻¹[div̂(U ⊗ U)]ᵢ
      =
    ((u · ∇)u)ᵢ

for the old logged velocity at absolute time `t+q`.

The proof uses a constant auxiliary spectral path containing the one snapshot.
That path is only a representation device for the already-proved generic
bridge; no time continuity or evolution statement is assumed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldAdvection
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The unprojected raw nonlinear Fourier term of an old canonical H³ snapshot
reconstructs pointwise to the old physical advection component. -/
theorem h3PreterminalTailCanonicalRawOuterDivergence_fourierInv_re_eq_old_advection
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (x : Point3) :
    let U : H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q
    (FourierTransformInv.fourierInv
      (h3RawFinOuterProductDivergence U U i)
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
      =
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3
      (logSpaceTimeVectorField u)
      (t + (q : ℝ))
      x).component
        (h3AxisOfFin3 i) := by
  dsimp only

  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  let W : ℝ → H3SpectralFinVectorState :=
    fun _ => U

  have hReal :
      H3SpectralVelocityRealizable (W 0) := by
    dsimp only [W, U]
    exact
      h3PreterminalTailCanonicalSpectralStateOnElapsed_realizable
        hNS ht hEnd hTail q

  have hDiv :
      H3SpectralFinRawDivergenceFree (W 0) := by
    dsimp only [W, U]
    exact
      h3PreterminalTailCanonicalSpectralStateOnElapsed_rawDivergenceFree
        hNS ht hEnd hTail q

  have hVelocity :
      h3SpectralRealVelocityOfPath W 0
        =
      logSpaceTimeVectorField u (t + (q : ℝ)) := by
    funext y

    apply tensor_eq_of_component_eq

    intro a

    let k : Fin 3 :=
      h3ClassicalizationFinOfAxis a

    have hAxis :
        h3AxisOfFin3 k = a := by
      dsimp only [k]
      cases a with
      | first =>
          rfl
      | next a =>
          cases a with
          | first =>
              rfl
          | next a =>
              cases a with
              | first =>
                  rfl

    have hComponent :=
      h3PreterminalTailCanonicalSpectralStateOnElapsed_component_eq_old
        hNS ht hEnd hTail q k

    have hy := congrFun hComponent y

    change
      h3SpectralVelocityRealC1RepresentativeOnPoint3
          (W 0)
          (h3ClassicalizationFinOfAxis a)
          y
        =
      (logSpaceTimeVectorField
        u
        (t + (q : ℝ))
        y).component a

    dsimp only [W, U, k] at hy ⊢

    calc
      h3SpectralVelocityRealC1RepresentativeOnPoint3
          (h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q)
          (h3ClassicalizationFinOfAxis a)
          y
          =
        loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 (h3ClassicalizationFinOfAxis a))
          y := hy
      _ =
        loggedVelocityComponent
          u
          (t + (q : ℝ))
          a
          y := by
        exact congrArg
          (fun j : PrimeTensor.Axis Depth.three =>
            loggedVelocityComponent u (t + (q : ℝ)) j y)
          hAxis
      _ =
        (logSpaceTimeVectorField
          u
          (t + (q : ℝ))
          y).component a := by
        rfl

  have hAdvection :
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (h3SpectralRealVelocityOfPath W)
        0
        x).component
          (h3AxisOfFin3 i)
        =
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (logSpaceTimeVectorField u)
        (t + (q : ℝ))
        x).component
          (h3AxisOfFin3 i) := by
    unfold PrimeTensor.Bridge.RealFluid.advection

    change
      PrimeTensor.Axis.fold
          (· + ·)
          Depth.three
          (fun a =>
            ((h3SpectralRealVelocityOfPath W) 0 x).component a *
              spatial3.d
                a
                (fun y =>
                  ((h3SpectralRealVelocityOfPath W) 0 y).component
                    (h3AxisOfFin3 i))
                x)
        =
      PrimeTensor.Axis.fold
          (· + ·)
          Depth.three
          (fun a =>
            ((logSpaceTimeVectorField u) (t + (q : ℝ)) x).component a *
              spatial3.d
                a
                (fun y =>
                  ((logSpaceTimeVectorField u) (t + (q : ℝ)) y).component
                    (h3AxisOfFin3 i))
                x)

    rw [hVelocity]

  have hGeneric :=
    h3RawFinOuterProductDivergence_fourierInv_re_eq_advection_of_realizable_of_rawDivergenceFree
      W 0 hReal hDiv i x

  calc
    (FourierTransformInv.fourierInv
      (h3RawFinOuterProductDivergence U U i)
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
        =
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (h3SpectralRealVelocityOfPath W)
        0
        x).component
          (h3AxisOfFin3 i) := by
      simpa only [W] using hGeneric
    _ =
      (PrimeTensor.Bridge.RealFluid.advection
        spatial3
        (logSpaceTimeVectorField u)
        (t + (q : ℝ))
        x).component
          (h3AxisOfFin3 i) :=
      hAdvection

end

end Euclidean
end Bridge
end PrimeTensor
