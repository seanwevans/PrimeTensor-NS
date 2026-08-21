import PrimeTensor.Bridge.EuclideanCurlLinear

/-!
# Third-order Euclidean partial commutation

The next linear curl identity,

    curl (Δu) = Δ(curl u),

requires commuting one coordinate derivative past a pure second derivative.
For a scalar field this is

    ∂ₐ ∂ᵢ ∂ᵢ f = ∂ᵢ ∂ᵢ ∂ₐ f.

Rather than formalizing symmetry of a third Fréchet derivative directly, we
reuse the already-proved `C²` Schwarz theorem twice.

The only new regularity fact needed is that if `f` is spatially `C³`, then each
first coordinate-partial field `∂ᵢ f` is spatially `C²`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable local instance axisFintypeThirdPartials
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-- Spatial `C³` regularity implies spatial `C²` regularity. -/
theorem SpatialC3.toSpatialC2
    {dim : Depth}
    {f :
      PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC3 f) :
    SpatialC2 f := by

  unfold SpatialC3 at hf
  unfold SpatialC2

  exact
    hf.of_le
      (by norm_num)

/--
For a spatially `C³` scalar field, the Fréchet derivative map is `C²`.
-/
theorem SpatialC3.fderiv_contDiff_two
    {dim : Depth}
    {f :
      PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC3 f) :
    ContDiff ℝ 2
      (fderiv ℝ f) := by

  unfold SpatialC3 at hf

  exact
    hf.fderiv_right
      (by norm_num)

/--
For a spatially `C³` field, the first coordinate-partial field has the same
global Fréchet representation already proved at `C²`.
-/
theorem SpatialC3.partialDeriv_fun_eq
    {dim : Depth}
    {f :
      PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC3 f)
    (j : PrimeTensor.Axis dim) :
    (
      fun y =>
        partialDeriv j f y
    )
      =
    (
      fun y =>
        (fderiv ℝ f y)
          (axisDirection j)
    ) := by

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_fun_eq
      (
        PrimeTensor.Bridge.Euclidean.SpatialC3.toSpatialC2
          hf
      )
      j

/--
Every first coordinate-partial field of a spatially `C³` scalar field is
spatially `C²`.
-/
theorem SpatialC3.partialDeriv_contDiff_two
    {dim : Depth}
    {f :
      PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC3 f)
    (j : PrimeTensor.Axis dim) :
    SpatialC2
      (
        fun y =>
          partialDeriv j f y
      ) := by

  change
    ContDiff ℝ 2
      (
        fun y =>
          partialDeriv j f y
      )

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_fun_eq
      hf j
  ]

  exact
    (
      PrimeTensor.Bridge.Euclidean.SpatialC3.fderiv_contDiff_two
        hf
    ).clm_apply
      contDiff_const

/--
A coordinate derivative commutes through a pure second coordinate derivative
of a spatially `C³` scalar field:

    ∂ₐ ∂ᵢ² f = ∂ᵢ² ∂ₐ f.
-/
theorem SpatialC3.spatial_d_square_comm
    {dim : Depth}
    {f :
      PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC3 f)
    (x : PrimeTensor.Point ℝ dim)
    (a i : PrimeTensor.Axis dim) :
    (spatial dim).d a
        (
          (spatial dim).d i
            (
              (spatial dim).d i f
            )
        )
        x
      =
    (spatial dim).d i
        (
          (spatial dim).d i
            (
              (spatial dim).d a f
            )
        )
        x := by

  have hf2 :
      SpatialC2 f :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.toSpatialC2
      hf

  have hPartial :
      SpatialC2
        (
          (spatial dim).d i f
        ) := by

    change
      SpatialC2
        (
          fun y =>
            partialDeriv i f y
        )

    exact
      PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
        hf i

  have hInner :
      (spatial dim).d a
          (
            (spatial dim).d i f
          )
        =
      (spatial dim).d i
          (
            (spatial dim).d a f
          ) := by

    funext y

    exact
      PrimeTensor.Bridge.Euclidean.SpatialC2.spatial_d_comm
        hf2 y a i

  calc
    (spatial dim).d a
          (
            (spatial dim).d i
              (
                (spatial dim).d i f
              )
          )
          x
        =
      (spatial dim).d i
          (
            (spatial dim).d a
              (
                (spatial dim).d i f
              )
          )
          x :=
      PrimeTensor.Bridge.Euclidean.SpatialC2.spatial_d_comm
        hPartial x a i

    _ =
      (spatial dim).d i
          (
            (spatial dim).d i
              (
                (spatial dim).d a f
              )
          )
          x := by
      rw [hInner]

namespace VorticitySolution3

/--
Every velocity component of a vorticity-regular solution satisfies the
third-order commutation identity needed for `curl (Δu) = Δ(curl u)`.
-/
theorem velocity_spatial_d_square_comm
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3)
    (k a i :
      PrimeTensor.Axis Depth.three) :
    spatial3.d a
        (
          spatial3.d i
            (
              spatial3.d i
                (
                  fun y =>
                    (s.velocity t y).component k
                )
            )
        )
        x
      =
    spatial3.d i
        (
          spatial3.d i
            (
              spatial3.d a
                (
                  fun y =>
                    (s.velocity t y).component k
                )
            )
        )
        x := by

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_square_comm
      (
        s.regularity.velocity_spatial_three
          t k
      )
      x a i

end VorticitySolution3

end Euclidean
end Bridge
end PrimeTensor
