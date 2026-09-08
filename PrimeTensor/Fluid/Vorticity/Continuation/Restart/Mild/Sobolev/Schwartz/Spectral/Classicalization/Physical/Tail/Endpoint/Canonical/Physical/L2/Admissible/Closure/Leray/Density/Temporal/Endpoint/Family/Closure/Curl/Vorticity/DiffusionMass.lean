import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.AdvectionMass
import PrimeTensor.Bridge.Euclidean.Curl.Laplacian.X

/-!
# Compact-test mass bound for the differentiated endpoint Laplacian

The nonlinear advection side is now closed.  The remaining linear part of the
pressure-free vorticity RHS contains one spatial derivative of one componentwise
Laplacian.

For a spatially `C³` component,

    ∂ₐ Δuⱼ
      =
    ∂ₐ∂x∂x uⱼ
      + (∂ₐ∂y∂y uⱼ + ∂ₐ∂z∂z uⱼ).

Every term is an order-three velocity derivative.  `SquareBound` already gives
the common endpoint square ceiling `2E`, while `Cauchy` converts that square
bound into a compact-test spatial mass bound.

This file packages the order-three weak-test estimate and then sums the three
Laplacian terms.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EndpointCurlVorticityDiffusionMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3EndpointCurlVorticityDiffusionMass :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A compact weak test times one third-order old-velocity derivative is
integrable at every endpoint slice. -/
theorem integrable_weakTestNorm_mul_norm_loggedVelocityComponent_spatial_d3_endpoint
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau)
    (a b c j : PrimeTensor.Axis Depth.three) :
    Integrable
      (fun x : Point3 =>
        ‖ψ x‖ *
          ‖spatial3.d
              a
              (spatial3.d
                b
                (spatial3.d
                  c
                  (loggedVelocityComponent
                    u (t + (q : ℝ)) j)))
              x‖)
      (volume : Measure Point3) := by
  have hs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith [ht.1, q.2.1]
    · linarith [hEnd, q.2.2]

  have hMeas :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS hs

  have hj := hMeas j
  dsimp only at hj

  let f : ScalarField3 :=
    spatial3.d
      a
      (spatial3.d
        b
        (spatial3.d
          c
          (loggedVelocityComponent
            u (t + (q : ℝ)) j)))

  have hfMeas :
      AEStronglyMeasurable
        f
        (volume : Measure Point3) := by
    dsimp only [f]
    exact hj.2.2.2 a b c

  have hBound :
      SpatialL2SquareBound
        f
        (2 * E) := by
    dsimp only [f]
    exact
      loggedVelocityComponent_spatial_d3_spatialL2SquareBound_endpoint_twoE
        hEnd hE hTail q a b c j

  have hψTwo :
      MemLp
        (ψ : Point3 → ℝ)
        2
        (volume : Measure Point3) :=
    ψ.continuous.memLp_of_hasCompactSupport
      ψ.hasCompactSupport

  have hfTwo :
      MemLp
        f
        2
        (volume : Measure Point3) :=
    memLp_two_of_spatialL2SquareBound
      hfMeas hBound

  have hInt :
      Integrable
        (fun x : Point3 =>
          ‖ψ x‖ * ‖f x‖)
        (volume : Measure Point3) :=
    MemLp.integrable_mul
      hψTwo.norm
      hfTwo.norm

  simpa only [f] using hInt

/-- Cauchy--Schwarz bound for one third-order old-velocity derivative. -/
theorem integral_weakTestNorm_mul_norm_loggedVelocityComponent_spatial_d3_le_endpointH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau)
    (a b c j : PrimeTensor.Axis Depth.three) :
    (∫ x : Point3,
        ‖ψ x‖ *
          ‖spatial3.d
              a
              (spatial3.d
                b
                (spatial3.d
                  c
                  (loggedVelocityComponent
                    u (t + (q : ℝ)) j)))
              x‖
      ∂volume)
      ≤
    h3WeakTestFunctionL2Mass ψ *
      (2 * E) ^ (1 / (2 : ℝ)) := by
  have hs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith [ht.1, q.2.1]
    · linarith [hEnd, q.2.2]

  have hMeas :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS hs

  have hj := hMeas j
  dsimp only at hj

  let f : ScalarField3 :=
    spatial3.d
      a
      (spatial3.d
        b
        (spatial3.d
          c
          (loggedVelocityComponent
            u (t + (q : ℝ)) j)))

  have hfMeas :
      AEStronglyMeasurable
        f
        (volume : Measure Point3) := by
    dsimp only [f]
    exact hj.2.2.2 a b c

  have hBound :
      SpatialL2SquareBound
        f
        (2 * E) := by
    dsimp only [f]
    exact
      loggedVelocityComponent_spatial_d3_spatialL2SquareBound_endpoint_twoE
        hEnd hE hTail q a b c j

  simpa only [f] using
    integral_weakTest_norm_mul_norm_le_of_spatialL2SquareBound
      ψ hfMeas hBound

/-- Uniform compact-test spatial mass bound for one differentiated
componentwise Laplacian. -/
theorem integral_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_le_endpointH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau)
    (a j : PrimeTensor.Axis Depth.three) :
    (∫ x : Point3,
        ‖ψ x‖ *
          ‖spatial3.d
              a
              (PrimeTensor.Bridge.RealFluid.laplacian
                spatial3
                (loggedVelocityComponent
                  u (t + (q : ℝ)) j))
              x‖
      ∂volume)
      ≤
    h3WeakTestFunctionL2Mass ψ *
        (2 * E) ^ (1 / (2 : ℝ))
      +
    (
      h3WeakTestFunctionL2Mass ψ *
          (2 * E) ^ (1 / (2 : ℝ))
        +
      h3WeakTestFunctionL2Mass ψ *
          (2 * E) ^ (1 / (2 : ℝ))
    ) := by
  have hs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith [ht.1, q.2.1]
    · linarith [hEnd, q.2.2]

  let pOld : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  let f : ScalarField3 :=
    loggedVelocityComponent
      u (t + (q : ℝ)) j

  have hf3 : SpatialC3 f := by
    dsimp only [f]
    change
      SpatialC3
        (fun x : Point3 =>
          (logSpaceTimeVectorField
            u (t + (q : ℝ)) x).component j)
    exact
      hPDE.regularity.velocity_spatial_three
        (t + (q : ℝ)) hs j

  let tx : ScalarField3 :=
    spatial3.d
      a
      (spatial3.d
        xAxis
        (spatial3.d xAxis f))

  let ty : ScalarField3 :=
    spatial3.d
      a
      (spatial3.d
        yAxis
        (spatial3.d yAxis f))

  let tz : ScalarField3 :=
    spatial3.d
      a
      (spatial3.d
        zAxis
        (spatial3.d zAxis f))

  let diff : ScalarField3 :=
    spatial3.d
      a
      (PrimeTensor.Bridge.RealFluid.laplacian
        spatial3 f)

  have hDiffEq :
      diff =
        fun x =>
          tx x + (ty x + tz x) := by
    funext x
    dsimp only [diff, tx, ty, tz]
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_laplacian3
        hf3 x a

  have hMeas :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS hs

  have hj := hMeas j
  dsimp only at hj

  have htxMeas :
      AEStronglyMeasurable
        tx
        (volume : Measure Point3) := by
    dsimp only [tx, f]
    exact hj.2.2.2 a xAxis xAxis

  have htyMeas :
      AEStronglyMeasurable
        ty
        (volume : Measure Point3) := by
    dsimp only [ty, f]
    exact hj.2.2.2 a yAxis yAxis

  have htzMeas :
      AEStronglyMeasurable
        tz
        (volume : Measure Point3) := by
    dsimp only [tz, f]
    exact hj.2.2.2 a zAxis zAxis

  have hDiffMeas :
      AEStronglyMeasurable
        diff
        (volume : Measure Point3) := by
    rw [hDiffEq]
    exact
      htxMeas.add
        (htyMeas.add htzMeas)

  let gx : Point3 → ℝ :=
    fun x => ‖ψ x‖ * ‖tx x‖

  let gy : Point3 → ℝ :=
    fun x => ‖ψ x‖ * ‖ty x‖

  let gz : Point3 → ℝ :=
    fun x => ‖ψ x‖ * ‖tz x‖

  have hgxInt :
      Integrable gx (volume : Measure Point3) := by
    dsimp only [gx, tx, f]
    exact
      integrable_weakTestNorm_mul_norm_loggedVelocityComponent_spatial_d3_endpoint
        hNS ht hEnd hE hTail
        ψ q a xAxis xAxis j

  have hgyInt :
      Integrable gy (volume : Measure Point3) := by
    dsimp only [gy, ty, f]
    exact
      integrable_weakTestNorm_mul_norm_loggedVelocityComponent_spatial_d3_endpoint
        hNS ht hEnd hE hTail
        ψ q a yAxis yAxis j

  have hgzInt :
      Integrable gz (volume : Measure Point3) := by
    dsimp only [gz, tz, f]
    exact
      integrable_weakTestNorm_mul_norm_loggedVelocityComponent_spatial_d3_endpoint
        hNS ht hEnd hE hTail
        ψ q a zAxis zAxis j

  let major : Point3 → ℝ :=
    fun x =>
      gx x + (gy x + gz x)

  have hMajorInt :
      Integrable major (volume : Measure Point3) := by
    dsimp only [major]
    exact hgxInt.add (hgyInt.add hgzInt)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          ‖ψ x‖ * ‖diff x‖)
        (volume : Measure Point3) :=
    ψ.continuous.aestronglyMeasurable.norm.mul
      hDiffMeas.norm

  have hPoint :
      ∀ x : Point3,
        ‖ψ x‖ * ‖diff x‖
          ≤
        major x := by
    intro x
    have hNorm :
        ‖diff x‖
          ≤
        ‖tx x‖ + (‖ty x‖ + ‖tz x‖) := by
      rw [hDiffEq]
      exact
        (norm_add_le
          (tx x)
          (ty x + tz x)).trans
          (add_le_add
            (le_refl ‖tx x‖)
            (norm_add_le (ty x) (tz x)))

    have hWeighted :=
      mul_le_mul_of_nonneg_left
        hNorm
        (norm_nonneg (ψ x))

    dsimp only [major, gx, gy, gz]
    simpa only [mul_add] using hWeighted

  have hTargetInt :
      Integrable
        (fun x : Point3 =>
          ‖ψ x‖ * ‖diff x‖)
        (volume : Measure Point3) := by
    refine
      hMajorInt.mono'
        hTargetMeas
        (Filter.Eventually.of_forall ?_)
    intro x
    rw [
      Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg
          (norm_nonneg (ψ x))
          (norm_nonneg (diff x)))
    ]
    exact hPoint x

  have hIntegralLe :
      (∫ x : Point3,
          ‖ψ x‖ * ‖diff x‖
        ∂volume)
        ≤
      ∫ x : Point3, major x ∂volume :=
    integral_mono_ae
      hTargetInt
      hMajorInt
      (Filter.Eventually.of_forall hPoint)

  have hOuter :
      (∫ x : Point3,
          gx x + (gy x + gz x)
        ∂volume)
        =
      (∫ x : Point3, gx x ∂volume)
        +
      (∫ x : Point3, gy x + gz x ∂volume) := by
    exact
      integral_add
        hgxInt
        (hgyInt.add hgzInt)

  have hYZ :
      (∫ x : Point3, gy x + gz x ∂volume)
        =
      (∫ x : Point3, gy x ∂volume)
        +
      (∫ x : Point3, gz x ∂volume) := by
    exact integral_add hgyInt hgzInt

  have hMajorIntegral :
      (∫ x : Point3, major x ∂volume)
        =
      (∫ x : Point3, gx x ∂volume)
        +
      (
        (∫ x : Point3, gy x ∂volume)
          +
        (∫ x : Point3, gz x ∂volume)
      ) := by
    dsimp only [major]
    calc
      (∫ x : Point3,
          gx x + (gy x + gz x)
        ∂volume)
          =
        (∫ x : Point3, gx x ∂volume)
          +
        (∫ x : Point3, gy x + gz x ∂volume) :=
        hOuter
      _ =
        (∫ x : Point3, gx x ∂volume)
          +
        (
          (∫ x : Point3, gy x ∂volume)
            +
          (∫ x : Point3, gz x ∂volume)
        ) := by rw [hYZ]

  have hBx :
      (∫ x : Point3, gx x ∂volume)
        ≤
      h3WeakTestFunctionL2Mass ψ *
        (2 * E) ^ (1 / (2 : ℝ)) := by
    dsimp only [gx, tx, f]
    exact
      integral_weakTestNorm_mul_norm_loggedVelocityComponent_spatial_d3_le_endpointH3
        hNS ht hEnd hE hTail
        ψ q a xAxis xAxis j

  have hBy :
      (∫ x : Point3, gy x ∂volume)
        ≤
      h3WeakTestFunctionL2Mass ψ *
        (2 * E) ^ (1 / (2 : ℝ)) := by
    dsimp only [gy, ty, f]
    exact
      integral_weakTestNorm_mul_norm_loggedVelocityComponent_spatial_d3_le_endpointH3
        hNS ht hEnd hE hTail
        ψ q a yAxis yAxis j

  have hBz :
      (∫ x : Point3, gz x ∂volume)
        ≤
      h3WeakTestFunctionL2Mass ψ *
        (2 * E) ^ (1 / (2 : ℝ)) := by
    dsimp only [gz, tz, f]
    exact
      integral_weakTestNorm_mul_norm_loggedVelocityComponent_spatial_d3_le_endpointH3
        hNS ht hEnd hE hTail
        ψ q a zAxis zAxis j

  rw [hMajorIntegral] at hIntegralLe

  dsimp only [diff, f] at hIntegralLe

  exact
    hIntegralLe.trans
      (by
        gcongr)

end

end Euclidean
end Bridge
end PrimeTensor
