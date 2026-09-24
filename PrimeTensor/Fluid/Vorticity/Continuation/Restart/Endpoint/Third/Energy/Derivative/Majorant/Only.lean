import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Derivative.Reduced.Domination
import PrimeTensor.Fluid.Vorticity.H3.Energy.Class.Split.Regularity

/-!
# Reduce the H³ dominated-differentiation frontier to local integrable majorants

`EnergyDerivativeReducedDomination` removed the nearby-time square
measurability assumptions because spatial `C³` already supplies them.

The derivative-product measurability assumptions are redundant as well.
Inside `PreterminalH3EnergyClass`:

* every spatial H³ jet factor is continuous;
* Navier--Stokes identifies the temporal jet factors with the momentum RHS;
* the high-order split-regularity theorem makes the order-one and order-two
  momentum pieces `SpatialC1`;
* one final spatial derivative of those `SpatialC1` fields is continuous.

Thus every product

    2 D^α u(t,x) D^α ∂ₜu(t,x),  |α| ≤ 3,

is automatically strongly measurable.

After this file the dominated-differentiation frontier contains only the
genuine whole-space hypothesis: a locally uniform integrable majorant for the
pointwise time derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EnergyDerivativeMajorantOnly
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Small continuity helpers -/

private theorem spatialC1_spatial_d_continuous_majorantOnly
    {f : ScalarField3}
    (hf : SpatialC1 f)
    (i : PrimeTensor.Axis Depth.three) :
    Continuous (spatial3.d i f) := by
  have hfun :
      (fun x : Point3 => partialDeriv i f x)
        =
      (fun x : Point3 =>
        (fderiv ℝ f x) (axisDirection i)) := by
    funext x
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC1.partialDeriv_eq_fderiv_axisDirection
        hf x i

  change Continuous (fun x : Point3 => partialDeriv i f x)
  rw [hfun]

  have hfd :
      ContDiff ℝ 0 (fderiv ℝ f) := by
    unfold SpatialC1 at hf
    exact hf.fderiv_right (by norm_num)

  exact
    (hfd.clm_apply contDiff_const).continuous

private theorem spatialC1_of_spatialC3_majorantOnly
    {f : ScalarField3}
    (hf : SpatialC3 f) :
    SpatialC1 f := by
  unfold SpatialC3 at hf
  unfold SpatialC1
  exact hf.of_le (by norm_num)

private theorem firstPartial_spatialC1_of_spatialC3_majorantOnly
    {f : ScalarField3}
    (hf : SpatialC3 f)
    (i : PrimeTensor.Axis Depth.three) :
    SpatialC1 (spatial3.d i f) := by
  have h2 :
      SpatialC2
        (fun x : Point3 => partialDeriv i f x) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hf i
  change SpatialC1 (fun x : Point3 => partialDeriv i f x)
  exact h2.of_le (by norm_num)

private theorem secondPartial_spatialC1_of_spatialC3_majorantOnly
    {f : ScalarField3}
    (hf : SpatialC3 f)
    (i k : PrimeTensor.Axis Depth.three) :
    SpatialC1 (spatial3.d i (spatial3.d k f)) := by
  have hk2 :
      SpatialC2 (spatial3.d k f) := by
    change SpatialC2 (fun x : Point3 => partialDeriv k f x)
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
        hf k
  exact
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hk2 i

/-! ## Automatic continuity of the order-zero momentum RHS -/

private theorem momentumRHS0Component_continuous_of_energyClass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : PrimeTensor.Axis Depth.three) :
    ∃ p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three,
      ∃ hPDE :
        PreterminalNavierStokes3
          (logSpaceTimeVectorField u) p T,
        Continuous
          (momentumRHS0Component
            (logSpaceTimeVectorField u) p t j) := by
  rcases hClass.pressure_witness with
    ⟨p, hPDE, hp4⟩

  have htPre :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  have htTail :
      t ∈ Set.Ico a T :=
    ⟨ht.1.le, ht.2⟩

  let f : ScalarField3 :=
    loggedVelocityComponent u t j

  have hf3 : SpatialC3 f := by
    dsimp only [f]
    change
      SpatialC3
        (fun x : Point3 =>
          (logSpaceTimeVectorField u t x).component j)
    exact
      hPDE.regularity.velocity_spatial_three
        t htPre j

  have hxx :
      Continuous
        (spatial3.d xAxis (spatial3.d xAxis f)) :=
    (hClass.velocity_spatial_five
      t htTail j xAxis xAxis).continuous

  have hyy :
      Continuous
        (spatial3.d yAxis (spatial3.d yAxis f)) :=
    (hClass.velocity_spatial_five
      t htTail j yAxis yAxis).continuous

  have hzz :
      Continuous
        (spatial3.d zAxis (spatial3.d zAxis f)) :=
    (hClass.velocity_spatial_five
      t htTail j zAxis zAxis).continuous

  have hLap :
      Continuous
        (PrimeTensor.Bridge.RealFluid.laplacian
          spatial3 f) := by
    have hEq :
        PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 f
          =
        fun x : Point3 =>
          spatial3.d xAxis
              (spatial3.d xAxis f) x
            +
          (spatial3.d yAxis
              (spatial3.d yAxis f) x
            +
           spatial3.d zAxis
              (spatial3.d zAxis f) x) := by
      funext x
      exact laplacian3_eq f x
    rw [hEq]
    exact hxx.add (hyy.add hzz)

  have hBaseC1
      (m : PrimeTensor.Axis Depth.three) :
      SpatialC1
        (fun x : Point3 =>
          (logSpaceTimeVectorField u t x).component m) :=
    spatialC1_of_spatialC3_majorantOnly
      (hPDE.regularity.velocity_spatial_three
        t htPre m)

  have hFirstC1
      (m r : PrimeTensor.Axis Depth.three) :
      SpatialC1
        (spatial3.d r
          (fun x : Point3 =>
            (logSpaceTimeVectorField u t x).component m)) :=
    firstPartial_spatialC1_of_spatialC3_majorantOnly
      (hPDE.regularity.velocity_spatial_three
        t htPre m)
      r

  have hTransport :
      Continuous
        (fun x : Point3 =>
          realAdvectionComponent
            (logSpaceTimeVectorField u)
            t x j) := by
    unfold realAdvectionComponent
    exact
      ((hBaseC1 xAxis).continuous.mul
        (hFirstC1 j xAxis).continuous).add
        (((hBaseC1 yAxis).continuous.mul
            (hFirstC1 j yAxis).continuous).add
          ((hBaseC1 zAxis).continuous.mul
            (hFirstC1 j zAxis).continuous))

  have hPressure :
      Continuous (spatial3.d j (p t)) :=
    (hp4 t htTail j).continuous

  refine ⟨p, hPDE, ?_⟩

  unfold momentumRHS0Component
  dsimp only [f] at hLap
  exact
    (hLap.sub hTransport).sub hPressure

/-! ## Automatic derivative-product measurability -/

theorem h3Order0_derivativeProduct_aestronglyMeasurable_of_energyClass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : PrimeTensor.Axis Depth.three) :
    AEStronglyMeasurable
      (fun x : Point3 =>
        2 *
          loggedVelocityComponent u t j x *
          loggedVelocityTemporalComponent u t j x)
      (volume : Measure Point3) := by
  rcases
    momentumRHS0Component_continuous_of_energyClass
      hClass ht j
  with
    ⟨p, hPDE, hRHS⟩

  have htPre :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  have hTemporalEq :
      loggedVelocityTemporalComponent u t j
        =
      momentumRHS0Component
        (logSpaceTimeVectorField u)
        p t j :=
    loggedVelocityTemporalComponent_eq_momentumRHS0
      hPDE htPre j

  have hBase :
      Continuous (loggedVelocityComponent u t j) := by
    change
      Continuous
        (fun x : Point3 =>
          (logSpaceTimeVectorField u t x).component j)
    exact
      (hPDE.regularity.velocity_spatial_three
        t htPre j).continuous

  have hTemporal :
      Continuous (loggedVelocityTemporalComponent u t j) := by
    rw [hTemporalEq]
    exact hRHS

  exact
    Continuous.aestronglyMeasurable
      ((continuous_const.mul hBase).mul hTemporal)

theorem h3Order1_derivativeProduct_aestronglyMeasurable_of_energyClass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i : PrimeTensor.Axis Depth.three) :
    AEStronglyMeasurable
      (fun x : Point3 =>
        2 *
          spatial3.d
            i
            (loggedVelocityComponent u t j)
            x *
          spatial3.d
            i
            (loggedVelocityTemporalComponent u t j)
            x)
      (volume : Measure Point3) := by
  rcases
    preterminalH3EnergyClass_produces_splitRegularity
      hClass ht
  with
    ⟨p, hPDE, hRegular⟩

  have htPre :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  have hf3 :
      SpatialC3 (loggedVelocityComponent u t j) := by
    change
      SpatialC3
        (fun x : Point3 =>
          (logSpaceTimeVectorField u t x).component j)
    exact
      hPDE.regularity.velocity_spatial_three
        t htPre j

  have hBase :
      Continuous
        (spatial3.d i
          (loggedVelocityComponent u t j)) :=
    (firstPartial_spatialC1_of_spatialC3_majorantOnly
      hf3 i).continuous

  have hRHS1C1 :
      SpatialC1
        (momentumRHS1Component
          (logSpaceTimeVectorField u)
          p t i j) := by
    rw [momentumRHS1Component_eq_split]
    exact
      (hRegular.1 i j).2.2.1.sub
        (hRegular.1 i j).2.2.2

  have hTemporalEq :
      spatial3.d i
          (loggedVelocityTemporalComponent u t j)
        =
      momentumRHS1Component
        (logSpaceTimeVectorField u)
        p t i j :=
    spatial_d_loggedVelocityTemporalComponent_eq_momentumRHS1
      hPDE htPre i j

  have hTemporal :
      Continuous
        (spatial3.d i
          (loggedVelocityTemporalComponent u t j)) := by
    rw [hTemporalEq]
    exact hRHS1C1.continuous

  exact
    Continuous.aestronglyMeasurable
      ((continuous_const.mul hBase).mul hTemporal)

theorem h3Order2_derivativeProduct_aestronglyMeasurable_of_energyClass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i k : PrimeTensor.Axis Depth.three) :
    AEStronglyMeasurable
      (fun x : Point3 =>
        2 *
          spatial3.d
            i
            (spatial3.d
              k
              (loggedVelocityComponent u t j))
            x *
          spatial3.d
            i
            (spatial3.d
              k
              (loggedVelocityTemporalComponent u t j))
            x)
      (volume : Measure Point3) := by
  rcases
    preterminalH3EnergyClass_produces_splitRegularity
      hClass ht
  with
    ⟨p, hPDE, hRegular⟩

  have htPre :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  have hf3 :
      SpatialC3 (loggedVelocityComponent u t j) := by
    change
      SpatialC3
        (fun x : Point3 =>
          (logSpaceTimeVectorField u t x).component j)
    exact
      hPDE.regularity.velocity_spatial_three
        t htPre j

  have hBase :
      Continuous
        (spatial3.d i
          (spatial3.d k
            (loggedVelocityComponent u t j))) :=
    (secondPartial_spatialC1_of_spatialC3_majorantOnly
      hf3 i k).continuous

  have hRHS2C1 :
      SpatialC1
        (momentumRHS2Component
          (logSpaceTimeVectorField u)
          p t i k j) := by
    rw [
      momentumRHS2Component_eq_split_of_spatialC1
        hRegular i k j
    ]
    exact
      (hRegular.2 i k j).2.2.1.sub
        (hRegular.2 i k j).2.2.2

  have hTemporalEq :
      spatial3.d i
          (spatial3.d k
            (loggedVelocityTemporalComponent u t j))
        =
      momentumRHS2Component
        (logSpaceTimeVectorField u)
        p t i k j :=
    spatial_d2_loggedVelocityTemporalComponent_eq_momentumRHS2
      hPDE htPre i k j

  have hTemporal :
      Continuous
        (spatial3.d i
          (spatial3.d k
            (loggedVelocityTemporalComponent u t j))) := by
    rw [hTemporalEq]
    exact hRHS2C1.continuous

  exact
    Continuous.aestronglyMeasurable
      ((continuous_const.mul hBase).mul hTemporal)

theorem h3Order3_derivativeProduct_aestronglyMeasurable_of_energyClass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i k l : PrimeTensor.Axis Depth.three) :
    AEStronglyMeasurable
      (fun x : Point3 =>
        2 *
          spatial3.d
            i
            (spatial3.d
              k
              (spatial3.d
                l
                (loggedVelocityComponent u t j)))
            x *
          spatial3.d
            i
            (spatial3.d
              k
              (spatial3.d
                l
                (loggedVelocityTemporalComponent u t j)))
            x)
      (volume : Measure Point3) := by
  rcases
    preterminalH3EnergyClass_produces_splitRegularity
      hClass ht
  with
    ⟨p, hPDE, hRegular⟩

  have htPre :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  have hf3 :
      SpatialC3 (loggedVelocityComponent u t j) := by
    change
      SpatialC3
        (fun x : Point3 =>
          (logSpaceTimeVectorField u t x).component j)
    exact
      hPDE.regularity.velocity_spatial_three
        t htPre j

  have hSecond :
      SpatialC1
        (spatial3.d k
          (spatial3.d l
            (loggedVelocityComponent u t j))) :=
    secondPartial_spatialC1_of_spatialC3_majorantOnly
      hf3 k l

  have hBase :
      Continuous
        (spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (loggedVelocityComponent u t j)))) :=
    spatialC1_spatial_d_continuous_majorantOnly
      hSecond i

  have hReg2 :=
    hRegular.2 k l j

  have hDiff3 :
      Continuous
        (momentumDiffusion3Component
          (logSpaceTimeVectorField u)
          t i k l j) := by
    unfold momentumDiffusion3Component
    exact
      spatialC1_spatial_d_continuous_majorantOnly
        hReg2.1 i

  have hTransport3 :
      Continuous
        (momentumTransport3Component
          (logSpaceTimeVectorField u)
          t i k l j) := by
    unfold momentumTransport3Component
    exact
      spatialC1_spatial_d_continuous_majorantOnly
        hReg2.2.1 i

  have hPressure3 :
      Continuous
        (momentumPressure3Component
          p t i k l j) := by
    unfold momentumPressure3Component
    exact
      spatialC1_spatial_d_continuous_majorantOnly
        hReg2.2.2.2 i

  have hRHS3 :
      Continuous
        (momentumRHS3Component
          (logSpaceTimeVectorField u)
          p t i k l j) := by
    rw [
      momentumRHS3Component_eq_split_of_spatialC1
        hRegular i k l j
    ]
    exact
      (hDiff3.sub hTransport3).sub hPressure3

  have hTemporalEq :
      spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (loggedVelocityTemporalComponent u t j)))
        =
      momentumRHS3Component
        (logSpaceTimeVectorField u)
        p t i k l j :=
    spatial_d3_loggedVelocityTemporalComponent_eq_momentumRHS3
      hPDE htPre i k l j

  have hTemporal :
      Continuous
        (spatial3.d i
          (spatial3.d k
            (spatial3.d l
              (loggedVelocityTemporalComponent u t j)))) := by
    rw [hTemporalEq]
    exact hRHS3

  exact
    Continuous.aestronglyMeasurable
      ((continuous_const.mul hBase).mul hTemporal)

/-! ## Majorant-only records -/

structure H3Order0EnergyDerivativeMajorantOnTailAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T t : ℝ) : Type where
  timeSet :
    PrimeTensor.Axis Depth.three → Set ℝ
  bound :
    PrimeTensor.Axis Depth.three → Point3 → ℝ
  timeSet_mem_nhds :
    ∀ j, timeSet j ∈ 𝓝 t
  timeSet_tail :
    ∀ j, timeSet j ⊆ Set.Ioo a T
  derivative_le_bound :
    ∀ j,
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ timeSet j,
          ‖2 *
              loggedVelocityComponent u s j x *
              loggedVelocityTemporalComponent u s j x‖
            ≤ bound j x
  bound_integrable :
    ∀ j,
      Integrable (bound j) (volume : Measure Point3)

structure H3Order1EnergyDerivativeMajorantOnTailAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T t : ℝ) : Type where
  timeSet :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three → Set ℝ
  bound :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        Point3 → ℝ
  timeSet_mem_nhds :
    ∀ j i, timeSet j i ∈ 𝓝 t
  timeSet_tail :
    ∀ j i, timeSet j i ⊆ Set.Ioo a T
  derivative_le_bound :
    ∀ j i,
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ timeSet j i,
          ‖2 *
              spatial3.d i
                (loggedVelocityComponent u s j) x *
              spatial3.d i
                (loggedVelocityTemporalComponent u s j) x‖
            ≤ bound j i x
  bound_integrable :
    ∀ j i,
      Integrable (bound j i) (volume : Measure Point3)

structure H3Order2EnergyDerivativeMajorantOnTailAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T t : ℝ) : Type where
  timeSet :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        PrimeTensor.Axis Depth.three → Set ℝ
  bound :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        PrimeTensor.Axis Depth.three →
          Point3 → ℝ
  timeSet_mem_nhds :
    ∀ j i k, timeSet j i k ∈ 𝓝 t
  timeSet_tail :
    ∀ j i k, timeSet j i k ⊆ Set.Ioo a T
  derivative_le_bound :
    ∀ j i k,
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ timeSet j i k,
          ‖2 *
              spatial3.d i
                (spatial3.d k
                  (loggedVelocityComponent u s j)) x *
              spatial3.d i
                (spatial3.d k
                  (loggedVelocityTemporalComponent u s j)) x‖
            ≤ bound j i k x
  bound_integrable :
    ∀ j i k,
      Integrable (bound j i k) (volume : Measure Point3)

structure H3Order3EnergyDerivativeMajorantOnTailAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T t : ℝ) : Type where
  timeSet :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        PrimeTensor.Axis Depth.three →
          PrimeTensor.Axis Depth.three → Set ℝ
  bound :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        PrimeTensor.Axis Depth.three →
          PrimeTensor.Axis Depth.three →
            Point3 → ℝ
  timeSet_mem_nhds :
    ∀ j i k l, timeSet j i k l ∈ 𝓝 t
  timeSet_tail :
    ∀ j i k l, timeSet j i k l ⊆ Set.Ioo a T
  derivative_le_bound :
    ∀ j i k l,
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ timeSet j i k l,
          ‖2 *
              spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityComponent u s j))) x *
              spatial3.d i
                (spatial3.d k
                  (spatial3.d l
                    (loggedVelocityTemporalComponent u s j))) x‖
            ≤ bound j i k l x
  bound_integrable :
    ∀ j i k l,
      Integrable (bound j i k l) (volume : Measure Point3)

structure H3EnergyDerivativeMajorantDataAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T t : ℝ) : Type where
  order0 :
    H3Order0EnergyDerivativeMajorantOnTailAt u a T t
  order1 :
    H3Order1EnergyDerivativeMajorantOnTailAt u a T t
  order2 :
    H3Order2EnergyDerivativeMajorantOnTailAt u a T t
  order3 :
    H3Order3EnergyDerivativeMajorantOnTailAt u a T t

def EnergyClassProducesH3EnergyDerivativeMajorants : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ),
      PreterminalH3EnergyClass u a T →
        ∀ t : ℝ,
          t ∈ Set.Ioo a T →
            Nonempty
              (H3EnergyDerivativeMajorantDataAt
                u a T t)

/-! ## Recover the reduced domination frontier -/

noncomputable def h3Order0ReducedDomination_of_majorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (h : H3Order0EnergyDerivativeMajorantOnTailAt u a T t) :
    H3Order0EnergyDerivativeReducedDominatedOnTailAt u a T t :=
  {
    timeSet := h.timeSet
    bound := h.bound
    timeSet_mem_nhds := h.timeSet_mem_nhds
    timeSet_tail := h.timeSet_tail
    derivative_aestronglyMeasurable :=
      h3Order0_derivativeProduct_aestronglyMeasurable_of_energyClass
        hClass ht
    derivative_le_bound := h.derivative_le_bound
    bound_integrable := h.bound_integrable
  }

noncomputable def h3Order1ReducedDomination_of_majorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (h : H3Order1EnergyDerivativeMajorantOnTailAt u a T t) :
    H3Order1EnergyDerivativeReducedDominatedOnTailAt u a T t :=
  {
    timeSet := h.timeSet
    bound := h.bound
    timeSet_mem_nhds := h.timeSet_mem_nhds
    timeSet_tail := h.timeSet_tail
    derivative_aestronglyMeasurable :=
      h3Order1_derivativeProduct_aestronglyMeasurable_of_energyClass
        hClass ht
    derivative_le_bound := h.derivative_le_bound
    bound_integrable := h.bound_integrable
  }

noncomputable def h3Order2ReducedDomination_of_majorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (h : H3Order2EnergyDerivativeMajorantOnTailAt u a T t) :
    H3Order2EnergyDerivativeReducedDominatedOnTailAt u a T t :=
  {
    timeSet := h.timeSet
    bound := h.bound
    timeSet_mem_nhds := h.timeSet_mem_nhds
    timeSet_tail := h.timeSet_tail
    derivative_aestronglyMeasurable :=
      h3Order2_derivativeProduct_aestronglyMeasurable_of_energyClass
        hClass ht
    derivative_le_bound := h.derivative_le_bound
    bound_integrable := h.bound_integrable
  }

noncomputable def h3Order3ReducedDomination_of_majorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (h : H3Order3EnergyDerivativeMajorantOnTailAt u a T t) :
    H3Order3EnergyDerivativeReducedDominatedOnTailAt u a T t :=
  {
    timeSet := h.timeSet
    bound := h.bound
    timeSet_mem_nhds := h.timeSet_mem_nhds
    timeSet_tail := h.timeSet_tail
    derivative_aestronglyMeasurable :=
      h3Order3_derivativeProduct_aestronglyMeasurable_of_energyClass
        hClass ht
    derivative_le_bound := h.derivative_le_bound
    bound_integrable := h.bound_integrable
  }

theorem energyClassProducesH3EnergyDerivativeReducedDomination_of_majorants
    (hMajorant : EnergyClassProducesH3EnergyDerivativeMajorants) :
    EnergyClassProducesH3EnergyDerivativeReducedDomination := by
  intro u a T hClass t ht
  rcases hMajorant u a T hClass t ht with ⟨h⟩
  exact
    ⟨
      {
        order0 :=
          h3Order0ReducedDomination_of_majorant
            hClass ht h.order0
        order1 :=
          h3Order1ReducedDomination_of_majorant
            hClass ht h.order1
        order2 :=
          h3Order2ReducedDomination_of_majorant
            hClass ht h.order2
        order3 :=
          h3Order3ReducedDomination_of_majorant
            hClass ht h.order3
      }
    ⟩

/-- Continuation with all measurability removed from the free domination
frontier.  The only remaining dominated-integral assumption is existence of
locally uniform integrable spatial majorants. -/
theorem h3ControlProducesExtension_of_unitViscositySmoothingEnergyDerivativeMajorants
    (hSmooth : H3SeedProducesEnergyClass)
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorant :
      EnergyClassProducesH3EnergyDerivativeMajorants) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscositySmoothingEnergyDerivativeReducedDomination
      hSmooth
      hTime
      (energyClassProducesH3EnergyDerivativeReducedDomination_of_majorants
        hMajorant)

end

end Euclidean
end Bridge
end PrimeTensor
