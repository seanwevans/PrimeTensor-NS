import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Derivative.Tail.Local.PDE.Split
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Preterminal.Canonical.Energy.Restart.Closure

/-!
# Remove redundant square-measurability assumptions from the H³ derivative frontier

The orderwise dominated-differentiation records carried two kinds of
measurability data:

* measurability of the square `|D^α u(s)|²` for nearby times `s`;
* measurability of the derivative product
  `2 D^α u(t) D^α ∂ₜu(t)` at the differentiation time.

The first item is not a genuine frontier on an energy-class tail.
Every interior preterminal slice is spatially `C³`, hence the complete H³ jet
is strongly measurable by
`velocityH3MeasurableAt_of_loggedPreterminalNavierStokes`.

This file removes that redundant field from all four orderwise domination
packages.  The remaining whole-space input is exactly:

* one neighborhood inside the terminal tail;
* measurability of the derivative product at the base time;
* an integrable spatial majorant for that derivative product.

The reduced data reconstruct the previous domination package automatically and
therefore drive the same pressure-free continuation theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EnergyDerivativeReducedDomination
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Automatic square measurability on an interior tail -/

/-- A coordinate derivative of a spatially `C¹` field is continuous.

Kept local here so the resulting `AEStronglyMeasurable` proof is built using
this file's `Point3` measurable/measure instances rather than transporting a
proof object created under another local `MeasureSpace Point3` instance. -/
private theorem spatialC1_spatial_d_continuous_reducedDomination
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


/-- Zeroth-order jet squares are strongly measurable at every nearby tail
time, with no additional analytic hypothesis. -/
theorem eventually_h3Order0_square_aestronglyMeasurable_onTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ha : 0 < a)
    (ht : t ∈ Set.Ioo a T)
    (j : PrimeTensor.Axis Depth.three) :
    ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable
        (fun x : Point3 =>
          (loggedVelocityComponent u s j x) ^ 2)
        (volume : Measure Point3) := by
  let p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs

  have hsPre :
      s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans ha hs.1, hs.2⟩

  have hf3 :
      SpatialC3 (loggedVelocityComponent u s j) := by
    change
      SpatialC3
        (fun x : Point3 =>
          (logSpaceTimeVectorField u s x).component j)
    exact
      hPDE.regularity.velocity_spatial_three
        s hsPre j

  have hf :
      Continuous (loggedVelocityComponent u s j) :=
    hf3.continuous

  exact
    Continuous.aestronglyMeasurable
      (hf.pow 2)

/-- First-order jet squares are strongly measurable at every nearby tail
time. -/
theorem eventually_h3Order1_square_aestronglyMeasurable_onTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ha : 0 < a)
    (ht : t ∈ Set.Ioo a T)
    (j i : PrimeTensor.Axis Depth.three) :
    ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable
        (fun x : Point3 =>
          (spatial3.d
            i
            (loggedVelocityComponent u s j)
            x) ^ 2)
        (volume : Measure Point3) := by
  let p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs

  have hsPre :
      s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans ha hs.1, hs.2⟩

  let f : ScalarField3 :=
    loggedVelocityComponent u s j

  have hf3 : SpatialC3 f := by
    dsimp only [f]
    change
      SpatialC3
        (fun x : Point3 =>
          (logSpaceTimeVectorField u s x).component j)
    exact
      hPDE.regularity.velocity_spatial_three
        s hsPre j

  have hdi2 :
      SpatialC2 (spatial3.d i f) := by
    change
      SpatialC2
        (fun x : Point3 =>
          partialDeriv i f x)
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
        hf3 i

  have hdi :
      Continuous (spatial3.d i f) :=
    hdi2.continuous

  dsimp only [f] at hdi
  exact
    Continuous.aestronglyMeasurable
      (hdi.pow 2)

/-- Second-order jet squares are strongly measurable at every nearby tail
time. -/
theorem eventually_h3Order2_square_aestronglyMeasurable_onTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ha : 0 < a)
    (ht : t ∈ Set.Ioo a T)
    (j i k : PrimeTensor.Axis Depth.three) :
    ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable
        (fun x : Point3 =>
          (spatial3.d
            i
            (spatial3.d
              k
              (loggedVelocityComponent u s j))
            x) ^ 2)
        (volume : Measure Point3) := by
  let p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs

  have hsPre :
      s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans ha hs.1, hs.2⟩

  let f : ScalarField3 :=
    loggedVelocityComponent u s j

  have hf3 : SpatialC3 f := by
    dsimp only [f]
    change
      SpatialC3
        (fun x : Point3 =>
          (logSpaceTimeVectorField u s x).component j)
    exact
      hPDE.regularity.velocity_spatial_three
        s hsPre j

  have hdk2 :
      SpatialC2 (spatial3.d k f) := by
    change
      SpatialC2
        (fun x : Point3 =>
          partialDeriv k f x)
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
        hf3 k

  have hdik1 :
      SpatialC1
        (spatial3.d i (spatial3.d k f)) := by
    change
      SpatialC1
        (fun x : Point3 =>
          partialDeriv i (spatial3.d k f) x)
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
        hdk2 i

  have hdik :
      Continuous
        (spatial3.d i (spatial3.d k f)) :=
    hdik1.continuous

  dsimp only [f] at hdik
  exact
    Continuous.aestronglyMeasurable
      (hdik.pow 2)

/-- Third-order jet squares are strongly measurable at every nearby tail
time. -/
theorem eventually_h3Order3_square_aestronglyMeasurable_onTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ha : 0 < a)
    (ht : t ∈ Set.Ioo a T)
    (j i k l : PrimeTensor.Axis Depth.three) :
    ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable
        (fun x : Point3 =>
          (spatial3.d
            i
            (spatial3.d
              k
              (spatial3.d
                l
                (loggedVelocityComponent u s j)))
            x) ^ 2)
        (volume : Measure Point3) := by
  let p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs

  have hsPre :
      s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans ha hs.1, hs.2⟩

  let f : ScalarField3 :=
    loggedVelocityComponent u s j

  have hf3 : SpatialC3 f := by
    dsimp only [f]
    change
      SpatialC3
        (fun x : Point3 =>
          (logSpaceTimeVectorField u s x).component j)
    exact
      hPDE.regularity.velocity_spatial_three
        s hsPre j

  have hdl2 :
      SpatialC2 (spatial3.d l f) := by
    change
      SpatialC2
        (fun x : Point3 =>
          partialDeriv l f x)
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
        hf3 l

  have hkdl1 :
      SpatialC1
        (spatial3.d k (spatial3.d l f)) := by
    change
      SpatialC1
        (fun x : Point3 =>
          partialDeriv k (spatial3.d l f) x)
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
        hdl2 k

  have hdikl :
      Continuous
        (spatial3.d
          i
          (spatial3.d
            k
            (spatial3.d l f))) :=
    spatialC1_spatial_d_continuous_reducedDomination
      hkdl1 i

  dsimp only [f] at hdikl
  exact
    Continuous.aestronglyMeasurable
      (hdikl.pow 2)

/-! ## Reduced domination records -/

/-- Zeroth-order domination with the automatically available square
measurability removed. -/
structure H3Order0EnergyDerivativeReducedDominatedOnTailAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T t : ℝ) : Type where

  timeSet :
    PrimeTensor.Axis Depth.three → Set ℝ

  bound :
    PrimeTensor.Axis Depth.three → Point3 → ℝ

  timeSet_mem_nhds :
    ∀ j : PrimeTensor.Axis Depth.three,
      timeSet j ∈ 𝓝 t

  timeSet_tail :
    ∀ j : PrimeTensor.Axis Depth.three,
      timeSet j ⊆ Set.Ioo a T

  derivative_aestronglyMeasurable :
    ∀ j : PrimeTensor.Axis Depth.three,
      AEStronglyMeasurable
        (fun x : Point3 =>
          2 *
            loggedVelocityComponent u t j x *
            loggedVelocityTemporalComponent u t j x)
        (volume : Measure Point3)

  derivative_le_bound :
    ∀ j : PrimeTensor.Axis Depth.three,
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ timeSet j,
          norm
            (2 *
              loggedVelocityComponent u s j x *
              loggedVelocityTemporalComponent u s j x)
            ≤
          bound j x

  bound_integrable :
    ∀ j : PrimeTensor.Axis Depth.three,
      Integrable
        (bound j)
        (volume : Measure Point3)

/-- First-order reduced domination. -/
structure H3Order1EnergyDerivativeReducedDominatedOnTailAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T t : ℝ) : Type where

  timeSet :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        Set ℝ

  bound :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        Point3 → ℝ

  timeSet_mem_nhds :
    ∀ j i : PrimeTensor.Axis Depth.three,
      timeSet j i ∈ 𝓝 t

  timeSet_tail :
    ∀ j i : PrimeTensor.Axis Depth.three,
      timeSet j i ⊆ Set.Ioo a T

  derivative_aestronglyMeasurable :
    ∀ j i : PrimeTensor.Axis Depth.three,
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
        (volume : Measure Point3)

  derivative_le_bound :
    ∀ j i : PrimeTensor.Axis Depth.three,
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ timeSet j i,
          norm
            (2 *
              spatial3.d
                i
                (loggedVelocityComponent u s j)
                x *
              spatial3.d
                i
                (loggedVelocityTemporalComponent u s j)
                x)
            ≤
          bound j i x

  bound_integrable :
    ∀ j i : PrimeTensor.Axis Depth.three,
      Integrable
        (bound j i)
        (volume : Measure Point3)

/-- Second-order reduced domination. -/
structure H3Order2EnergyDerivativeReducedDominatedOnTailAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T t : ℝ) : Type where

  timeSet :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        PrimeTensor.Axis Depth.three →
          Set ℝ

  bound :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        PrimeTensor.Axis Depth.three →
          Point3 → ℝ

  timeSet_mem_nhds :
    ∀ j i k : PrimeTensor.Axis Depth.three,
      timeSet j i k ∈ 𝓝 t

  timeSet_tail :
    ∀ j i k : PrimeTensor.Axis Depth.three,
      timeSet j i k ⊆ Set.Ioo a T

  derivative_aestronglyMeasurable :
    ∀ j i k : PrimeTensor.Axis Depth.three,
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
        (volume : Measure Point3)

  derivative_le_bound :
    ∀ j i k : PrimeTensor.Axis Depth.three,
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ timeSet j i k,
          norm
            (2 *
              spatial3.d
                i
                (spatial3.d
                  k
                  (loggedVelocityComponent u s j))
                x *
              spatial3.d
                i
                (spatial3.d
                  k
                  (loggedVelocityTemporalComponent u s j))
                x)
            ≤
          bound j i k x

  bound_integrable :
    ∀ j i k : PrimeTensor.Axis Depth.three,
      Integrable
        (bound j i k)
        (volume : Measure Point3)

/-- Third-order reduced domination. -/
structure H3Order3EnergyDerivativeReducedDominatedOnTailAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T t : ℝ) : Type where

  timeSet :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        PrimeTensor.Axis Depth.three →
          PrimeTensor.Axis Depth.three →
            Set ℝ

  bound :
    PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
        PrimeTensor.Axis Depth.three →
          PrimeTensor.Axis Depth.three →
            Point3 → ℝ

  timeSet_mem_nhds :
    ∀ j i k l : PrimeTensor.Axis Depth.three,
      timeSet j i k l ∈ 𝓝 t

  timeSet_tail :
    ∀ j i k l : PrimeTensor.Axis Depth.three,
      timeSet j i k l ⊆ Set.Ioo a T

  derivative_aestronglyMeasurable :
    ∀ j i k l : PrimeTensor.Axis Depth.three,
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
        (volume : Measure Point3)

  derivative_le_bound :
    ∀ j i k l : PrimeTensor.Axis Depth.three,
      ∀ᵐ x : Point3 ∂(volume : Measure Point3),
        ∀ s ∈ timeSet j i k l,
          norm
            (2 *
              spatial3.d
                i
                (spatial3.d
                  k
                  (spatial3.d
                    l
                    (loggedVelocityComponent u s j)))
                x *
              spatial3.d
                i
                (spatial3.d
                  k
                  (spatial3.d
                    l
                    (loggedVelocityTemporalComponent u s j)))
                x)
            ≤
          bound j i k l x

  bound_integrable :
    ∀ j i k l : PrimeTensor.Axis Depth.three,
      Integrable
        (bound j i k l)
        (volume : Measure Point3)

/-! ## Reconstruct the previous domination packages -/

noncomputable def h3Order0EnergyDerivativeDominatedAt_of_reducedOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ha : 0 < a)
    (ht : t ∈ Set.Ioo a T)
    (h :
      H3Order0EnergyDerivativeReducedDominatedOnTailAt
        u a T t) :
    H3Order0EnergyDerivativeDominatedAt u T t := by
  refine
    {
      timeSet := h.timeSet
      bound := h.bound
      timeSet_mem_nhds := h.timeSet_mem_nhds
      timeSet_preterminal := ?_
      square_aestronglyMeasurable := ?_
      derivative_aestronglyMeasurable := h.derivative_aestronglyMeasurable
      derivative_le_bound := h.derivative_le_bound
      bound_integrable := h.bound_integrable
    }

  · intro j s hs
    have hsTail := h.timeSet_tail j hs
    exact ⟨lt_trans ha hsTail.1, hsTail.2⟩

  · intro j
    exact
      eventually_h3Order0_square_aestronglyMeasurable_onTail
        hNS ha ht j

noncomputable def h3Order1EnergyDerivativeDominatedAt_of_reducedOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ha : 0 < a)
    (ht : t ∈ Set.Ioo a T)
    (h :
      H3Order1EnergyDerivativeReducedDominatedOnTailAt
        u a T t) :
    H3Order1EnergyDerivativeDominatedAt u T t := by
  refine
    {
      timeSet := h.timeSet
      bound := h.bound
      timeSet_mem_nhds := h.timeSet_mem_nhds
      timeSet_preterminal := ?_
      square_aestronglyMeasurable := ?_
      derivative_aestronglyMeasurable := h.derivative_aestronglyMeasurable
      derivative_le_bound := h.derivative_le_bound
      bound_integrable := h.bound_integrable
    }

  · intro j i s hs
    have hsTail := h.timeSet_tail j i hs
    exact ⟨lt_trans ha hsTail.1, hsTail.2⟩

  · intro j i
    exact
      eventually_h3Order1_square_aestronglyMeasurable_onTail
        hNS ha ht j i

noncomputable def h3Order2EnergyDerivativeDominatedOnTailAt_of_reduced
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ha : 0 < a)
    (ht : t ∈ Set.Ioo a T)
    (h :
      H3Order2EnergyDerivativeReducedDominatedOnTailAt
        u a T t) :
    H3Order2EnergyDerivativeDominatedOnTailAt u a T t := by
  let hBase :
      H3Order2EnergyDerivativeDominatedAt u T t :=
    {
      timeSet := h.timeSet
      bound := h.bound
      timeSet_mem_nhds := h.timeSet_mem_nhds
      timeSet_preterminal := by
        intro j i k s hs
        have hsTail := h.timeSet_tail j i k hs
        exact ⟨lt_trans ha hsTail.1, hsTail.2⟩
      square_aestronglyMeasurable := by
        intro j i k
        exact
          eventually_h3Order2_square_aestronglyMeasurable_onTail
            hNS ha ht j i k
      derivative_aestronglyMeasurable :=
        h.derivative_aestronglyMeasurable
      derivative_le_bound :=
        h.derivative_le_bound
      bound_integrable :=
        h.bound_integrable
    }

  exact
    {
      dominated := hBase
      timeSet_tail := h.timeSet_tail
    }

noncomputable def h3Order3EnergyDerivativeDominatedOnTailAt_of_reduced
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ha : 0 < a)
    (ht : t ∈ Set.Ioo a T)
    (h :
      H3Order3EnergyDerivativeReducedDominatedOnTailAt
        u a T t) :
    H3Order3EnergyDerivativeDominatedOnTailAt u a T t := by
  let hBase :
      H3Order3EnergyDerivativeDominatedAt u T t :=
    {
      timeSet := h.timeSet
      bound := h.bound
      timeSet_mem_nhds := h.timeSet_mem_nhds
      timeSet_preterminal := by
        intro j i k l s hs
        have hsTail := h.timeSet_tail j i k l hs
        exact ⟨lt_trans ha hsTail.1, hsTail.2⟩
      square_aestronglyMeasurable := by
        intro j i k l
        exact
          eventually_h3Order3_square_aestronglyMeasurable_onTail
            hNS ha ht j i k l
      derivative_aestronglyMeasurable :=
        h.derivative_aestronglyMeasurable
      derivative_le_bound :=
        h.derivative_le_bound
      bound_integrable :=
        h.bound_integrable
    }

  exact
    {
      dominated := hBase
      timeSet_tail := h.timeSet_tail
    }

/-! ## Reduced bundled frontier -/

structure H3EnergyDerivativeReducedDominationDataAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T t : ℝ) : Type where

  order0 :
    H3Order0EnergyDerivativeReducedDominatedOnTailAt
      u a T t

  order1 :
    H3Order1EnergyDerivativeReducedDominatedOnTailAt
      u a T t

  order2 :
    H3Order2EnergyDerivativeReducedDominatedOnTailAt
      u a T t

  order3 :
    H3Order3EnergyDerivativeReducedDominatedOnTailAt
      u a T t

/-- Energy-class domination frontier after deleting the automatically available
square-measurability hypotheses. -/
def EnergyClassProducesH3EnergyDerivativeReducedDomination : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ),
      PreterminalH3EnergyClass u a T →
        ∀ t : ℝ,
          t ∈ Set.Ioo a T →
            Nonempty
              (H3EnergyDerivativeReducedDominationDataAt
                u a T t)

/-- The reduced domination package reconstructs the previous tail-local
domination frontier. -/
theorem energyClassProducesH3EnergyDerivativeTailLocalDomination_of_reduced
    (hReduced :
      EnergyClassProducesH3EnergyDerivativeReducedDomination) :
    EnergyClassProducesH3EnergyDerivativeTailLocalDomination := by
  intro u a T hClass t ht

  rcases hReduced u a T hClass t ht with
    ⟨h⟩

  rcases hClass.pressure_witness with
    ⟨p, hPDE, hPressure⟩

  let hNS :
      LoggedPreterminalNavierStokesAdmissible u T :=
    ⟨p, hPDE⟩

  let ha : 0 < a :=
    hClass.terminal_start.1

  exact
    ⟨
      {
        order0 :=
          h3Order0EnergyDerivativeDominatedAt_of_reducedOnTail
            hNS ha ht h.order0
        order1 :=
          h3Order1EnergyDerivativeDominatedAt_of_reducedOnTail
            hNS ha ht h.order1
        order2 :=
          h3Order2EnergyDerivativeDominatedOnTailAt_of_reduced
            hNS ha ht h.order2
        order3 :=
          h3Order3EnergyDerivativeDominatedOnTailAt_of_reduced
            hNS ha ht h.order3
      }
    ⟩

/-- Pressure-free continuation with the square-measurability part of the
domination frontier discharged automatically from preterminal regularity. -/
theorem h3ControlProducesExtension_of_unitViscositySmoothingEnergyDerivativeReducedDomination
    (hSmooth : H3SeedProducesEnergyClass)
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hReduced :
      EnergyClassProducesH3EnergyDerivativeReducedDomination) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscositySmoothingEnergyDerivativeTailLocalPDE
      hSmooth
      hTime
      (energyClassProducesH3EnergyDerivativeTailLocalDomination_of_reduced
        hReduced)

end

end Euclidean
end Bridge
end PrimeTensor
