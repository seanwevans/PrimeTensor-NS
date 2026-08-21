import PrimeTensor.Fluid.VorticityLogarithmicGronwall

/-!
# Splitting the BKM PDE frontier

The scalar logarithmic Grönwall/Osgood step is now proved.  The remaining
continuation-side hypothesis is the PDE statement

    VorticityEnvelopeProducesBKMH3Growth.

This file splits that statement into the two analytically different estimates
which classical BKM arguments compose:

1. a differentiated high-order energy estimate controlled by a spatial
   velocity-gradient envelope;

2. an endpoint logarithmic estimate which controls that gradient envelope by
   the vorticity envelope and the high-order energy.

The split is deliberately componentwise, matching the existing Euclidean bridge
and avoiding any hidden vector/Sobolev norm API.

No claim is made here that either analytic estimate has already been proved.
The theorem in this file proves only that the two explicit estimates compose to
the exact BKM growth proposition already used downstream.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

/--
A common pointwise envelope for every first spatial derivative of the logged
velocity.

This is the componentwise version of a bound on `‖∇u(t)‖_∞`.
-/
def VelocityGradientEnvelope
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (h : ℝ → ℝ)
    (t : ℝ) : Prop :=
  ∀
    (i j : PrimeTensor.Axis Depth.three)
    (x : Point3),
      abs
        (
          spatial3.d
            i
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component j
            )
            x
        )
        ≤
      h t

/--
The ordinary high-order energy inequality before the endpoint vorticity
estimate is inserted.

If `E` is the normalized H³ energy profile and `h` bounds all first spatial
velocity derivatives, the desired differentiated energy estimate has the form

    E'(t) ≤ A (1 + |h(t)|) E(t).

The harmless `1 +` absorbs lower-order terms.
-/
def H3GradientGrowthInequalityFrom
    (a T : ℝ)
    (h E : ℝ → ℝ)
    (A : ℝ) : Prop :=
  ∀ t : ℝ,
    t ∈ Set.Ioo a T →
      deriv E t
        ≤
      A
        * (1 + |h t|)
        * E t

/--
First PDE obligation: construct a high-order energy profile and a gradient
envelope satisfying the differentiated Navier--Stokes energy inequality.

The vorticity envelope is carried as an input only so this proposition has the
same external data as the final BKM statement; the intended energy estimate
itself uses the velocity-gradient envelope `h`.
-/
def VorticityEnvelopeProducesH3GradientGrowth : Prop :=
  ∀
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ)
    (g : ℝ → ℝ),
      LoggedPreterminalNavierStokesAdmissible
          u T
        →
      PreterminalH3Seed
          u T
        →
      MeasureTheory.IntegrableOn
          g
          (Set.Ioo (0 : ℝ) T)
        →
      (
        ∀ t : ℝ,
          t ∈ Set.Ioo (0 : ℝ) T →
            VorticityEnvelope
              u g t
      )
        →
      ∃
        (a : ℝ)
        (E h : ℝ → ℝ)
        (A : ℝ),
          a ∈ Set.Ioo (0 : ℝ) T
            ∧
          0 ≤ A
            ∧
          H3EnergyProfileFrom
            u a T E
            ∧
          EnergyLocallyC1OnTail
            a T E
            ∧
          (
            ∀ t : ℝ,
              t ∈ Set.Ioo a T →
                VelocityGradientEnvelope
                  u h t
          )
            ∧
          H3GradientGrowthInequalityFrom
            a T h E A

/--
Second PDE/harmonic-analysis obligation: the endpoint logarithmic estimate.

Once `g` bounds vorticity, `h` bounds the velocity gradient, and `E ≥ 1` is a
high-order energy profile, there is a fixed nonnegative constant `B` such that

    1 + |h(t)|
      ≤ B (1 + |g(t)|) (1 + log E(t))

throughout the terminal tail.

This deliberately uses a slightly coarse multiplicative form.  It is strong
enough for the downstream BKM growth inequality and leaves constants/lower
order terms outside the logical core.
-/
def VorticityControlsGradientLogarithmically : Prop :=
  ∀
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (a T : ℝ)
    (g E h : ℝ → ℝ),
      a ∈ Set.Ioo (0 : ℝ) T
        →
      (
        ∀ t : ℝ,
          t ∈ Set.Ioo a T →
            VorticityEnvelope
              u g t
      )
        →
      H3EnergyProfileFrom
          u a T E
        →
      (
        ∀ t : ℝ,
          t ∈ Set.Ioo a T →
            VelocityGradientEnvelope
              u h t
      )
        →
      ∃ B : ℝ,
        0 ≤ B
          ∧
        ∀ t : ℝ,
          t ∈ Set.Ioo a T →
            1 + |h t|
              ≤
            B
              * (1 + |g t|)
              * (1 + Real.log (E t))

/--
The differentiated H³ energy estimate and the endpoint logarithmic gradient
estimate compose to the exact BKM logarithmic growth proposition.
-/
theorem vorticityEnvelopeProducesBKMH3Growth_of_energy_and_endpoint
    (
      hEnergy :
        VorticityEnvelopeProducesH3GradientGrowth
    )
    (
      hEndpoint :
        VorticityControlsGradientLogarithmically
    ) :
    VorticityEnvelopeProducesBKMH3Growth := by

  intro
    u T g
    hAdmissible
    hSeed
    hgIntegrable
    hgEnvelope

  obtain
    ⟨
      a,
      E,
      h,
      A,
      ha,
      hA,
      hProfile,
      hC1,
      hGradient,
      hEnergyGrowth
    ⟩ :=
    hEnergy
      u T g
      hAdmissible
      hSeed
      hgIntegrable
      hgEnvelope

  have hgTail :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          VorticityEnvelope
            u g t := by

    intro t ht

    apply
      hgEnvelope
        t

    exact
      ⟨
        lt_trans ha.1 ht.1,
        ht.2
      ⟩

  obtain
    ⟨
      B,
      hB,
      hEndpointBound
    ⟩ :=
    hEndpoint
      u a T g E h
      ha
      hgTail
      hProfile
      hGradient

  let C : ℝ :=
    A * B

  refine
    ⟨
      a,
      E,
      C,
      ha,
      ?_,
      hProfile,
      hC1,
      ?_
    ⟩

  · dsimp only [C]

    exact
      mul_nonneg
        hA
        hB

  · intro t ht

    have hEtOne :
        1 ≤ E t :=
      (hProfile t ⟨le_of_lt ht.1, ht.2⟩).1

    have hEtNonnegative :
        0 ≤ E t :=
      le_trans
        (by norm_num)
        hEtOne

    have hEndpointAt :
        1 + |h t|
          ≤
        B
          * (1 + |g t|)
          * (1 + Real.log (E t)) :=
      hEndpointBound
        t ht

    calc
      deriv E t
          ≤
        A
          * (1 + |h t|)
          * E t :=
        hEnergyGrowth
          t ht

      _ ≤
        A
          *
        (
          B
            * (1 + |g t|)
            * (1 + Real.log (E t))
        )
          * E t := by

        exact
          mul_le_mul_of_nonneg_right
            (
              mul_le_mul_of_nonneg_left
                hEndpointAt
                hA
            )
            hEtNonnegative

      _ =
        C
          * (1 + |g t|)
          * E t
          * (1 + Real.log (E t)) := by

        dsimp only [C]
        ring

/--
After the scalar Osgood theorem already proved in
`VorticityLogarithmicGronwall`, the two PDE estimates directly imply the
terminal-tail H³ control.
-/
theorem vorticityL1LinfProducesH3Control_of_energy_and_endpoint
    (
      hEnergy :
        VorticityEnvelopeProducesH3GradientGrowth
    )
    (
      hEndpoint :
        VorticityControlsGradientLogarithmically
    ) :
    VorticityL1LinfProducesH3Control := by

  apply
    vorticityL1LinfProducesH3Control_of_BKMGrowth_closedScalar

  exact
    vorticityEnvelopeProducesBKMH3Growth_of_energy_and_endpoint
      hEnergy
      hEndpoint

/--
With the standard H³ restart/extension theorem added, the same two PDE
estimates imply the honest seeded vorticity continuation criterion.
-/
theorem seededVorticityL1LinfProducesExtension_of_energy_and_endpoint
    (
      hEnergy :
        VorticityEnvelopeProducesH3GradientGrowth
    )
    (
      hEndpoint :
        VorticityControlsGradientLogarithmically
    )
    (
      hH3ToExtension :
        H3ControlProducesExtension
    ) :
    SeededVorticityL1LinfProducesExtension := by

  apply
    seededVorticityL1LinfProducesExtension_of_BKMGrowth_closedScalar
      (
        vorticityEnvelopeProducesBKMH3Growth_of_energy_and_endpoint
          hEnergy
          hEndpoint
      )
      hH3ToExtension

end Euclidean
end Bridge
end PrimeTensor
