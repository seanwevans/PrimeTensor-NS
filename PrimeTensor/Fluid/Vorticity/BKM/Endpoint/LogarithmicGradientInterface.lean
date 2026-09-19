import PrimeTensor.Fluid.Vorticity.BKM.Energy.Endpoint

/-!
# BKM endpoint: well-posed logarithmic gradient interface

The original abstract endpoint proposition quantified over an arbitrary function
`h` satisfying `VelocityGradientEnvelope u h t` and then attempted to bound
`h` itself.

That quantifier is too strong: `VelocityGradientEnvelope` is monotone in its
scalar envelope.  Once one envelope works, it can be enlarged arbitrarily
without changing the underlying velocity field.  Therefore harmonic analysis
should bound the actual first derivatives, and only afterwards package that
pointwise estimate into one concrete velocity-gradient envelope.

This file records that corrected interface without yet changing the older
downstream proposition.

The analytic target is

    1 + |∂ᵢ uⱼ(t,x)|
      ≤ B (1 + |g(t)|) (1 + log E(t))

for every component, coordinate and point.  It explicitly includes the
preterminal Navier--Stokes hypothesis used by the Fourier/divergence-free
BKM reconstruction.

From such an actual-gradient estimate we construct the canonical envelope

    h(t) = B (1 + |g(t)|) (1 + log E(t)),

and show that it satisfies both `VelocityGradientEnvelope` and a logarithmic
bound of the same form, with harmless constant `B + 1`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/--
A logarithmic bound on the actual first spatial derivatives of the logged
velocity, rather than on an arbitrary upper-envelope function.
-/
def ActualVelocityGradientLogBoundFrom
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (a T : ℝ)
    (g E : ℝ → ℝ)
    (B : ℝ) : Prop :=
  ∀
    (t : ℝ),
      t ∈ Set.Ioo a T →
        ∀
          (i j : PrimeTensor.Axis Depth.three)
          (x : Point3),
            1
                +
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
            B
              * (1 + |g t|)
              * (1 + Real.log (E t))

/--
Correctly quantified BKM endpoint obligation.

The endpoint estimate applies to a genuine logged preterminal Navier--Stokes
solution, a vorticity envelope, and an H³ energy profile, and bounds the actual
velocity derivatives.
-/
def VorticityControlsActualGradientLogarithmically : Prop :=
  ∀
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (a T : ℝ)
    (g E : ℝ → ℝ),
      LoggedPreterminalNavierStokesAdmissible
          u T
        →
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
      ∃ B : ℝ,
        0 ≤ B
          ∧
        ActualVelocityGradientLogBoundFrom
          u a T g E B

/--
The canonical scalar envelope associated to an actual-gradient logarithmic
bound.
-/
noncomputable def h3BKMLogarithmicGradientEnvelope
    (g E : ℝ → ℝ)
    (B : ℝ) :
    ℝ → ℝ :=
  fun t =>
    B
      * (1 + |g t|)
      * (1 + Real.log (E t))

/--
An actual-gradient logarithmic estimate immediately gives a genuine
`VelocityGradientEnvelope` for the canonical logarithmic envelope.
-/
theorem velocityGradientEnvelope_h3BKMLogarithmicGradientEnvelope
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T : ℝ}
    {g E : ℝ → ℝ}
    {B : ℝ}
    (hBound :
      ActualVelocityGradientLogBoundFrom
        u a T g E B)
    {t : ℝ}
    (ht : t ∈ Set.Ioo a T) :
    VelocityGradientEnvelope
      u
      (h3BKMLogarithmicGradientEnvelope g E B)
      t := by

  intro i j x

  have hAt :=
    hBound t ht i j x

  unfold h3BKMLogarithmicGradientEnvelope

  linarith

/--
If `E ≥ 1` and `B ≥ 0`, the canonical envelope is nonnegative.
-/
theorem h3BKMLogarithmicGradientEnvelope_nonneg
    {g E : ℝ → ℝ}
    {B t : ℝ}
    (hB : 0 ≤ B)
    (hE : 1 ≤ E t) :
    0 ≤ h3BKMLogarithmicGradientEnvelope g E B t := by

  have hLog :
      0 ≤ Real.log (E t) := by
    exact
      Real.log_nonneg
        hE

  unfold h3BKMLogarithmicGradientEnvelope

  exact
    mul_nonneg
      (
        mul_nonneg
          hB
          (by positivity)
      )
      (by positivity)

/--
The canonical envelope itself satisfies the same logarithmic structure, at the
cost of replacing `B` by `B + 1`.
-/
theorem one_add_abs_h3BKMLogarithmicGradientEnvelope_le
    {g E : ℝ → ℝ}
    {B t : ℝ}
    (hB : 0 ≤ B)
    (hE : 1 ≤ E t) :
    1
        +
      |h3BKMLogarithmicGradientEnvelope g E B t|
      ≤
    (B + 1)
      * (1 + |g t|)
      * (1 + Real.log (E t)) := by

  have hLog :
      0 ≤ Real.log (E t) := by
    exact
      Real.log_nonneg
        hE

  have hG :
      1 ≤ 1 + |g t| := by
    linarith [abs_nonneg (g t)]

  have hLogOne :
      1 ≤ 1 + Real.log (E t) := by
    linarith

  have hProduct :
      1
        ≤
      (1 + |g t|)
        * (1 + Real.log (E t)) := by
    nlinarith

  have hEnvNonneg :
      0
        ≤
      h3BKMLogarithmicGradientEnvelope
        g E B t :=
    h3BKMLogarithmicGradientEnvelope_nonneg
      hB hE

  rw [abs_of_nonneg hEnvNonneg]

  unfold h3BKMLogarithmicGradientEnvelope

  nlinarith

/--
The corrected actual-gradient endpoint produces one concrete gradient envelope
whose scalar size satisfies the logarithmic BKM estimate.

This is the quantifier pattern needed by the energy argument: harmonic analysis
constructs the envelope instead of attempting to control every possible
inflation of one.
-/
theorem vorticityControlsActualGradientLogarithmically_produces_envelope
    (
      hEndpoint :
        VorticityControlsActualGradientLogarithmically
    )
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (a T : ℝ)
    (g E : ℝ → ℝ)
    (hNS :
      LoggedPreterminalNavierStokesAdmissible
        u T)
    (ha :
      a ∈ Set.Ioo (0 : ℝ) T)
    (hVorticity :
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          VorticityEnvelope
            u g t)
    (hEnergy :
      H3EnergyProfileFrom
        u a T E) :
    ∃
      (h : ℝ → ℝ)
      (C : ℝ),
        0 ≤ C
          ∧
        (
          ∀ t : ℝ,
            t ∈ Set.Ioo a T →
              VelocityGradientEnvelope
                u h t
        )
          ∧
        (
          ∀ t : ℝ,
            t ∈ Set.Ioo a T →
              1 + |h t|
                ≤
              C
                * (1 + |g t|)
                * (1 + Real.log (E t))
        ) := by

  obtain
    ⟨
      B,
      hB,
      hActual
    ⟩ :=
    hEndpoint
      u a T g E
      hNS
      ha
      hVorticity
      hEnergy

  let h : ℝ → ℝ :=
    h3BKMLogarithmicGradientEnvelope
      g E B

  let C : ℝ :=
    B + 1

  refine
    ⟨
      h,
      C,
      ?_,
      ?_,
      ?_
    ⟩

  · dsimp only [C]
    linarith

  · intro t ht

    dsimp only [h]

    exact
      velocityGradientEnvelope_h3BKMLogarithmicGradientEnvelope
        hActual
        ht

  · intro t ht

    have hEt :
        1 ≤ E t :=
      (hEnergy
        t
        ⟨
          le_of_lt ht.1,
          ht.2
        ⟩).1

    dsimp only [h, C]

    exact
      one_add_abs_h3BKMLogarithmicGradientEnvelope_le
        hB
        hEt

end Euclidean
end Bridge
end PrimeTensor
