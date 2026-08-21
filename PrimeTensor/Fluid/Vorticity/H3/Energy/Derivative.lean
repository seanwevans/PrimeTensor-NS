import PrimeTensor.Fluid.Vorticity.H3.Energy.Functional

/-!
# Canonical H³ energy derivative

`VorticityH3EnergyFunctional` fixed the scalar energy

    E_H3(t) = 1 + E₀(t) + E₁(t) + E₂(t) + E₃(t).

This file fixes its corresponding formal time derivative.  For every scalar
spatial derivative `F(t,x)` appearing in the energy, the expected contribution
is

    2 ∫ F(t,x) * ∂ₜF(t,x) dx.

The only analytic step hidden by this formula is differentiation under the
spatial integral (together with the mixed time/space derivative identities).
That step is isolated as `H3OrderEnergyDerivativeIdentities`.

Everything after that point in this file is proved: the four orderwise
identities compose to a derivative formula for the exact canonical normalized
H³ energy.

The next PDE module can therefore substitute Navier--Stokes into one concrete
quantity:

    velocityH3FormalDerivativeAt u t.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-- Logged temporal derivative of one velocity component. -/
noncomputable def loggedVelocityTemporalComponent
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    temporal.d
      (
        fun τ =>
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u τ x
          ).component j
      )
      t

/--
The bilinear energy-pairing contribution associated with a scalar spatial
field `f` and its time derivative `ft`.
-/
noncomputable def spatialEnergyPairing
    (f ft : ScalarField3) : ℝ :=
  2 * ∫ x : Point3, f x * ft x

/-- Formal zeroth-order contribution to `d/dt E_H3`. -/
noncomputable def velocityH3FormalDerivative0At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    spatialEnergyPairing
      (loggedVelocityComponent u t j)
      (loggedVelocityTemporalComponent u t j)

/-- Formal first-order contribution to `d/dt E_H3`. -/
noncomputable def velocityH3FormalDerivative1At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ i : PrimeTensor.Axis Depth.three,
      spatialEnergyPairing
        (
          spatial3.d
            i
            (loggedVelocityComponent u t j)
        )
        (
          spatial3.d
            i
            (loggedVelocityTemporalComponent u t j)
        )

/-- Formal second-order contribution to `d/dt E_H3`. -/
noncomputable def velocityH3FormalDerivative2At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        spatialEnergyPairing
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t j)
              )
          )
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityTemporalComponent u t j)
              )
          )

/-- Formal third-order contribution to `d/dt E_H3`. -/
noncomputable def velocityH3FormalDerivative3At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three,
          spatialEnergyPairing
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityComponent u t j)
                    )
                )
            )
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityTemporalComponent u t j)
                    )
                )
            )

/-- The exact formal derivative corresponding to `velocityH3EnergyAt`. -/
noncomputable def velocityH3FormalDerivativeAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  velocityH3FormalDerivative0At u t
    + velocityH3FormalDerivative1At u t
    + velocityH3FormalDerivative2At u t
    + velocityH3FormalDerivative3At u t

/--
Analytic differentiation-under-the-integral / mixed-derivative frontier for the
four finite energy blocks.

This is the precise point at which one must justify

    d/dt ∫ F(t,x)^2 dx = 2 ∫ F(t,x) ∂ₜF(t,x) dx

for all spatial derivatives through order three.
-/
def H3OrderEnergyDerivativeIdentities
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  HasDerivAt
      (velocityH3Energy0At u)
      (velocityH3FormalDerivative0At u t)
      t
    ∧
  HasDerivAt
      (velocityH3Energy1At u)
      (velocityH3FormalDerivative1At u t)
      t
    ∧
  HasDerivAt
      (velocityH3Energy2At u)
      (velocityH3FormalDerivative2At u t)
      t
    ∧
  HasDerivAt
      (velocityH3Energy3At u)
      (velocityH3FormalDerivative3At u t)
      t

/--
Once the four orderwise differentiation-under-integral identities are known,
the exact canonical normalized H³ energy has the formal derivative defined
above.
-/
theorem hasDerivAt_velocityH3EnergyAt
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      h :
        H3OrderEnergyDerivativeIdentities
          u t
    ) :
    HasDerivAt
      (velocityH3EnergyAt u)
      (velocityH3FormalDerivativeAt u t)
      t := by

  rcases h with
    ⟨
      h0,
      h1,
      h2,
      h3
    ⟩

  have h01 :
      HasDerivAt
        (
          fun s =>
            1
              + velocityH3Energy0At u s
              + velocityH3Energy1At u s
        )
        (
          velocityH3FormalDerivative0At u t
            + velocityH3FormalDerivative1At u t
        )
        t := by

    exact
      (h0.const_add 1).add h1

  have h012 :
      HasDerivAt
        (
          fun s =>
            1
              + velocityH3Energy0At u s
              + velocityH3Energy1At u s
              + velocityH3Energy2At u s
        )
        (
          velocityH3FormalDerivative0At u t
            + velocityH3FormalDerivative1At u t
            + velocityH3FormalDerivative2At u t
        )
        t := by

    exact
      h01.add h2

  have h0123 :
      HasDerivAt
        (
          fun s =>
            1
              + velocityH3Energy0At u s
              + velocityH3Energy1At u s
              + velocityH3Energy2At u s
              + velocityH3Energy3At u s
        )
        (
          velocityH3FormalDerivative0At u t
            + velocityH3FormalDerivative1At u t
            + velocityH3FormalDerivative2At u t
            + velocityH3FormalDerivative3At u t
        )
        t := by

    exact
      h012.add h3

  change
    HasDerivAt
      (
        fun s =>
          1
            + velocityH3Energy0At u s
            + velocityH3Energy1At u s
            + velocityH3Energy2At u s
            + velocityH3Energy3At u s
      )
      (
        velocityH3FormalDerivative0At u t
          + velocityH3FormalDerivative1At u t
          + velocityH3FormalDerivative2At u t
          + velocityH3FormalDerivative3At u t
      )
      t

  exact h0123

/--
Derivative equality extracted from the canonical derivative theorem.
-/
theorem deriv_velocityH3EnergyAt
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      h :
        H3OrderEnergyDerivativeIdentities
          u t
    ) :
    deriv
        (velocityH3EnergyAt u)
        t
      =
    velocityH3FormalDerivativeAt
      u t := by

  exact
    (
      hasDerivAt_velocityH3EnergyAt
        h
    ).deriv

/--
Terminal-tail version of the differentiation-under-integral frontier.
-/
def CanonicalH3EnergyDifferentiableOnTail
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (a T : ℝ) : Prop :=
  ∀ t : ℝ,
    t ∈ Set.Ioo a T →
      H3OrderEnergyDerivativeIdentities
        u t

/--
On a tail where the orderwise identities hold, the derivative of the canonical
energy is pointwise equal to the canonical formal PDE energy derivative.
-/
theorem deriv_velocityH3EnergyAt_onTail
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T t : ℝ}
    (
      hTail :
        CanonicalH3EnergyDifferentiableOnTail
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    ) :
    deriv
        (velocityH3EnergyAt u)
        t
      =
    velocityH3FormalDerivativeAt
      u t := by

  exact
    deriv_velocityH3EnergyAt
      (
        hTail
          t ht
      )

end Euclidean
end Bridge
end PrimeTensor
