import PrimeTensor.Fluid.Vorticity.Continuation.Handoff

/-!
# Concrete vorticity `L¹_t L∞_x` continuation control

The analytic handoff is now explicit:

    persistent multiplicative cascade
      -> failure of any admissible continuation control.

This file fixes the first concrete preterminal control.

Rather than requiring a normed-space structure on the vector-valued vorticity,
we use an equivalent componentwise envelope formulation.  A logged velocity
satisfies `VorticityL1LinfControl u T` when there is a real function `g(t)`
which is integrable on `(0,T)` and which bounds the absolute value of all three
classical vorticity components at every spatial point:

    |ωₓ(t,x)| ≤ g(t),
    |ωᵧ(t,x)| ≤ g(t),
    |ω_z(t,x)| ≤ g(t).

This is the exact shape needed for a vorticity `L¹_t L∞_x` continuation
criterion while keeping the definition independent of any vector norm API.

No Navier--Stokes continuation theorem is asserted in this file.  The missing
analytic statement is exposed as `VorticityL1LinfClosesJets`.  Supplying a proof
of that proposition for a chosen admissibility predicate constructs a concrete
`ContinuationControl`, after which the multiplicative cascade theorems apply
without further assumptions.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

/--
A common scalar envelope for all three components of the classical vorticity of
the logged velocity.
-/
def VorticityEnvelope
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (g : ℝ → ℝ)
    (t : ℝ) : Prop :=
  ∀ x : Point3,
    |realVorticityX
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x| ≤ g t
    ∧
    |realVorticityY
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x| ≤ g t
    ∧
    |realVorticityZ
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x| ≤ g t

/--
Concrete preterminal vorticity `L¹_t L∞_x`-style control.

The existence of an integrable common envelope avoids introducing a supremum
over space or a norm on the vorticity vector.  It directly expresses uniform
spatial boundedness with an integrable time profile.
-/
def VorticityL1LinfControl
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ) : Prop :=
  ∃ g : ℝ → ℝ,
    MeasureTheory.IntegrableOn
        g
        (Set.Ioo (0 : ℝ) T)
      ∧
    ∀ t : ℝ,
      t ∈ Set.Ioo (0 : ℝ) T →
        VorticityEnvelope u g t

/--
The precise unresolved analytic theorem for the componentwise vorticity
`L¹_t L∞_x` criterion.

`Admissible u T` is intentionally supplied by the eventual classical
Navier--Stokes solution-class layer.  The conclusion is exactly the terminal
jet closure required by the multiplicative cascade.
-/
def VorticityL1LinfClosesJets
    (
      Admissible :
        PrimeTensor.SpaceTimeVectorField
            ℝ ℝ PrimeTensor.MulReal Depth.three →
          ℝ →
          Prop
    ) : Prop :=
  ∀
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ)
    (x : Point3),
      Admissible u T →
      VorticityL1LinfControl u T →
      VelocityLogSpatialC3 u →
      ¬ VelocityJetFailureAt u T x

/--
A proof of the classical vorticity continuation implication produces a
concrete `ContinuationControl`.
-/
noncomputable def vorticityL1LinfContinuationControl
    (
      Admissible :
        PrimeTensor.SpaceTimeVectorField
            ℝ ℝ PrimeTensor.MulReal Depth.three →
          ℝ →
          Prop
    )
    (
      hClose :
        VorticityL1LinfClosesJets
          Admissible
    ) :
    ContinuationControl where

  Admissible :=
    Admissible

  Holds :=
    VorticityL1LinfControl

  closesJets :=
    hClose

/--
Once the classical vorticity continuation theorem is supplied, a cofinally
unresolved X-vorticity balance forces failure of the concrete
`L¹_t L∞_x` vorticity control.
-/
theorem not_vorticityL1LinfControl_of_cofinalVorticityBalancePathX
    {
      Admissible :
        PrimeTensor.SpaceTimeVectorField
            ℝ ℝ PrimeTensor.MulReal Depth.three →
          ℝ →
          Prop
    }
    (
      hClose :
        VorticityL1LinfClosesJets
          Admissible
    )
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    (
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceX
            u (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceX
          u T x
    )
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hAdmissible :
        Admissible u T
    )
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (
            vorticityBalancePerturbationPathX
              (constantVelocityRefinement u)
              u τ T x
          )
    ) :
    ¬ VorticityL1LinfControl u T := by

  let C : ContinuationControl :=
    vorticityL1LinfContinuationControl
      Admissible hClose

  exact
    C.not_holds_of_cofinalVorticityBalancePathX
      hτ
      hStages
      hLimit
      hSpatial
      hAdmissible
      hFailure

/--
Y-component analogue.
-/
theorem not_vorticityL1LinfControl_of_cofinalVorticityBalancePathY
    {
      Admissible :
        PrimeTensor.SpaceTimeVectorField
            ℝ ℝ PrimeTensor.MulReal Depth.three →
          ℝ →
          Prop
    }
    (
      hClose :
        VorticityL1LinfClosesJets
          Admissible
    )
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    (
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceY
            u (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceY
          u T x
    )
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hAdmissible :
        Admissible u T
    )
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (
            vorticityBalancePerturbationPathY
              (constantVelocityRefinement u)
              u τ T x
          )
    ) :
    ¬ VorticityL1LinfControl u T := by

  let C : ContinuationControl :=
    vorticityL1LinfContinuationControl
      Admissible hClose

  exact
    C.not_holds_of_cofinalVorticityBalancePathY
      hτ
      hStages
      hLimit
      hSpatial
      hAdmissible
      hFailure

/--
Z-component analogue.
-/
theorem not_vorticityL1LinfControl_of_cofinalVorticityBalancePathZ
    {
      Admissible :
        PrimeTensor.SpaceTimeVectorField
            ℝ ℝ PrimeTensor.MulReal Depth.three →
          ℝ →
          Prop
    }
    (
      hClose :
        VorticityL1LinfClosesJets
          Admissible
    )
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    (
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceZ
            u (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceZ
          u T x
    )
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hAdmissible :
        Admissible u T
    )
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (
            vorticityBalancePerturbationPathZ
              (constantVelocityRefinement u)
              u τ T x
          )
    ) :
    ¬ VorticityL1LinfControl u T := by

  let C : ContinuationControl :=
    vorticityL1LinfContinuationControl
      Admissible hClose

  exact
    C.not_holds_of_cofinalVorticityBalancePathZ
      hτ
      hStages
      hLimit
      hSpatial
      hAdmissible
      hFailure

/--
Positive X-component form: an admissible field satisfying the concrete
vorticity `L¹_t L∞_x` control cannot support a cofinally unresolved
multiplicative balance path.
-/
theorem noCofinalVorticityBalancePathX_of_vorticityL1LinfControl
    {
      Admissible :
        PrimeTensor.SpaceTimeVectorField
            ℝ ℝ PrimeTensor.MulReal Depth.three →
          ℝ →
          Prop
    }
    (
      hClose :
        VorticityL1LinfClosesJets
          Admissible
    )
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    (
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceX
            u (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceX
          u T x
    )
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hAdmissible :
        Admissible u T
    )
    (
      hControl :
        VorticityL1LinfControl u T
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathX
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  let C : ContinuationControl :=
    vorticityL1LinfContinuationControl
      Admissible hClose

  exact
    C.noCofinalVorticityBalancePathX_of_holds
      hτ
      hStages
      hLimit
      hSpatial
      hAdmissible
      hControl

/-- Y-component positive form. -/
theorem noCofinalVorticityBalancePathY_of_vorticityL1LinfControl
    {
      Admissible :
        PrimeTensor.SpaceTimeVectorField
            ℝ ℝ PrimeTensor.MulReal Depth.three →
          ℝ →
          Prop
    }
    (
      hClose :
        VorticityL1LinfClosesJets
          Admissible
    )
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    (
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceY
            u (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceY
          u T x
    )
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hAdmissible :
        Admissible u T
    )
    (
      hControl :
        VorticityL1LinfControl u T
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathY
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  let C : ContinuationControl :=
    vorticityL1LinfContinuationControl
      Admissible hClose

  exact
    C.noCofinalVorticityBalancePathY_of_holds
      hτ
      hStages
      hLimit
      hSpatial
      hAdmissible
      hControl

/-- Z-component positive form. -/
theorem noCofinalVorticityBalancePathZ_of_vorticityL1LinfControl
    {
      Admissible :
        PrimeTensor.SpaceTimeVectorField
            ℝ ℝ PrimeTensor.MulReal Depth.three →
          ℝ →
          Prop
    }
    (
      hClose :
        VorticityL1LinfClosesJets
          Admissible
    )
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    (
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceZ
            u (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceZ
          u T x
    )
    (
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hAdmissible :
        Admissible u T
    )
    (
      hControl :
        VorticityL1LinfControl u T
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathZ
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  let C : ContinuationControl :=
    vorticityL1LinfContinuationControl
      Admissible hClose

  exact
    C.noCofinalVorticityBalancePathZ_of_holds
      hτ
      hStages
      hLimit
      hSpatial
      hAdmissible
      hControl

end Euclidean
end Bridge
end PrimeTensor
