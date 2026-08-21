import PrimeTensor.Fluid.Vorticity.Coupling.Continuity

/-!
# Primitive cofinal leaves of a native vorticity cascade

`VorticityCouplingContinuity` proves that a cofinal stretching-coupling cascade
is incompatible with convergence of all six primitive inputs

    ωₓ, ∂ₓuⱼ, ωᵧ, ∂ᵧuⱼ, ω_z, ∂_zuⱼ.

This file puts that obstruction into the intrinsic cofinal form appropriate for
a cascade argument.

For a `MulReal` refinement sequence, failure to converge is exactly the
existence of one fixed positive intrinsic scale at which failure occurs
arbitrarily late:

    ¬ (sₙ → x)
      ↔
    ∃ level, ∀ anchor, ∃ n ≥ anchor,
      ¬ ScaleNear level (sₙ) x.

Thus a cofinal unresolved vorticity cascade has an actual primitive leaf:
one of the three native vorticity values or one of the three matching
velocity-gradient values fails cofinally at one fixed intrinsic scale.

No diagonal convergence rate is asserted.  The failed scale may depend on the
primitive leaf, but once chosen it is fixed while the refinement stage runs
cofinally late.
-/

namespace PrimeTensor

namespace MulReal

/--
A refinement sequence fails at one fixed intrinsic scale arbitrarily late.
-/
def CofinalFailureAtScale
    (s : Seq)
    (x : MulReal)
    (level : Depth) : Prop :=
  ∀ anchor : Depth,
    ∃ n : Depth,
      Depth.AtOrAfter anchor n
        ∧
      ¬ ScaleNear level (s n) x

/--
Intrinsic nonconvergence is exactly cofinal failure at some fixed positive
intrinsic scale.
-/
theorem not_convergesTo_iff_exists_cofinalFailureAtScale
    (s : Seq)
    (x : MulReal) :
    ¬ ConvergesTo s x
      ↔
    ∃ level : Depth,
      CofinalFailureAtScale
        s x level := by

  unfold ConvergesTo
  unfold CofinalFailureAtScale
  push_neg
  rfl

end MulReal

namespace Bridge
namespace Euclidean

/--
One of the six primitive inputs to stretching component `j` fails cofinally at
a fixed intrinsic scale.
-/
def StretchingPrimitiveCofinalFailure
    (U : VelocityRefinementSeq)
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : Prop :=
  (
    ∃ level : Depth,
      PrimeTensor.MulReal.CofinalFailureAtScale
        (vorticityPointSeqX U t x)
        (mulVorticityX u t x)
        level
  )
    ∨
  (
    ∃ level : Depth,
      PrimeTensor.MulReal.CofinalFailureAtScale
        (velocityGradientPointSeqX U t x j)
        (
          mulSpatial3.d
            xAxis
            (fun y => (u t y).component j)
            x
        )
        level
  )
    ∨
  (
    ∃ level : Depth,
      PrimeTensor.MulReal.CofinalFailureAtScale
        (vorticityPointSeqY U t x)
        (mulVorticityY u t x)
        level
  )
    ∨
  (
    ∃ level : Depth,
      PrimeTensor.MulReal.CofinalFailureAtScale
        (velocityGradientPointSeqY U t x j)
        (
          mulSpatial3.d
            yAxis
            (fun y => (u t y).component j)
            x
        )
        level
  )
    ∨
  (
    ∃ level : Depth,
      PrimeTensor.MulReal.CofinalFailureAtScale
        (vorticityPointSeqZ U t x)
        (mulVorticityZ u t x)
        level
  )
    ∨
  (
    ∃ level : Depth,
      PrimeTensor.MulReal.CofinalFailureAtScale
        (velocityGradientPointSeqZ U t x j)
        (
          mulSpatial3.d
            zAxis
            (fun y => (u t y).component j)
            x
        )
        level
  )

/--
Failure of simultaneous convergence of all six primitive stretching inputs
produces an explicit cofinal primitive leaf.
-/
theorem stretchingPrimitiveCofinalFailure_of_not_convergent
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    {j : PrimeTensor.Axis Depth.three}
    (
      h :
        ¬ StretchingPrimitiveConvergent
            U u t x j
    ) :
    StretchingPrimitiveCofinalFailure
      U u t x j := by

  unfold StretchingPrimitiveCofinalFailure

  by_cases hωx :
    PrimeTensor.MulReal.ConvergesTo
      (vorticityPointSeqX U t x)
      (mulVorticityX u t x)

  · by_cases hDx :
      PrimeTensor.MulReal.ConvergesTo
        (velocityGradientPointSeqX U t x j)
        (
          mulSpatial3.d
            xAxis
            (fun y => (u t y).component j)
            x
        )

    · by_cases hωy :
        PrimeTensor.MulReal.ConvergesTo
          (vorticityPointSeqY U t x)
          (mulVorticityY u t x)

      · by_cases hDy :
          PrimeTensor.MulReal.ConvergesTo
            (velocityGradientPointSeqY U t x j)
            (
              mulSpatial3.d
                yAxis
                (fun y => (u t y).component j)
                x
            )

        · by_cases hωz :
            PrimeTensor.MulReal.ConvergesTo
              (vorticityPointSeqZ U t x)
              (mulVorticityZ u t x)

          · by_cases hDz :
              PrimeTensor.MulReal.ConvergesTo
                (velocityGradientPointSeqZ U t x j)
                (
                  mulSpatial3.d
                    zAxis
                    (fun y => (u t y).component j)
                    x
                )

            · exfalso
              apply h
              unfold StretchingPrimitiveConvergent
              exact
                ⟨hωx, hDx, hωy, hDy, hωz, hDz⟩

            · have hLeaf :=
                (
                  PrimeTensor.MulReal.not_convergesTo_iff_exists_cofinalFailureAtScale
                    _
                    _
                ).1 hDz

              exact
                Or.inr
                  (
                    Or.inr
                      (
                        Or.inr
                          (
                            Or.inr
                              (
                                Or.inr hLeaf
                              )
                          )
                      )
                  )

          · have hLeaf :=
              (
                PrimeTensor.MulReal.not_convergesTo_iff_exists_cofinalFailureAtScale
                  _
                  _
              ).1 hωz

            exact
              Or.inr
                (
                  Or.inr
                    (
                      Or.inr
                        (
                          Or.inr
                            (
                              Or.inl hLeaf
                            )
                        )
                    )
                )

        · have hLeaf :=
            (
              PrimeTensor.MulReal.not_convergesTo_iff_exists_cofinalFailureAtScale
                _
                _
            ).1 hDy

          exact
            Or.inr
              (
                Or.inr
                  (
                    Or.inr
                      (
                        Or.inl hLeaf
                      )
                  )
              )

      · have hLeaf :=
          (
            PrimeTensor.MulReal.not_convergesTo_iff_exists_cofinalFailureAtScale
              _
              _
          ).1 hωy

        exact
          Or.inr
            (
              Or.inr
                (
                  Or.inl hLeaf
                )
            )

    · have hLeaf :=
        (
          PrimeTensor.MulReal.not_convergesTo_iff_exists_cofinalFailureAtScale
            _
            _
        ).1 hDx

      exact
        Or.inr
          (
            Or.inl hLeaf
          )

  · have hLeaf :=
      (
        PrimeTensor.MulReal.not_convergesTo_iff_exists_cofinalFailureAtScale
          _
          _
      ).1 hωx

    exact
      Or.inl hLeaf

/--
Cofinal failure among the nonlinear stretching coupling terms produces an
explicit primitive cofinal leaf.
-/
theorem stretchingPrimitiveCofinalFailure_of_cofinalStretchCouplingFailure
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    {j : PrimeTensor.Axis Depth.three}
    (
      hFailure :
        CofinalStretchCouplingFailureAtEveryScale
          U u t x j
    ) :
    StretchingPrimitiveCofinalFailure
      U u t x j := by

  apply
    stretchingPrimitiveCofinalFailure_of_not_convergent

  exact
    not_stretchingPrimitiveConvergent_of_cofinalStretchCouplingFailure
      hFailure

/--
Full x-component primitive leaf theorem.

A balanced refinement family with cofinal unresolved x-vorticity demand and
convergent x-vorticity second jets has at least one primitive vorticity or
velocity-gradient channel that fails at a fixed intrinsic scale arbitrarily
late.
-/
theorem vorticityBalancePerturbationSeqX_primitiveCofinalFailure
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (hStages :
      ∀ n : Depth,
        MulVorticityBalanceX
          (U n) t x)
    (hLimit :
      MulVorticityBalanceX
        u t x)
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (vorticityBalancePerturbationSeqX
            U u t x)
    )
    (
      hSecondJet :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldSeqX U t)
          (vorticityFieldX u t)
    ) :
    StretchingPrimitiveCofinalFailure
      U u t x xAxis := by

  apply
    stretchingPrimitiveCofinalFailure_of_not_convergent

  exact
    vorticityBalancePerturbationSeqX_primitiveObstruction
      hStages hLimit hFailure hSecondJet

/-- Full y-component primitive leaf theorem. -/
theorem vorticityBalancePerturbationSeqY_primitiveCofinalFailure
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (hStages :
      ∀ n : Depth,
        MulVorticityBalanceY
          (U n) t x)
    (hLimit :
      MulVorticityBalanceY
        u t x)
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (vorticityBalancePerturbationSeqY
            U u t x)
    )
    (
      hSecondJet :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldSeqY U t)
          (vorticityFieldY u t)
    ) :
    StretchingPrimitiveCofinalFailure
      U u t x yAxis := by

  apply
    stretchingPrimitiveCofinalFailure_of_not_convergent

  exact
    vorticityBalancePerturbationSeqY_primitiveObstruction
      hStages hLimit hFailure hSecondJet

/-- Full z-component primitive leaf theorem. -/
theorem vorticityBalancePerturbationSeqZ_primitiveCofinalFailure
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (hStages :
      ∀ n : Depth,
        MulVorticityBalanceZ
          (U n) t x)
    (hLimit :
      MulVorticityBalanceZ
        u t x)
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (vorticityBalancePerturbationSeqZ
            U u t x)
    )
    (
      hSecondJet :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldSeqZ U t)
          (vorticityFieldZ u t)
    ) :
    StretchingPrimitiveCofinalFailure
      U u t x zAxis := by

  apply
    stretchingPrimitiveCofinalFailure_of_not_convergent

  exact
    vorticityBalancePerturbationSeqZ_primitiveObstruction
      hStages hLimit hFailure hSecondJet

end Euclidean
end Bridge
end PrimeTensor
