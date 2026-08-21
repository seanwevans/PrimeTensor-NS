import PrimeTensor.Fluid.VorticityAsymptoticStretching

/-!
# Native vortex-stretching scale demand

The asymptotic vorticity theorem has already concentrated cofinal unresolved
right-hand balance demand into the stretching slot, provided the diffusion
branch converges.

This file opens that stretching slot one algebraic layer further.

For a component `j`, native vortex stretching is exactly

    C(ωₓ, ∂ₓuⱼ) * (C(ωᵧ, ∂ᵧuⱼ) * C(ω_z, ∂_zuⱼ)),

where `C` is the canonical completed log-product coupling.

Because multiplication consumes one intrinsic refinement level, if all three
relative coupling terms are resolved two levels finer than a requested
stretching-product scale, then the whole relative stretching product is
resolved.  Contrapositively, unresolved stretching forces at least one of the
three actual coupling terms to remain unresolved.

Applied to the cofinal asymptotic stretching theorem, this yields cofinal
failure among the three nonlinear coupling terms.

This deliberately stops at the coupling boundary.  The current project proves
the scale control needed to construct and descend the canonical completed
coupling, but does not yet expose a quotient-level theorem saying that
`MulReal.ScaleNear` inputs produce `MulReal.ScaleNear` coupling outputs.
Therefore no claim is made here that a failed coupling output already implies
failure of its vorticity input or velocity-gradient input.

No norm, subtraction, additive identity, ordinary metric, logarithm, or
zeroth scale is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- The x-directed coupling term contributing to stretching component `j`. -/
noncomputable def mulVortexStretchTermX
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.MulReal :=
  PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
    (mulVorticityX u t x)
    (
      mulSpatial3.d
        xAxis
        (fun y =>
          (u t y).component j)
        x
    )

/-- The y-directed coupling term contributing to stretching component `j`. -/
noncomputable def mulVortexStretchTermY
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.MulReal :=
  PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
    (mulVorticityY u t x)
    (
      mulSpatial3.d
        yAxis
        (fun y =>
          (u t y).component j)
        x
    )

/-- The z-directed coupling term contributing to stretching component `j`. -/
noncomputable def mulVortexStretchTermZ
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.MulReal :=
  PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
    (mulVorticityZ u t x)
    (
      mulSpatial3.d
        zAxis
        (fun y =>
          (u t y).component j)
        x
    )

/--
The native stretching component is definitionally the three coupling terms
combined by the native multiplicative fold.
-/
theorem mulVortexStretchComponent_eq_terms
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    mulVortexStretchComponent u t x j
      =
    mulVortexStretchTermX u t x j
      *
    (
      mulVortexStretchTermY u t x j
        *
      mulVortexStretchTermZ u t x j
    ) := by
  rfl

/-- Relative x-directed stretching coupling term between two fields. -/
noncomputable def mulVortexStretchTermRatioX
    (
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.MulReal :=
  MulReal.ratio
    (mulVortexStretchTermX u t x j)
    (mulVortexStretchTermX v t x j)

/-- Relative y-directed stretching coupling term between two fields. -/
noncomputable def mulVortexStretchTermRatioY
    (
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.MulReal :=
  MulReal.ratio
    (mulVortexStretchTermY u t x j)
    (mulVortexStretchTermY v t x j)

/-- Relative z-directed stretching coupling term between two fields. -/
noncomputable def mulVortexStretchTermRatioZ
    (
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.MulReal :=
  MulReal.ratio
    (mulVortexStretchTermZ u t x j)
    (mulVortexStretchTermZ v t x j)

/--
The relative stretching component factors exactly into the three relative
coupling terms.
-/
theorem ratio_mulVortexStretchComponent_eq_termRatios
    (
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    MulReal.ratio
        (mulVortexStretchComponent u t x j)
        (mulVortexStretchComponent v t x j)
      =
    mulVortexStretchTermRatioX u v t x j
      *
    (
      mulVortexStretchTermRatioY u v t x j
        *
      mulVortexStretchTermRatioZ u v t x j
    ) := by

  rw [
    mulVortexStretchComponent_eq_terms,
    mulVortexStretchComponent_eq_terms,
    MulReal.ratio_mul_pair,
    MulReal.ratio_mul_pair
  ]

  rfl

/--
At a balance scale `level`, failure of at least one of the three stretching
coupling terms is measured three successors deeper.

One successor is already present in `StretchingFailureAt`; the remaining two
are the exact cost of resolving a three-factor multiplicative product.
-/
def StretchCouplingFailureAt
    (
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three)
    (level : Depth) : Prop :=
  (
    ¬ MulReal.ScaleNear
        (.succ (.succ (.succ level)))
        (mulVortexStretchTermRatioX u v t x j)
        1
  )
    ∨
  (
    ¬ MulReal.ScaleNear
        (.succ (.succ (.succ level)))
        (mulVortexStretchTermRatioY u v t x j)
        1
  )
    ∨
  (
    ¬ MulReal.ScaleNear
        (.succ (.succ (.succ level)))
        (mulVortexStretchTermRatioZ u v t x j)
        1
  )

/--
If the whole relative stretching component fails at the one-finer scale used
by the balance fork, then at least one actual coupling term fails three levels
deeper than the balance scale.
-/
theorem stretchCouplingFailure_of_stretchingRatioFailure
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    {j : PrimeTensor.Axis Depth.three}
    {level : Depth}
    (
      hFailure :
        ¬ MulReal.ScaleNear
            (.succ level)
            (
              MulReal.ratio
                (mulVortexStretchComponent u t x j)
                (mulVortexStretchComponent v t x j)
            )
            1
    ) :
    StretchCouplingFailureAt
      u v t x j level := by

  unfold StretchCouplingFailureAt

  by_cases hx :
    MulReal.ScaleNear
      (.succ (.succ (.succ level)))
      (mulVortexStretchTermRatioX u v t x j)
      1

  · by_cases hy :
      MulReal.ScaleNear
        (.succ (.succ (.succ level)))
        (mulVortexStretchTermRatioY u v t x j)
        1

    · by_cases hz :
        MulReal.ScaleNear
          (.succ (.succ (.succ level)))
          (mulVortexStretchTermRatioZ u v t x j)
          1

      · have hx' :
          MulReal.ScaleNear
            (.succ (.succ level))
            (mulVortexStretchTermRatioX u v t x j)
            1 :=
          MulReal.scaleNear_succ_weaken hx

        have hyz :
            MulReal.ScaleNear
              (.succ (.succ level))
              (
                mulVortexStretchTermRatioY u v t x j
                  *
                mulVortexStretchTermRatioZ u v t x j
              )
              1 := by

          have hProduct :=
            MulReal.scaleNear_mul hy hz

          simpa using hProduct

        have hAll :
            MulReal.ScaleNear
              (.succ level)
              (
                mulVortexStretchTermRatioX u v t x j
                  *
                (
                  mulVortexStretchTermRatioY u v t x j
                    *
                  mulVortexStretchTermRatioZ u v t x j
                )
              )
              1 := by

          have hProduct :=
            MulReal.scaleNear_mul hx' hyz

          simpa using hProduct

        rw [
          ratio_mulVortexStretchComponent_eq_termRatios
        ] at hFailure

        exact False.elim (hFailure hAll)

      · exact Or.inr (Or.inr hz)

    · exact Or.inr (Or.inl hy)

  · exact Or.inl hx

/--
The stretching slot of the relative x-vorticity balance state failing at
`level` forces failure of one of the three actual x-component stretching
coupling terms.
-/
theorem vorticityBalancePerturbationX_stretchCouplingFailure
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    {level : Depth}
    (
      hFailure :
        MulBalanceState.StretchingFailureAt
          (vorticityBalancePerturbationX u v t x)
          level
    ) :
    StretchCouplingFailureAt
      u v t x xAxis level := by

  apply
    stretchCouplingFailure_of_stretchingRatioFailure

  simpa [
    MulBalanceState.StretchingFailureAt,
    vorticityBalancePerturbationX,
    MulBalanceState.ratio,
    vorticityBalanceStateX
  ] using hFailure

/--
The stretching slot of the relative y-vorticity balance state failing at
`level` forces failure of one of the three actual y-component stretching
coupling terms.
-/
theorem vorticityBalancePerturbationY_stretchCouplingFailure
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    {level : Depth}
    (
      hFailure :
        MulBalanceState.StretchingFailureAt
          (vorticityBalancePerturbationY u v t x)
          level
    ) :
    StretchCouplingFailureAt
      u v t x yAxis level := by

  apply
    stretchCouplingFailure_of_stretchingRatioFailure

  simpa [
    MulBalanceState.StretchingFailureAt,
    vorticityBalancePerturbationY,
    MulBalanceState.ratio,
    vorticityBalanceStateY
  ] using hFailure

/--
The stretching slot of the relative z-vorticity balance state failing at
`level` forces failure of one of the three actual z-component stretching
coupling terms.
-/
theorem vorticityBalancePerturbationZ_stretchCouplingFailure
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    {level : Depth}
    (
      hFailure :
        MulBalanceState.StretchingFailureAt
          (vorticityBalancePerturbationZ u v t x)
          level
    ) :
    StretchCouplingFailureAt
      u v t x zAxis level := by

  apply
    stretchCouplingFailure_of_stretchingRatioFailure

  simpa [
    MulBalanceState.StretchingFailureAt,
    vorticityBalancePerturbationZ,
    MulBalanceState.ratio,
    vorticityBalanceStateZ
  ] using hFailure

/--
For a velocity refinement family, stretching coupling failure occurs
arbitrarily late at every intrinsic balance scale.
-/
def CofinalStretchCouplingFailureAtEveryScale
    (U : VelocityRefinementSeq)
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : Prop :=
  ∀ level anchor : Depth,
    ∃ n : Depth,
      Depth.AtOrAfter anchor n
        ∧
      StretchCouplingFailureAt
        (U n) u t x j level

/--
Cofinal x-component stretching failure descends to cofinal failure among the
three actual nonlinear coupling terms.
-/
theorem vorticityBalancePerturbationSeqX_cofinalStretchCouplingFailure
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
    (
      hStretch :
        MulBalanceState.CofinalStretchingFailureAtEveryScale
          (vorticityBalancePerturbationSeqX U u t x)
    ) :
    CofinalStretchCouplingFailureAtEveryScale
      U u t x xAxis := by

  intro level anchor

  obtain ⟨n, hn, hFailure⟩ :=
    hStretch level anchor

  refine ⟨n, hn, ?_⟩

  exact
    vorticityBalancePerturbationX_stretchCouplingFailure
      hFailure

/--
Cofinal y-component stretching failure descends to cofinal failure among the
three actual nonlinear coupling terms.
-/
theorem vorticityBalancePerturbationSeqY_cofinalStretchCouplingFailure
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
    (
      hStretch :
        MulBalanceState.CofinalStretchingFailureAtEveryScale
          (vorticityBalancePerturbationSeqY U u t x)
    ) :
    CofinalStretchCouplingFailureAtEveryScale
      U u t x yAxis := by

  intro level anchor

  obtain ⟨n, hn, hFailure⟩ :=
    hStretch level anchor

  refine ⟨n, hn, ?_⟩

  exact
    vorticityBalancePerturbationY_stretchCouplingFailure
      hFailure

/--
Cofinal z-component stretching failure descends to cofinal failure among the
three actual nonlinear coupling terms.
-/
theorem vorticityBalancePerturbationSeqZ_cofinalStretchCouplingFailure
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
    (
      hStretch :
        MulBalanceState.CofinalStretchingFailureAtEveryScale
          (vorticityBalancePerturbationSeqZ U u t x)
    ) :
    CofinalStretchCouplingFailureAtEveryScale
      U u t x zAxis := by

  intro level anchor

  obtain ⟨n, hn, hFailure⟩ :=
    hStretch level anchor

  refine ⟨n, hn, ?_⟩

  exact
    vorticityBalancePerturbationZ_stretchCouplingFailure
      hFailure

end Euclidean
end Bridge
end PrimeTensor
