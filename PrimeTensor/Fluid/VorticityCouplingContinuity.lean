import PrimeTensor.Fluid.VorticityStretchingDemand
import PrimeTensor.Bridge.MulRealScaleSemantics

/-!
# Sequential continuity of the canonical coupling and primitive stretching obstruction

The canonical completed logarithmic product coupling satisfies

    log C(a,b) = log a * log b.

The completed intrinsic topology has already been identified exactly with
ordinary convergence of canonical logarithmic coordinates.  Therefore the
canonical coupling is sequentially continuous in both inputs for the intrinsic
`MulReal.ConvergesTo` relation.

This is the correct continuity statement for the log-product coupling.  A
global input-scale modulus independent of the base inputs would be false in
general because the sensitivity of `log a * log b` depends on the base point.

The continuity theorem closes the next link in the vorticity cascade:

* cofinal unresolved balance,
* plus convergent diffusion,
* forces cofinal stretching failure;
* stretching failure forces failure among the three actual coupling terms;
* if all six primitive inputs `ω_i` and `∂_i u_j` converged, sequential
  continuity of the coupling would make all three coupling-term ratios converge
  to the pivot.

Hence a cofinal stretching cascade forces failure of convergence in at least
one primitive vorticity or velocity-gradient channel.

No norm, subtraction, additive identity, ordinary metric, or zeroth native
scale is introduced into the native statements.
-/

namespace PrimeTensor
namespace Bridge
namespace PrimePairApprox

/--
The canonical completed log-product coupling preserves intrinsic sequential
convergence in both inputs.
-/
theorem logProductCoupling_converges
    {a b : PrimeTensor.MulReal.Seq}
    {x y : PrimeTensor.MulReal}
    (ha : PrimeTensor.MulReal.ConvergesTo a x)
    (hb : PrimeTensor.MulReal.ConvergesTo b y) :
    PrimeTensor.MulReal.ConvergesTo
      (
        fun n =>
          logProductCoupling.couple
            (a n)
            (b n)
      )
      (logProductCoupling.couple x y) := by

  apply
    (
      PrimeTensor.Bridge.MulReal.convergesTo_iff_logValue_tendsto
          (
            fun n =>
              logProductCoupling.couple
                (a n)
                (b n)
          )
          (logProductCoupling.couple x y)
    ).2

  have haLog :=
    (
      PrimeTensor.Bridge.MulReal.convergesTo_iff_logValue_tendsto
          a x
    ).1 ha

  have hbLog :=
    (
      PrimeTensor.Bridge.MulReal.convergesTo_iff_logValue_tendsto
          b y
    ).1 hb

  have hProduct :=
    haLog.mul hbLog

  simpa only [
    logProductCoupling_logValue
  ] using hProduct

/--
The relative output of the canonical coupling converges to the multiplicative
pivot whenever both inputs converge.
-/
theorem logProductCoupling_ratio_convergesTo_one
    {a b : PrimeTensor.MulReal.Seq}
    {x y : PrimeTensor.MulReal}
    (ha : PrimeTensor.MulReal.ConvergesTo a x)
    (hb : PrimeTensor.MulReal.ConvergesTo b y) :
    PrimeTensor.MulReal.ConvergesTo
      (
        fun n =>
          PrimeTensor.MulReal.ratio
            (
              logProductCoupling.couple
                (a n)
                (b n)
            )
            (logProductCoupling.couple x y)
      )
      1 := by

  have hCoupling :=
    logProductCoupling_converges
      ha hb

  have hLimit :=
    PrimeTensor.MulReal.converges_constant
      (logProductCoupling.couple x y)

  have hRatio :=
    PrimeTensor.MulReal.converges_ratio
      hCoupling hLimit

  simpa using hRatio

end PrimePairApprox

namespace Euclidean

/-- Native x-vorticity values along a velocity refinement family at fixed `t,x`. -/
noncomputable def vorticityPointSeqX
    (U : VelocityRefinementSeq)
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.MulReal.Seq :=
  fun n =>
    mulVorticityX
      (U n) t x

/-- Native y-vorticity values along a velocity refinement family at fixed `t,x`. -/
noncomputable def vorticityPointSeqY
    (U : VelocityRefinementSeq)
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.MulReal.Seq :=
  fun n =>
    mulVorticityY
      (U n) t x

/-- Native z-vorticity values along a velocity refinement family at fixed `t,x`. -/
noncomputable def vorticityPointSeqZ
    (U : VelocityRefinementSeq)
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.MulReal.Seq :=
  fun n =>
    mulVorticityZ
      (U n) t x

/-- The x-directed velocity-gradient input to stretching component `j`. -/
noncomputable def velocityGradientPointSeqX
    (U : VelocityRefinementSeq)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.MulReal.Seq :=
  fun n =>
    mulSpatial3.d
      xAxis
      (
        fun y =>
          ((U n) t y).component j
      )
      x

/-- The y-directed velocity-gradient input to stretching component `j`. -/
noncomputable def velocityGradientPointSeqY
    (U : VelocityRefinementSeq)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.MulReal.Seq :=
  fun n =>
    mulSpatial3.d
      yAxis
      (
        fun y =>
          ((U n) t y).component j
      )
      x

/-- The z-directed velocity-gradient input to stretching component `j`. -/
noncomputable def velocityGradientPointSeqZ
    (U : VelocityRefinementSeq)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.MulReal.Seq :=
  fun n =>
    mulSpatial3.d
      zAxis
      (
        fun y =>
          ((U n) t y).component j
      )
      x

/--
All six primitive inputs needed by one stretching component converge at the
chosen spacetime point.
-/
def StretchingPrimitiveConvergent
    (U : VelocityRefinementSeq)
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : Prop :=
  PrimeTensor.MulReal.ConvergesTo
      (vorticityPointSeqX U t x)
      (mulVorticityX u t x)
    ∧
  PrimeTensor.MulReal.ConvergesTo
      (velocityGradientPointSeqX U t x j)
      (
        mulSpatial3.d
          xAxis
          (fun y => (u t y).component j)
          x
      )
    ∧
  PrimeTensor.MulReal.ConvergesTo
      (vorticityPointSeqY U t x)
      (mulVorticityY u t x)
    ∧
  PrimeTensor.MulReal.ConvergesTo
      (velocityGradientPointSeqY U t x j)
      (
        mulSpatial3.d
          yAxis
          (fun y => (u t y).component j)
          x
      )
    ∧
  PrimeTensor.MulReal.ConvergesTo
      (vorticityPointSeqZ U t x)
      (mulVorticityZ u t x)
    ∧
  PrimeTensor.MulReal.ConvergesTo
      (velocityGradientPointSeqZ U t x j)
      (
        mulSpatial3.d
          zAxis
          (fun y => (u t y).component j)
          x
      )

/--
Convergence of the x-directed primitive pair makes the relative x-directed
stretching coupling term converge to the pivot.
-/
theorem mulVortexStretchTermRatioX_convergesTo_one
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
      hω :
        PrimeTensor.MulReal.ConvergesTo
          (vorticityPointSeqX U t x)
          (mulVorticityX u t x)
    )
    (
      hD :
        PrimeTensor.MulReal.ConvergesTo
          (velocityGradientPointSeqX U t x j)
          (
            mulSpatial3.d
              xAxis
              (fun y => (u t y).component j)
              x
          )
    ) :
    PrimeTensor.MulReal.ConvergesTo
      (
        fun n =>
          mulVortexStretchTermRatioX
            (U n) u t x j
      )
      1 := by

  have hCoupling :=
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling_ratio_convergesTo_one
        hω hD

  simpa [
    vorticityPointSeqX,
    velocityGradientPointSeqX,
    mulVortexStretchTermRatioX,
    mulVortexStretchTermX
  ] using hCoupling

/--
Convergence of the y-directed primitive pair makes the relative y-directed
stretching coupling term converge to the pivot.
-/
theorem mulVortexStretchTermRatioY_convergesTo_one
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
      hω :
        PrimeTensor.MulReal.ConvergesTo
          (vorticityPointSeqY U t x)
          (mulVorticityY u t x)
    )
    (
      hD :
        PrimeTensor.MulReal.ConvergesTo
          (velocityGradientPointSeqY U t x j)
          (
            mulSpatial3.d
              yAxis
              (fun y => (u t y).component j)
              x
          )
    ) :
    PrimeTensor.MulReal.ConvergesTo
      (
        fun n =>
          mulVortexStretchTermRatioY
            (U n) u t x j
      )
      1 := by

  have hCoupling :=
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling_ratio_convergesTo_one
        hω hD

  simpa [
    vorticityPointSeqY,
    velocityGradientPointSeqY,
    mulVortexStretchTermRatioY,
    mulVortexStretchTermY
  ] using hCoupling

/--
Convergence of the z-directed primitive pair makes the relative z-directed
stretching coupling term converge to the pivot.
-/
theorem mulVortexStretchTermRatioZ_convergesTo_one
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
      hω :
        PrimeTensor.MulReal.ConvergesTo
          (vorticityPointSeqZ U t x)
          (mulVorticityZ u t x)
    )
    (
      hD :
        PrimeTensor.MulReal.ConvergesTo
          (velocityGradientPointSeqZ U t x j)
          (
            mulSpatial3.d
              zAxis
              (fun y => (u t y).component j)
              x
          )
    ) :
    PrimeTensor.MulReal.ConvergesTo
      (
        fun n =>
          mulVortexStretchTermRatioZ
            (U n) u t x j
      )
      1 := by

  have hCoupling :=
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling_ratio_convergesTo_one
        hω hD

  simpa [
    vorticityPointSeqZ,
    velocityGradientPointSeqZ,
    mulVortexStretchTermRatioZ,
    mulVortexStretchTermZ
  ] using hCoupling

/--
Cofinal failure among the three stretching coupling terms is incompatible with
convergence of all six primitive inputs.

Thus at least one native vorticity channel or one matching velocity-gradient
channel must fail to converge.
-/
theorem not_stretchingPrimitiveConvergent_of_cofinalStretchCouplingFailure
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
    ¬ StretchingPrimitiveConvergent
        U u t x j := by

  intro hPrimitive

  rcases hPrimitive with
    ⟨hωx, hDx, hωy, hDy, hωz, hDz⟩

  have hX :=
    mulVortexStretchTermRatioX_convergesTo_one
      hωx hDx

  have hY :=
    mulVortexStretchTermRatioY_convergesTo_one
      hωy hDy

  have hZ :=
    mulVortexStretchTermRatioZ_convergesTo_one
      hωz hDz

  let level : Depth := .one

  obtain ⟨xAnchor, hXTail⟩ :=
    hX (.succ (.succ (.succ level)))

  obtain ⟨yAnchor, hYTail⟩ :=
    hY (.succ (.succ (.succ level)))

  obtain ⟨zAnchor, hZTail⟩ :=
    hZ (.succ (.succ (.succ level)))

  let yzAnchor :=
    Depth.join yAnchor zAnchor

  let commonAnchor :=
    Depth.join xAnchor yzAnchor

  obtain ⟨n, hnCommon, hFailN⟩ :=
    hFailure level commonAnchor

  have hnX :
      Depth.AtOrAfter xAnchor n := by

    exact
      Depth.atOrAfter_trans
        (Depth.left_atOrAfter xAnchor yzAnchor)
        hnCommon

  have hnYZ :
      Depth.AtOrAfter yzAnchor n := by

    exact
      Depth.atOrAfter_trans
        (Depth.right_atOrAfter xAnchor yzAnchor)
        hnCommon

  have hnY :
      Depth.AtOrAfter yAnchor n := by

    exact
      Depth.atOrAfter_trans
        (Depth.left_atOrAfter yAnchor zAnchor)
        hnYZ

  have hnZ :
      Depth.AtOrAfter zAnchor n := by

    exact
      Depth.atOrAfter_trans
        (Depth.right_atOrAfter yAnchor zAnchor)
        hnYZ

  have hXNear :=
    hXTail n hnX

  have hYNear :=
    hYTail n hnY

  have hZNear :=
    hZTail n hnZ

  unfold StretchCouplingFailureAt at hFailN

  rcases hFailN with hFailX | hFailY | hFailZ

  · exact hFailX hXNear
  · exact hFailY hYNear
  · exact hFailZ hZNear

/--
Full x-component primitive obstruction.

Balanced approximants with cofinal unresolved x-vorticity demand and convergent
x-vorticity second jets cannot have all six primitive stretching inputs
converge at the selected point.
-/
theorem vorticityBalancePerturbationSeqX_primitiveObstruction
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
    ¬ StretchingPrimitiveConvergent
        U u t x xAxis := by

  have hStretch :=
    vorticityBalancePerturbationSeqX_cofinalStretching
      hStages hLimit hFailure hSecondJet

  have hCoupling :=
    vorticityBalancePerturbationSeqX_cofinalStretchCouplingFailure
      hStretch

  exact
    not_stretchingPrimitiveConvergent_of_cofinalStretchCouplingFailure
      hCoupling

/-- Full y-component primitive obstruction. -/
theorem vorticityBalancePerturbationSeqY_primitiveObstruction
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
    ¬ StretchingPrimitiveConvergent
        U u t x yAxis := by

  have hStretch :=
    vorticityBalancePerturbationSeqY_cofinalStretching
      hStages hLimit hFailure hSecondJet

  have hCoupling :=
    vorticityBalancePerturbationSeqY_cofinalStretchCouplingFailure
      hStretch

  exact
    not_stretchingPrimitiveConvergent_of_cofinalStretchCouplingFailure
      hCoupling

/-- Full z-component primitive obstruction. -/
theorem vorticityBalancePerturbationSeqZ_primitiveObstruction
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
    ¬ StretchingPrimitiveConvergent
        U u t x zAxis := by

  have hStretch :=
    vorticityBalancePerturbationSeqZ_cofinalStretching
      hStages hLimit hFailure hSecondJet

  have hCoupling :=
    vorticityBalancePerturbationSeqZ_cofinalStretchCouplingFailure
      hStretch

  exact
    not_stretchingPrimitiveConvergent_of_cofinalStretchCouplingFailure
      hCoupling

end Euclidean
end Bridge
end PrimeTensor
