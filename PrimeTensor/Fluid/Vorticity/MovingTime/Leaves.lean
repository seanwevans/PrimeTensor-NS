import PrimeTensor.Fluid.Vorticity.MovingTime

/-!
# Moving-time stretching descent and primitive cofinal leaves

`VorticityMovingTime` carries the native balance/diffusion cascade along a
stage-dependent real time path `τ n`, comparing stage `(U n, τ n)` with a
terminal field/time pair `(u,T)`.

This file opens the moving-time stretching slot and descends it to the same six
primitive channels as the fixed-time theory.

The central algebraic observation is independent of whether the numerator and
denominator are evaluated at the same time:

    ratio (stretch Uₙ (τₙ)) (stretch u T)

still factors exactly into the three ratios

    ratio C(ωₓ(Uₙ,τₙ), ∂ₓUₙⱼ(τₙ))
          C(ωₓ(u,T),   ∂ₓuⱼ(T))

and the corresponding y/z terms.

Consequently, cofinal unresolved moving-time balance demand plus convergent
diffusion forces a fixed-scale cofinal failure in at least one of

    ωₓ, ∂ₓuⱼ, ωᵧ, ∂ᵧuⱼ, ω_z, ∂_zuⱼ

along the actual moving-time path.

No convergence assumption on `τ` is made here.  A later finite-time
continuation module may impose `τ n -> T` and prove that PDE regularity forces
these primitive paths to converge, thereby contradicting the leaf theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Two-time relative x-directed stretching coupling term. -/
noncomputable def mulVortexStretchTermRatioAtX
    (
      a b :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (ta tb : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.MulReal :=
  MulReal.ratio
    (mulVortexStretchTermX a ta x j)
    (mulVortexStretchTermX b tb x j)

/-- Two-time relative y-directed stretching coupling term. -/
noncomputable def mulVortexStretchTermRatioAtY
    (
      a b :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (ta tb : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.MulReal :=
  MulReal.ratio
    (mulVortexStretchTermY a ta x j)
    (mulVortexStretchTermY b tb x j)

/-- Two-time relative z-directed stretching coupling term. -/
noncomputable def mulVortexStretchTermRatioAtZ
    (
      a b :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (ta tb : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.MulReal :=
  MulReal.ratio
    (mulVortexStretchTermZ a ta x j)
    (mulVortexStretchTermZ b tb x j)

/--
Two-time relative stretching factors exactly into the three two-time coupling
ratios.
-/
theorem ratio_mulVortexStretchComponent_eq_termRatiosAt
    (
      a b :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (ta tb : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    MulReal.ratio
        (mulVortexStretchComponent a ta x j)
        (mulVortexStretchComponent b tb x j)
      =
    mulVortexStretchTermRatioAtX a b ta tb x j
      *
    (
      mulVortexStretchTermRatioAtY a b ta tb x j
        *
      mulVortexStretchTermRatioAtZ a b ta tb x j
    ) := by

  rw [
    mulVortexStretchComponent_eq_terms,
    mulVortexStretchComponent_eq_terms,
    MulReal.ratio_mul_pair,
    MulReal.ratio_mul_pair
  ]

  rfl

/--
At balance scale `level`, a two-time stretching coupling failure means one of
the three coupling-term ratios fails at the exact three-successor scale.
-/
def StretchCouplingFailureAtTimes
    (
      a b :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (ta tb : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three)
    (level : Depth) : Prop :=
  (
    ¬ MulReal.ScaleNear
        (.succ (.succ (.succ level)))
        (mulVortexStretchTermRatioAtX
          a b ta tb x j)
        1
  )
    ∨
  (
    ¬ MulReal.ScaleNear
        (.succ (.succ (.succ level)))
        (mulVortexStretchTermRatioAtY
          a b ta tb x j)
        1
  )
    ∨
  (
    ¬ MulReal.ScaleNear
        (.succ (.succ (.succ level)))
        (mulVortexStretchTermRatioAtZ
          a b ta tb x j)
        1
  )

/--
Failure of the whole two-time stretching ratio forces one of the three
two-time coupling ratios to fail.
-/
theorem stretchCouplingFailureAtTimes_of_stretchingRatioFailure
    {
      a b :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {ta tb : ℝ}
    {x : Point3}
    {j : PrimeTensor.Axis Depth.three}
    {level : Depth}
    (
      hFailure :
        ¬ MulReal.ScaleNear
            (.succ level)
            (
              MulReal.ratio
                (mulVortexStretchComponent
                  a ta x j)
                (mulVortexStretchComponent
                  b tb x j)
            )
            1
    ) :
    StretchCouplingFailureAtTimes
      a b ta tb x j level := by

  unfold StretchCouplingFailureAtTimes

  by_cases hx :
    MulReal.ScaleNear
      (.succ (.succ (.succ level)))
      (mulVortexStretchTermRatioAtX
        a b ta tb x j)
      1

  · by_cases hy :
      MulReal.ScaleNear
        (.succ (.succ (.succ level)))
        (mulVortexStretchTermRatioAtY
          a b ta tb x j)
        1

    · by_cases hz :
        MulReal.ScaleNear
          (.succ (.succ (.succ level)))
          (mulVortexStretchTermRatioAtZ
            a b ta tb x j)
          1

      · have hx' :
          MulReal.ScaleNear
            (.succ (.succ level))
            (mulVortexStretchTermRatioAtX
              a b ta tb x j)
            1 :=
          MulReal.scaleNear_succ_weaken hx

        have hyz :
            MulReal.ScaleNear
              (.succ (.succ level))
              (
                mulVortexStretchTermRatioAtY
                    a b ta tb x j
                  *
                mulVortexStretchTermRatioAtZ
                    a b ta tb x j
              )
              1 := by

          have hProduct :=
            MulReal.scaleNear_mul hy hz

          simpa using hProduct

        have hAll :
            MulReal.ScaleNear
              (.succ level)
              (
                mulVortexStretchTermRatioAtX
                    a b ta tb x j
                  *
                (
                  mulVortexStretchTermRatioAtY
                      a b ta tb x j
                    *
                  mulVortexStretchTermRatioAtZ
                      a b ta tb x j
                )
              )
              1 := by

          have hProduct :=
            MulReal.scaleNear_mul hx' hyz

          simpa using hProduct

        rw [
          ratio_mulVortexStretchComponent_eq_termRatiosAt
        ] at hFailure

        exact False.elim (hFailure hAll)

      · exact Or.inr (Or.inr hz)

    · exact Or.inr (Or.inl hy)

  · exact Or.inl hx

/-- Moving-time x-balance stretching failure descends to the three couplings. -/
theorem vorticityBalancePerturbationPathX_stretchCouplingFailure
    {
      U : VelocityRefinementSeq
    }
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
    {n level : Depth}
    (
      hFailure :
        MulBalanceState.StretchingFailureAt
          (vorticityBalancePerturbationPathX
            U u τ T x n)
          level
    ) :
    StretchCouplingFailureAtTimes
      (U n) u (τ n) T x xAxis level := by

  apply
    stretchCouplingFailureAtTimes_of_stretchingRatioFailure

  simpa [
    MulBalanceState.StretchingFailureAt,
    vorticityBalancePerturbationPathX,
    MulBalanceState.ratio,
    vorticityBalanceStateX
  ] using hFailure

/-- Moving-time y-balance stretching failure descends to the three couplings. -/
theorem vorticityBalancePerturbationPathY_stretchCouplingFailure
    {
      U : VelocityRefinementSeq
    }
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
    {n level : Depth}
    (
      hFailure :
        MulBalanceState.StretchingFailureAt
          (vorticityBalancePerturbationPathY
            U u τ T x n)
          level
    ) :
    StretchCouplingFailureAtTimes
      (U n) u (τ n) T x yAxis level := by

  apply
    stretchCouplingFailureAtTimes_of_stretchingRatioFailure

  simpa [
    MulBalanceState.StretchingFailureAt,
    vorticityBalancePerturbationPathY,
    MulBalanceState.ratio,
    vorticityBalanceStateY
  ] using hFailure

/-- Moving-time z-balance stretching failure descends to the three couplings. -/
theorem vorticityBalancePerturbationPathZ_stretchCouplingFailure
    {
      U : VelocityRefinementSeq
    }
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
    {n level : Depth}
    (
      hFailure :
        MulBalanceState.StretchingFailureAt
          (vorticityBalancePerturbationPathZ
            U u τ T x n)
          level
    ) :
    StretchCouplingFailureAtTimes
      (U n) u (τ n) T x zAxis level := by

  apply
    stretchCouplingFailureAtTimes_of_stretchingRatioFailure

  simpa [
    MulBalanceState.StretchingFailureAt,
    vorticityBalancePerturbationPathZ,
    MulBalanceState.ratio,
    vorticityBalanceStateZ
  ] using hFailure

/--
Cofinal failure among the three actual stretching coupling terms along a
moving-time path.
-/
def CofinalStretchCouplingFailureAlongPath
    (U : VelocityRefinementSeq)
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (τ : TimeRefinementSeq)
    (T : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : Prop :=
  ∀ level anchor : Depth,
    ∃ n : Depth,
      Depth.AtOrAfter anchor n
        ∧
      StretchCouplingFailureAtTimes
        (U n) u (τ n) T x j level

/-- Cofinal x-stretching failure descends to moving-time coupling failure. -/
theorem vorticityBalancePerturbationPathX_cofinalStretchCouplingFailure
    {
      U : VelocityRefinementSeq
    }
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
      hStretch :
        MulBalanceState.CofinalStretchingFailureAtEveryScale
          (vorticityBalancePerturbationPathX
            U u τ T x)
    ) :
    CofinalStretchCouplingFailureAlongPath
      U u τ T x xAxis := by

  intro level anchor

  obtain ⟨n, hn, hFailure⟩ :=
    hStretch level anchor

  refine ⟨n, hn, ?_⟩

  exact
    vorticityBalancePerturbationPathX_stretchCouplingFailure
      hFailure

/-- Cofinal y-stretching failure descends to moving-time coupling failure. -/
theorem vorticityBalancePerturbationPathY_cofinalStretchCouplingFailure
    {
      U : VelocityRefinementSeq
    }
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
      hStretch :
        MulBalanceState.CofinalStretchingFailureAtEveryScale
          (vorticityBalancePerturbationPathY
            U u τ T x)
    ) :
    CofinalStretchCouplingFailureAlongPath
      U u τ T x yAxis := by

  intro level anchor

  obtain ⟨n, hn, hFailure⟩ :=
    hStretch level anchor

  refine ⟨n, hn, ?_⟩

  exact
    vorticityBalancePerturbationPathY_stretchCouplingFailure
      hFailure

/-- Cofinal z-stretching failure descends to moving-time coupling failure. -/
theorem vorticityBalancePerturbationPathZ_cofinalStretchCouplingFailure
    {
      U : VelocityRefinementSeq
    }
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
      hStretch :
        MulBalanceState.CofinalStretchingFailureAtEveryScale
          (vorticityBalancePerturbationPathZ
            U u τ T x)
    ) :
    CofinalStretchCouplingFailureAlongPath
      U u τ T x zAxis := by

  intro level anchor

  obtain ⟨n, hn, hFailure⟩ :=
    hStretch level anchor

  refine ⟨n, hn, ?_⟩

  exact
    vorticityBalancePerturbationPathZ_stretchCouplingFailure
      hFailure

/-- Moving-time native x-vorticity point sequence. -/
noncomputable def vorticityPointPathX
    (U : VelocityRefinementSeq)
    (τ : TimeRefinementSeq)
    (x : Point3) :
    PrimeTensor.MulReal.Seq :=
  fun n =>
    mulVorticityX
      (U n) (τ n) x

/-- Moving-time native y-vorticity point sequence. -/
noncomputable def vorticityPointPathY
    (U : VelocityRefinementSeq)
    (τ : TimeRefinementSeq)
    (x : Point3) :
    PrimeTensor.MulReal.Seq :=
  fun n =>
    mulVorticityY
      (U n) (τ n) x

/-- Moving-time native z-vorticity point sequence. -/
noncomputable def vorticityPointPathZ
    (U : VelocityRefinementSeq)
    (τ : TimeRefinementSeq)
    (x : Point3) :
    PrimeTensor.MulReal.Seq :=
  fun n =>
    mulVorticityZ
      (U n) (τ n) x

/-- Moving-time x-directed velocity-gradient point sequence. -/
noncomputable def velocityGradientPointPathX
    (U : VelocityRefinementSeq)
    (τ : TimeRefinementSeq)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.MulReal.Seq :=
  fun n =>
    mulSpatial3.d
      xAxis
      (
        fun y =>
          ((U n) (τ n) y).component j
      )
      x

/-- Moving-time y-directed velocity-gradient point sequence. -/
noncomputable def velocityGradientPointPathY
    (U : VelocityRefinementSeq)
    (τ : TimeRefinementSeq)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.MulReal.Seq :=
  fun n =>
    mulSpatial3.d
      yAxis
      (
        fun y =>
          ((U n) (τ n) y).component j
      )
      x

/-- Moving-time z-directed velocity-gradient point sequence. -/
noncomputable def velocityGradientPointPathZ
    (U : VelocityRefinementSeq)
    (τ : TimeRefinementSeq)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.MulReal.Seq :=
  fun n =>
    mulSpatial3.d
      zAxis
      (
        fun y =>
          ((U n) (τ n) y).component j
      )
      x

/--
All six primitive moving-time inputs converge to their terminal values at
`(u,T,x)`.
-/
def StretchingPrimitivePathConvergent
    (U : VelocityRefinementSeq)
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (τ : TimeRefinementSeq)
    (T : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : Prop :=
  PrimeTensor.MulReal.ConvergesTo
      (vorticityPointPathX U τ x)
      (mulVorticityX u T x)
    ∧
  PrimeTensor.MulReal.ConvergesTo
      (velocityGradientPointPathX U τ x j)
      (
        mulSpatial3.d
          xAxis
          (fun y => (u T y).component j)
          x
      )
    ∧
  PrimeTensor.MulReal.ConvergesTo
      (vorticityPointPathY U τ x)
      (mulVorticityY u T x)
    ∧
  PrimeTensor.MulReal.ConvergesTo
      (velocityGradientPointPathY U τ x j)
      (
        mulSpatial3.d
          yAxis
          (fun y => (u T y).component j)
          x
      )
    ∧
  PrimeTensor.MulReal.ConvergesTo
      (vorticityPointPathZ U τ x)
      (mulVorticityZ u T x)
    ∧
  PrimeTensor.MulReal.ConvergesTo
      (velocityGradientPointPathZ U τ x j)
      (
        mulSpatial3.d
          zAxis
          (fun y => (u T y).component j)
          x
      )

/-- Moving-time x coupling ratio converges when its primitive pair converges. -/
theorem mulVortexStretchTermRatioAtX_path_convergesTo_one
    {
      U : VelocityRefinementSeq
    }
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
    {j : PrimeTensor.Axis Depth.three}
    (
      hω :
        PrimeTensor.MulReal.ConvergesTo
          (vorticityPointPathX U τ x)
          (mulVorticityX u T x)
    )
    (
      hD :
        PrimeTensor.MulReal.ConvergesTo
          (velocityGradientPointPathX U τ x j)
          (
            mulSpatial3.d
              xAxis
              (fun y => (u T y).component j)
              x
          )
    ) :
    PrimeTensor.MulReal.ConvergesTo
      (
        fun n =>
          mulVortexStretchTermRatioAtX
            (U n) u (τ n) T x j
      )
      1 := by

  have hCoupling :=
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling_ratio_convergesTo_one
      hω hD

  simpa [
    vorticityPointPathX,
    velocityGradientPointPathX,
    mulVortexStretchTermRatioAtX,
    mulVortexStretchTermX
  ] using hCoupling

/-- Moving-time y coupling ratio converges when its primitive pair converges. -/
theorem mulVortexStretchTermRatioAtY_path_convergesTo_one
    {
      U : VelocityRefinementSeq
    }
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
    {j : PrimeTensor.Axis Depth.three}
    (
      hω :
        PrimeTensor.MulReal.ConvergesTo
          (vorticityPointPathY U τ x)
          (mulVorticityY u T x)
    )
    (
      hD :
        PrimeTensor.MulReal.ConvergesTo
          (velocityGradientPointPathY U τ x j)
          (
            mulSpatial3.d
              yAxis
              (fun y => (u T y).component j)
              x
          )
    ) :
    PrimeTensor.MulReal.ConvergesTo
      (
        fun n =>
          mulVortexStretchTermRatioAtY
            (U n) u (τ n) T x j
      )
      1 := by

  have hCoupling :=
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling_ratio_convergesTo_one
      hω hD

  simpa [
    vorticityPointPathY,
    velocityGradientPointPathY,
    mulVortexStretchTermRatioAtY,
    mulVortexStretchTermY
  ] using hCoupling

/-- Moving-time z coupling ratio converges when its primitive pair converges. -/
theorem mulVortexStretchTermRatioAtZ_path_convergesTo_one
    {
      U : VelocityRefinementSeq
    }
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
    {j : PrimeTensor.Axis Depth.three}
    (
      hω :
        PrimeTensor.MulReal.ConvergesTo
          (vorticityPointPathZ U τ x)
          (mulVorticityZ u T x)
    )
    (
      hD :
        PrimeTensor.MulReal.ConvergesTo
          (velocityGradientPointPathZ U τ x j)
          (
            mulSpatial3.d
              zAxis
              (fun y => (u T y).component j)
              x
          )
    ) :
    PrimeTensor.MulReal.ConvergesTo
      (
        fun n =>
          mulVortexStretchTermRatioAtZ
            (U n) u (τ n) T x j
      )
      1 := by

  have hCoupling :=
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling_ratio_convergesTo_one
      hω hD

  simpa [
    vorticityPointPathZ,
    velocityGradientPointPathZ,
    mulVortexStretchTermRatioAtZ,
    mulVortexStretchTermZ
  ] using hCoupling

/--
Cofinal moving-time coupling failure is incompatible with convergence of all
six primitive moving-time channels.
-/
theorem not_stretchingPrimitivePathConvergent_of_cofinalStretchCouplingFailure
    {
      U : VelocityRefinementSeq
    }
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
    {j : PrimeTensor.Axis Depth.three}
    (
      hFailure :
        CofinalStretchCouplingFailureAlongPath
          U u τ T x j
    ) :
    ¬ StretchingPrimitivePathConvergent
        U u τ T x j := by

  intro hPrimitive

  rcases hPrimitive with
    ⟨hωx, hDx, hωy, hDy, hωz, hDz⟩

  have hX :=
    mulVortexStretchTermRatioAtX_path_convergesTo_one
      hωx hDx

  have hY :=
    mulVortexStretchTermRatioAtY_path_convergesTo_one
      hωy hDy

  have hZ :=
    mulVortexStretchTermRatioAtZ_path_convergesTo_one
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

  unfold StretchCouplingFailureAtTimes at hFailN

  rcases hFailN with hFailX | hFailY | hFailZ

  · exact hFailX hXNear
  · exact hFailY hYNear
  · exact hFailZ hZNear

/--
Explicit six-way moving-time primitive cofinal leaf.
-/
def StretchingPrimitivePathCofinalFailure
    (U : VelocityRefinementSeq)
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (τ : TimeRefinementSeq)
    (T : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : Prop :=
  (
    ∃ level : Depth,
      PrimeTensor.MulReal.CofinalFailureAtScale
        (vorticityPointPathX U τ x)
        (mulVorticityX u T x)
        level
  )
    ∨
  (
    ∃ level : Depth,
      PrimeTensor.MulReal.CofinalFailureAtScale
        (velocityGradientPointPathX U τ x j)
        (
          mulSpatial3.d
            xAxis
            (fun y => (u T y).component j)
            x
        )
        level
  )
    ∨
  (
    ∃ level : Depth,
      PrimeTensor.MulReal.CofinalFailureAtScale
        (vorticityPointPathY U τ x)
        (mulVorticityY u T x)
        level
  )
    ∨
  (
    ∃ level : Depth,
      PrimeTensor.MulReal.CofinalFailureAtScale
        (velocityGradientPointPathY U τ x j)
        (
          mulSpatial3.d
            yAxis
            (fun y => (u T y).component j)
            x
        )
        level
  )
    ∨
  (
    ∃ level : Depth,
      PrimeTensor.MulReal.CofinalFailureAtScale
        (vorticityPointPathZ U τ x)
        (mulVorticityZ u T x)
        level
  )
    ∨
  (
    ∃ level : Depth,
      PrimeTensor.MulReal.CofinalFailureAtScale
        (velocityGradientPointPathZ U τ x j)
        (
          mulSpatial3.d
            zAxis
            (fun y => (u T y).component j)
            x
        )
        level
  )

/--
Nonconvergence of the six-way primitive path yields an explicit fixed-scale
cofinal leaf.
-/
theorem stretchingPrimitivePathCofinalFailure_of_not_convergent
    {
      U : VelocityRefinementSeq
    }
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
    {j : PrimeTensor.Axis Depth.three}
    (
      h :
        ¬ StretchingPrimitivePathConvergent
            U u τ T x j
    ) :
    StretchingPrimitivePathCofinalFailure
      U u τ T x j := by

  unfold StretchingPrimitivePathCofinalFailure

  by_cases hωx :
    PrimeTensor.MulReal.ConvergesTo
      (vorticityPointPathX U τ x)
      (mulVorticityX u T x)

  · by_cases hDx :
      PrimeTensor.MulReal.ConvergesTo
        (velocityGradientPointPathX U τ x j)
        (
          mulSpatial3.d
            xAxis
            (fun y => (u T y).component j)
            x
        )

    · by_cases hωy :
        PrimeTensor.MulReal.ConvergesTo
          (vorticityPointPathY U τ x)
          (mulVorticityY u T x)

      · by_cases hDy :
          PrimeTensor.MulReal.ConvergesTo
            (velocityGradientPointPathY U τ x j)
            (
              mulSpatial3.d
                yAxis
                (fun y => (u T y).component j)
                x
            )

        · by_cases hωz :
            PrimeTensor.MulReal.ConvergesTo
              (vorticityPointPathZ U τ x)
              (mulVorticityZ u T x)

          · by_cases hDz :
              PrimeTensor.MulReal.ConvergesTo
                (velocityGradientPointPathZ U τ x j)
                (
                  mulSpatial3.d
                    zAxis
                    (fun y => (u T y).component j)
                    x
                )

            · exfalso
              apply h
              unfold StretchingPrimitivePathConvergent
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
Cofinal moving-time coupling failure produces an explicit primitive cofinal
leaf.
-/
theorem stretchingPrimitivePathCofinalFailure_of_cofinalStretchCouplingFailure
    {
      U : VelocityRefinementSeq
    }
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
    {j : PrimeTensor.Axis Depth.three}
    (
      hFailure :
        CofinalStretchCouplingFailureAlongPath
          U u τ T x j
    ) :
    StretchingPrimitivePathCofinalFailure
      U u τ T x j := by

  apply
    stretchingPrimitivePathCofinalFailure_of_not_convergent

  exact
    not_stretchingPrimitivePathConvergent_of_cofinalStretchCouplingFailure
      hFailure

/--
Full moving-time x-component primitive leaf theorem.
-/
theorem vorticityBalancePerturbationPathX_primitiveCofinalFailure
    {
      U : VelocityRefinementSeq
    }
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
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceX
            (U n) (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceX
          u T x
    )
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (vorticityBalancePerturbationPathX
            U u τ T x)
    )
    (
      hSecondJet :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldPathX U τ)
          (vorticityFieldX u T)
    ) :
    StretchingPrimitivePathCofinalFailure
      U u τ T x xAxis := by

  have hStretch :=
    vorticityBalancePerturbationPathX_cofinalStretching
      hStages hLimit hFailure hSecondJet

  have hCoupling :=
    vorticityBalancePerturbationPathX_cofinalStretchCouplingFailure
      hStretch

  exact
    stretchingPrimitivePathCofinalFailure_of_cofinalStretchCouplingFailure
      hCoupling

/-- Full moving-time y-component primitive leaf theorem. -/
theorem vorticityBalancePerturbationPathY_primitiveCofinalFailure
    {
      U : VelocityRefinementSeq
    }
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
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceY
            (U n) (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceY
          u T x
    )
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (vorticityBalancePerturbationPathY
            U u τ T x)
    )
    (
      hSecondJet :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldPathY U τ)
          (vorticityFieldY u T)
    ) :
    StretchingPrimitivePathCofinalFailure
      U u τ T x yAxis := by

  have hStretch :=
    vorticityBalancePerturbationPathY_cofinalStretching
      hStages hLimit hFailure hSecondJet

  have hCoupling :=
    vorticityBalancePerturbationPathY_cofinalStretchCouplingFailure
      hStretch

  exact
    stretchingPrimitivePathCofinalFailure_of_cofinalStretchCouplingFailure
      hCoupling

/-- Full moving-time z-component primitive leaf theorem. -/
theorem vorticityBalancePerturbationPathZ_primitiveCofinalFailure
    {
      U : VelocityRefinementSeq
    }
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
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceZ
            (U n) (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceZ
          u T x
    )
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (vorticityBalancePerturbationPathZ
            U u τ T x)
    )
    (
      hSecondJet :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldPathZ U τ)
          (vorticityFieldZ u T)
    ) :
    StretchingPrimitivePathCofinalFailure
      U u τ T x zAxis := by

  have hStretch :=
    vorticityBalancePerturbationPathZ_cofinalStretching
      hStages hLimit hFailure hSecondJet

  have hCoupling :=
    vorticityBalancePerturbationPathZ_cofinalStretchCouplingFailure
      hStretch

  exact
    stretchingPrimitivePathCofinalFailure_of_cofinalStretchCouplingFailure
      hCoupling

end Euclidean
end Bridge
end PrimeTensor
