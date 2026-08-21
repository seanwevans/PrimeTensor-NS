import PrimeTensor.Fluid.Vorticity.Pointwise.Diffusion

/-!
# Time continuity of the pointwise vorticity second jet

The pointwise diffusion layer reduced the diffusion hypothesis to convergence of
the three same-axis second derivatives of one vorticity component at the
selected point.

This file translates that intrinsic hypothesis into ordinary real continuity.

For a native vorticity field `Ω(t,·)` and its logged classical vorticity field
`ω(t,·)`, logarithmic differential compatibility gives

    log (D_i D_i Ω(t,x)) = ∂_i ∂_i ω(t,x).

Therefore continuity in time of the three real observables
`∂_i² ω(t,x)` at `T`, together with `τ n -> T`, forces intrinsic convergence of
the native second jet along the moving-time path.

The remaining analytic expansion

    ∂_i² ω = difference of third spatial derivatives of velocity

is deliberately left to the next module.  That step needs classical derivative
linearity / spatial regularity hypotheses; it is separate from the logarithmic
topology bridge proved here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
Time continuity at `(T,x)` of all three same-axis second derivatives of the
classical x-vorticity of the logged velocity.
-/
def VorticitySecondJetXContinuousAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ)
    (x : Point3) : Prop :=
  ∀ i : PrimeTensor.Axis Depth.three,
    ContinuousAt
      (
        fun t =>
          spatial3.d
            i
            (
              spatial3.d
                i
                (
                  fun y =>
                    realVorticityX
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      t y
                )
            )
            x
      )
      T

/-- Same condition for the classical y-vorticity. -/
def VorticitySecondJetYContinuousAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ)
    (x : Point3) : Prop :=
  ∀ i : PrimeTensor.Axis Depth.three,
    ContinuousAt
      (
        fun t =>
          spatial3.d
            i
            (
              spatial3.d
                i
                (
                  fun y =>
                    realVorticityY
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      t y
                )
            )
            x
      )
      T

/-- Same condition for the classical z-vorticity. -/
def VorticitySecondJetZContinuousAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ)
    (x : Point3) : Prop :=
  ∀ i : PrimeTensor.Axis Depth.three,
    ContinuousAt
      (
        fun t =>
          spatial3.d
            i
            (
              spatial3.d
                i
                (
                  fun y =>
                    realVorticityZ
                      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                      t y
                )
            )
            x
      )
      T

/--
All three vorticity components have time-continuous same-axis second jets at
`(T,x)`.
-/
def VorticitySecondJetContinuousAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ)
    (x : Point3) : Prop :=
  VorticitySecondJetXContinuousAt u T x ∧
  VorticitySecondJetYContinuousAt u T x ∧
  VorticitySecondJetZContinuousAt u T x

/--
Generic logarithmic bridge from real second-jet time continuity to intrinsic
pointwise second-jet convergence.

`omega` is the native scalar field at each time and `realOmega` is its exact
logarithmic coordinate field.
-/
theorem secondDerivativePathConvergesToAt_of_logContinuous
    {
      omega :
        ℝ →
          FieldScale.Field
            ℝ Depth.three
    }
    {
      realOmega :
        ℝ →
          PrimeTensor.ScalarField
            ℝ ℝ Depth.three
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
      hLog :
        ∀ (t : ℝ) (y : Point3),
          PrimeTensor.Bridge.MulReal.logValue
              (omega t y)
            =
          realOmega t y
    )
    (
      hContinuous :
        ∀ i : PrimeTensor.Axis Depth.three,
          ContinuousAt
            (
              fun t =>
                spatial3.d
                  i
                  (spatial3.d i (realOmega t))
                  x
            )
            T
    ) :
    FieldScale.SecondDerivativeConvergesToAt
      mulSpatial3
      (fun n => omega (τ n))
      (omega T)
      x := by

  have hAxisConverges :
      ∀ i : PrimeTensor.Axis Depth.three,
        PrimeTensor.MulReal.ConvergesTo
          (
            fun n =>
              mulSpatial3.d
                i
                (mulSpatial3.d i (omega (τ n)))
                x
          )
          (
            mulSpatial3.d
              i
              (mulSpatial3.d i (omega T))
              x
          ) := by

    intro i

    have hNativeContinuous :
        ContinuousAt
          (
            fun t =>
              PrimeTensor.Bridge.MulReal.logValue
                (
                  mulSpatial3.d
                    i
                    (mulSpatial3.d i (omega t))
                    x
                )
          )
          T := by

      have hFunctions :
          (
            fun t =>
              PrimeTensor.Bridge.MulReal.logValue
                (
                  mulSpatial3.d
                    i
                    (mulSpatial3.d i (omega t))
                    x
                )
          )
            =
          (
            fun t =>
              spatial3.d
                i
                (spatial3.d i (realOmega t))
                x
          ) := by

        funext t

        have hD2 :=
          PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d2_log
            i
            (omega t)
            x

        have hField :
            (
              fun y =>
                PrimeTensor.Bridge.MulReal.logValue
                  (omega t y)
            )
              =
            realOmega t := by

          funext y
          exact hLog t y

        rw [hField] at hD2

        exact hD2.symm

      rw [hFunctions]

      exact hContinuous i

    exact
      mulReal_timePath_converges_of_logContinuousAt
        (
          f :=
            fun t =>
              mulSpatial3.d
                i
                (mulSpatial3.d i (omega t))
                x
        )
        hτ
        hNativeContinuous

  unfold FieldScale.SecondDerivativeConvergesToAt

  intro level

  obtain ⟨xAnchor, hxTail⟩ :=
    hAxisConverges xAxis level

  obtain ⟨yAnchor, hyTail⟩ :=
    hAxisConverges yAxis level

  obtain ⟨zAnchor, hzTail⟩ :=
    hAxisConverges zAxis level

  let yzAnchor :=
    Depth.join yAnchor zAnchor

  let anchor :=
    Depth.join xAnchor yzAnchor

  refine ⟨anchor, ?_⟩

  intro n hn

  have hxn :
      Depth.AtOrAfter xAnchor n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter xAnchor yzAnchor)
      hn

  have hyn :
      Depth.AtOrAfter yAnchor n := by

    have hy_yz :
        Depth.AtOrAfter yAnchor yzAnchor :=
      Depth.left_atOrAfter yAnchor zAnchor

    have hyz_anchor :
        Depth.AtOrAfter yzAnchor anchor :=
      Depth.right_atOrAfter xAnchor yzAnchor

    exact
      Depth.atOrAfter_trans
        hy_yz
        (Depth.atOrAfter_trans hyz_anchor hn)

  have hzn :
      Depth.AtOrAfter zAnchor n := by

    have hz_yz :
        Depth.AtOrAfter zAnchor yzAnchor :=
      Depth.right_atOrAfter yAnchor zAnchor

    have hyz_anchor :
        Depth.AtOrAfter yzAnchor anchor :=
      Depth.right_atOrAfter xAnchor yzAnchor

    exact
      Depth.atOrAfter_trans
        hz_yz
        (Depth.atOrAfter_trans hyz_anchor hn)

  unfold FieldScale.SecondDerivativeNearAt

  intro i

  cases i with
  | first =>
      exact hxTail n hxn

  | next i =>
      cases i with
      | first =>
          exact hyTail n hyn

      | next i =>
          cases i with
          | first =>
              exact hzTail n hzn

/--
Time continuity of the classical x-vorticity second jet implies intrinsic
pointwise second-jet convergence of the native x-vorticity along any convergent
time path.
-/
theorem vorticityFieldPathX_secondDerivativeConvergesToAt_of_continuous
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
      hContinuous :
        VorticitySecondJetXContinuousAt
          u T x
    ) :
    FieldScale.SecondDerivativeConvergesToAt
      mulSpatial3
      (
        vorticityFieldPathX
          (constantVelocityRefinement u)
          τ
      )
      (vorticityFieldX u T)
      x := by

  have h :=
    secondDerivativePathConvergesToAt_of_logContinuous
      (
        omega :=
          fun t =>
            vorticityFieldX u t
      )
      (
        realOmega :=
          fun t y =>
            realVorticityX
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t y
      )
      hτ
      (
        fun t y =>
          logValue_mulVorticityX
            u t y
      )
      hContinuous

  change
    FieldScale.SecondDerivativeConvergesToAt
      mulSpatial3
      (
        fun n =>
          vorticityFieldX
            u (τ n)
      )
      (vorticityFieldX u T)
      x

  exact h

/-- Y-vorticity analogue. -/
theorem vorticityFieldPathY_secondDerivativeConvergesToAt_of_continuous
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
      hContinuous :
        VorticitySecondJetYContinuousAt
          u T x
    ) :
    FieldScale.SecondDerivativeConvergesToAt
      mulSpatial3
      (
        vorticityFieldPathY
          (constantVelocityRefinement u)
          τ
      )
      (vorticityFieldY u T)
      x := by

  have h :=
    secondDerivativePathConvergesToAt_of_logContinuous
      (
        omega :=
          fun t =>
            vorticityFieldY u t
      )
      (
        realOmega :=
          fun t y =>
            realVorticityY
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t y
      )
      hτ
      (
        fun t y =>
          logValue_mulVorticityY
            u t y
      )
      hContinuous

  change
    FieldScale.SecondDerivativeConvergesToAt
      mulSpatial3
      (
        fun n =>
          vorticityFieldY
            u (τ n)
      )
      (vorticityFieldY u T)
      x

  exact h

/-- Z-vorticity analogue. -/
theorem vorticityFieldPathZ_secondDerivativeConvergesToAt_of_continuous
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
      hContinuous :
        VorticitySecondJetZContinuousAt
          u T x
    ) :
    FieldScale.SecondDerivativeConvergesToAt
      mulSpatial3
      (
        vorticityFieldPathZ
          (constantVelocityRefinement u)
          τ
      )
      (vorticityFieldZ u T)
      x := by

  have h :=
    secondDerivativePathConvergesToAt_of_logContinuous
      (
        omega :=
          fun t =>
            vorticityFieldZ u t
      )
      (
        realOmega :=
          fun t y =>
            realVorticityZ
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t y
      )
      hτ
      (
        fun t y =>
          logValue_mulVorticityZ
            u t y
      )
      hContinuous

  change
    FieldScale.SecondDerivativeConvergesToAt
      mulSpatial3
      (
        fun n =>
          vorticityFieldZ
            u (τ n)
      )
      (vorticityFieldZ u T)
      x

  exact h

/--
The x-component continuation criterion with the intrinsic diffusion hypothesis
replaced by ordinary time continuity of the classical x-vorticity second jet.
-/
theorem noCofinalVorticityBalancePathX_of_continuousJets
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
      hFirstJet :
        VelocityFirstJetLogContinuousAt
          u T x
    )
    (
      hSecondJet :
        VorticitySecondJetXContinuousAt
          u T x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathX
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  exact
    noCofinalVorticityBalancePathX_of_pointwiseJets
      hτ
      hStages
      hLimit
      (
        vorticityFieldPathX_secondDerivativeConvergesToAt_of_continuous
          hτ hSecondJet
      )
      hFirstJet

/-- Y-component continuation criterion from ordinary jet continuity. -/
theorem noCofinalVorticityBalancePathY_of_continuousJets
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
      hFirstJet :
        VelocityFirstJetLogContinuousAt
          u T x
    )
    (
      hSecondJet :
        VorticitySecondJetYContinuousAt
          u T x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathY
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  exact
    noCofinalVorticityBalancePathY_of_pointwiseJets
      hτ
      hStages
      hLimit
      (
        vorticityFieldPathY_secondDerivativeConvergesToAt_of_continuous
          hτ hSecondJet
      )
      hFirstJet

/-- Z-component continuation criterion from ordinary jet continuity. -/
theorem noCofinalVorticityBalancePathZ_of_continuousJets
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
      hFirstJet :
        VelocityFirstJetLogContinuousAt
          u T x
    )
    (
      hSecondJet :
        VorticitySecondJetZContinuousAt
          u T x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathZ
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  exact
    noCofinalVorticityBalancePathZ_of_pointwiseJets
      hτ
      hStages
      hLimit
      (
        vorticityFieldPathZ_secondDerivativeConvergesToAt_of_continuous
          hτ hSecondJet
      )
      hFirstJet

end Euclidean
end Bridge
end PrimeTensor
