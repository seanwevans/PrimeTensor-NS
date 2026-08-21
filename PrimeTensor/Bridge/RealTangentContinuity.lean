import PrimeTensor.Bridge.RealTangentSpace

/-!
# Intrinsic tangent scale control gives real continuity

A native `MulTangentMap.ScaleControlled` hypothesis is quantitative control
around the multiplicative pivot.  Under the now-bijective logarithmic
coordinate, this becomes ordinary continuity at additive zero of the
conjugated additive real endomorphism.

The proof uses the exact completed-scale sandwich already established:

* strict log bound  -> native `ScaleNear`;
* native `ScaleNear` -> closed log bound.

For a requested real epsilon, we choose a native output scale whose logarithmic
radius is strictly below epsilon.  Scale control supplies the corresponding
input gain.  The input logarithmic radius itself is then a positive real delta.
-/

namespace PrimeTensor
namespace Bridge
namespace MulTangentMap

/--
One native successor refinement has strictly smaller logarithmic radius than
its base level.
-/
theorem logScaleRadius_advance_one_lt
    (level : Depth) :
    PrimeTensor.Bridge.logScaleRadius
        (Depth.advance level (.one))
      <
    PrimeTensor.Bridge.logScaleRadius level := by

  change
    PrimeTensor.Bridge.logScaleRadius (.succ level)
      <
    PrimeTensor.Bridge.logScaleRadius level

  rw [
    PrimeTensor.Bridge.logScaleRadius_succ
  ]

  have hPos :
      0 <
        PrimeTensor.Bridge.logScaleRadius level :=
    PrimeTensor.Bridge.logScaleRadius_pos level

  linarith

/--
Intrinsic quantitative scale control implies ordinary continuity at zero of
the real additive conjugate.
-/
theorem scaleControlled_realAdditive_continuousAt_zero
    {D : PrimeTensor.MulTangentMap}
    (hControlled :
      PrimeTensor.MulTangentMap.ScaleControlled D) :
    ContinuousAt
      (PrimeTensor.Bridge.MulTangentMap.realAdditive D)
      0 := by

  rw [Metric.continuousAt_iff]

  intro ε hε

  obtain ⟨level, hLevelRadius⟩ :=
    PrimeTensor.Bridge.exists_logScaleRadius_lt
      hε

  obtain ⟨sourceGain, hControl⟩ :=
    hControlled (.one)

  let δ : ℝ :=
    PrimeTensor.Bridge.logScaleRadius
      (Depth.advance level sourceGain)

  have hδ :
      0 < δ := by
    unfold δ
    exact
      PrimeTensor.Bridge.logScaleRadius_pos
        (Depth.advance level sourceGain)

  refine ⟨δ, hδ, ?_⟩

  intro r hr

  let x : PrimeTensor.MulReal :=
    PrimeTensor.Bridge.MulReal.logEquiv.symm r

  have hLogX :
      PrimeTensor.Bridge.MulReal.logValue x =
        r := by

    unfold x

    change
      PrimeTensor.Bridge.MulReal.logEquiv
          (
            PrimeTensor.Bridge.MulReal.logEquiv.symm r
          )
        =
      r

    exact
      PrimeTensor.Bridge.MulReal.logEquiv.apply_symm_apply
        r

  have hInputAbs :
      abs r < δ := by

    simpa [
      Real.dist_0_eq_abs
    ] using hr

  have hInputLog :
      abs
          (
            PrimeTensor.Bridge.MulReal.logValue x -
              PrimeTensor.Bridge.MulReal.logValue
                (1 : PrimeTensor.MulReal)
          )
        <
      PrimeTensor.Bridge.logScaleRadius
        (Depth.advance level sourceGain) := by

    rw [
      hLogX,
      PrimeTensor.Bridge.MulReal.logValue_one
    ]

    simpa [δ] using hInputAbs

  have hInputNear :
      PrimeTensor.MulReal.ScaleNear
        (Depth.advance level sourceGain)
        x
        1 := by

    exact
      PrimeTensor.Bridge.MulReal.scaleNear_of_logValue_lt
        hInputLog

  have hOutputNear :
      PrimeTensor.MulReal.ScaleNear
        (Depth.advance level (.one))
        (D x)
        1 :=
    hControl
      level
      x
      hInputNear

  have hOutputBound :
      abs
          (
            PrimeTensor.Bridge.MulReal.logValue (D x) -
              PrimeTensor.Bridge.MulReal.logValue
                (1 : PrimeTensor.MulReal)
          )
        ≤
      PrimeTensor.Bridge.logScaleRadius
        (Depth.advance level (.one)) :=
    PrimeTensor.Bridge.MulReal.scaleNear_logValue_le
      hOutputNear

  have hOutputAbs :
      abs
          (
            PrimeTensor.Bridge.MulReal.logValue (D x)
          )
        ≤
      PrimeTensor.Bridge.logScaleRadius
        (Depth.advance level (.one)) := by

    simpa [
      PrimeTensor.Bridge.MulReal.logValue_one
    ] using hOutputBound

  have hOutputRadius :
      PrimeTensor.Bridge.logScaleRadius
          (Depth.advance level (.one))
        <
      ε := by

    exact
      lt_trans
        (
          logScaleRadius_advance_one_lt
            level
        )
        hLevelRadius

  have hRealValue :
      PrimeTensor.Bridge.MulTangentMap.realAdditive D r =
        PrimeTensor.Bridge.MulReal.logValue (D x) := by

    rw [
      PrimeTensor.Bridge.MulTangentMap.realAdditive_apply
    ]

    have h :=
      PrimeTensor.Bridge.MulTangentMap.realConjugate_logValue
        D x

    rw [hLogX] at h

    exact h

  rw [
    PrimeTensor.Bridge.MulTangentMap.realAdditive_zero,
    Real.dist_0_eq_abs
  ]

  rw [hRealValue]

  exact
    lt_of_le_of_lt
      hOutputAbs
      hOutputRadius

end MulTangentMap
end Bridge
end PrimeTensor
