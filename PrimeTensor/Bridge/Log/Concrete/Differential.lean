import PrimeTensor.Bridge.Real.Log.LittleO
import PrimeTensor.Bridge.Fluid.Log.Semantics

/-!
# Canonical logarithmic differentials

The fluid bridge previously accepted compatibility witnesses

    SpatialLogCompatible D DR
    TemporalLogCompatible Dt DtR

as hypotheses.

Now that the completed logarithmic coordinate is a genuine equivalence

    MulReal ≃ ℝ,

those witnesses can be constructed canonically.

Given any ordinary real spatial differential `DR`, pull it back through the
logarithmic equivalence:

    D f := L⁻¹ ( DR (L ∘ f) ).

Likewise in time.

The resulting native operators satisfy the log-compatibility equations by
construction.  This removes the compatibility assumptions from the generic
fluid-to-real bridge whenever the native differential is chosen as this
canonical logarithmic pullback.

No topology or coordinate geometry on `X` or `T` is assumed here; those remain
the responsibility of the supplied conventional differentials.
-/

namespace PrimeTensor
namespace Bridge

namespace Differential

/--
Canonical native multiplicative spatial differential obtained by pulling a
real differential back through the completed logarithmic equivalence.
-/
noncomputable def logPullback
    {X : Type} {dim : Depth}
    (DR : PrimeTensor.Differential X ℝ dim) :
    PrimeTensor.Differential X PrimeTensor.MulReal dim where

  d :=
    fun i f x =>
      PrimeTensor.Bridge.MulReal.logEquiv.symm
        (
          DR.d i
            (
              fun y =>
                PrimeTensor.Bridge.MulReal.logValue
                  (f y)
            )
            x
        )

/--
Applying `logValue` to the canonical pulled-back derivative recovers the
original real derivative exactly.
-/
@[simp]
theorem logValue_logPullback_d
    {X : Type} {dim : Depth}
    (DR : PrimeTensor.Differential X ℝ dim)
    (i : PrimeTensor.Axis dim)
    (f :
      PrimeTensor.ScalarField
        X PrimeTensor.MulReal dim)
    (x : PrimeTensor.Point X dim) :
    PrimeTensor.Bridge.MulReal.logValue
        (
          (logPullback DR).d i f x
        )
      =
    DR.d i
      (
        fun y =>
          PrimeTensor.Bridge.MulReal.logValue
            (f y)
      )
      x := by

  unfold logPullback

  change
    PrimeTensor.Bridge.MulReal.logEquiv
        (
          PrimeTensor.Bridge.MulReal.logEquiv.symm
            (
              DR.d i
                (
                  fun y =>
                    PrimeTensor.Bridge.MulReal.logValue
                      (f y)
                )
                x
            )
        )
      =
    DR.d i
      (
        fun y =>
          PrimeTensor.Bridge.MulReal.logValue
            (f y)
      )
      x

  exact
    PrimeTensor.Bridge.MulReal.logEquiv.apply_symm_apply
      (
        DR.d i
          (
            fun y =>
              PrimeTensor.Bridge.MulReal.logValue
                (f y)
          )
          x
      )

/--
The canonical spatial logarithmic pullback is automatically compatible with
the real differential from which it was constructed.
-/
theorem logPullback_compatible
    {X : Type} {dim : Depth}
    (DR : PrimeTensor.Differential X ℝ dim) :
    PrimeTensor.Bridge.SpatialLogCompatible
      (logPullback DR)
      DR := by

  constructor

  intro i f x

  symm

  exact
    logValue_logPullback_d
      DR i f x

end Differential

namespace TemporalDifferential

/--
Canonical native multiplicative temporal differential obtained by pulling a
real temporal differential back through the completed logarithmic equivalence.
-/
noncomputable def logPullback
    {T : Type}
    (DtR :
      PrimeTensor.TemporalDifferential T ℝ) :
    PrimeTensor.TemporalDifferential
      T PrimeTensor.MulReal where

  d :=
    fun f t =>
      PrimeTensor.Bridge.MulReal.logEquiv.symm
        (
          DtR.d
            (
              fun s =>
                PrimeTensor.Bridge.MulReal.logValue
                  (f s)
            )
            t
        )

/--
Applying `logValue` to the canonical pulled-back temporal derivative recovers
the real temporal derivative exactly.
-/
@[simp]
theorem logValue_logPullback_d
    {T : Type}
    (DtR :
      PrimeTensor.TemporalDifferential T ℝ)
    (f : T → PrimeTensor.MulReal)
    (t : T) :
    PrimeTensor.Bridge.MulReal.logValue
        (
          (logPullback DtR).d f t
        )
      =
    DtR.d
      (
        fun s =>
          PrimeTensor.Bridge.MulReal.logValue
            (f s)
      )
      t := by

  unfold logPullback

  change
    PrimeTensor.Bridge.MulReal.logEquiv
        (
          PrimeTensor.Bridge.MulReal.logEquiv.symm
            (
              DtR.d
                (
                  fun s =>
                    PrimeTensor.Bridge.MulReal.logValue
                      (f s)
                )
                t
            )
        )
      =
    DtR.d
      (
        fun s =>
          PrimeTensor.Bridge.MulReal.logValue
            (f s)
      )
      t

  exact
    PrimeTensor.Bridge.MulReal.logEquiv.apply_symm_apply
      (
        DtR.d
          (
            fun s =>
              PrimeTensor.Bridge.MulReal.logValue
                (f s)
          )
          t
      )

/--
The canonical temporal logarithmic pullback is automatically compatible with
the real temporal differential from which it was constructed.
-/
theorem logPullback_compatible
    {T : Type}
    (DtR :
      PrimeTensor.TemporalDifferential T ℝ) :
    PrimeTensor.Bridge.TemporalLogCompatible
      (logPullback DtR)
      DtR := by

  constructor

  intro f t

  symm

  exact
    logValue_logPullback_d
      DtR f t

end TemporalDifferential

namespace PrimePairApprox

/--
With canonical logarithmic pullback differentials, the fluid bridge no longer
needs separate spatial or temporal compatibility hypotheses.
-/
noncomputable def LogProductSolution.toRealCanonical
    {T X : Type} {dim : Depth}
    {DtR :
      PrimeTensor.TemporalDifferential T ℝ}
    {DR :
      PrimeTensor.Differential X ℝ dim}
    (
      s :
        LogProductSolution
          (
            PrimeTensor.Bridge.TemporalDifferential.logPullback
              DtR
          )
          (
            PrimeTensor.Bridge.Differential.logPullback
              DR
          )
    ) :
    RealFluid.Solution DtR DR :=

  s.toReal
    (
      PrimeTensor.Bridge.TemporalDifferential.logPullback_compatible
        DtR
    )
    (
      PrimeTensor.Bridge.Differential.logPullback_compatible
        DR
    )

@[simp]
theorem LogProductSolution.toRealCanonical_velocity
    {T X : Type} {dim : Depth}
    {DtR :
      PrimeTensor.TemporalDifferential T ℝ}
    {DR :
      PrimeTensor.Differential X ℝ dim}
    (
      s :
        LogProductSolution
          (
            PrimeTensor.Bridge.TemporalDifferential.logPullback
              DtR
          )
          (
            PrimeTensor.Bridge.Differential.logPullback
              DR
          )
    ) :
    s.toRealCanonical.velocity =
      logSpaceTimeVectorField s.velocity := by

  rfl

@[simp]
theorem LogProductSolution.toRealCanonical_pressure
    {T X : Type} {dim : Depth}
    {DtR :
      PrimeTensor.TemporalDifferential T ℝ}
    {DR :
      PrimeTensor.Differential X ℝ dim}
    (
      s :
        LogProductSolution
          (
            PrimeTensor.Bridge.TemporalDifferential.logPullback
              DtR
          )
          (
            PrimeTensor.Bridge.Differential.logPullback
              DR
          )
    ) :
    s.toRealCanonical.pressure =
      logSpaceTimeScalarField s.pressure := by

  rfl

end PrimePairApprox

end Bridge
end PrimeTensor
