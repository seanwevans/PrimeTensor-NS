import PrimeTensor.Fluid.VorticityPreterminalExtension

/-!
# Local transfer from a preterminal field to its continuation

A continuation field is represented as a total native spacetime field `v` which
agrees with the original preterminal field `u` on the open interval `(0,T)`.

The native vorticity balance contains one temporal derivative, so equality of a
single time slice is not enough to transfer the complete balance.  Agreement on
the whole open interval is enough: for every interior time `t`, Mathlib
locality of `deriv` transfers the temporal-vorticity term, while the remaining
transport, stretching, and diffusion terms depend only on the time slice.

This file proves that locality bridge and then connects
`SmoothContinuationExtension` directly to the existing no-cascade theorems.

No PDE continuation estimate is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/--
Equality of native velocity slices gives equality of their logged real slices.
-/
theorem loggedVelocitySlice_eq_of_nativeSlice_eq
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      h :
        u t = v t
    ) :
    PrimeTensor.Bridge.logSpaceTimeVectorField u t
      =
    PrimeTensor.Bridge.logSpaceTimeVectorField v t := by

  unfold PrimeTensor.Bridge.logSpaceTimeVectorField
  rw [h]

/--
Classical x-vorticity depends only on the velocity time slice.
-/
theorem realVorticityX_eq_of_slice_eq
    {
      a b :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      h :
        a t = b t
    )
    (x : Point3) :
    realVorticityX a t x =
      realVorticityX b t x := by

  unfold realVorticityX
  rw [h]

/--
Classical y-vorticity depends only on the velocity time slice.
-/
theorem realVorticityY_eq_of_slice_eq
    {
      a b :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      h :
        a t = b t
    )
    (x : Point3) :
    realVorticityY a t x =
      realVorticityY b t x := by

  unfold realVorticityY
  rw [h]

/--
Classical z-vorticity depends only on the velocity time slice.
-/
theorem realVorticityZ_eq_of_slice_eq
    {
      a b :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      h :
        a t = b t
    )
    (x : Point3) :
    realVorticityZ a t x =
      realVorticityZ b t x := by

  unfold realVorticityZ
  rw [h]

/--
The x-vorticity transport term depends only on one velocity time slice.
-/
theorem realVorticityTransportX_eq_of_slice_eq
    {
      a b :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      h :
        a t = b t
    )
    (x : Point3) :
    realVorticityTransportX a t x =
      realVorticityTransportX b t x := by

  have hω :
      (fun y =>
        realVorticityX a t y)
        =
      (fun y =>
        realVorticityX b t y) := by
    funext y
    exact
      realVorticityX_eq_of_slice_eq
        h y

  unfold realVorticityTransportX
  rw [h, hω]

/--
The y-vorticity transport term depends only on one velocity time slice.
-/
theorem realVorticityTransportY_eq_of_slice_eq
    {
      a b :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      h :
        a t = b t
    )
    (x : Point3) :
    realVorticityTransportY a t x =
      realVorticityTransportY b t x := by

  have hω :
      (fun y =>
        realVorticityY a t y)
        =
      (fun y =>
        realVorticityY b t y) := by
    funext y
    exact
      realVorticityY_eq_of_slice_eq
        h y

  unfold realVorticityTransportY
  rw [h, hω]

/--
The z-vorticity transport term depends only on one velocity time slice.
-/
theorem realVorticityTransportZ_eq_of_slice_eq
    {
      a b :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      h :
        a t = b t
    )
    (x : Point3) :
    realVorticityTransportZ a t x =
      realVorticityTransportZ b t x := by

  have hω :
      (fun y =>
        realVorticityZ a t y)
        =
      (fun y =>
        realVorticityZ b t y) := by
    funext y
    exact
      realVorticityZ_eq_of_slice_eq
        h y

  unfold realVorticityTransportZ
  rw [h, hω]

/--
Classical vortex stretching depends only on one velocity time slice.
-/
theorem realVortexStretchComponent_eq_of_slice_eq
    {
      a b :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      h :
        a t = b t
    )
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    realVortexStretchComponent a t x j =
      realVortexStretchComponent b t x j := by

  have hx :
      realVorticityX a t x =
        realVorticityX b t x :=
    realVorticityX_eq_of_slice_eq
      h x

  have hy :
      realVorticityY a t x =
        realVorticityY b t x :=
    realVorticityY_eq_of_slice_eq
      h x

  have hz :
      realVorticityZ a t x =
        realVorticityZ b t x :=
    realVorticityZ_eq_of_slice_eq
      h x

  unfold realVortexStretchComponent
  rw [h, hx, hy, hz]

/--
The classical x-vorticity Laplacian depends only on one velocity time slice.
-/
theorem realVorticityLaplacianX_eq_of_slice_eq
    {
      a b :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      h :
        a t = b t
    )
    (x : Point3) :
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (fun y =>
          realVorticityX a t y)
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (fun y =>
          realVorticityX b t y)
        x := by

  have hω :
      (fun y =>
        realVorticityX a t y)
        =
      (fun y =>
        realVorticityX b t y) := by
    funext y
    exact
      realVorticityX_eq_of_slice_eq
        h y

  rw [hω]

/--
The classical y-vorticity Laplacian depends only on one velocity time slice.
-/
theorem realVorticityLaplacianY_eq_of_slice_eq
    {
      a b :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      h :
        a t = b t
    )
    (x : Point3) :
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (fun y =>
          realVorticityY a t y)
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (fun y =>
          realVorticityY b t y)
        x := by

  have hω :
      (fun y =>
        realVorticityY a t y)
        =
      (fun y =>
        realVorticityY b t y) := by
    funext y
    exact
      realVorticityY_eq_of_slice_eq
        h y

  rw [hω]

/--
The classical z-vorticity Laplacian depends only on one velocity time slice.
-/
theorem realVorticityLaplacianZ_eq_of_slice_eq
    {
      a b :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {t : ℝ}
    (
      h :
        a t = b t
    )
    (x : Point3) :
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (fun y =>
          realVorticityZ a t y)
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (fun y =>
          realVorticityZ b t y)
        x := by

  have hω :
      (fun y =>
        realVorticityZ a t y)
        =
      (fun y =>
        realVorticityZ b t y) := by
    funext y
    exact
      realVorticityZ_eq_of_slice_eq
        h y

  rw [hω]

/--
Agreement of native fields on `(0,T)` gives equality of the temporal
x-vorticity derivative at every interior time.
-/
theorem temporalRealVorticityX_eq_of_agreesBeforeT
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T t : ℝ}
    (
      hAgree :
        AgreesBeforeT u v T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (x : Point3) :
    temporal.d
        (
          fun τ =>
            realVorticityX
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              τ x
        )
        t
      =
    temporal.d
        (
          fun τ =>
            realVorticityX
              (PrimeTensor.Bridge.logSpaceTimeVectorField v)
              τ x
        )
        t := by

  have hEqOn :
      Set.EqOn
        (
          fun τ =>
            realVorticityX
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              τ x
        )
        (
          fun τ =>
            realVorticityX
              (PrimeTensor.Bridge.logSpaceTimeVectorField v)
              τ x
        )
        (Set.Ioo (0 : ℝ) T) := by

    intro τ hτ

    exact
      realVorticityX_eq_of_slice_eq
        (
          loggedVelocitySlice_eq_of_nativeSlice_eq
            (hAgree τ hτ)
        )
        x

  unfold temporal

  exact
    (
      hEqOn.deriv
        isOpen_Ioo
    )
    ht

/--
Agreement of native fields on `(0,T)` gives equality of the temporal
y-vorticity derivative at every interior time.
-/
theorem temporalRealVorticityY_eq_of_agreesBeforeT
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T t : ℝ}
    (
      hAgree :
        AgreesBeforeT u v T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (x : Point3) :
    temporal.d
        (
          fun τ =>
            realVorticityY
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              τ x
        )
        t
      =
    temporal.d
        (
          fun τ =>
            realVorticityY
              (PrimeTensor.Bridge.logSpaceTimeVectorField v)
              τ x
        )
        t := by

  have hEqOn :
      Set.EqOn
        (
          fun τ =>
            realVorticityY
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              τ x
        )
        (
          fun τ =>
            realVorticityY
              (PrimeTensor.Bridge.logSpaceTimeVectorField v)
              τ x
        )
        (Set.Ioo (0 : ℝ) T) := by

    intro τ hτ

    exact
      realVorticityY_eq_of_slice_eq
        (
          loggedVelocitySlice_eq_of_nativeSlice_eq
            (hAgree τ hτ)
        )
        x

  unfold temporal

  exact
    (
      hEqOn.deriv
        isOpen_Ioo
    )
    ht

/--
Agreement of native fields on `(0,T)` gives equality of the temporal
z-vorticity derivative at every interior time.
-/
theorem temporalRealVorticityZ_eq_of_agreesBeforeT
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T t : ℝ}
    (
      hAgree :
        AgreesBeforeT u v T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (x : Point3) :
    temporal.d
        (
          fun τ =>
            realVorticityZ
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              τ x
        )
        t
      =
    temporal.d
        (
          fun τ =>
            realVorticityZ
              (PrimeTensor.Bridge.logSpaceTimeVectorField v)
              τ x
        )
        t := by

  have hEqOn :
      Set.EqOn
        (
          fun τ =>
            realVorticityZ
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              τ x
        )
        (
          fun τ =>
            realVorticityZ
              (PrimeTensor.Bridge.logSpaceTimeVectorField v)
              τ x
        )
        (Set.Ioo (0 : ℝ) T) := by

    intro τ hτ

    exact
      realVorticityZ_eq_of_slice_eq
        (
          loggedVelocitySlice_eq_of_nativeSlice_eq
            (hAgree τ hτ)
        )
        x

  unfold temporal

  exact
    (
      hEqOn.deriv
        isOpen_Ioo
    )
    ht

/--
The native x-vorticity balance transfers from a preterminal field to any field
which agrees with it on `(0,T)`.
-/
theorem mulVorticityBalanceX_of_agreesBeforeT
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T t : ℝ}
    {x : Point3}
    (
      hAgree :
        AgreesBeforeT u v T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (
      hBalance :
        MulVorticityBalanceX u t x
    ) :
    MulVorticityBalanceX v t x := by

  have hLogged :=
    (
      mulVorticityBalanceX_iff_loggedEquation
        u t x
    ).1 hBalance

  apply
    (
      mulVorticityBalanceX_iff_loggedEquation
        v t x
    ).2

  have hSlice :
      PrimeTensor.Bridge.logSpaceTimeVectorField u t
        =
      PrimeTensor.Bridge.logSpaceTimeVectorField v t :=
    loggedVelocitySlice_eq_of_nativeSlice_eq
      (hAgree t ht)

  have hTemporal :=
    temporalRealVorticityX_eq_of_agreesBeforeT
      hAgree ht x

  have hTransport :=
    realVorticityTransportX_eq_of_slice_eq
      hSlice x

  have hStretch :=
    realVortexStretchComponent_eq_of_slice_eq
      hSlice x xAxis

  have hLaplacian :=
    realVorticityLaplacianX_eq_of_slice_eq
      hSlice x

  rw [
    ← hTemporal,
    ← hTransport,
    ← hStretch,
    ← hLaplacian
  ]

  exact hLogged

/--
The native y-vorticity balance transfers from a preterminal field to any field
which agrees with it on `(0,T)`.
-/
theorem mulVorticityBalanceY_of_agreesBeforeT
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T t : ℝ}
    {x : Point3}
    (
      hAgree :
        AgreesBeforeT u v T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (
      hBalance :
        MulVorticityBalanceY u t x
    ) :
    MulVorticityBalanceY v t x := by

  have hLogged :=
    (
      mulVorticityBalanceY_iff_loggedEquation
        u t x
    ).1 hBalance

  apply
    (
      mulVorticityBalanceY_iff_loggedEquation
        v t x
    ).2

  have hSlice :
      PrimeTensor.Bridge.logSpaceTimeVectorField u t
        =
      PrimeTensor.Bridge.logSpaceTimeVectorField v t :=
    loggedVelocitySlice_eq_of_nativeSlice_eq
      (hAgree t ht)

  have hTemporal :=
    temporalRealVorticityY_eq_of_agreesBeforeT
      hAgree ht x

  have hTransport :=
    realVorticityTransportY_eq_of_slice_eq
      hSlice x

  have hStretch :=
    realVortexStretchComponent_eq_of_slice_eq
      hSlice x yAxis

  have hLaplacian :=
    realVorticityLaplacianY_eq_of_slice_eq
      hSlice x

  rw [
    ← hTemporal,
    ← hTransport,
    ← hStretch,
    ← hLaplacian
  ]

  exact hLogged

/--
The native z-vorticity balance transfers from a preterminal field to any field
which agrees with it on `(0,T)`.
-/
theorem mulVorticityBalanceZ_of_agreesBeforeT
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T t : ℝ}
    {x : Point3}
    (
      hAgree :
        AgreesBeforeT u v T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (
      hBalance :
        MulVorticityBalanceZ u t x
    ) :
    MulVorticityBalanceZ v t x := by

  have hLogged :=
    (
      mulVorticityBalanceZ_iff_loggedEquation
        u t x
    ).1 hBalance

  apply
    (
      mulVorticityBalanceZ_iff_loggedEquation
        v t x
    ).2

  have hSlice :
      PrimeTensor.Bridge.logSpaceTimeVectorField u t
        =
      PrimeTensor.Bridge.logSpaceTimeVectorField v t :=
    loggedVelocitySlice_eq_of_nativeSlice_eq
      (hAgree t ht)

  have hTemporal :=
    temporalRealVorticityZ_eq_of_agreesBeforeT
      hAgree ht x

  have hTransport :=
    realVorticityTransportZ_eq_of_slice_eq
      hSlice x

  have hStretch :=
    realVortexStretchComponent_eq_of_slice_eq
      hSlice x zAxis

  have hLaplacian :=
    realVorticityLaplacianZ_eq_of_slice_eq
      hSlice x

  rw [
    ← hTemporal,
    ← hTransport,
    ← hStretch,
    ← hLaplacian
  ]

  exact hLogged

/--
Stagewise X-balances transfer along any refinement path which remains strictly
inside `(0,T)`.
-/
theorem balancePathX_of_agreesBeforeT
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    (
      hAgree :
        AgreesBeforeT u v T
    )
    (
      hBefore :
        TimePathStrictlyBefore τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceX
            u (τ n) x
    ) :
    ∀ n : Depth,
      MulVorticityBalanceX
        v (τ n) x := by

  intro n

  exact
    mulVorticityBalanceX_of_agreesBeforeT
      hAgree
      (hBefore n)
      (hStages n)

/--
Stagewise Y-balances transfer along any refinement path which remains strictly
inside `(0,T)`.
-/
theorem balancePathY_of_agreesBeforeT
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    (
      hAgree :
        AgreesBeforeT u v T
    )
    (
      hBefore :
        TimePathStrictlyBefore τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceY
            u (τ n) x
    ) :
    ∀ n : Depth,
      MulVorticityBalanceY
        v (τ n) x := by

  intro n

  exact
    mulVorticityBalanceY_of_agreesBeforeT
      hAgree
      (hBefore n)
      (hStages n)

/--
Stagewise Z-balances transfer along any refinement path which remains strictly
inside `(0,T)`.
-/
theorem balancePathZ_of_agreesBeforeT
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    (
      hAgree :
        AgreesBeforeT u v T
    )
    (
      hBefore :
        TimePathStrictlyBefore τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceZ
            u (τ n) x
    ) :
    ∀ n : Depth,
      MulVorticityBalanceZ
        v (τ n) x := by

  intro n

  exact
    mulVorticityBalanceZ_of_agreesBeforeT
      hAgree
      (hBefore n)
      (hStages n)

/--
A smooth continuation extension rules out an X-component cofinal cascade along
every strictly preterminal time path whose original stages satisfy the native
X-vorticity balance.
-/
theorem SmoothContinuationExtension.noCofinalVorticityBalancePathX
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    (
      hExt :
        SmoothContinuationExtension u v T
    )
    (
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hBefore :
        TimePathStrictlyBefore τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceX
            u (τ n) x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathX
            (constantVelocityRefinement v)
            v τ T x
        ) := by

  have hStagesV :
      ∀ n : Depth,
        MulVorticityBalanceX
          v (τ n) x :=
    balancePathX_of_agreesBeforeT
      hExt.agrees_before
      hBefore
      hStages

  have hLimit :
      MulVorticityBalanceX
        v T x :=
    (hExt.terminal_balanced x).1

  have hSpatial :
      VelocityLogSpatialC3 v :=
    hExt.terminal_regular.1

  have hNoFailure :
      ¬ VelocityJetFailureAt v T x :=
    hExt.terminal_regular.2 x

  exact
    noCofinalVorticityBalancePathX_of_noVelocityJetFailure
      hτ
      hStagesV
      hLimit
      hSpatial
      hNoFailure

/--
Y-component continuation/cascade incompatibility.
-/
theorem SmoothContinuationExtension.noCofinalVorticityBalancePathY
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    (
      hExt :
        SmoothContinuationExtension u v T
    )
    (
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hBefore :
        TimePathStrictlyBefore τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceY
            u (τ n) x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathY
            (constantVelocityRefinement v)
            v τ T x
        ) := by

  have hStagesV :
      ∀ n : Depth,
        MulVorticityBalanceY
          v (τ n) x :=
    balancePathY_of_agreesBeforeT
      hExt.agrees_before
      hBefore
      hStages

  have hLimit :
      MulVorticityBalanceY
        v T x :=
    (hExt.terminal_balanced x).2.1

  have hSpatial :
      VelocityLogSpatialC3 v :=
    hExt.terminal_regular.1

  have hNoFailure :
      ¬ VelocityJetFailureAt v T x :=
    hExt.terminal_regular.2 x

  exact
    noCofinalVorticityBalancePathY_of_noVelocityJetFailure
      hτ
      hStagesV
      hLimit
      hSpatial
      hNoFailure

/--
Z-component continuation/cascade incompatibility.
-/
theorem SmoothContinuationExtension.noCofinalVorticityBalancePathZ
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    (
      hExt :
        SmoothContinuationExtension u v T
    )
    (
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hBefore :
        TimePathStrictlyBefore τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceZ
            u (τ n) x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathZ
            (constantVelocityRefinement v)
            v τ T x
        ) := by

  have hStagesV :
      ∀ n : Depth,
        MulVorticityBalanceZ
          v (τ n) x :=
    balancePathZ_of_agreesBeforeT
      hExt.agrees_before
      hBefore
      hStages

  have hLimit :
      MulVorticityBalanceZ
        v T x :=
    (hExt.terminal_balanced x).2.2

  have hSpatial :
      VelocityLogSpatialC3 v :=
    hExt.terminal_regular.1

  have hNoFailure :
      ¬ VelocityJetFailureAt v T x :=
    hExt.terminal_regular.2 x

  exact
    noCofinalVorticityBalancePathZ_of_noVelocityJetFailure
      hτ
      hStagesV
      hLimit
      hSpatial
      hNoFailure

end Euclidean
end Bridge
end PrimeTensor
