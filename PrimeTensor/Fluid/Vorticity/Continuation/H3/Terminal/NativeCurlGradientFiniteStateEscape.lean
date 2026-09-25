import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeCurlGradientDoubleEscape

/-!
# Escape from every fixed finite native curl / gradient state

The double-directional native theorem gives a fixed native curl ratio and a
fixed native constituent gradient whose logarithmic coordinates escape
one-sidedly on the same terminal spacetime sequence.

This file converts that asymptotic statement into an eventual finite-state
exclusion.

For a native sequence `Ωₙ` with fixed orientation:

* positive escape means that for every fixed `q : MulReal`,
  `logValue q < logValue Ωₙ` eventually;
* negative escape means that for every fixed `q : MulReal`,
  `logValue Ωₙ < logValue q` eventually.

Consequently every fixed native state is eventually avoided exactly:
`Ωₙ ≠ q` eventually.

No order on `MulReal` is introduced.  All comparisons remain in the faithful
real logarithmic coordinate.

All statements remain necessary consequences conditional on hypothetical
failure of smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Directional escape past every fixed finite state -/

def H3TerminalNativeLogEscapesEveryFiniteState
    (Ω : ℕ → PrimeTensor.MulReal)
    (s : H3TerminalOrientation) : Prop :=
  match s with
  | .positive =>
      ∀ q : PrimeTensor.MulReal,
        ∀ᶠ n : ℕ in atTop,
          PrimeTensor.Bridge.MulReal.logValue q
            <
          PrimeTensor.Bridge.MulReal.logValue (Ω n)
  | .negative =>
      ∀ q : PrimeTensor.MulReal,
        ∀ᶠ n : ℕ in atTop,
          PrimeTensor.Bridge.MulReal.logValue (Ω n)
            <
          PrimeTensor.Bridge.MulReal.logValue q

/--
One-sided logarithmic divergence eventually passes every fixed finite native
state in the corresponding direction.
-/
theorem nativeLogEscapesEveryFiniteState_of_directionalEscape
    {Ω : ℕ → PrimeTensor.MulReal}
    {s : H3TerminalOrientation}
    (hDirectional :
      H3TerminalNativeLogDirectionalEscape
        Ω s) :
    H3TerminalNativeLogEscapesEveryFiniteState
      Ω s := by

  cases s with

  | positive =>

      unfold H3TerminalNativeLogDirectionalEscape at hDirectional
      unfold H3TerminalNativeLogEscapesEveryFiniteState

      intro q

      have hEventually :
          ∀ᶠ n : ℕ in atTop,
            PrimeTensor.Bridge.MulReal.logValue q + 1
              ≤
            PrimeTensor.Bridge.MulReal.logValue (Ω n) :=
        (tendsto_atTop.1 hDirectional)
          (
            PrimeTensor.Bridge.MulReal.logValue q + 1
          )

      filter_upwards
        [hEventually]
        with n hn

      linarith

  | negative =>

      unfold H3TerminalNativeLogDirectionalEscape at hDirectional
      unfold H3TerminalNativeLogEscapesEveryFiniteState

      intro q

      have hEventually :
          ∀ᶠ n : ℕ in atTop,
            PrimeTensor.Bridge.MulReal.logValue (Ω n)
              ≤
            PrimeTensor.Bridge.MulReal.logValue q - 1 :=
        (tendsto_atBot.1 hDirectional)
          (
            PrimeTensor.Bridge.MulReal.logValue q - 1
          )

      filter_upwards
        [hEventually]
        with n hn

      linarith

/-! ## Eventual exact avoidance -/

def H3TerminalNativeEventuallyAvoidsEveryFiniteState
    (Ω : ℕ → PrimeTensor.MulReal) : Prop :=
  ∀ q : PrimeTensor.MulReal,
    ∀ᶠ n : ℕ in atTop,
      Ω n ≠ q

/--
Directional finite-state escape implies eventual exact avoidance of every
fixed native state.
-/
theorem nativeEventuallyAvoidsEveryFiniteState_of_logEscape
    {Ω : ℕ → PrimeTensor.MulReal}
    {s : H3TerminalOrientation}
    (hEscape :
      H3TerminalNativeLogEscapesEveryFiniteState
        Ω s) :
    H3TerminalNativeEventuallyAvoidsEveryFiniteState
      Ω := by

  intro q

  cases s with

  | positive =>

      unfold H3TerminalNativeLogEscapesEveryFiniteState at hEscape

      have hEventually :=
        hEscape q

      filter_upwards
        [hEventually]
        with n hn

      intro hEq

      rw [hEq] at hn

      exact
        (lt_irrefl
          (
            PrimeTensor.Bridge.MulReal.logValue q
          ))
          hn

  | negative =>

      unfold H3TerminalNativeLogEscapesEveryFiniteState at hEscape

      have hEventually :=
        hEscape q

      filter_upwards
        [hEventually]
        with n hn

      intro hEq

      rw [hEq] at hn

      exact
        (lt_irrefl
          (
            PrimeTensor.Bridge.MulReal.logValue q
          ))
          hn

/-! ## Fixed native pair finite-state escape package -/

def H3TerminalNativeCurlGradientFiniteStateEscape
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation) : Prop :=
  ∃
    τ : ℕ → ℝ,
    ∃ x : ℕ → Point3,
      (
        ∀ n : ℕ,
          τ n ∈ Set.Ioo a T
            ∧
          τ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
      )
        ∧
      Tendsto τ atTop (𝓝 T)
        ∧
      H3TerminalNativeLogEscapesEveryFiniteState
        (
          fun n : ℕ =>
            h3TerminalNativeCurlForPair
              u p
              (τ n)
              (x n)
        )
        sCurl
        ∧
      H3TerminalNativeLogEscapesEveryFiniteState
        (
          fun n : ℕ =>
            h3TerminalNativeGradientForPair
              u p
              (τ n)
              (x n)
        )
        sGradient
        ∧
      H3TerminalNativeEventuallyAvoidsEveryFiniteState
        (
          fun n : ℕ =>
            h3TerminalNativeCurlForPair
              u p
              (τ n)
              (x n)
        )
        ∧
      H3TerminalNativeEventuallyAvoidsEveryFiniteState
        (
          fun n : ℕ =>
            h3TerminalNativeGradientForPair
              u p
              (τ n)
              (x n)
        )

/--
Transport the fixed double-directional native escape into eventual escape past,
and exact avoidance of, every fixed finite native state.
-/
theorem nativeCurlGradientFiniteStateEscape_of_doubleDirectionalEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hDirectional :
      H3TerminalNativeCurlGradientDoubleDirectionalEscape
        u a T p sCurl sGradient) :
    H3TerminalNativeCurlGradientFiniteStateEscape
      u a T p sCurl sGradient := by

  obtain
    ⟨
      τ,
      x,
      hτ,
      hTauTendsto,
      hCurlDirectional,
      hGradientDirectional
    ⟩ :=
    hDirectional

  have hCurlEscape :
      H3TerminalNativeLogEscapesEveryFiniteState
        (
          fun n : ℕ =>
            h3TerminalNativeCurlForPair
              u p
              (τ n)
              (x n)
        )
        sCurl :=
    nativeLogEscapesEveryFiniteState_of_directionalEscape
      hCurlDirectional

  have hGradientEscape :
      H3TerminalNativeLogEscapesEveryFiniteState
        (
          fun n : ℕ =>
            h3TerminalNativeGradientForPair
              u p
              (τ n)
              (x n)
        )
        sGradient :=
    nativeLogEscapesEveryFiniteState_of_directionalEscape
      hGradientDirectional

  have hCurlAvoid :
      H3TerminalNativeEventuallyAvoidsEveryFiniteState
        (
          fun n : ℕ =>
            h3TerminalNativeCurlForPair
              u p
              (τ n)
              (x n)
        ) :=
    nativeEventuallyAvoidsEveryFiniteState_of_logEscape
      hCurlEscape

  have hGradientAvoid :
      H3TerminalNativeEventuallyAvoidsEveryFiniteState
        (
          fun n : ℕ =>
            h3TerminalNativeGradientForPair
              u p
              (τ n)
              (x n)
        ) :=
    nativeEventuallyAvoidsEveryFiniteState_of_logEscape
      hGradientEscape

  refine
    ⟨
      τ,
      x,
      ?_,
      hTauTendsto,
      hCurlEscape,
      hGradientEscape,
      hCurlAvoid,
      hGradientAvoid
    ⟩

  intro n

  exact
    ⟨
      (hτ n).1,
      (hτ n).2.1
    ⟩

/-! ## Finite-state escape under hypothetical nonextension -/

/--
Under hypothetical nonextension, one fixed native curl/gradient structural
pair and fixed directions admit a common terminal spacetime sequence on which
both native states eventually pass every fixed finite logarithmic state in
their respective directions and eventually avoid every fixed `MulReal` value.
-/
theorem fixed_nativeCurlGradient_finiteStateEscape_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃
      p : H3TerminalCurlGradientPair,
      ∃
        sCurl sGradient : H3TerminalOrientation,
        H3TerminalNativeCurlGradientFiniteStateEscape
          u a T p sCurl sGradient := by

  obtain
    ⟨
      p,
      sCurl,
      sGradient,
      hDirectional
    ⟩ :=
    fixed_nativeCurlGradient_doubleDirectionalEscape_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  exact
    ⟨
      p,
      sCurl,
      sGradient,
      nativeCurlGradientFiniteStateEscape_of_doubleDirectionalEscape
        hDirectional
    ⟩

/-! ## Neutral package -/

/--
Neutral multiplicative terminal formulation.

Either the H³ path extends smoothly, or one fixed native curl/gradient pair
escapes every fixed finite logarithmic state in fixed directions and
eventually avoids every fixed native value on one common terminal sequence.
-/
theorem smoothContinuationExtension_or_fixed_nativeCurlGradient_finiteStateEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∃
        p : H3TerminalCurlGradientPair,
        ∃
          sCurl sGradient : H3TerminalOrientation,
          H3TerminalNativeCurlGradientFiniteStateEscape
            u a T p sCurl sGradient
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (
          fixed_nativeCurlGradient_finiteStateEscape_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
