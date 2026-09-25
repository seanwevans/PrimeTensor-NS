import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeCurlGradientEnstrophyCascade

/-!
# Synchronized finite-state escape of native curl, gradient, and enstrophy

The synchronized enstrophy cascade already puts three native objects on one
common terminal spacetime sequence:

* one fixed native vorticity ratio,
* one fixed native constituent velocity derivative,
* the native multiplicative enstrophy state.

The first two have fixed one-sided logarithmic escape directions.  The
enstrophy logarithm tends to `+∞`.

This file converts the enstrophy limit into the same finite-state language
already used for the native curl and gradient.  Thus, on one common sequence,

* the fixed native curl passes every finite logarithmic state in its fixed
  direction and eventually avoids every fixed `MulReal` value;
* the fixed native gradient does the same in its fixed direction;
* native enstrophy passes every finite logarithmic state in the positive
  direction and eventually avoids every fixed `MulReal` value.

The quantitative bound

    n² < realEnstrophyDensity

is retained on that same sequence.

No order on `MulReal` is introduced.

All statements remain necessary consequences conditional on hypothetical
failure of smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Triple finite-state escape package -/

def H3TerminalNativeCurlGradientEnstrophyFiniteStateEscape
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
            ∧
          (n : ℝ) ^ 2
            <
          realEnstrophyDensity
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ n)
            (x n)
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
      H3TerminalNativeLogEscapesEveryFiniteState
        (
          fun n : ℕ =>
            mulEnstrophyDensity
              u
              (τ n)
              (x n)
        )
        H3TerminalOrientation.positive
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
        ∧
      H3TerminalNativeEventuallyAvoidsEveryFiniteState
        (
          fun n : ℕ =>
            mulEnstrophyDensity
              u
              (τ n)
              (x n)
        )
        ∧
      Tendsto
        (
          fun n : ℕ =>
            realEnstrophyDensity
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              (τ n)
              (x n)
        )
        atTop
        atTop
        ∧
      Tendsto
        (
          fun n : ℕ =>
            PrimeTensor.Bridge.MulReal.logValue
              (
                mulEnstrophyDensity
                  u
                  (τ n)
                  (x n)
              )
        )
        atTop
        atTop

/-! ## Enstrophy finite-state escape from its positive logarithmic divergence -/

/--
A native enstrophy sequence whose logarithmic coordinate tends to `+∞`
escapes every fixed finite native state in the positive direction.
-/
theorem nativeEnstrophyLogEscapesEveryFiniteState_of_tendsto
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hTendsto :
      Tendsto
        (
          fun n : ℕ =>
            PrimeTensor.Bridge.MulReal.logValue
              (
                mulEnstrophyDensity
                  u
                  (τ n)
                  (x n)
              )
        )
        atTop
        atTop) :
    H3TerminalNativeLogEscapesEveryFiniteState
      (
        fun n : ℕ =>
          mulEnstrophyDensity
            u
            (τ n)
            (x n)
      )
      H3TerminalOrientation.positive := by

  apply
    nativeLogEscapesEveryFiniteState_of_directionalEscape

  unfold H3TerminalNativeLogDirectionalEscape

  exact hTendsto

/--
The same positive logarithmic escape implies eventual exact avoidance of every
fixed native enstrophy state.
-/
theorem nativeEnstrophyEventuallyAvoidsEveryFiniteState_of_tendsto
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hTendsto :
      Tendsto
        (
          fun n : ℕ =>
            PrimeTensor.Bridge.MulReal.logValue
              (
                mulEnstrophyDensity
                  u
                  (τ n)
                  (x n)
              )
        )
        atTop
        atTop) :
    H3TerminalNativeEventuallyAvoidsEveryFiniteState
      (
        fun n : ℕ =>
          mulEnstrophyDensity
            u
            (τ n)
            (x n)
      ) := by

  exact
    nativeEventuallyAvoidsEveryFiniteState_of_logEscape
      (
        nativeEnstrophyLogEscapesEveryFiniteState_of_tendsto
          hTendsto
      )

/-! ## Upgrade the synchronized enstrophy cascade -/

/--
Upgrade the synchronized native curl/gradient enstrophy cascade so that all
three native states escape every fixed finite logarithmic state and eventually
avoid every fixed native value on the same spacetime sequence.
-/
theorem nativeCurlGradientEnstrophyFiniteStateEscape_of_cascade
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hCascade :
      H3TerminalNativeCurlGradientEnstrophyCascade
        u a T p sCurl sGradient) :
    H3TerminalNativeCurlGradientEnstrophyFiniteStateEscape
      u a T p sCurl sGradient := by

  obtain
    ⟨
      τ,
      x,
      hτ,
      hTauTendsto,
      hCurlDirectional,
      hGradientDirectional,
      hCurlFinite,
      hGradientFinite,
      hEnstrophyTendsto,
      hNativeEnstrophyTendsto
    ⟩ :=
    hCascade

  have hEnstrophyFinite :
      H3TerminalNativeLogEscapesEveryFiniteState
        (
          fun n : ℕ =>
            mulEnstrophyDensity
              u
              (τ n)
              (x n)
        )
        H3TerminalOrientation.positive :=
    nativeEnstrophyLogEscapesEveryFiniteState_of_tendsto
      hNativeEnstrophyTendsto

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
      hCurlFinite

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
      hGradientFinite

  have hEnstrophyAvoid :
      H3TerminalNativeEventuallyAvoidsEveryFiniteState
        (
          fun n : ℕ =>
            mulEnstrophyDensity
              u
              (τ n)
              (x n)
        ) :=
    nativeEventuallyAvoidsEveryFiniteState_of_logEscape
      hEnstrophyFinite

  exact
    ⟨
      τ,
      x,
      hτ,
      hTauTendsto,
      hCurlFinite,
      hGradientFinite,
      hEnstrophyFinite,
      hCurlAvoid,
      hGradientAvoid,
      hEnstrophyAvoid,
      hEnstrophyTendsto,
      hNativeEnstrophyTendsto
    ⟩

/-! ## Triple finite-state escape under hypothetical nonextension -/

/--
Under hypothetical nonextension, one fixed native curl/gradient structural
pair and one common localized terminal spacetime sequence carry simultaneous
finite-state escape of

* the fixed native curl ratio in its fixed direction;
* the fixed native constituent gradient in its fixed direction;
* native enstrophy in the positive logarithmic direction.

All three eventually avoid every fixed `MulReal` value, and the same sequence
retains `n² < realEnstrophyDensity`.
-/
theorem fixed_nativeCurlGradientEnstrophy_finiteStateEscape_of_noH3PathExtension
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
        H3TerminalNativeCurlGradientEnstrophyFiniteStateEscape
          u a T p sCurl sGradient := by

  obtain
    ⟨
      p,
      sCurl,
      sGradient,
      hCascade
    ⟩ :=
    fixed_nativeCurlGradient_enstrophyCascade_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  exact
    ⟨
      p,
      sCurl,
      sGradient,
      nativeCurlGradientEnstrophyFiniteStateEscape_of_cascade
        hCascade
    ⟩

/-! ## Neutral package -/

/--
Neutral synchronized multiplicative terminal formulation.

Either the H³ path extends smoothly, or one fixed native curl/gradient pair
and native enstrophy all escape every fixed finite native state on the same
terminal spacetime sequence, with the curl and gradient using their respective
fixed directions and enstrophy escaping positively in logarithmic coordinates.
-/
theorem smoothContinuationExtension_or_fixed_nativeCurlGradientEnstrophy_finiteStateEscape
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
          H3TerminalNativeCurlGradientEnstrophyFiniteStateEscape
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
          fixed_nativeCurlGradientEnstrophy_finiteStateEscape_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
