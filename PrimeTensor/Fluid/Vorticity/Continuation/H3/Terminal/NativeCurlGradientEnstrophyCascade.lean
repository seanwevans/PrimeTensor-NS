import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeCurlGradientFiniteStateEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.EnstrophySequence

/-!
# Fixed native curl / gradient escape with synchronized enstrophy cascade

The fixed native curl/gradient theorem gives, under hypothetical nonextension,

* one fixed structurally valid curl / constituent-gradient pair,
* one fixed orientation for each member, and
* one common localized terminal spacetime sequence

on which both native logarithmic coordinates escape one-sidedly.

Because the curl component itself is fixed, the same sequence has a sharper
enstrophy consequence than the earlier varying-component sequence.

For the selected structural pair `p`,

    |ω_p| ≤ max(|ωₓ|, |ωᵧ|, |ω_z|),

and therefore

    ω_p² ≤ realEnstrophyDensity.

The oriented lower bound

    n < oriented(ω_p)

implies

    n < |ω_p|,

so on exactly the same points

    n² < realEnstrophyDensity.

Consequently both the real pointwise enstrophy density and the logarithm of the
native multiplicative enstrophy state tend to `+∞` along the same terminal
sequence on which the fixed native curl and native gradient escape in their
fixed directions.

This remains a necessary consequence conditional on hypothetical failure of
smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## The packaged fixed curl component is controlled by the vorticity max -/

theorem abs_h3TerminalCurlFieldForPair_le_vorticityComponentMax
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (x : Point3) :
    abs
        (
          h3TerminalCurlFieldForPair
            u p t x
        )
      ≤
    max
      (
        abs
          (
            realVorticityX
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
          )
      )
      (
        max
          (
            abs
              (
                realVorticityY
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t x
              )
          )
          (
            abs
              (
                realVorticityZ
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t x
              )
          )
      ) := by

  cases p with

  | x_yz =>
      exact
        le_max_left _ _

  | x_zy =>
      exact
        le_max_left _ _

  | y_zx =>
      exact
        le_trans
          (le_max_left _ _)
          (le_max_right _ _)

  | y_xz =>
      exact
        le_trans
          (le_max_left _ _)
          (le_max_right _ _)

  | z_xy =>
      exact
        le_trans
          (le_max_right _ _)
          (le_max_right _ _)

  | z_yx =>
      exact
        le_trans
          (le_max_right _ _)
          (le_max_right _ _)

/--
The square of the fixed curl component selected by the structural pair is
bounded by the real pointwise enstrophy density.
-/
theorem sq_h3TerminalCurlFieldForPair_le_realEnstrophyDensity
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (x : Point3) :
    (
      h3TerminalCurlFieldForPair
        u p t x
    ) ^ 2
      ≤
    realEnstrophyDensity
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      t x := by

  let W : ℝ :=
    max
      (
        abs
          (
            realVorticityX
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
          )
      )
      (
        max
          (
            abs
              (
                realVorticityY
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t x
              )
          )
          (
            abs
              (
                realVorticityZ
                  (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                  t x
              )
          )
      )

  have hAbs :
      abs
          (
            h3TerminalCurlFieldForPair
              u p t x
          )
        ≤
      W := by

    dsimp only [W]

    exact
      abs_h3TerminalCurlFieldForPair_le_vorticityComponentMax
        u p t x

  have hWNonneg :
      0 ≤ W := by

    dsimp only [W]

    exact
      le_max_of_le_left
        (abs_nonneg _)

  have hSq :
      (
        abs
          (
            h3TerminalCurlFieldForPair
              u p t x
          )
      ) ^ 2
        ≤
      W ^ 2 := by

    nlinarith [
      abs_nonneg
        (
          h3TerminalCurlFieldForPair
            u p t x
        )
    ]

  have hMaxSq :
      W ^ 2
        ≤
      realEnstrophyDensity
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x := by

    dsimp only [W]

    exact
      sq_vorticityComponentMax_le_realEnstrophyDensity
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x

  calc
    (
      h3TerminalCurlFieldForPair
        u p t x
    ) ^ 2
        =
      (
        abs
          (
            h3TerminalCurlFieldForPair
              u p t x
          )
      ) ^ 2 := by
        rw [sq_abs]

    _ ≤ W ^ 2 :=
      hSq

    _ ≤
      realEnstrophyDensity
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x :=
      hMaxSq

/-! ## Orientation implies absolute-value largeness -/

theorem lt_abs_of_lt_h3TerminalOrientedValue
    (s : H3TerminalOrientation)
    (M z : ℝ)
    (h :
      M <
        h3TerminalOrientedValue
          s z) :
    M < abs z := by

  cases s with

  | positive =>

      simpa only [
        h3TerminalOrientedValue_positive
      ] using
        lt_of_lt_of_le
          h
          (le_abs_self z)

  | negative =>

      have hNeg :
          M < -z := by

        simpa only [
          h3TerminalOrientedValue_negative
        ] using h

      have hNegLeAbs :
          -z ≤ abs z := by

        have hBase :
            -z ≤ abs (-z) :=
          le_abs_self (-z)

        simpa only [abs_neg] using hBase

      exact
        lt_of_lt_of_le
          hNeg
          hNegLeAbs

/-! ## Synchronized enstrophy cascade package -/

def H3TerminalNativeCurlGradientEnstrophyCascade
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
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeCurlForPair
              u p
              (τ n)
              (x n)
        )
        sCurl
        ∧
      H3TerminalNativeLogDirectionalEscape
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

/--
The fixed double-directional native curl/gradient sequence carries a quadratic
pointwise enstrophy lower bound and native enstrophy logarithmic divergence on
the same spacetime points.
-/
theorem nativeCurlGradientEnstrophyCascade_of_doubleDirectionalEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hDirectional :
      H3TerminalNativeCurlGradientDoubleDirectionalEscape
        u a T p sCurl sGradient) :
    H3TerminalNativeCurlGradientEnstrophyCascade
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

  have hCurlFinite :
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

  have hGradientFinite :
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

  have hEnstrophy :
      ∀ n : ℕ,
        (n : ℝ) ^ 2
          <
        realEnstrophyDensity
          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          (τ n)
          (x n) := by

    intro n

    have hCurlOriented :
        (n : ℝ)
          <
        h3TerminalOrientedValue
          sCurl
          (
            h3TerminalCurlFieldForPair
              u p
              (τ n)
              (x n)
          ) := by

      have hNative :=
        (hτ n).2.2.1

      rw [
        logValue_h3TerminalNativeCurlForPair
          u p
          (τ n)
          (x n)
      ] at hNative

      exact hNative

    have hCurlAbs :
        (n : ℝ)
          <
        abs
          (
            h3TerminalCurlFieldForPair
              u p
              (τ n)
              (x n)
          ) :=
      lt_abs_of_lt_h3TerminalOrientedValue
        sCurl
        (n : ℝ)
        (
          h3TerminalCurlFieldForPair
            u p
            (τ n)
            (x n)
        )
        hCurlOriented

    have hSq :
        (n : ℝ) ^ 2
          <
        (
          h3TerminalCurlFieldForPair
            u p
            (τ n)
            (x n)
        ) ^ 2 := by

      have hAbsSq :
          (n : ℝ) ^ 2
            <
          (
            abs
              (
                h3TerminalCurlFieldForPair
                  u p
                  (τ n)
                  (x n)
              )
          ) ^ 2 :=
        (sq_lt_sq₀
          (Nat.cast_nonneg n)
          (abs_nonneg _)).2
          hCurlAbs

      simpa only [sq_abs] using hAbsSq

    exact
      lt_of_lt_of_le
        hSq
        (
          sq_h3TerminalCurlFieldForPair_le_realEnstrophyDensity
            u p
            (τ n)
            (x n)
        )

  have hEnstrophyTendsto :
      Tendsto
        (
          fun n : ℕ =>
            realEnstrophyDensity
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              (τ n)
              (x n)
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro M

    obtain
      ⟨N : ℕ, hN⟩ :=
      exists_nat_gt
        (max M 1)

    filter_upwards
      [eventually_ge_atTop N]
      with n hn

    have hNLe :
        (N : ℝ) ≤ n := by
      exact_mod_cast hn

    have hMltN :
        M < (N : ℝ) := by

      exact
        lt_of_le_of_lt
          (le_max_left M 1)
          hN

    have hOneLtN :
        1 < (N : ℝ) := by

      exact
        lt_of_le_of_lt
          (le_max_right M 1)
          hN

    have hOneLeN :
        1 ≤ (n : ℝ) := by
      linarith

    have hNNonneg :
        0 ≤ (n : ℝ) :=
      Nat.cast_nonneg n

    have hNSq :
        (n : ℝ)
          ≤
        (n : ℝ) ^ 2 := by

      nlinarith [
        mul_nonneg
          hNNonneg
          (sub_nonneg.mpr hOneLeN)
      ]

    exact
      le_of_lt
        (
          lt_trans
            (lt_of_lt_of_le hMltN hNLe)
            (
              lt_of_le_of_lt
                hNSq
                (hEnstrophy n)
            )
        )

  have hNativeEnstrophyTendsto :
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
        atTop := by

    have hEq :
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
          =
        (
          fun n : ℕ =>
            realEnstrophyDensity
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              (τ n)
              (x n)
        ) := by

      funext n

      exact
        logValue_mulEnstrophyDensity
          u
          (τ n)
          (x n)

    rw [hEq]

    exact
      hEnstrophyTendsto

  refine
    ⟨
      τ,
      x,
      ?_,
      hTauTendsto,
      hCurlDirectional,
      hGradientDirectional,
      hCurlFinite,
      hGradientFinite,
      hEnstrophyTendsto,
      hNativeEnstrophyTendsto
    ⟩

  intro n

  exact
    ⟨
      (hτ n).1,
      (hτ n).2.1,
      hEnstrophy n
    ⟩

/-! ## Synchronized cascade under hypothetical nonextension -/

/--
Under hypothetical nonextension, one fixed native curl/gradient structural
pair, fixed directions, and one common terminal spacetime sequence carry all
of the following simultaneously:

* one-sided native curl logarithmic escape;
* one-sided native constituent-gradient logarithmic escape;
* escape past every fixed finite native state for both;
* the quantitative lower bound `n² < realEnstrophyDensity`;
* real pointwise enstrophy divergence;
* native multiplicative enstrophy logarithmic divergence.
-/
theorem fixed_nativeCurlGradient_enstrophyCascade_of_noH3PathExtension
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
        H3TerminalNativeCurlGradientEnstrophyCascade
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
      nativeCurlGradientEnstrophyCascade_of_doubleDirectionalEscape
        hDirectional
    ⟩

/-! ## Neutral package -/

/--
Neutral synchronized terminal formulation.

Either the H³ path extends smoothly, or one fixed native curl/gradient pair
and fixed directions carry the synchronized enstrophy cascade described above
on one common terminal spacetime sequence.
-/
theorem smoothContinuationExtension_or_fixed_nativeCurlGradient_enstrophyCascade
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
          H3TerminalNativeCurlGradientEnstrophyCascade
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
          fixed_nativeCurlGradient_enstrophyCascade_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
