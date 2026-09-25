import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeCurlGradientEnstrophyFiniteStateEscape

/-!
# Quadratic native curl / enstrophy coupling

The synchronized terminal development already places a fixed native vorticity
ratio, a fixed native constituent velocity derivative, and native enstrophy on
one common terminal spacetime sequence.

There is also an exact pointwise quantitative relation which does not depend on
hypothetical nonextension.

For every one of the six packaged structural curl/gradient pairs,

    (logValue nativeCurl)²
      =
    (real fixed curl component)²
      ≤
    realEnstrophyDensity
      =
    logValue nativeEnstrophy.

Thus the native enstrophy logarithm dominates the square of the selected native
curl logarithm pointwise.

Under hypothetical nonextension, the already-selected synchronized terminal
sequence therefore carries

    n² < logValue nativeEnstrophy

together with the stronger intrinsic coupling

    (logValue nativeCurl)² ≤ logValue nativeEnstrophy

at every selected point, while retaining the fixed one-sided native curl and
gradient escapes.

These remain necessary consequences conditional on hypothetical failure of
smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Universal pointwise quadratic bridge -/

/--
For every packaged fixed curl component, the square of the logarithmic native
curl coordinate is bounded by the logarithmic native enstrophy coordinate.
-/
theorem sq_logValue_h3TerminalNativeCurlForPair_le_logValue_mulEnstrophyDensity
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (x : Point3) :
    (
      PrimeTensor.Bridge.MulReal.logValue
        (
          h3TerminalNativeCurlForPair
            u p t x
        )
    ) ^ 2
      ≤
    PrimeTensor.Bridge.MulReal.logValue
      (
        mulEnstrophyDensity
          u t x
      ) := by

  rw [
    logValue_h3TerminalNativeCurlForPair,
    logValue_mulEnstrophyDensity
  ]

  exact
    sq_h3TerminalCurlFieldForPair_le_realEnstrophyDensity
      u p t x

/-! ## Synchronized quadratic cascade package -/

def H3TerminalNativeCurlEnstrophyQuadraticCascade
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
          PrimeTensor.Bridge.MulReal.logValue
            (
              mulEnstrophyDensity
                u
                (τ n)
                (x n)
            )
            ∧
          (
            PrimeTensor.Bridge.MulReal.logValue
              (
                h3TerminalNativeCurlForPair
                  u p
                  (τ n)
                  (x n)
              )
          ) ^ 2
            ≤
          PrimeTensor.Bridge.MulReal.logValue
            (
              mulEnstrophyDensity
                u
                (τ n)
                (x n)
            )
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
Upgrade the synchronized enstrophy cascade with the exact native quadratic
curl/enstrophy coupling.
-/
theorem nativeCurlEnstrophyQuadraticCascade_of_enstrophyCascade
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hCascade :
      H3TerminalNativeCurlGradientEnstrophyCascade
        u a T p sCurl sGradient) :
    H3TerminalNativeCurlEnstrophyQuadraticCascade
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
      hRealEnstrophyTendsto,
      hNativeEnstrophyTendsto
    ⟩ :=
    hCascade

  refine
    ⟨
      τ,
      x,
      ?_,
      hTauTendsto,
      hCurlDirectional,
      hGradientDirectional,
      hNativeEnstrophyTendsto
    ⟩

  intro n

  refine
    ⟨
      (hτ n).1,
      (hτ n).2.1,
      ?_,
      ?_
    ⟩

  · rw [
      logValue_mulEnstrophyDensity
    ]

    exact
      (hτ n).2.2

  · exact
      sq_logValue_h3TerminalNativeCurlForPair_le_logValue_mulEnstrophyDensity
        u p
        (τ n)
        (x n)

/-! ## Quadratic terminal consequence under hypothetical nonextension -/

/--
Under hypothetical nonextension, one fixed native curl/gradient structural pair
and one common localized terminal spacetime sequence carry both fixed
directional native escapes and the pointwise quadratic native curl/enstrophy
coupling.
-/
theorem fixed_nativeCurl_enstrophyQuadraticCascade_of_noH3PathExtension
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
        H3TerminalNativeCurlEnstrophyQuadraticCascade
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
      nativeCurlEnstrophyQuadraticCascade_of_enstrophyCascade
        hCascade
    ⟩

/-! ## Neutral package -/

/--
Neutral terminal formulation with the exact native quadratic curl/enstrophy
coupling retained on the synchronized sequence.
-/
theorem smoothContinuationExtension_or_fixed_nativeCurl_enstrophyQuadraticCascade
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
          H3TerminalNativeCurlEnstrophyQuadraticCascade
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
          fixed_nativeCurl_enstrophyQuadraticCascade_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
