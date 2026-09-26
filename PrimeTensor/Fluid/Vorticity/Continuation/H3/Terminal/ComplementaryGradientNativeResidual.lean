import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.ComplementaryGradientCancellationSubsequence
import PrimeTensor.Bridge.MulReal.Log.Algebra
import PrimeTensor.Bridge.MulReal.Log.Embedding
import PrimeTensor.Analysis.Chain

/-!
# Native multiplicative residual behind complementary-gradient cancellation

The terminal complementary-gradient analysis has so far been phrased mostly in
logarithmic coordinates.

For each packaged structural pair there is, however, a single native state
whose logarithm is exactly the correctly signed curl logarithm seen by the
selected constituent derivative.

If the selected derivative is the numerator of the native curl ratio, this
state is the native curl itself.  If the selected derivative is the
denominator, it is the inverse native curl.

Call this the selected-signed native curl.  Then for all six structural pairs,

    nativeComplement
      =
    MulReal.ratio nativeSelected nativeSignedCurl.

Equivalently,

    nativeComplement * nativeSignedCurl
      =
    nativeSelected.

Thus the complementary derivative is literally the intrinsic multiplicative
residual between the selected derivative and the correctly oriented native
curl state.  Its logarithm is the additive cancellation defect already studied
in the preceding files.

These identities are pointwise and unconditional.  The final theorem merely
packages them with the existing neutral three-branch terminal alternative
under hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## The native state underlying the signed curl logarithm -/

noncomputable def h3TerminalSelectedSignedNativeCurlForPair
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (x : Point3) :
    MulReal :=
  match h3TerminalSelectedCurlSignForPair p with
  | .positive =>
      h3TerminalNativeCurlForPair
        u p t x
  | .negative =>
      (
        h3TerminalNativeCurlForPair
          u p t x
      )⁻¹

/--
The logarithm of the selected-signed native curl is exactly the signed curl
logarithm used in the cancellation analysis.
-/
theorem logValue_h3TerminalSelectedSignedNativeCurlForPair
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (
          h3TerminalSelectedSignedNativeCurlForPair
            u p t x
        )
      =
    h3TerminalSelectedSignedNativeCurlLog
      u p t x := by

  cases p <;>
    simp [
      h3TerminalSelectedSignedNativeCurlForPair,
      h3TerminalSelectedCurlSignForPair,
      h3TerminalSelectedSignedNativeCurlLog,
      h3TerminalOrientedValue,
      logValue_h3TerminalNativeCurlForPair,
      PrimeTensor.Bridge.MulReal.logValue_inv
    ]

/-! ## Exact native residual identity -/

/--
For every structural pair, the complementary native derivative is exactly the
multiplicative ratio of the selected native derivative to the correctly signed
native curl state.
-/
theorem h3TerminalNativeComplementGradientForPair_eq_residualRatio
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (x : Point3) :
    h3TerminalNativeComplementGradientForPair
        u p t x
      =
    PrimeTensor.MulReal.ratio
      (
        h3TerminalNativeGradientForPair
          u p t x
      )
      (
        h3TerminalSelectedSignedNativeCurlForPair
          u p t x
      ) := by

  apply
    PrimeTensor.Bridge.MulReal.logValue_injective

  calc
    PrimeTensor.Bridge.MulReal.logValue
        (
          h3TerminalNativeComplementGradientForPair
            u p t x
        )
        =
      PrimeTensor.Bridge.MulReal.logValue
          (
            h3TerminalNativeGradientForPair
              u p t x
          )
        -
      h3TerminalSelectedSignedNativeCurlLog
        u p t x :=
      logValue_nativeComplement_eq_gradient_sub_signedCurl
        u p t x

    _ =
      PrimeTensor.Bridge.MulReal.logValue
        (
          PrimeTensor.MulReal.ratio
            (
              h3TerminalNativeGradientForPair
                u p t x
            )
            (
              h3TerminalSelectedSignedNativeCurlForPair
                u p t x
            )
        ) := by

      rw [
        PrimeTensor.Bridge.MulReal.logValue_ratio,
        logValue_h3TerminalSelectedSignedNativeCurlForPair
      ]

/--
Multiplying the native residual by the correctly signed native curl reconstructs
the selected native velocity derivative exactly.
-/
theorem h3TerminalNativeComplement_mul_signedCurl_eq_selectedGradient
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (x : Point3) :
    h3TerminalNativeComplementGradientForPair
        u p t x
      *
    h3TerminalSelectedSignedNativeCurlForPair
        u p t x
      =
    h3TerminalNativeGradientForPair
      u p t x := by

  rw [
    h3TerminalNativeComplementGradientForPair_eq_residualRatio
  ]

  exact
    PrimeTensor.MulReal.ratio_mul_right
      (
        h3TerminalNativeGradientForPair
          u p t x
      )
      (
        h3TerminalSelectedSignedNativeCurlForPair
          u p t x
      )

/--
The logarithmic size of the intrinsic residual ratio is exactly the logarithmic
size of the complementary native derivative.
-/
theorem abs_logValue_residualRatio_eq_abs_logValue_complement
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (x : Point3) :
    abs
      (
        PrimeTensor.Bridge.MulReal.logValue
          (
            PrimeTensor.MulReal.ratio
              (
                h3TerminalNativeGradientForPair
                  u p t x
              )
              (
                h3TerminalSelectedSignedNativeCurlForPair
                  u p t x
              )
          )
      )
      =
    abs
      (
        PrimeTensor.Bridge.MulReal.logValue
          (
            h3TerminalNativeComplementGradientForPair
              u p t x
          )
      ) := by

  rw [
    ←
    h3TerminalNativeComplementGradientForPair_eq_residualRatio
      u p t x
  ]

/-! ## Pointwise residual law -/

def H3TerminalNativeCurlGradientResidualLaw
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair) : Prop :=
  ∀ t : ℝ,
    ∀ x : Point3,
      (
        h3TerminalNativeComplementGradientForPair
            u p t x
          =
        PrimeTensor.MulReal.ratio
          (
            h3TerminalNativeGradientForPair
              u p t x
          )
          (
            h3TerminalSelectedSignedNativeCurlForPair
              u p t x
          )
      )
        ∧
      (
        h3TerminalNativeComplementGradientForPair
            u p t x
          *
        h3TerminalSelectedSignedNativeCurlForPair
            u p t x
          =
        h3TerminalNativeGradientForPair
          u p t x
      )

theorem h3TerminalNativeCurlGradientResidualLaw
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair) :
    H3TerminalNativeCurlGradientResidualLaw
      u p := by

  intro t x

  exact
    ⟨
      h3TerminalNativeComplementGradientForPair_eq_residualRatio
        u p t x,
      h3TerminalNativeComplement_mul_signedCurl_eq_selectedGradient
        u p t x
    ⟩

/-! ## Package with the exhaustive terminal alternative -/

/--
Under hypothetical nonextension, the fixed structural pair from the exhaustive
three-branch terminal theorem also satisfies the exact native residual law at
every spacetime point.

The three branches remain neutral:

1. reinforcing signs force complementary escape;
2. cancellation-compatible unbounded residual yields synchronized triple
   escape on a subsequence;
3. cancellation-compatible bounded residual yields bounded-error and ratio-one
   matching.

The additional statement here is that the complementary state in every branch
is intrinsically the multiplicative residual

    ratio selected signedCurl.
-/
theorem fixed_nativeComplementGradient_threeBranchAlternative_withResidualLaw_of_noH3PathExtension
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
        H3TerminalNativeCurlGradientResidualLaw
          u p
          ∧
        (
          (
            H3TerminalComplementForcedRegime
              p sCurl sGradient
              ∧
            H3TerminalNativeComplementGradientForcedCascade
              u a T p sCurl sGradient
          )
            ∨
          (
            ∃ sComplement : H3TerminalOrientation,
              H3TerminalNativeCurlGradientComplementTripleEscape
                u a T p sCurl sGradient sComplement
          )
            ∨
          H3TerminalNativeComplementBoundedRatioMatching
            u a T p sCurl sGradient
        ) := by

  obtain
    ⟨
      p,
      sCurl,
      sGradient,
      hAlternative
    ⟩ :=
    fixed_nativeComplementGradient_threeBranchAlternative_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  exact
    ⟨
      p,
      sCurl,
      sGradient,
      h3TerminalNativeCurlGradientResidualLaw
        u p,
      hAlternative
    ⟩

/-! ## Neutral package -/

/--
Neutral continuation alternative exposing both the exact intrinsic residual law
and the exhaustive three-branch terminal structure.
-/
theorem smoothContinuationExtension_or_fixed_nativeComplementGradient_threeBranchAlternative_withResidualLaw
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
          H3TerminalNativeCurlGradientResidualLaw
            u p
            ∧
          (
            (
              H3TerminalComplementForcedRegime
                p sCurl sGradient
                ∧
              H3TerminalNativeComplementGradientForcedCascade
                u a T p sCurl sGradient
            )
              ∨
            (
              ∃ sComplement : H3TerminalOrientation,
                H3TerminalNativeCurlGradientComplementTripleEscape
                  u a T p sCurl sGradient sComplement
            )
              ∨
            H3TerminalNativeComplementBoundedRatioMatching
              u a T p sCurl sGradient
          )
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl hExtension

  · exact
      Or.inr
        (
          fixed_nativeComplementGradient_threeBranchAlternative_withResidualLaw_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
