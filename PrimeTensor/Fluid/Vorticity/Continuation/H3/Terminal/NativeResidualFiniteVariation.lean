import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeConvergenceCauchyCriterion
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Finite variation criterion for the full terminal native residual factor

The previous file reduced existence of a full canonical native proportionality
factor on a fixed terminal spacetime sequence to a Cauchy property for the
residual logarithm.

This file identifies a concrete sufficient estimate for that Cauchy property.

Let

    R n =
      logValue
        (ratio
          selectedGradient_n
          selectedSignedCurl_n).

If the total consecutive variation

    sum_n dist (R n) (R (n+1))

is finite, then `R` is Cauchy.  More generally, it is enough to dominate each
consecutive distance by any summable nonnegative majorant.

The implication is a direct application of mathlib's
`cauchySeq_of_summable_dist` / `cauchySeq_of_dist_le_of_summable`.

Thus the remaining full-sequence problem can be sharpened from

    prove the bounded residual converges

to

    prove summable terminal variation of its logarithm
    (or find a summable majorant for that variation).

No such PDE estimate is assumed or manufactured here.  In particular,
boundedness, ratio-one dominant matching, and relative negligibility still do
not by themselves imply finite variation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Residual logarithmic sequence and its variation -/

/--
Canonical logarithmic coordinate of the exact complementary residual ratio on
a fixed terminal spacetime sequence.
-/
noncomputable def h3TerminalNativeComplementResidualLogSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (n : ℕ) : ℝ :=
  PrimeTensor.Bridge.MulReal.logValue
    (
      PrimeTensor.MulReal.ratio
        (
          h3TerminalNativeGradientForPair
            u p
            (τ n)
            (x n)
        )
        (
          h3TerminalSelectedSignedNativeCurlForPair
            u p
            (τ n)
            (x n)
        )
    )

/--
Consecutive logarithmic variation of the exact complementary residual.
-/
noncomputable def h3TerminalNativeComplementResidualLogIncrement
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (n : ℕ) : ℝ :=
  dist
    (
      h3TerminalNativeComplementResidualLogSequence
        u p τ x n
    )
    (
      h3TerminalNativeComplementResidualLogSequence
        u p τ x n.succ
    )

/--
The exact complementary residual has finite total logarithmic variation along
the fixed terminal spacetime sequence.
-/
def H3TerminalNativeComplementResidualFiniteVariation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  Summable
    (
      h3TerminalNativeComplementResidualLogIncrement
        u p τ x
    )

/-! ## Finite variation implies the exact Cauchy frontier -/

/--
Finite total residual-log variation forces the residual logarithmic sequence
to be Cauchy.
-/
theorem nativeComplementResidualLogCauchy_of_finiteVariation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (hVariation :
      H3TerminalNativeComplementResidualFiniteVariation
        u p τ x) :
    H3TerminalNativeComplementResidualLogCauchy
      u p τ x := by

  unfold
    H3TerminalNativeComplementResidualFiniteVariation
    h3TerminalNativeComplementResidualLogIncrement
    h3TerminalNativeComplementResidualLogSequence
    at hVariation

  simpa [
    H3TerminalNativeComplementResidualLogCauchy,
    h3TerminalNativeComplementResidualLogSequence
  ] using
    (cauchySeq_of_summable_dist hVariation)

/--
Consequently, finite total residual-log variation gives a unique full native
proportionality factor on the entire fixed terminal sequence.
-/
theorem nativeComplementHasCanonicalFactor_of_finiteVariation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (hVariation :
      H3TerminalNativeComplementResidualFiniteVariation
        u p τ x) :
    H3TerminalNativeComplementHasCanonicalFactor
      u p τ x := by

  apply
    (
      nativeComplementHasCanonicalFactor_iff_residualLogCauchy
        u p τ x
    ).2

  exact
    nativeComplementResidualLogCauchy_of_finiteVariation
      u p τ x
      hVariation

/-! ## A summable-majorant criterion -/

/--
A summable majorant for consecutive residual-log distances is sufficient for
the full canonical native factor.

This is the form most directly suited to a later PDE estimate: one does not
need to compute the total variation exactly, only dominate each consecutive
increment by a summable scalar sequence.
-/
theorem nativeComplementHasCanonicalFactor_of_summable_increment_majorant
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (d : ℕ → ℝ)
    (hd :
      Summable d)
    (hIncrement :
      ∀ n : ℕ,
        dist
          (
            h3TerminalNativeComplementResidualLogSequence
              u p τ x n
          )
          (
            h3TerminalNativeComplementResidualLogSequence
              u p τ x n.succ
          )
          ≤
        d n) :
    H3TerminalNativeComplementHasCanonicalFactor
      u p τ x := by

  have hCauchy :
      CauchySeq
        (
          h3TerminalNativeComplementResidualLogSequence
            u p τ x
        ) :=
    cauchySeq_of_dist_le_of_summable
      d
      hIncrement
      hd

  apply
    (
      nativeComplementHasCanonicalFactor_iff_residualLogCauchy
        u p τ x
    ).2

  unfold
    H3TerminalNativeComplementResidualLogCauchy

  change
    CauchySeq
      (
        h3TerminalNativeComplementResidualLogSequence
          u p τ x
      )

  exact hCauchy

/-! ## Equivalent formulation using the complementary native gradient -/

/--
The finite-variation condition can be read directly on the complementary
native gradient, since that quantity is pointwise the exact residual ratio.
-/
theorem nativeComplementResidualFiniteVariation_iff_complementLogFiniteVariation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) :
    H3TerminalNativeComplementResidualFiniteVariation
        u p τ x
      ↔
    Summable
      (
        fun n : ℕ =>
          dist
            (
              PrimeTensor.Bridge.MulReal.logValue
                (
                  h3TerminalNativeComplementGradientForPair
                    u p
                    (τ n)
                    (x n)
                )
            )
            (
              PrimeTensor.Bridge.MulReal.logValue
                (
                  h3TerminalNativeComplementGradientForPair
                    u p
                    (τ n.succ)
                    (x n.succ)
                )
            )
      ) := by

  unfold
    H3TerminalNativeComplementResidualFiniteVariation
    h3TerminalNativeComplementResidualLogIncrement
    h3TerminalNativeComplementResidualLogSequence

  simp only [
    ← h3TerminalNativeComplementGradientForPair_eq_residualRatio
  ]

/--
Direct complementary-gradient version of the finite-variation criterion.
-/
theorem nativeComplementHasCanonicalFactor_of_complementLogFiniteVariation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (hVariation :
      Summable
        (
          fun n : ℕ =>
            dist
              (
                PrimeTensor.Bridge.MulReal.logValue
                  (
                    h3TerminalNativeComplementGradientForPair
                      u p
                      (τ n)
                      (x n)
                  )
              )
              (
                PrimeTensor.Bridge.MulReal.logValue
                  (
                    h3TerminalNativeComplementGradientForPair
                      u p
                      (τ n.succ)
                      (x n.succ)
                  )
              )
        )) :
    H3TerminalNativeComplementHasCanonicalFactor
      u p τ x := by

  apply
    nativeComplementHasCanonicalFactor_of_finiteVariation
      u p τ x

  exact
    (
      nativeComplementResidualFiniteVariation_iff_complementLogFiniteVariation
        u p τ x
    ).2 hVariation

end

end Euclidean
end Bridge
end PrimeTensor
