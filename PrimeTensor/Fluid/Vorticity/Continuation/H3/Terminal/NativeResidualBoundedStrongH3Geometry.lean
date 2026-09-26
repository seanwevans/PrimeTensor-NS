import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSpatialH3Criterion
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualBoundedExclusiveFactorDichotomy

/-!
# Thread strong H³ endpoint control through the bounded cancellation branch

The bounded cancellation package already fixes one terminal spacetime sequence
and retains all of the structural data on that same sequence:

* cancellation orientation;
* curl and gradient directional escape;
* eventual complementary-log boundedness;
* ratio-one matching;
* residual negligibility relative to both dominant scales;
* canonical factor or two distinct finite cluster factors.

The strong-H³ endpoint development now removes the three geometric analytic
frontiers on any such selected terminal sequence:

* endpoint temporal modulus;
* selected spatial equicontinuity;
* terminal spatial decay.

This file threads that reduction through the original bounded branch without
discarding any of its structural witnesses.

The only new hypothesis is stated explicitly: for the fixed terminal pair,
every strict selected sequence converging to `T` has the strong H³ endpoint
property.  Under that condition the two-cluster side of the bounded factor
dichotomy becomes the intrinsic terminal geometry alternative:

    pivot at spatial infinity + compact peak locus

or

    bounded selected spatial range + positive terminal contrast.

The result remains neutral.  Neither geometric branch is declared impossible,
and no global regularity or blowup conclusion is inferred.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Sequence-uniform strong H³ endpoint criterion -/

/--
For one fixed terminal derivative pair, every strict selected time sequence
converging to `T` has a strong spectral H³ endpoint.

This is the remaining analytic endpoint condition after the temporal,
spatial-equicontinuity, and spatial-decay reductions.
-/
def H3TerminalComplementGradientStrongH3EndpointOnAllSelectedTerminalSequences
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (p : H3TerminalCurlGradientPair) : Prop :=
  ∀
    (τ : ℕ → ℝ)
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T),
    Tendsto τ atTop (𝓝 T) →
      H3TerminalComplementGradientSelectedStrongH3Endpoint
        hH3 hTauStrict p

/-! ## Geometry package on one fixed bounded-branch sequence -/

/--
The noncanonical bounded branch geometry on one fixed selected sequence,
including explicit witnesses of the strict-time, terminal convergence, and
strong-H³ endpoint data used to construct the intrinsic terminal modulus.
-/
def H3TerminalNativeComplementStrongH3GeometryAlternativeOnTerminalSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  ∃
    hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T,
    ∃
      hTau :
        Tendsto τ atTop (𝓝 T),
      ∃
        hStrong :
          H3TerminalComplementGradientSelectedStrongH3Endpoint
            hH3 hTauStrict p,
        let hEndpoint :
            H3TerminalComplementGradientSelectedEndpointTemporalModulus
              u p τ x T :=
          selectedEndpointTemporalModulus_of_strongH3Endpoint
            hH3 hTauStrict hStrong
        let hSpatialEquicontinuity :
            H3TerminalComplementGradientSelectedSpatialEquicontinuity
              u p τ x :=
          selectedSpatialEquicontinuity_of_strongH3Endpoint
            hH3 hTauStrict hTau hStrong
        let hTerminalModulus :
            H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
              u p x T :=
          selectedTerminalSpatialUniformModulus_of_spatialEquicontinuity_of_endpointTemporalModulus
            hTau
            hSpatialEquicontinuity
            hEndpoint
        H3TerminalNativeComplementHasPivotInfinityAndCompactPeakLocus
            u p τ x T hTerminalModulus
          ∨
        (
          Bornology.IsBounded (Set.range x)
            ∧
          H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrastSeparation
            u p x T
        )

/-! ## Refined bounded cancellation package -/

/--
The original bounded cancellation package with its final topology refined to

* a full canonical native factor, or
* the strong-H³ intrinsic terminal geometry alternative,

on the same selected spacetime sequence.
-/
def H3TerminalNativeComplementBoundedStrongH3GeometryAlternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (a : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation) : Prop :=
  ∃
    τ : ℕ → ℝ,
    ∃ x : ℕ → Point3,
      ∃ N : ℕ,
        ∃ C : ℝ,
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
          H3TerminalComplementCancellationRegime
            p sCurl sGradient
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
          (
            ∀ n : ℕ,
              N ≤ n →
              (
                abs
                  (
                    PrimeTensor.Bridge.MulReal.logValue
                      (
                        h3TerminalNativeComplementGradientForPair
                          u p
                          (τ n)
                          (x n)
                      )
                  )
                  ≤ C
              )
                ∧
              (
                abs
                  (
                    PrimeTensor.Bridge.MulReal.logValue
                      (
                        h3TerminalNativeGradientForPair
                          u p
                          (τ n)
                          (x n)
                      )
                      -
                    h3TerminalSelectedSignedNativeCurlLog
                      u p
                      (τ n)
                      (x n)
                  )
                  ≤ C
              )
          )
            ∧
          Tendsto
            (
              fun n : ℕ =>
                (
                  h3TerminalOrientedValue
                    sGradient
                    (
                      PrimeTensor.Bridge.MulReal.logValue
                        (
                          h3TerminalNativeGradientForPair
                            u p
                            (τ n)
                            (x n)
                        )
                    )
                )
                  /
                (
                  h3TerminalOrientedValue
                    sGradient
                    (
                      h3TerminalSelectedSignedNativeCurlLog
                        u p
                        (τ n)
                        (x n)
                    )
                )
            )
            atTop
            (𝓝 1)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                abs
                  (
                    PrimeTensor.Bridge.MulReal.logValue
                      (
                        h3TerminalNativeComplementGradientForPair
                          u p
                          (τ n)
                          (x n)
                      )
                  )
                  /
                h3TerminalOrientedValue
                  sGradient
                  (
                    h3TerminalSelectedSignedNativeCurlLog
                      u p
                      (τ n)
                      (x n)
                  )
            )
            atTop
            (𝓝 0)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                abs
                  (
                    PrimeTensor.Bridge.MulReal.logValue
                      (
                        h3TerminalNativeComplementGradientForPair
                          u p
                          (τ n)
                          (x n)
                      )
                  )
                  /
                h3TerminalOrientedValue
                  sGradient
                  (
                    PrimeTensor.Bridge.MulReal.logValue
                      (
                        h3TerminalNativeGradientForPair
                          u p
                          (τ n)
                          (x n)
                      )
                  )
            )
            atTop
            (𝓝 0)
            ∧
          (
            H3TerminalNativeComplementHasCanonicalFactor
                u p τ x
              ∨
            H3TerminalNativeComplementStrongH3GeometryAlternativeOnTerminalSequence
              hH3 p τ x
          )

/-! ## Refine the old bounded branch on the same witnesses -/

/--
If every selected terminal sequence for the fixed pair has the strong H³
endpoint property, the original bounded-factor branch refines on its same
witnesses to canonical convergence or intrinsic terminal geometry.
-/
theorem nativeComplementBoundedStrongH3GeometryAlternative_of_boundedFactorAlternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hAllStrong :
      H3TerminalComplementGradientStrongH3EndpointOnAllSelectedTerminalSequences
        hH3 p)
    (hBounded :
      H3TerminalNativeComplementBoundedFactorAlternative
        u a T p sCurl sGradient) :
    H3TerminalNativeComplementBoundedStrongH3GeometryAlternative
      hH3 a p sCurl sGradient := by

  obtain
    ⟨
      τ,
      x,
      N,
      C,
      hτ,
      hTau,
      hCancellation,
      hCurlDirectional,
      hGradientDirectional,
      hBound,
      hRatio,
      hRelativeCurl,
      hRelativeGradient,
      hFactorAlternative
    ⟩ :=
    hBounded

  have hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T := by

    intro n

    have hTail :
        τ n ∈ Set.Ioo a T :=
      (hτ n).1

    exact
      ⟨
        lt_trans
          hClass.terminal_start.1
          hTail.1,
        hTail.2
      ⟩

  have hStrong :
      H3TerminalComplementGradientSelectedStrongH3Endpoint
        hH3 hTauStrict p :=
    hAllStrong
      τ
      hTauStrict
      hTau

  have hFinal :
      H3TerminalNativeComplementHasCanonicalFactor
          u p τ x
        ∨
      H3TerminalNativeComplementStrongH3GeometryAlternativeOnTerminalSequence
        hH3 p τ x := by

    rcases hFactorAlternative with hCanonical | hTwo

    · exact
        Or.inl hCanonical

    · have hNoCanonical :
          ¬
            H3TerminalNativeComplementHasCanonicalFactor
              u p τ x := by

        intro hCanonical

        exact
          (
            not_twoDistinctClusterFactors_of_nativeComplementHasCanonicalFactor
              hCanonical
          )
            hTwo

      have hGeometry :=
        nativeComplement_noCanonicalFactor_forces_pivotInfinityAndCompactPeakLocus_or_boundedTerminalContrast_of_strongH3Endpoint
          hH3
          hTauStrict
          hTau
          hStrong
          (fun n hn => (hBound n hn).1)
          hNoCanonical

      exact
        Or.inr
          ⟨
            hTauStrict,
            hTau,
            hStrong,
            hGeometry
          ⟩

  exact
    ⟨
      τ,
      x,
      N,
      C,
      hτ,
      hTau,
      hCancellation,
      hCurlDirectional,
      hGradientDirectional,
      hBound,
      hRatio,
      hRelativeCurl,
      hRelativeGradient,
      hFinal
    ⟩

/-! ## Thread the refinement into the fixed terminal three-branch theorem -/

/--
Under nonextension, if every terminal pair and every strict selected terminal
sequence has the strong H³ endpoint property, the bounded cancellation branch
is refined to canonical factor or intrinsic terminal geometry while the two
unbounded branches are retained unchanged.
-/
theorem fixed_nativeComplementGradient_threeBranchAlternative_withBoundedStrongH3Geometry_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hAllStrong :
      ∀ p : H3TerminalCurlGradientPair,
        H3TerminalComplementGradientStrongH3EndpointOnAllSelectedTerminalSequences
          hH3 p) :
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
          H3TerminalNativeComplementBoundedStrongH3GeometryAlternative
            hH3 a p sCurl sGradient
        ) := by

  obtain
    ⟨
      p,
      sCurl,
      sGradient,
      hResidualLaw,
      hAlternative
    ⟩ :=
    fixed_nativeComplementGradient_threeBranchAlternative_withBoundedFactorAlternative_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  rcases hAlternative with hForced | hRest

  · exact
      ⟨
        p,
        sCurl,
        sGradient,
        hResidualLaw,
        Or.inl hForced
      ⟩

  · rcases hRest with hTriple | hBounded

    · exact
        ⟨
          p,
          sCurl,
          sGradient,
          hResidualLaw,
          Or.inr
            (
              Or.inl hTriple
            )
        ⟩

    · exact
        ⟨
          p,
          sCurl,
          sGradient,
          hResidualLaw,
          Or.inr
            (
              Or.inr
                (
                  nativeComplementBoundedStrongH3GeometryAlternative_of_boundedFactorAlternative
                    hH3
                    hClass
                    (hAllStrong p)
                    hBounded
                )
            )
        ⟩

/-! ## Neutral global continuation package -/

/--
Neutral global continuation alternative with the bounded branch geometrically
resolved under the explicit strong-H³ endpoint criterion.

The theorem still permits:

1. smooth continuation;
2. reinforcing complementary escape;
3. cancellation-compatible synchronized triple escape;
4. bounded cancellation with either a canonical factor or intrinsic terminal
   spatial geometry.

No branch is ruled out.
-/
theorem smoothContinuationExtension_or_fixed_nativeComplementGradient_threeBranchAlternative_withBoundedStrongH3Geometry
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hAllStrong :
      ∀ p : H3TerminalCurlGradientPair,
        H3TerminalComplementGradientStrongH3EndpointOnAllSelectedTerminalSequences
          hH3 p) :
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
            H3TerminalNativeComplementBoundedStrongH3GeometryAlternative
              hH3 a p sCurl sGradient
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
          fixed_nativeComplementGradient_threeBranchAlternative_withBoundedStrongH3Geometry_of_noH3PathExtension
            hH3
            hExtension
            hClass
            hAllStrong
        )

end

end Euclidean
end Bridge
end PrimeTensor
