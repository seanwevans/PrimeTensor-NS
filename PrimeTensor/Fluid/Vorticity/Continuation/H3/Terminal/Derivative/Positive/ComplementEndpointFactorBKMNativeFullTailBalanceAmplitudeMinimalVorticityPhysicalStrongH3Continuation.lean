import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalStrongH3Endpoint
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualStrongH3EndpointContradiction

/-!
# Physical strong H³ endpoint continuation criterion

The previous physical reduction showed that, on one selected terminal
sequence, strong spectral H³ endpoint control for the two constituent
first-derivative fields forming one actual vorticity component supplies all of
the physical endpoint regularity needed to eliminate both spatial branches.

This file removes the selected sequence from that formulation.

For a fixed physical vorticity component, require the two constituent strong
H³ endpoints on every strict selected terminal sequence.  Requiring this for
all three physical components is exactly enough to cover all six structural
curl-gradient pairs:

    ωₓ : x_zy and x_yz
    ωᵧ : y_xz and y_zx
    ω_z : z_yx and z_xy.

Hence the three-component physical criterion implies the existing all-six-pair
strong-H³ endpoint criterion, and therefore smooth continuation.

The contrapositive isolates a neutral remaining frontier: hypothetical
nonextension forces at least one physical vorticity component to fail
sequence-uniform strong H³ endpoint control.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Sequence-uniform physical strong H³ endpoint control -/

/--
For one fixed actual-vorticity component, every strict selected time sequence
converging to `T` has strong H³ endpoint control for both constituent velocity
components whose first derivatives form that vorticity component.
-/
def H3TerminalActualVorticityStrongH3EndpointOnAllSelectedTerminalSequences
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (i : Fin 3) : Prop :=
  ∀
    (τ : ℕ → ℝ)
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T),
    Tendsto τ atTop (𝓝 T) →
      H3TerminalActualVorticitySelectedStrongH3Endpoint
        hH3 hTauStrict i

/-! ## Three physical components cover all six structural pairs -/

/--
Sequence-uniform strong H³ endpoint control for all three physical vorticity
components implies the pairwise sequence-uniform criterion for every one of
the six structural curl-gradient pairs.
-/
theorem allPairs_strongH3Endpoint_of_allActualVorticityComponents_strongH3Endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hAllPhysical :
      ∀ i : Fin 3,
        H3TerminalActualVorticityStrongH3EndpointOnAllSelectedTerminalSequences
          hH3 i) :
    ∀ p : H3TerminalCurlGradientPair,
      H3TerminalComplementGradientStrongH3EndpointOnAllSelectedTerminalSequences
        hH3 p := by

  intro p τ hTauStrict hTau

  cases p with

  | x_yz =>
      have hPhysical :=
        hAllPhysical
          (0 : Fin 3)
          τ
          hTauStrict
          hTau

      simpa [
        H3TerminalActualVorticitySelectedStrongH3Endpoint,
        h3TerminalActualVorticityPositiveComplementPair,
        h3TerminalActualVorticityNegativeComplementPair
      ] using
        hPhysical.2

  | x_zy =>
      have hPhysical :=
        hAllPhysical
          (0 : Fin 3)
          τ
          hTauStrict
          hTau

      simpa [
        H3TerminalActualVorticitySelectedStrongH3Endpoint,
        h3TerminalActualVorticityPositiveComplementPair,
        h3TerminalActualVorticityNegativeComplementPair
      ] using
        hPhysical.1

  | y_zx =>
      have hPhysical :=
        hAllPhysical
          (1 : Fin 3)
          τ
          hTauStrict
          hTau

      simpa [
        H3TerminalActualVorticitySelectedStrongH3Endpoint,
        h3TerminalActualVorticityPositiveComplementPair,
        h3TerminalActualVorticityNegativeComplementPair
      ] using
        hPhysical.2

  | y_xz =>
      have hPhysical :=
        hAllPhysical
          (1 : Fin 3)
          τ
          hTauStrict
          hTau

      simpa [
        H3TerminalActualVorticitySelectedStrongH3Endpoint,
        h3TerminalActualVorticityPositiveComplementPair,
        h3TerminalActualVorticityNegativeComplementPair
      ] using
        hPhysical.1

  | z_xy =>
      have hPhysical :=
        hAllPhysical
          (2 : Fin 3)
          τ
          hTauStrict
          hTau

      simpa [
        H3TerminalActualVorticitySelectedStrongH3Endpoint,
        h3TerminalActualVorticityPositiveComplementPair,
        h3TerminalActualVorticityNegativeComplementPair
      ] using
        hPhysical.2

  | z_yx =>
      have hPhysical :=
        hAllPhysical
          (2 : Fin 3)
          τ
          hTauStrict
          hTau

      simpa [
        H3TerminalActualVorticitySelectedStrongH3Endpoint,
        h3TerminalActualVorticityPositiveComplementPair,
        h3TerminalActualVorticityNegativeComplementPair
      ] using
        hPhysical.1

/-! ## Physical strong H³ continuation criterion -/

/--
If all three actual-vorticity components have sequence-uniform strong H³
endpoint control for their two constituent velocity components, then the H³
path has a smooth continuation extension.
-/
theorem smoothContinuationExtension_of_allActualVorticityComponents_strongH3Endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hAllPhysical :
      ∀ i : Fin 3,
        H3TerminalActualVorticityStrongH3EndpointOnAllSelectedTerminalSequences
          hH3 i) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension
        u v T := by

  exact
    smoothContinuationExtension_of_allPairs_strongH3Endpoint
      hH3
      hClass
      (
        allPairs_strongH3Endpoint_of_allActualVorticityComponents_strongH3Endpoint
          hH3
          hAllPhysical
      )

/-! ## Neutral failure formulation -/

/--
Hypothetical nonextension forces failure of sequence-uniform strong H³ endpoint
control for at least one physical vorticity component.

This does not identify which component or which constituent endpoint fails; it
only isolates the necessary physical strong-H³ obstruction.
-/
theorem exists_actualVorticityComponent_strongH3EndpointFailure_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬
        ∃
          v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension
            u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T) :
    ∃ i : Fin 3,
      ¬
        H3TerminalActualVorticityStrongH3EndpointOnAllSelectedTerminalSequences
          hH3 i := by

  by_contra hNoFailure

  have hAllPhysical :
      ∀ i : Fin 3,
        H3TerminalActualVorticityStrongH3EndpointOnAllSelectedTerminalSequences
          hH3 i := by

    intro i

    by_contra hi

    exact
      hNoFailure
        ⟨
          i,
          hi
        ⟩

  exact
    hNoExtension
      (
        smoothContinuationExtension_of_allActualVorticityComponents_strongH3Endpoint
          hH3
          hClass
          hAllPhysical
      )

/--
Neutral alternative: either the H³ path continues smoothly, or at least one
physical vorticity component fails sequence-uniform strong H³ endpoint control.
-/
theorem smoothContinuationExtension_or_actualVorticityComponent_strongH3EndpointFailure
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension
          u v T
    )
      ∨
    (
      ∃ i : Fin 3,
        ¬
          H3TerminalActualVorticityStrongH3EndpointOnAllSelectedTerminalSequences
            hH3 i
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension
          u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (
          exists_actualVorticityComponent_strongH3EndpointFailure_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
