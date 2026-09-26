import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSelectedClosureTrace
import Mathlib.Topology.Sequences

/-!
# Canonical terminal trace function on the selected spatial closure

The preceding development constructed a total, single-valued terminal trace
relation at every sequential cluster point of the selected spatial set.

Because `Point3` is metrizable and hence Fréchet--Urysohn, sequential closure
coincides with ordinary topological closure.  This file therefore replaces the
custom cluster predicate by the standard closed set

    closure (Set.range x)

and packages the unique terminal trace as an actual real-valued function on
that closure.

The resulting canonical trace function has three basic properties:

* it is defined at every point of the ordinary selected spatial closure;
* its graph is exactly the previously defined selected-closure trace relation;
* at every actually selected point `x n`, it agrees with the actual terminal
  complementary-gradient value `F(T, x n)`.

Thus the terminal field on the selected set has been extended canonically to
its closure, without assuming ambient continuity of the original field there.

The previously isolated nonzero finite core becomes a point of this ordinary
closure at which the canonical trace function is nonzero.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualSelectedClosureFunction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Sequential cluster points equal ordinary closure points -/

/--
For the selected spatial sequence in `Point3`, the custom sequential cluster
predicate is exactly membership in the ordinary topological closure of its
range.
-/
theorem selectedSpatialClusterPoint_iff_mem_closure_range
    (x : ℕ → Point3)
    (y : Point3) :
    H3TerminalSelectedSpatialClusterPoint x y
      ↔
    y ∈ closure (Set.range x) := by

  constructor

  · rintro
      ⟨
        k,
        hPoint
      ⟩

    exact
      isClosed_closure.mem_of_tendsto
        hPoint
        (
          Filter.Eventually.of_forall
            (
              fun j =>
                subset_closure
                  ⟨
                    k j,
                    rfl
                  ⟩
            )
        )

  · intro hy

    obtain
      ⟨
        z,
        hzRange,
        hzTendsto
      ⟩ :=
      (
        mem_closure_iff_seq_limit
      ).1
        hy

    choose k hk using
      hzRange

    refine
      ⟨
        k,
        ?_
      ⟩

    simpa only [hk] using
      hzTendsto

/-! ## The ordinary selected spatial closure -/

/--
The ordinary topological closure of the selected spatial points.
-/
abbrev H3TerminalSelectedSpatialClosure
    (x : ℕ → Point3) :=
  ↥(closure (Set.range x))

/--
Every actually selected point defines a canonical point of the selected
spatial closure.
-/
def h3TerminalSelectedSpatialClosurePoint
    (x : ℕ → Point3)
    (n : ℕ) :
    H3TerminalSelectedSpatialClosure x :=
  ⟨
    x n,
    subset_closure
      ⟨
        n,
        rfl
      ⟩
  ⟩

/-! ## Canonical closure trace value -/

/--
The unique terminal complementary-gradient trace at a point of the selected
spatial closure.
-/
noncomputable def h3TerminalComplementGradientSelectedClosureTraceValue
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (y : H3TerminalSelectedSpatialClosure x) : ℝ :=
  Classical.choose
    (
      exists_selectedClosureTrace_of_clusterPoint_of_terminalSpatialModulus
        hModulus
        (
          (
            selectedSpatialClusterPoint_iff_mem_closure_range
              x
              y.1
          ).2
            y.2
        )
    )

/--
The canonical closure trace value satisfies the selected-closure trace
relation at its closure point.
-/
theorem selectedClosureTraceValue_spec
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (y : H3TerminalSelectedSpatialClosure x) :
    H3TerminalComplementGradientSelectedClosureTraceAt
      u p x T y.1
      (
        h3TerminalComplementGradientSelectedClosureTraceValue
          hModulus
          y
      ) := by

  unfold
    h3TerminalComplementGradientSelectedClosureTraceValue

  exact
    Classical.choose_spec
      (
        exists_selectedClosureTrace_of_clusterPoint_of_terminalSpatialModulus
          hModulus
          (
            (
              selectedSpatialClusterPoint_iff_mem_closure_range
                x
                y.1
            ).2
              y.2
          )
      )

/--
The trace relation is exactly equality with the canonical closure trace
function.
-/
theorem selectedClosureTraceAt_iff_eq_traceValue
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (y : H3TerminalSelectedSpatialClosure x)
    (L : ℝ) :
    H3TerminalComplementGradientSelectedClosureTraceAt
        u p x T y.1 L
      ↔
    L
      =
    h3TerminalComplementGradientSelectedClosureTraceValue
      hModulus
      y := by

  constructor

  · intro hTrace

    exact
      selectedClosureTrace_unique_of_terminalSpatialModulus
        hModulus
        hTrace
        (
          selectedClosureTraceValue_spec
            hModulus
            y
        )

  · intro hEq

    rw [hEq]

    exact
      selectedClosureTraceValue_spec
        hModulus
        y

/-! ## The closure trace extends the selected terminal field -/

/--
At every actually selected point, the canonical closure trace equals the
actual terminal complementary-gradient value.
-/
theorem selectedClosureTraceValue_selectedPoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (n : ℕ) :
    h3TerminalComplementGradientSelectedClosureTraceValue
        hModulus
        (h3TerminalSelectedSpatialClosurePoint x n)
      =
    h3TerminalComplementGradientFieldForPair
      u p T (x n) := by

  have hDirect :
      H3TerminalComplementGradientSelectedClosureTraceAt
        u p x T
        (x n)
        (
          h3TerminalComplementGradientFieldForPair
            u p T (x n)
        ) := by

    refine
      ⟨
        fun _ : ℕ => n,
        ?_,
        ?_
      ⟩

    · exact
        tendsto_const_nhds

    · exact
        tendsto_const_nhds

  have hCanonical :
      H3TerminalComplementGradientSelectedClosureTraceAt
        u p x T
        (x n)
        (
          h3TerminalComplementGradientSelectedClosureTraceValue
            hModulus
            (h3TerminalSelectedSpatialClosurePoint x n)
        ) := by

    simpa only [
      h3TerminalSelectedSpatialClosurePoint
    ] using
      selectedClosureTraceValue_spec
        hModulus
        (h3TerminalSelectedSpatialClosurePoint x n)

  exact
    selectedClosureTrace_unique_of_terminalSpatialModulus
      hModulus
      hCanonical
      hDirect

/-! ## The nonzero core as a point of the canonical closure trace function -/

/--
A nonzero intrinsic selected-closure trace yields an ordinary closure point at
which the canonical trace function is nonzero.
-/
theorem exists_selectedClosurePoint_traceValue_ne_zero_of_nonzeroIntrinsicTrace
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hNonzero :
      H3TerminalComplementGradientHasNonzeroIntrinsicSelectedClosureTrace
        u p x T) :
    ∃ y : H3TerminalSelectedSpatialClosure x,
      h3TerminalComplementGradientSelectedClosureTraceValue
          hModulus
          y
        ≠
      0 := by

  obtain
    ⟨
      y,
      L,
      hLNe,
      hTrace,
      _hUnique
    ⟩ :=
    hNonzero

  obtain
    ⟨
      k,
      hPoint,
      hValue
    ⟩ :=
    hTrace

  have hyCluster :
      H3TerminalSelectedSpatialClusterPoint
        x y :=
    ⟨
      k,
      hPoint
    ⟩

  have hyClosure :
      y ∈ closure (Set.range x) :=
    (
      selectedSpatialClusterPoint_iff_mem_closure_range
        x y
    ).1
      hyCluster

  let Y : H3TerminalSelectedSpatialClosure x :=
    ⟨
      y,
      hyClosure
    ⟩

  refine
    ⟨
      Y,
      ?_
    ⟩

  have hEq :
      L
        =
      h3TerminalComplementGradientSelectedClosureTraceValue
        hModulus
        Y :=
    (
      selectedClosureTraceAt_iff_eq_traceValue
        hModulus
        Y
        L
    ).1
      (
        by
          simpa only [Y] using
            (
              show
                H3TerminalComplementGradientSelectedClosureTraceAt
                  u p x T y L
                from
                  ⟨
                    k,
                    hPoint,
                    hValue
                  ⟩
            )
      )

  intro hZero

  apply hLNe

  rw [
    hEq,
    hZero
  ]

/-! ## Closure-function escape-side package -/

/--
The escape-side obstruction, now expressed using the canonical trace function
on the ordinary selected spatial closure.
-/
def H3TerminalNativeComplementHasPivotInfinityAndNonzeroClosureTraceValue
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (T : ℝ)
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T) : Prop :=
  H3TerminalNativeComplementHasCofinalPivotClusterAtSpatialInfinity
      u p τ x T
    ∧
  (
    ∃ y : H3TerminalSelectedSpatialClosure x,
      h3TerminalComplementGradientSelectedClosureTraceValue
          hModulus
          y
        ≠
      0
  )
    ∧
  H3TerminalComplementGradientHasFiniteCoreInfinityContrast
      u p x T

/--
Under endpoint temporal control, selected spatial equicontinuity, terminal
decay at infinity, and eventual boundedness of the residual logarithm, failure
of the canonical factor forces either

* pivot behavior at infinity together with a nonzero value of the canonical
  trace function on the ordinary selected spatial closure and quantitative
  finite-core contrast; or
* bounded selected range with positive terminal spatial contrast and positive
  witness separation.
-/
theorem nativeComplement_noCanonicalFactor_forces_pivotInfinityAndNonzeroClosureTraceValue_or_boundedTerminalContrast
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hEndpoint :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u p τ x T)
    (hSpatialEquicontinuity :
      H3TerminalComplementGradientSelectedSpatialEquicontinuity
        u p τ x)
    (hDecay :
      H3TerminalComplementGradientSelectedTerminalDecayAtInfinity
        u p x T)
    (hResidualBounded :
      H3TerminalNativeComplementResidualLogEventuallyBounded
        u p τ x)
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x) :
    let hTerminalModulus :
        H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
          u p x T :=
      selectedTerminalSpatialUniformModulus_of_spatialEquicontinuity_of_endpointTemporalModulus
        hTau
        hSpatialEquicontinuity
        hEndpoint
    H3TerminalNativeComplementHasPivotInfinityAndNonzeroClosureTraceValue
        u p τ x T hTerminalModulus
      ∨
    (
      Bornology.IsBounded (Set.range x)
        ∧
      H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrastSeparation
        u p x T
    ) := by

  dsimp only

  let hTerminalModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T :=
    selectedTerminalSpatialUniformModulus_of_spatialEquicontinuity_of_endpointTemporalModulus
      hTau
      hSpatialEquicontinuity
      hEndpoint

  rcases
    nativeComplement_noCanonicalFactor_forces_pivotInfinityAndNonzeroClosureTrace_or_boundedTerminalContrast
      hTau
      hEndpoint
      hSpatialEquicontinuity
      hDecay
      hResidualBounded
      hNoFactor
    with
    hEscapeSide | hContrast

  · left

    have hNonzeroValue :
        ∃ y : H3TerminalSelectedSpatialClosure x,
          h3TerminalComplementGradientSelectedClosureTraceValue
              hTerminalModulus
              y
            ≠
          0 :=
      exists_selectedClosurePoint_traceValue_ne_zero_of_nonzeroIntrinsicTrace
        hTerminalModulus
        hEscapeSide.2.1

    exact
      ⟨
        hEscapeSide.1,
        hNonzeroValue,
        hEscapeSide.2.2
      ⟩

  · exact
      Or.inr
        hContrast

end

end Euclidean
end Bridge
end PrimeTensor
