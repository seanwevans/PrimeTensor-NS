import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSelectedClosurePeak

/-!
# Compact global peak locus of the selected-closure terminal trace

The selected-closure trace now has a strictly positive global peak magnitude.
The particular maximizer chosen in the previous file is not canonical and
need not be unique.

This file removes that choice from the geometry.

The global peak locus is defined intrinsically as the set of all closure
points whose trace magnitude dominates the trace magnitude at every other
closure point.  Once existence of a positive global peak is known, this locus
is exactly the level set at the intrinsic peak magnitude.

Consequently:

* the peak locus is nonempty;
* the peak locus is closed;
* under closure-level decay at infinity, the peak locus is compact;
* every peak point is approached by actual selected points whose terminal
  complementary-gradient values converge to the peak trace value.

Thus the terminal concentration geometry is represented by a compact
choice-free argmax set rather than by one arbitrarily chosen maximizer.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualSelectedClosurePeakLocus
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Intrinsic peak locus -/

/--
The intrinsic global argmax locus of the magnitude of the canonical
selected-closure terminal trace.
-/
def H3TerminalComplementGradientSelectedClosurePeakLocus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T) :
    Set (H3TerminalSelectedSpatialClosure x) :=
  {
    y |
      ∀ z : H3TerminalSelectedSpatialClosure x,
        dist
            (
              h3TerminalComplementGradientSelectedClosureTraceValue
                hModulus
                z
            )
            0
          ≤
        dist
          (
            h3TerminalComplementGradientSelectedClosureTraceValue
              hModulus
              y
          )
          0
  }

/--
A point belongs to the intrinsic peak locus exactly when its trace magnitude
equals the intrinsic peak magnitude.
-/
theorem mem_selectedClosurePeakLocus_iff_eq_peakMagnitude
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hPeak :
      H3TerminalComplementGradientHasPositiveSelectedClosureGlobalPeak
        hModulus)
    (y : H3TerminalSelectedSpatialClosure x) :
    y ∈
        H3TerminalComplementGradientSelectedClosurePeakLocus
          hModulus
      ↔
    dist
        (
          h3TerminalComplementGradientSelectedClosureTraceValue
            hModulus
            y
        )
        0
      =
    h3TerminalComplementGradientSelectedClosurePeakMagnitude
      hModulus
      hPeak := by

  constructor

  · intro hy

    have hUpper :
        dist
            (
              h3TerminalComplementGradientSelectedClosureTraceValue
                hModulus
                y
            )
            0
          ≤
        h3TerminalComplementGradientSelectedClosurePeakMagnitude
          hModulus
          hPeak :=
      selectedClosureTraceValue_le_peakMagnitude
        hModulus
        hPeak
        y

    have hLower :
        h3TerminalComplementGradientSelectedClosurePeakMagnitude
            hModulus
            hPeak
          ≤
        dist
          (
            h3TerminalComplementGradientSelectedClosureTraceValue
              hModulus
              y
          )
          0 := by

      unfold
        h3TerminalComplementGradientSelectedClosurePeakMagnitude

      exact
        hy
          (Classical.choose hPeak)

    exact
      le_antisymm
        hUpper
        hLower

  · intro hy z

    have hz :
        dist
            (
              h3TerminalComplementGradientSelectedClosureTraceValue
                hModulus
                z
            )
            0
          ≤
        h3TerminalComplementGradientSelectedClosurePeakMagnitude
          hModulus
          hPeak :=
      selectedClosureTraceValue_le_peakMagnitude
        hModulus
        hPeak
        z

    simpa only [hy] using
      hz

/-! ## Nonemptiness and closedness -/

/--
The intrinsic global peak locus is nonempty whenever a positive global peak
exists.
-/
theorem selectedClosurePeakLocus_nonempty
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hPeak :
      H3TerminalComplementGradientHasPositiveSelectedClosureGlobalPeak
        hModulus) :
    (
      H3TerminalComplementGradientSelectedClosurePeakLocus
        hModulus
    ).Nonempty := by

  refine
    ⟨
      Classical.choose hPeak,
      ?_
    ⟩

  exact
    (Classical.choose_spec hPeak).2

/--
The intrinsic global peak locus is closed.
-/
theorem selectedClosurePeakLocus_isClosed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hPeak :
      H3TerminalComplementGradientHasPositiveSelectedClosureGlobalPeak
        hModulus) :
    IsClosed
      (
        H3TerminalComplementGradientSelectedClosurePeakLocus
          hModulus
      ) := by

  let f :
      H3TerminalSelectedSpatialClosure x → ℝ :=
    fun y =>
      dist
        (
          h3TerminalComplementGradientSelectedClosureTraceValue
            hModulus
            y
        )
        0

  let M : ℝ :=
    h3TerminalComplementGradientSelectedClosurePeakMagnitude
      hModulus
      hPeak

  have hContinuousTrace :
      Continuous
        (
          h3TerminalComplementGradientSelectedClosureTraceValue
            hModulus
        ) :=
    selectedClosureTraceValue_continuous
      hModulus

  have hContinuousF :
      Continuous f := by

    dsimp only [f]

    exact
      hContinuousTrace.dist
        continuous_const

  have hSetEq :
      H3TerminalComplementGradientSelectedClosurePeakLocus
          hModulus
        =
      {
        y : H3TerminalSelectedSpatialClosure x |
          f y = M
      } := by

    ext y

    exact
      mem_selectedClosurePeakLocus_iff_eq_peakMagnitude
        hModulus
        hPeak
        y

  rw [hSetEq]

  exact
    isClosed_eq
      hContinuousF
      continuous_const

/-! ## Compactness of the peak locus -/

/--
Under closure-level decay at infinity, the intrinsic global peak locus is
compact.
-/
theorem selectedClosurePeakLocus_isCompact_of_vanishesAtInfinity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hPeak :
      H3TerminalComplementGradientHasPositiveSelectedClosureGlobalPeak
        hModulus)
    (hVanish :
      H3TerminalComplementGradientSelectedClosureTraceVanishesAtInfinity
        hModulus) :
    IsCompact
      (
        H3TerminalComplementGradientSelectedClosurePeakLocus
          hModulus
      ) := by

  let M : ℝ :=
    h3TerminalComplementGradientSelectedClosurePeakMagnitude
      hModulus
      hPeak

  have hMPos :
      0 < M := by

    dsimp only [M]

    exact
      selectedClosurePeakMagnitude_pos
        hModulus
        hPeak

  have hHalfPos :
      0 < M / 2 := by
    linarith

  have hCompactSuperlevel :
      IsCompact
        (
          H3TerminalComplementGradientSelectedClosureSuperlevel
            hModulus
            (M / 2)
        ) :=
    selectedClosureSuperlevel_isCompact_of_vanishesAtInfinity
      hModulus
      hVanish
      hHalfPos

  have hClosedPeak :
      IsClosed
        (
          H3TerminalComplementGradientSelectedClosurePeakLocus
            hModulus
        ) :=
    selectedClosurePeakLocus_isClosed
      hModulus
      hPeak

  have hSubset :
      H3TerminalComplementGradientSelectedClosurePeakLocus
          hModulus
        ⊆
      H3TerminalComplementGradientSelectedClosureSuperlevel
        hModulus
        (M / 2) := by

    intro y hy

    have hEq :
        dist
            (
              h3TerminalComplementGradientSelectedClosureTraceValue
                hModulus
                y
            )
            0
          =
        M := by

      dsimp only [M]

      exact
        (
          mem_selectedClosurePeakLocus_iff_eq_peakMagnitude
            hModulus
            hPeak
            y
        ).1
          hy

    change
      M / 2
        ≤
      dist
        (
          h3TerminalComplementGradientSelectedClosureTraceValue
            hModulus
            y
        )
        0

    rw [hEq]

    linarith

  exact
    hCompactSuperlevel.of_isClosed_subset
      hClosedPeak
      hSubset

/--
The intrinsic peak locus is nonempty and compact.
-/
def H3TerminalComplementGradientHasNonemptyCompactSelectedClosurePeakLocus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T) : Prop :=
  (
    H3TerminalComplementGradientSelectedClosurePeakLocus
      hModulus
  ).Nonempty
    ∧
  IsCompact
    (
      H3TerminalComplementGradientSelectedClosurePeakLocus
        hModulus
    )

/--
A positive global peak together with closure-level decay yields a nonempty
compact intrinsic peak locus.
-/
theorem nonemptyCompactSelectedClosurePeakLocus_of_peak_of_vanishesAtInfinity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hPeak :
      H3TerminalComplementGradientHasPositiveSelectedClosureGlobalPeak
        hModulus)
    (hVanish :
      H3TerminalComplementGradientSelectedClosureTraceVanishesAtInfinity
        hModulus) :
    H3TerminalComplementGradientHasNonemptyCompactSelectedClosurePeakLocus
      hModulus :=
  ⟨
    selectedClosurePeakLocus_nonempty
      hModulus
      hPeak,
    selectedClosurePeakLocus_isCompact_of_vanishesAtInfinity
      hModulus
      hPeak
      hVanish
  ⟩

/-! ## Every peak point is selected-approachable -/

/--
Every point of the intrinsic peak locus is approached by actual selected
spatial points, and the actual terminal complementary-gradient values along
that approach converge to the peak trace value.
-/
theorem selectedClosurePeakPoint_has_selected_terminal_approach
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hPeak :
      H3TerminalComplementGradientHasPositiveSelectedClosureGlobalPeak
        hModulus)
    (y : H3TerminalSelectedSpatialClosure x)
    (hy :
      y ∈
        H3TerminalComplementGradientSelectedClosurePeakLocus
          hModulus) :
    ∃ k : ℕ → ℕ,
      Tendsto
          (fun j : ℕ => x (k j))
          atTop
          (𝓝 y.1)
        ∧
      Tendsto
        (
          fun j : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x (k j))
        )
        atTop
        (
          𝓝
            (
              h3TerminalComplementGradientSelectedClosureTraceValue
                hModulus
                y
            )
        )
        ∧
      dist
          (
            h3TerminalComplementGradientSelectedClosureTraceValue
              hModulus
              y
          )
          0
        =
      h3TerminalComplementGradientSelectedClosurePeakMagnitude
        hModulus
        hPeak := by

  obtain
    ⟨
      k,
      hPoint,
      hTrace
    ⟩ :=
    selectedClosureTraceValue_spec
      hModulus
      y

  refine
    ⟨
      k,
      hPoint,
      hTrace,
      ?_
    ⟩

  exact
    (
      mem_selectedClosurePeakLocus_iff_eq_peakMagnitude
        hModulus
        hPeak
        y
    ).1
      hy

/-! ## Escape-side package with compact argmax locus -/

/--
The escape-side obstruction contains

* a native pivot cluster at spatial infinity;
* a nonempty compact positive closure core;
* a strictly positive global terminal trace peak;
* a nonempty compact intrinsic argmax locus;
* closure-level vanishing at infinity;
* quantitative finite-core versus infinity contrast.
-/
def H3TerminalNativeComplementHasPivotInfinityAndCompactPeakLocus
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
  H3TerminalComplementGradientHasNonemptyCompactSelectedClosureCore
      hModulus
    ∧
  H3TerminalComplementGradientHasPositiveSelectedClosureGlobalPeak
      hModulus
    ∧
  H3TerminalComplementGradientHasNonemptyCompactSelectedClosurePeakLocus
      hModulus
    ∧
  H3TerminalComplementGradientSelectedClosureTraceVanishesAtInfinity
      hModulus
    ∧
  H3TerminalComplementGradientHasFiniteCoreInfinityContrast
      u p x T

/--
Under endpoint temporal control, selected spatial equicontinuity, terminal
decay at infinity, and eventual boundedness of the residual logarithm, failure
of the canonical native factor forces either

* pivot behavior at infinity together with a compact nonzero terminal core and
  a nonempty compact intrinsic global peak locus; or
* bounded selected range with positive terminal spatial contrast and positive
  witness separation.
-/
theorem nativeComplement_noCanonicalFactor_forces_pivotInfinityAndCompactPeakLocus_or_boundedTerminalContrast
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
    H3TerminalNativeComplementHasPivotInfinityAndCompactPeakLocus
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
    nativeComplement_noCanonicalFactor_forces_pivotInfinityAndGlobalClosurePeak_or_boundedTerminalContrast
      hTau
      hEndpoint
      hSpatialEquicontinuity
      hDecay
      hResidualBounded
      hNoFactor
    with
    hEscapeSide | hContrast

  · left

    have hPeakLocus :
        H3TerminalComplementGradientHasNonemptyCompactSelectedClosurePeakLocus
          hTerminalModulus :=
      nonemptyCompactSelectedClosurePeakLocus_of_peak_of_vanishesAtInfinity
        hTerminalModulus
        hEscapeSide.2.2.1
        hEscapeSide.2.2.2.1

    exact
      ⟨
        hEscapeSide.1,
        hEscapeSide.2.1,
        hEscapeSide.2.2.1,
        hPeakLocus,
        hEscapeSide.2.2.2.1,
        hEscapeSide.2.2.2.2
      ⟩

  · exact
      Or.inr
        hContrast

end

end Euclidean
end Bridge
end PrimeTensor
