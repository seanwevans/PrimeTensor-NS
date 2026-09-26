import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSelectedClosureTraceFunction

/-!
# Uniform continuity of the canonical selected-closure terminal trace

The canonical terminal trace function has been constructed on the ordinary
selected spatial closure

    closure (Set.range x).

This file proves that the trace function inherits a uniform spatial modulus
from the terminal selected spatial modulus on the dense selected set.

The proof approximates two arbitrary closure points by selected sequences,
uses the original selected-point modulus at one sufficiently late common
index, and passes the estimate through the two trace limits.

Consequently the canonical selected-closure trace function is uniformly
continuous, hence continuous.

A nonzero trace value therefore cannot be isolated: it generates a
positive-radius neighborhood inside the selected closure on which the trace
stays quantitatively away from zero.

This upgrades the finite-core obstruction from a single closure point to a
nonzero closure neighborhood.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualSelectedClosureTraceContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Uniform continuity of the closure trace -/

/--
The canonical selected-closure trace function is uniformly continuous.
-/
theorem selectedClosureTraceValue_uniformContinuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T) :
    UniformContinuous
      (
        h3TerminalComplementGradientSelectedClosureTraceValue
          hModulus
      ) := by

  rw [Metric.uniformContinuous_iff]

  intro ε hε

  have hThirdPos :
      0 < ε / 3 := by
    linarith

  obtain
    ⟨
      ρ,
      hρ,
      hUniform
    ⟩ :=
    hModulus
      (ε / 3)
      hThirdPos

  have hRhoThirdPos :
      0 < ρ / 3 := by
    linarith

  refine
    ⟨
      ρ / 3,
      hRhoThirdPos,
      ?_
    ⟩

  intro y z hyz

  have hyz' :
      dist y.1 z.1 < ρ / 3 := by

    rw [← Subtype.dist_eq y z]

    exact
      hyz

  obtain
    ⟨
      k₁,
      hPoint₁,
      hTrace₁
    ⟩ :=
    selectedClosureTraceValue_spec
      hModulus
      y

  obtain
    ⟨
      k₂,
      hPoint₂,
      hTrace₂
    ⟩ :=
    selectedClosureTraceValue_spec
      hModulus
      z

  rw [Metric.tendsto_atTop] at hPoint₁
  rw [Metric.tendsto_atTop] at hPoint₂
  rw [Metric.tendsto_atTop] at hTrace₁
  rw [Metric.tendsto_atTop] at hTrace₂

  obtain
    ⟨
      N₁,
      hN₁
    ⟩ :=
    hPoint₁
      (ρ / 3)
      hRhoThirdPos

  obtain
    ⟨
      N₂,
      hN₂
    ⟩ :=
    hPoint₂
      (ρ / 3)
      hRhoThirdPos

  obtain
    ⟨
      N₃,
      hN₃
    ⟩ :=
    hTrace₁
      (ε / 3)
      hThirdPos

  obtain
    ⟨
      N₄,
      hN₄
    ⟩ :=
    hTrace₂
      (ε / 3)
      hThirdPos

  let J : ℕ :=
    max (max N₁ N₂) (max N₃ N₄)

  have hN₁J :
      N₁ ≤ J := by

    dsimp only [J]

    exact
      le_trans
        (le_max_left N₁ N₂)
        (le_max_left (max N₁ N₂) (max N₃ N₄))

  have hN₂J :
      N₂ ≤ J := by

    dsimp only [J]

    exact
      le_trans
        (le_max_right N₁ N₂)
        (le_max_left (max N₁ N₂) (max N₃ N₄))

  have hN₃J :
      N₃ ≤ J := by

    dsimp only [J]

    exact
      le_trans
        (le_max_left N₃ N₄)
        (le_max_right (max N₁ N₂) (max N₃ N₄))

  have hN₄J :
      N₄ ≤ J := by

    dsimp only [J]

    exact
      le_trans
        (le_max_right N₃ N₄)
        (le_max_right (max N₁ N₂) (max N₃ N₄))

  have hPointNear₁ :
      dist
          (x (k₁ J))
          y.1
        < ρ / 3 :=
    hN₁
      J
      hN₁J

  have hPointNear₂ :
      dist
          (x (k₂ J))
          z.1
        < ρ / 3 :=
    hN₂
      J
      hN₂J

  have hSelectedNear :
      dist
          (x (k₁ J))
          (x (k₂ J))
        < ρ := by

    have hTriangle₁ :
        dist
            (x (k₁ J))
            (x (k₂ J))
          ≤
        dist
            (x (k₁ J))
            y.1
          +
        dist
            y.1
            (x (k₂ J)) :=
      dist_triangle
        (x (k₁ J))
        y.1
        (x (k₂ J))

    have hTriangle₂ :
        dist
            y.1
            (x (k₂ J))
          ≤
        dist
            y.1
            z.1
          +
        dist
            z.1
            (x (k₂ J)) :=
      dist_triangle
        y.1
        z.1
        (x (k₂ J))

    have hPointNear₂' :
        dist
            z.1
            (x (k₂ J))
          < ρ / 3 := by

      simpa only [dist_comm] using
        hPointNear₂

    linarith

  let A : ℝ :=
    h3TerminalComplementGradientSelectedClosureTraceValue
      hModulus
      y

  let A₀ : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      T
      (x (k₁ J))

  let B₀ : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      T
      (x (k₂ J))

  let B : ℝ :=
    h3TerminalComplementGradientSelectedClosureTraceValue
      hModulus
      z

  have hA₀A :
      dist A₀ A < ε / 3 := by

    dsimp only [A₀, A]

    exact
      hN₃
        J
        hN₃J

  have hAA₀ :
      dist A A₀ < ε / 3 := by

    simpa only [dist_comm] using
      hA₀A

  have hA₀B₀ :
      dist A₀ B₀ < ε / 3 := by

    dsimp only [A₀, B₀]

    exact
      hUniform
        (k₁ J)
        (k₂ J)
        hSelectedNear

  have hB₀B :
      dist B₀ B < ε / 3 := by

    dsimp only [B₀, B]

    exact
      hN₄
        J
        hN₄J

  have hTriangle₁ :
      dist A B
        ≤
      dist A A₀
        +
      dist A₀ B :=
    dist_triangle
      A A₀ B

  have hTriangle₂ :
      dist A₀ B
        ≤
      dist A₀ B₀
        +
      dist B₀ B :=
    dist_triangle
      A₀ B₀ B

  have hFinal :
      dist A B < ε := by
    linarith

  simpa only [A, B] using
    hFinal

/--
The canonical selected-closure trace function is continuous.
-/
theorem selectedClosureTraceValue_continuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T) :
    Continuous
      (
        h3TerminalComplementGradientSelectedClosureTraceValue
          hModulus
      ) :=
  (
    selectedClosureTraceValue_uniformContinuous
      hModulus
  ).continuous

/-! ## A nonzero closure point expands to a nonzero closure neighborhood -/

/--
The canonical selected-closure trace has a quantitatively nonzero neighborhood:
there is a closure point `y`, a radius `ρ > 0`, and a level `δ > 0` such that
every closure point within radius `ρ` has terminal trace magnitude at least
`δ`.
-/
def H3TerminalComplementGradientHasNonzeroSelectedClosureNeighborhood
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T) : Prop :=
  ∃ y : H3TerminalSelectedSpatialClosure x,
    ∃ ρ : ℝ,
      0 < ρ
        ∧
      ∃ δ : ℝ,
        0 < δ
          ∧
        ∀ z : H3TerminalSelectedSpatialClosure x,
          dist z y < ρ →
          δ
            ≤
          dist
            (
              h3TerminalComplementGradientSelectedClosureTraceValue
                hModulus
                z
            )
            0

/--
A nonzero value of the canonical selected-closure trace produces a positive
radius neighborhood on which the trace stays uniformly away from zero.
-/
theorem nonzeroSelectedClosureNeighborhood_of_traceValue_ne_zero
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    {y : H3TerminalSelectedSpatialClosure x}
    (hy :
      h3TerminalComplementGradientSelectedClosureTraceValue
          hModulus
          y
        ≠
      0) :
    H3TerminalComplementGradientHasNonzeroSelectedClosureNeighborhood
      hModulus := by

  let L : ℝ :=
    h3TerminalComplementGradientSelectedClosureTraceValue
      hModulus
      y

  let δ : ℝ :=
    dist L 0 / 2

  have hLNe :
      L ≠ 0 := by

    simpa only [L] using
      hy

  have hDistPos :
      0 < dist L 0 :=
    dist_pos.mpr
      hLNe

  have hδPos :
      0 < δ := by

    dsimp only [δ]

    linarith

  have hUniform :
      UniformContinuous
        (
          h3TerminalComplementGradientSelectedClosureTraceValue
            hModulus
        ) :=
    selectedClosureTraceValue_uniformContinuous
      hModulus

  rw [Metric.uniformContinuous_iff] at hUniform

  obtain
    ⟨
      ρ,
      hρ,
      hρControl
    ⟩ :=
    hUniform
      δ
      hδPos

  refine
    ⟨
      y,
      ρ,
      hρ,
      δ,
      hδPos,
      ?_
    ⟩

  intro z hz

  have hClose :
      dist
          (
            h3TerminalComplementGradientSelectedClosureTraceValue
              hModulus
              z
          )
          L
        < δ := by

    dsimp only [L]

    exact
      hρControl
        hz

  have hTriangle :
      dist L 0
        ≤
      dist
          L
          (
            h3TerminalComplementGradientSelectedClosureTraceValue
              hModulus
              z
          )
        +
      dist
          (
            h3TerminalComplementGradientSelectedClosureTraceValue
              hModulus
              z
          )
          0 :=
    dist_triangle
      L
      (
        h3TerminalComplementGradientSelectedClosureTraceValue
          hModulus
          z
      )
      0

  have hClose' :
      dist
          L
          (
            h3TerminalComplementGradientSelectedClosureTraceValue
              hModulus
              z
          )
        < δ := by

    simpa only [dist_comm] using
      hClose

  dsimp only [δ] at *

  linarith

/--
A nonzero intrinsic selected-closure trace therefore yields a quantitatively
nonzero neighborhood for the canonical closure trace function.
-/
theorem nonzeroSelectedClosureNeighborhood_of_nonzeroIntrinsicTrace
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
    H3TerminalComplementGradientHasNonzeroSelectedClosureNeighborhood
      hModulus := by

  obtain
    ⟨
      y,
      hy
    ⟩ :=
    exists_selectedClosurePoint_traceValue_ne_zero_of_nonzeroIntrinsicTrace
      hModulus
      hNonzero

  exact
    nonzeroSelectedClosureNeighborhood_of_traceValue_ne_zero
      hModulus
      hy

/-! ## Closure-neighborhood escape-side package -/

/--
The escape-side obstruction expressed as

* a pivot cluster at spatial infinity;
* a nonzero positive-radius core neighborhood in the canonical closure trace;
* quantitative contrast between a finite core and every selected route to
  infinity.
-/
def H3TerminalNativeComplementHasPivotInfinityAndNonzeroClosureNeighborhood
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
  H3TerminalComplementGradientHasNonzeroSelectedClosureNeighborhood
      hModulus
    ∧
  H3TerminalComplementGradientHasFiniteCoreInfinityContrast
      u p x T

/--
Under endpoint temporal control, selected spatial equicontinuity, terminal
decay at infinity, and eventual boundedness of the residual logarithm, failure
of the canonical factor forces either

* pivot behavior at infinity together with a quantitatively nonzero
  positive-radius core neighborhood in the selected-closure trace; or
* bounded selected range with positive terminal spatial contrast and positive
  witness separation.
-/
theorem nativeComplement_noCanonicalFactor_forces_pivotInfinityAndNonzeroClosureNeighborhood_or_boundedTerminalContrast
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
    H3TerminalNativeComplementHasPivotInfinityAndNonzeroClosureNeighborhood
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

    have hNeighborhood :
        H3TerminalComplementGradientHasNonzeroSelectedClosureNeighborhood
          hTerminalModulus :=
      nonzeroSelectedClosureNeighborhood_of_nonzeroIntrinsicTrace
        hTerminalModulus
        hEscapeSide.2.1

    exact
      ⟨
        hEscapeSide.1,
        hNeighborhood,
        hEscapeSide.2.2
      ⟩

  · exact
      Or.inr
        hContrast

end

end Euclidean
end Bridge
end PrimeTensor
