import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualFiniteCoreInfinityContrast

/-!
# Intrinsic terminal trace at a finite selected spatial cluster

The escape-side branch now contains a finite spatial core channel carrying a
nonzero terminal complementary-gradient trace and a quantitative contrast with
spatial infinity.

The next issue is whether that trace depends on the particular cofinal channel
used to approach the finite cluster point.

The terminal selected spatial modulus removes that ambiguity.

If two selected spatial sequences both converge to the same point `y`, then
their mutual spatial distance tends to zero.  The uniform terminal spatial
modulus therefore forces the corresponding terminal complementary-gradient
values to synchronize.  Consequently, if one selected approach to `y`
converges to a real trace `L`, every selected approach to `y` converges to the
same `L`.

This produces an intrinsic terminal trace on the closure of the selected
spatial set, without requiring the terminal field itself to have been proved
continuous at the ambient point `y`.

For the distinct finite native residual channel, the intrinsic trace is

    L = logValue q ≠ 0.

Thus the escape-side obstruction becomes:

* pivot behavior at spatial infinity;
* a finite spatial cluster carrying an intrinsic nonzero selected terminal
  trace;
* quantitative contrast between that finite core and every selected route to
  infinity.

No identification with the literal ambient value `F(T,y)` is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualIntrinsicFiniteTrace
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Uniqueness of the selected terminal trace at a cluster point -/

/--
Under the selected terminal spatial modulus, one convergent selected terminal
trace determines the trace along every selected sequence approaching the same
spatial cluster point.
-/
theorem terminalTrace_tendsto_of_sameSelectedCluster_of_terminalSpatialModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T L : ℝ}
    {y : Point3}
    {k ell : ℕ → ℕ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hKPoint :
      Tendsto
        (fun j : ℕ => x (k j))
        atTop
        (𝓝 y))
    (hKTrace :
      Tendsto
        (
          fun j : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x (k j))
        )
        atTop
        (𝓝 L))
    (hEllPoint :
      Tendsto
        (fun j : ℕ => x (ell j))
        atTop
        (𝓝 y)) :
    Tendsto
      (
        fun j : ℕ =>
          h3TerminalComplementGradientFieldForPair
            u p
            T
            (x (ell j))
      )
      atTop
      (𝓝 L) := by

  rw [Metric.tendsto_atTop]

  intro ε hε

  have hHalfPos :
      0 < ε / 2 := by
    linarith

  obtain
    ⟨
      η,
      hη,
      hUniform
    ⟩ :=
    hModulus
      (ε / 2)
      hHalfPos

  have hEtaHalfPos :
      0 < η / 2 := by
    linarith

  rw [Metric.tendsto_atTop] at hKPoint
  rw [Metric.tendsto_atTop] at hEllPoint
  rw [Metric.tendsto_atTop] at hKTrace

  obtain
    ⟨
      N₁,
      hN₁
    ⟩ :=
    hKPoint
      (η / 2)
      hEtaHalfPos

  obtain
    ⟨
      N₂,
      hN₂
    ⟩ :=
    hEllPoint
      (η / 2)
      hEtaHalfPos

  obtain
    ⟨
      N₃,
      hN₃
    ⟩ :=
    hKTrace
      (ε / 2)
      hHalfPos

  refine
    ⟨
      max (max N₁ N₂) N₃,
      ?_
    ⟩

  intro j hj

  have hN₁j :
      N₁ ≤ j :=
    le_trans
      (le_trans
        (le_max_left N₁ N₂)
        (le_max_left (max N₁ N₂) N₃))
      hj

  have hN₂j :
      N₂ ≤ j :=
    le_trans
      (le_trans
        (le_max_right N₁ N₂)
        (le_max_left (max N₁ N₂) N₃))
      hj

  have hN₃j :
      N₃ ≤ j :=
    le_trans
      (le_max_right (max N₁ N₂) N₃)
      hj

  have hKNear :
      dist
          (x (k j))
          y
        < η / 2 :=
    hN₁
      j
      hN₁j

  have hEllNear :
      dist
          (x (ell j))
          y
        < η / 2 :=
    hN₂
      j
      hN₂j

  have hSelectedNear :
      dist
          (x (ell j))
          (x (k j))
        < η := by

    have hTriangle :
        dist
            (x (ell j))
            (x (k j))
          ≤
        dist
            (x (ell j))
            y
          +
        dist
            y
            (x (k j)) :=
      dist_triangle
        (x (ell j))
        y
        (x (k j))

    have hKNear' :
        dist
            y
            (x (k j))
          < η / 2 := by

      simpa only [dist_comm] using
        hKNear

    linarith

  let A : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      T
      (x (ell j))

  let B : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      T
      (x (k j))

  have hAB :
      dist A B < ε / 2 := by

    dsimp only [A, B]

    exact
      hUniform
        (ell j)
        (k j)
        hSelectedNear

  have hBL :
      dist B L < ε / 2 := by

    dsimp only [B]

    exact
      hN₃
        j
        hN₃j

  have hTriangle :
      dist A L
        ≤
      dist A B + dist B L :=
    dist_triangle
      A B L

  have hAL :
      dist A L < ε := by
    linarith

  simpa only [A] using
    hAL

/-! ## Intrinsic finite terminal trace channel -/

/--
A distinct finite native factor `q ≠ 1` determines an intrinsic nonzero
terminal trace at a finite selected spatial cluster point: every selected
sequence approaching that point has terminal complementary-gradient values
converging to `logValue q`.
-/
def H3TerminalNativeComplementHasDistinctIntrinsicFiniteTerminalTraceChannel
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  ∃ q : MulReal,
    q ≠ (1 : MulReal)
      ∧
    PrimeTensor.Bridge.MulReal.logValue q ≠ 0
      ∧
    ∃ y : Point3,
      ∃ k : ℕ → ℕ,
        Tendsto k atTop atTop
          ∧
        Tendsto
          (fun j : ℕ => τ (k j))
          atTop
          (𝓝 T)
          ∧
        Tendsto
          (fun j : ℕ => x (k j))
          atTop
          (𝓝 y)
          ∧
        H3TerminalNativeComplementProportionalityFactor
          u p
          (fun j : ℕ => τ (k j))
          (fun j : ℕ => x (k j))
          q
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
                PrimeTensor.Bridge.MulReal.logValue q
              )
          )
          ∧
        ∀ ell : ℕ → ℕ,
          Tendsto
              (fun j : ℕ => x (ell j))
              atTop
              (𝓝 y)
            →
          Tendsto
            (
              fun j : ℕ =>
                h3TerminalComplementGradientFieldForPair
                  u p
                  T
                  (x (ell j))
            )
            atTop
            (
              𝓝
                (
                  PrimeTensor.Bridge.MulReal.logValue q
                )
            )

/--
A distinct finite terminal trace channel becomes intrinsic at its finite
selected spatial cluster point under the terminal selected spatial modulus.
-/
theorem distinctIntrinsicFiniteTerminalTraceChannel_of_distinctFiniteTerminalTrace_of_terminalSpatialModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hTrace :
      H3TerminalNativeComplementHasDistinctFiniteTerminalTraceChannel
        u p τ x T) :
    H3TerminalNativeComplementHasDistinctIntrinsicFiniteTerminalTraceChannel
      u p τ x T := by

  obtain
    ⟨
      q,
      hqNe,
      hqLogNe,
      y,
      k,
      hkTop,
      hTime,
      hPoint,
      hFactor,
      hTerminal
    ⟩ :=
    hTrace

  refine
    ⟨
      q,
      hqNe,
      hqLogNe,
      y,
      k,
      hkTop,
      hTime,
      hPoint,
      hFactor,
      hTerminal,
      ?_
    ⟩

  intro ell hEllPoint

  exact
    terminalTrace_tendsto_of_sameSelectedCluster_of_terminalSpatialModulus
      hModulus
      hPoint
      hTerminal
      hEllPoint

/-! ## Escape-side package with an intrinsic finite core trace -/

/--
The escape-side obstruction contains

* a native pivot cluster at spatial infinity;
* a distinct intrinsic nonzero terminal trace at a finite selected spatial
  cluster point; and
* quantitative contrast between that finite core and every selected route to
  infinity.
-/
def H3TerminalNativeComplementHasPivotInfinityAndIntrinsicFiniteCoreTrace
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  H3TerminalNativeComplementHasCofinalPivotClusterAtSpatialInfinity
      u p τ x T
    ∧
  H3TerminalNativeComplementHasDistinctIntrinsicFiniteTerminalTraceChannel
      u p τ x T
    ∧
  H3TerminalComplementGradientHasFiniteCoreInfinityContrast
      u p x T

/--
Under endpoint temporal control, selected spatial equicontinuity, terminal
decay at infinity, and eventual boundedness of the residual logarithm, failure
of the canonical factor forces either

* a pivot cluster at infinity together with an intrinsic nonzero finite core
  trace and quantitative core-versus-infinity contrast; or
* bounded selected range with positive terminal spatial contrast and positive
  witness separation.
-/
theorem nativeComplement_noCanonicalFactor_forces_pivotInfinityAndIntrinsicFiniteCoreTrace_or_boundedTerminalContrast
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
    H3TerminalNativeComplementHasPivotInfinityAndIntrinsicFiniteCoreTrace
        u p τ x T
      ∨
    (
      Bornology.IsBounded (Set.range x)
        ∧
      H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrastSeparation
        u p x T
    ) := by

  have hTerminalModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T :=
    selectedTerminalSpatialUniformModulus_of_spatialEquicontinuity_of_endpointTemporalModulus
      hTau
      hSpatialEquicontinuity
      hEndpoint

  rcases
    nativeComplement_noCanonicalFactor_forces_pivotInfinityAndFiniteCoreContrast_or_boundedTerminalContrast
      hTau
      hEndpoint
      hSpatialEquicontinuity
      hDecay
      hResidualBounded
      hNoFactor
    with
    hEscapeSide | hContrast

  · left

    have hIntrinsic :
        H3TerminalNativeComplementHasDistinctIntrinsicFiniteTerminalTraceChannel
          u p τ x T :=
      distinctIntrinsicFiniteTerminalTraceChannel_of_distinctFiniteTerminalTrace_of_terminalSpatialModulus
        hTerminalModulus
        hEscapeSide.2.1

    exact
      ⟨
        hEscapeSide.1,
        hIntrinsic,
        hEscapeSide.2.2
      ⟩

  · exact
      Or.inr
        hContrast

end

end Euclidean
end Bridge
end PrimeTensor
