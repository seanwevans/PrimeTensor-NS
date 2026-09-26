import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualEndpointSpatialContrast

/-!
# Terminal selected spatial modulus and quantitative terminal separation

The bounded noncanonical branch has now been identified with a positive spatial
contrast in the actual complementary-gradient field at time `T`.

This file transfers the preterminal selected spatial equicontinuity estimate
to the terminal time itself.

The transfer uses the endpoint temporal modulus uniformly at the two selected
spatial points:

    F(T,x_m)
      ~ F(τ_r,x_m)
      ~ F(τ_r,x_n)
      ~ F(T,x_n).

Thus spatial equicontinuity along the selected preterminal times plus uniform
endpoint temporal control yields a uniform spatial modulus on the selected
terminal field.

Consequently, a positive terminal complementary-gradient contrast cannot occur
between selected points that become arbitrarily close.  The two fixed terminal
witnesses are quantitatively separated in physical space.

This remains a neutral geometric consequence.  A positive terminal spatial
contrast between positively separated points is not ruled out.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualTerminalSpatialModulus
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Terminal selected spatial modulus -/

/--
Uniform spatial continuity of the actual terminal complementary-gradient field
on the selected spatial points.
-/
def H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ η : ℝ,
      0 < η
        ∧
      ∀ m n : ℕ,
        dist (x m) (x n) < η →
        dist
          (
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x m)
          )
          (
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x n)
          )
          < ε

/--
Selected spatial equicontinuity on the preterminal family plus a uniform
endpoint temporal modulus transfers to a uniform spatial modulus at the actual
terminal time.
-/
theorem selectedTerminalSpatialUniformModulus_of_spatialEquicontinuity_of_endpointTemporalModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hSpatialEquicontinuity :
      H3TerminalComplementGradientSelectedSpatialEquicontinuity
        u p τ x)
    (hEndpoint :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u p τ x T) :
    H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
      u p x T := by

  intro ε hε

  have hThirdPos :
      0 < ε / 3 := by
    linarith

  obtain
    ⟨
      ρ,
      hρ,
      hSpatial
    ⟩ :=
    hSpatialEquicontinuity
      (ε / 3)
      hThirdPos

  obtain
    ⟨
      η,
      hη,
      hEndpointUniform
    ⟩ :=
    hEndpoint
      (ε / 3)
      hThirdPos

  rw [Metric.tendsto_atTop] at hTau

  obtain
    ⟨
      R,
      hR
    ⟩ :=
    hTau
      η
      hη

  have hTimeNear :
      dist
          (τ R)
          T
        < η :=
    hR
      R
      le_rfl

  refine
    ⟨
      ρ,
      hρ,
      ?_
    ⟩

  intro m n hmn

  let A : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      T
      (x m)

  let A₀ : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      (τ R)
      (x m)

  let B₀ : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      (τ R)
      (x n)

  let B : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      T
      (x n)

  have hLeft :
      dist A₀ A < ε / 3 := by

    dsimp only [A₀, A]

    exact
      hEndpointUniform
        m
        R
        hTimeNear

  have hMiddle :
      dist A₀ B₀ < ε / 3 := by

    dsimp only [A₀, B₀]

    exact
      hSpatial
        R
        m
        n
        hmn

  have hRight :
      dist B₀ B < ε / 3 := by

    dsimp only [B₀, B]

    exact
      hEndpointUniform
        n
        R
        hTimeNear

  have hLeft' :
      dist A A₀ < ε / 3 := by

    simpa only [dist_comm] using
      hLeft

  have hTriangleOne :
      dist A B
        ≤
      dist A A₀
        +
      dist A₀ B :=
    dist_triangle
      A A₀ B

  have hTriangleTwo :
      dist A₀ B
        ≤
      dist A₀ B₀
        +
      dist B₀ B :=
    dist_triangle
      A₀ B₀ B

  have hCombined :
      dist A B
        ≤
      dist A A₀
        +
      dist A₀ B₀
        +
      dist B₀ B := by

    linarith

  have hFinal :
      dist A B < ε := by

    linarith

  simpa only [A, B] using
    hFinal

/-! ## Quantitative terminal spatial separation -/

/--
The terminal complementary-gradient field has a positive contrast at two
selected points, and those points themselves are separated by a fixed positive
spatial distance.
-/
def H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrastSeparation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ η : ℝ,
      0 < η
        ∧
      ∃ a b : ℕ,
        η
          ≤
        dist
          (x a)
          (x b)
          ∧
        δ
          ≤
        dist
          (
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x a)
          )
          (
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x b)
          )

/--
A positive selected terminal contrast plus a selected terminal spatial modulus
forces a quantitative positive separation of the two witness points.
-/
theorem positiveSelectedTerminalSpatialContrastSeparation_of_contrast_of_terminalSpatialModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hContrast :
      H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrast
        u p x T) :
    H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrastSeparation
      u p x T := by

  obtain
    ⟨
      δ,
      hδ,
      a,
      b,
      _hab,
      hGap
    ⟩ :=
    hContrast

  obtain
    ⟨
      η,
      hη,
      hUniform
    ⟩ :=
    hModulus
      δ
      hδ

  have hPointGap :
      η
        ≤
      dist
        (x a)
        (x b) := by

    apply le_of_not_gt

    intro hNear

    have hSmall :
        dist
          (
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x a)
          )
          (
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x b)
          )
          < δ :=
      hUniform
        a
        b
        hNear

    exact
      (
        not_lt_of_ge
          hGap
      )
        hSmall

  exact
    ⟨
      δ,
      hδ,
      η,
      hη,
      a,
      b,
      hPointGap,
      hGap
    ⟩

/-! ## Bounded noncanonical branch with quantitative terminal geometry -/

/--
Under terminal-time convergence, bounded selected points, selected spatial
equicontinuity, and the uniform endpoint temporal modulus, failure of the
canonical native residual factor forces both

* a positive contrast in the actual terminal complementary-gradient field; and
* a fixed positive spatial separation between the two selected witness points.

The conclusion does not assert that this configuration is impossible.
-/
theorem positiveSelectedTerminalSpatialContrastSeparation_of_noCanonicalFactor_of_endpointModulus_of_spatialEquicontinuity_of_bounded
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
    (hBounded :
      Bornology.IsBounded (Set.range x))
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x) :
    H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrastSeparation
      u p x T := by

  have hTerminalModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T :=
    selectedTerminalSpatialUniformModulus_of_spatialEquicontinuity_of_endpointTemporalModulus
      hTau
      hSpatialEquicontinuity
      hEndpoint

  have hContrast :
      H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrast
        u p x T :=
    positiveSelectedTerminalSpatialContrast_of_noCanonicalFactor_of_endpointModulus_of_spatialEquicontinuity_of_bounded
      hTau
      hEndpoint
      hSpatialEquicontinuity
      hBounded
      hNoFactor

  exact
    positiveSelectedTerminalSpatialContrastSeparation_of_contrast_of_terminalSpatialModulus
      hTerminalModulus
      hContrast

end

end Euclidean
end Bridge
end PrimeTensor
