import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Spatial.Geometry
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Native.Residual.Spatial.Decay.Automatic

/-!
# Exclude physical vorticity spatial escape under endpoint temporal control

The preceding physical obstruction has a geometric alternative:

* finite-core concentration; or
* a cofinal spatial escape.

At every strict preterminal time, each physical vorticity component is a
difference of two first velocity derivatives.  The H³ Fourier /
Riemann--Lebesgue decay theorem already sends each of those derivatives to zero
along spatial escape, hence every fixed physical vorticity component also
vanishes at spatial infinity at every strict time.

The only missing transfer to the moving terminal sequence is uniform temporal
control.  This file isolates the exact endpoint modulus for the fixed physical
vorticity component and proves that, under this modulus, an escaping selected
refinement must have physical vorticity tending to zero.

That contradicts the existing one-sided lower bound

    n < orientedValue s (actualVorticityComponent ...)

on the same quantitative physical sequence.

Thus the spatial-infinity branch is impossible under the endpoint temporal
modulus, leaving finite-core concentration.  No claim is made here that the
endpoint modulus already follows from the current H³ hypotheses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalMinimalVorticityPhysicalSpatialEscapeExclusion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Endpoint temporal modulus for one fixed physical vorticity component -/

/--
Uniform convergence in time to the actual terminal value of one fixed physical
vorticity component over the selected spatial family.
-/
def H3TerminalActualVorticitySelectedEndpointTemporalModulus
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (i : Fin 3)
    (τ : ℕ → ℝ)
    (z : ℕ → Point3)
    (T : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ η : ℝ,
      0 < η
        ∧
      ∀ r n : ℕ,
        dist (τ n) T < η →
        dist
          (h3NativeActualVorticityComponentAt
            u i (τ n) (z r))
          (h3NativeActualVorticityComponentAt
            u i T (z r))
          < ε

/-! ## Strict-time spatial decay of actual vorticity -/

/--
At every strict preterminal time of an H³-path-admissible solution, each fixed
physical vorticity component tends to zero along every spatially escaping
sequence.
-/
theorem actualVorticityComponent_strictTime_tendsto_zero_of_h3Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (i : Fin 3)
    {y : ℕ → Point3}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T)
    (hEscape :
      Tendsto
        (fun n : ℕ =>
          dist
            (0 : Point3)
            (y n))
        atTop
        atTop) :
    Tendsto
      (fun n : ℕ =>
        h3NativeActualVorticityComponentAt
          u i t (y n))
      atTop
      (𝓝 0) := by

  fin_cases i

  · have hFirst :
        Tendsto
          (fun n : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u .x_zy t (y n))
          atTop
          (𝓝 0) :=
      terminalComplementGradient_strictTime_tendsto_zero_of_h3Path
        hH3 ht hEscape

    have hSecond :
        Tendsto
          (fun n : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u .x_yz t (y n))
          atTop
          (𝓝 0) :=
      terminalComplementGradient_strictTime_tendsto_zero_of_h3Path
        hH3 ht hEscape

    simpa [
      h3NativeActualVorticityComponentAt,
      h3TerminalComplementGradientFieldForPair,
      h3TerminalComplementDerivativeAxisForPair,
      h3TerminalComplementComponentAxisForPair,
      realVorticityX
    ] using
      hFirst.sub hSecond

  · have hFirst :
        Tendsto
          (fun n : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u .y_xz t (y n))
          atTop
          (𝓝 0) :=
      terminalComplementGradient_strictTime_tendsto_zero_of_h3Path
        hH3 ht hEscape

    have hSecond :
        Tendsto
          (fun n : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u .y_zx t (y n))
          atTop
          (𝓝 0) :=
      terminalComplementGradient_strictTime_tendsto_zero_of_h3Path
        hH3 ht hEscape

    simpa [
      h3NativeActualVorticityComponentAt,
      h3TerminalComplementGradientFieldForPair,
      h3TerminalComplementDerivativeAxisForPair,
      h3TerminalComplementComponentAxisForPair,
      realVorticityY
    ] using
      hFirst.sub hSecond

  · have hFirst :
        Tendsto
          (fun n : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u .z_yx t (y n))
          atTop
          (𝓝 0) :=
      terminalComplementGradient_strictTime_tendsto_zero_of_h3Path
        hH3 ht hEscape

    have hSecond :
        Tendsto
          (fun n : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u .z_xy t (y n))
          atTop
          (𝓝 0) :=
      terminalComplementGradient_strictTime_tendsto_zero_of_h3Path
        hH3 ht hEscape

    simpa [
      h3NativeActualVorticityComponentAt,
      h3TerminalComplementGradientFieldForPair,
      h3TerminalComplementDerivativeAxisForPair,
      h3TerminalComplementComponentAxisForPair,
      realVorticityZ
    ] using
      hFirst.sub hSecond

/-! ## Transfer strict-time decay to the moving terminal sequence -/

/--
Uniform endpoint temporal control transfers fixed-time H³ spatial decay to the
moving selected physical-vorticity values on any escaping terminal
refinement.
-/
theorem actualVorticityComponent_tendsto_zero_of_terminalEscapeRefinement_of_endpointTemporalModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {i : Fin 3}
    {τ : ℕ → ℝ}
    {z : ℕ → Point3}
    {T : ℝ}
    {k : ℕ → ℕ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    (hTime :
      Tendsto
        (fun j : ℕ => τ (k j))
        atTop
        (𝓝 T))
    (hSpatial :
      Tendsto
        (fun j : ℕ =>
          dist
            (0 : Point3)
            (z (k j)))
        atTop
        atTop)
    (hEndpoint :
      H3TerminalActualVorticitySelectedEndpointTemporalModulus
        u i τ z T) :
    Tendsto
      (fun j : ℕ =>
        h3NativeActualVorticityComponentAt
          u i
          (τ (k j))
          (z (k j)))
      atTop
      (𝓝 0) := by

  rw [Metric.tendsto_atTop]

  intro ε hε

  have hThirdPos :
      0 < ε / 3 := by
    linarith

  obtain
    ⟨η, hη, hEndpointUniform⟩ :=
    hEndpoint
      (ε / 3)
      hThirdPos

  rw [Metric.tendsto_atTop] at hTime

  obtain
    ⟨N, hNearN⟩ :=
    hTime
      η
      hη

  have hFixedNear :
      dist (τ (k N)) T < η :=
    hNearN
      N
      le_rfl

  have hFixedStrict :
      τ (k N) ∈ Set.Ioo (0 : ℝ) T :=
    hTauStrict
      (k N)

  have hFixedDecay :
      Tendsto
        (fun j : ℕ =>
          h3NativeActualVorticityComponentAt
            u i
            (τ (k N))
            (z (k j)))
        atTop
        (𝓝 0) :=
    actualVorticityComponent_strictTime_tendsto_zero_of_h3Path
      i
      hH3
      hFixedStrict
      hSpatial

  rw [Metric.tendsto_atTop] at hFixedDecay

  obtain
    ⟨J₀, hJ₀⟩ :=
    hFixedDecay
      (ε / 3)
      hThirdPos

  obtain
    ⟨J₁, hJ₁⟩ :=
    hTime
      η
      hη

  refine
    ⟨
      max J₀ J₁,
      ?_
    ⟩

  intro j hj

  have hJ₀j :
      J₀ ≤ j :=
    le_trans
      (le_max_left J₀ J₁)
      hj

  have hJ₁j :
      J₁ ≤ j :=
    le_trans
      (le_max_right J₀ J₁)
      hj

  let A : ℝ :=
    h3NativeActualVorticityComponentAt
      u i
      (τ (k j))
      (z (k j))

  let B : ℝ :=
    h3NativeActualVorticityComponentAt
      u i
      T
      (z (k j))

  let C : ℝ :=
    h3NativeActualVorticityComponentAt
      u i
      (τ (k N))
      (z (k j))

  have hAB :
      dist A B < ε / 3 := by

    dsimp only [A, B]

    exact
      hEndpointUniform
        (k j)
        (k j)
        (hJ₁ j hJ₁j)

  have hCB :
      dist C B < ε / 3 := by

    dsimp only [C, B]

    exact
      hEndpointUniform
        (k j)
        (k N)
        hFixedNear

  have hBC :
      dist B C < ε / 3 := by
    simpa only [dist_comm] using
      hCB

  have hC0 :
      dist C 0 < ε / 3 := by

    dsimp only [C]

    exact
      hJ₀
        j
        hJ₀j

  have hTriangle₁ :
      dist A 0
        ≤
      dist A B + dist B 0 :=
    dist_triangle
      A B 0

  have hTriangle₂ :
      dist B 0
        ≤
      dist B C + dist C 0 :=
    dist_triangle
      B C 0

  have hA0 :
      dist A 0 < ε := by
    linarith

  simpa only [A] using
    hA0

/-! ## The physical spatial-infinity branch is impossible -/

/--
The oriented linear physical-vorticity lower bound is incompatible with an
escaping cofinal refinement once the fixed component has the uniform endpoint
temporal modulus.
-/
theorem terminal_minimalVorticityPhysical_spatialEscape_impossible_of_endpointTemporalModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    {i : Fin 3}
    {s : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {z : ℕ → Point3}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hOrientedLower :
      ∀ n : ℕ,
        (n : ℝ) <
          h3TerminalOrientedValue
            s
            (h3NativeActualVorticityComponentAt
              u i (τ n) (z n)))
    (hEscape :
      H3TerminalSelectedPointEscapesToInfinity z)
    (hEndpoint :
      H3TerminalActualVorticitySelectedEndpointTemporalModulus
        u i τ z T) :
    False := by

  obtain
    ⟨k, hkTop, hSpatial⟩ :=
    hEscape

  have hTime :
      Tendsto
        (fun j : ℕ => τ (k j))
        atTop
        (𝓝 T) :=
    hTau.comp
      hkTop

  have hZero :
      Tendsto
        (fun j : ℕ =>
          h3NativeActualVorticityComponentAt
            u i
            (τ (k j))
            (z (k j)))
        atTop
        (𝓝 0) :=
    actualVorticityComponent_tendsto_zero_of_terminalEscapeRefinement_of_endpointTemporalModulus
      hH3
      hTauStrict
      hTime
      hSpatial
      hEndpoint

  rw [Metric.tendsto_atTop] at hZero

  obtain
    ⟨J, hSmall⟩ :=
    hZero
      1
      zero_lt_one

  have hIndexLarge :
      ∀ᶠ j : ℕ in atTop,
        2 ≤ k j :=
    (
      tendsto_atTop.1
        hkTop
    )
      2

  obtain
    ⟨K, hK⟩ :=
    eventually_atTop.1
      hIndexLarge

  let j : ℕ :=
    max J K

  have hJ :
      J ≤ j :=
    le_max_left
      J K

  have hKj :
      K ≤ j :=
    le_max_right
      J K

  have hkTwo :
      2 ≤ k j :=
    hK
      j
      hKj

  let V : ℝ :=
    h3NativeActualVorticityComponentAt
      u i
      (τ (k j))
      (z (k j))

  have hSmallV :
      |V| < 1 := by

    have hDist :
        dist V 0 < 1 := by

      dsimp only [V]

      exact
        hSmall
          j
          hJ

    simpa [Real.dist_eq] using
      hDist

  have hLower :
      (k j : ℝ) <
        h3TerminalOrientedValue
          s
          V := by

    dsimp only [V]

    exact
      hOrientedLower
        (k j)

  have hTwoReal :
      (2 : ℝ) ≤ (k j : ℝ) := by
    exact_mod_cast
      hkTwo

  have hOrientedLeAbs :
      h3TerminalOrientedValue
          s
          V
        ≤
      |V| := by

    cases s

    · simpa [h3TerminalOrientedValue] using
        (le_abs_self V)

    · simpa [h3TerminalOrientedValue] using
        (neg_le_abs V)

  linarith

/--
For a physical spatial-geometry witness, endpoint temporal control for its
fixed actual-vorticity component collapses the geometric alternative to the
finite-cluster branch.
-/
theorem terminal_minimalVorticityPhysical_finiteCluster_of_spatialGeometryData_of_endpointTemporalModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    {i : Fin 3}
    {s : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {z : ℕ → Point3}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hOrientedLower :
      ∀ n : ℕ,
        (n : ℝ) <
          h3TerminalOrientedValue
            s
            (h3NativeActualVorticityComponentAt
              u i (τ n) (z n)))
    (hGeometry :
      H3TerminalSelectedPointHasFiniteCluster z
        ∨
      H3TerminalSelectedPointEscapesToInfinity z)
    (hEndpoint :
      H3TerminalActualVorticitySelectedEndpointTemporalModulus
        u i τ z T) :
    H3TerminalSelectedPointHasFiniteCluster z := by

  rcases hGeometry with
    hFinite | hEscape

  · exact
      hFinite

  · exact
      False.elim
        (
          terminal_minimalVorticityPhysical_spatialEscape_impossible_of_endpointTemporalModulus
            hH3
            hTauStrict
            hTau
            hOrientedLower
            hEscape
            hEndpoint
        )

end

end Euclidean
end Bridge
end PrimeTensor
