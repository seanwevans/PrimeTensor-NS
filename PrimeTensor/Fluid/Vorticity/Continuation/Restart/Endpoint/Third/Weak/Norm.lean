import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Spectral.Continuity

/-!
# Ordered-third endpoint continuity: weak-plus-norm reduction

`SpectralContinuity` reduced the complete ordered-third physical `L²`
continuity frontier to strong continuity of the weighted H³ spectral state.

This file performs the standard Hilbert-space reduction one level further.

For one weighted spectral coordinate `F(q)`, assume:

* every fixed-vector real weak pairing

      q ↦ Re ⟪F(q), Φ⟫

  is continuous; and

* the scalar norm

      q ↦ ‖F(q)‖

  is continuous.

Then for a fixed base point `q₀`, the identity

    ‖F(q) - F(q₀)‖²
      =
    ‖F(q)‖²
      - 2 Re ⟪F(q), F(q₀)⟫
      + ‖F(q₀)‖²

shows that the squared strong distance is continuous and vanishes at `q₀`.
Taking the square root proves strong continuity.

The finite velocity-component product is then continuous coordinatewise.

No Navier--Stokes estimate is introduced here.  The ordered-third branch is
reduced to two analytically distinct questions:

1. weak continuity of each weighted H³ spectral coordinate;
2. continuity of each weighted H³ spectral-coordinate norm.

The first is the natural target for the already-proved zeroth physical `L²`
continuity plus the uniform H³ tail bound.  The second is the genuine top-order
energy/norm continuity question.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityThirdWeakNorm
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Weak real-pairing continuity for every weighted H³ spectral coordinate. -/
def H3PreterminalCanonicalSpectralWeakContinuousOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ (j : Fin 3) (Φ : H3SpectralScalarState),
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        (inner ℂ
          (h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q j)
          Φ).re)

/-- Scalar norm continuity for every weighted H³ spectral coordinate. -/
def H3PreterminalCanonicalSpectralCoordinateNormContinuousOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ j : Fin 3,
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q j‖)

/-- Package of the two Hilbert-space inputs needed for strong weighted H³
spectral continuity. -/
def H3PreterminalCanonicalSpectralWeakNormContinuousOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  H3PreterminalCanonicalSpectralWeakContinuousOnElapsed
      hNS ht hEnd hTail
    ∧
  H3PreterminalCanonicalSpectralCoordinateNormContinuousOnElapsed
      hNS ht hEnd hTail

/-- Generic complex-Hilbert weak-plus-norm continuity lemma in the exact
orientation used by the spectral state below. -/
theorem continuous_of_weakRealPairings_of_norm
    {α H : Type*}
    [TopologicalSpace α]
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (F : α → H)
    (hWeak :
      ∀ Φ : H,
        Continuous
          (fun q : α =>
            (inner ℂ (F q) Φ).re))
    (hNorm :
      Continuous
        (fun q : α => ‖F q‖)) :
    Continuous F := by
  rw [continuous_iff_continuousAt]
  intro q₀

  apply tendsto_iff_norm_sub_tendsto_zero.2

  have hPair :
      Continuous
        (fun q : α =>
          (inner ℂ (F q) (F q₀)).re) :=
    hWeak (F q₀)

  have hSqFormula :
      (fun q : α =>
        ‖F q - F q₀‖ ^ 2)
        =
      (fun q : α =>
        ‖F q‖ ^ 2
          -
        2 * (inner ℂ (F q) (F q₀)).re
          +
        ‖F q₀‖ ^ 2) := by
    funext q
    exact
      norm_sub_sq (𝕜 := ℂ) (F q) (F q₀)

  have hSqContinuous :
      Continuous
        (fun q : α =>
          ‖F q - F q₀‖ ^ 2) := by
    rw [hSqFormula]

    exact
      ((hNorm.pow 2).sub
          (continuous_const.mul hPair)).add
        continuous_const

  have hSqAt :
      Tendsto
        (fun q : α =>
          ‖F q - F q₀‖ ^ 2)
        (𝓝 q₀)
        (𝓝
          ((fun q : α =>
            ‖F q - F q₀‖ ^ 2) q₀)) :=
    hSqContinuous.continuousAt

  have hSqZero :
      (fun q : α =>
        ‖F q - F q₀‖ ^ 2) q₀
        =
      0 := by
    simp

  have hSqTendsto :
      Tendsto
        (fun q : α =>
          ‖F q - F q₀‖ ^ 2)
        (𝓝 q₀)
        (𝓝 0) := by
    rw [hSqZero] at hSqAt
    exact hSqAt

  have hSqrtAt :
      Tendsto
        Real.sqrt
        (𝓝 (0 : ℝ))
        (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt

  have hSqrt :
      Tendsto
        (fun q : α =>
          Real.sqrt (‖F q - F q₀‖ ^ 2))
        (𝓝 q₀)
        (𝓝 (Real.sqrt 0)) := by
    exact hSqrtAt.comp hSqTendsto

  have hNormTendsto :
      Tendsto
        (fun q : α =>
          ‖F q - F q₀‖)
        (𝓝 q₀)
        (𝓝 0) := by
    simpa only [
      Real.sqrt_sq_eq_abs,
      abs_of_nonneg,
      norm_nonneg,
      Real.sqrt_zero
    ] using hSqrt

  exact hNormTendsto

/-- Weak continuity plus coordinate-norm continuity gives strong continuity of
the complete weighted H³ spectral state. -/
theorem h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_weak_of_norm
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hWeak :
      H3PreterminalCanonicalSpectralWeakContinuousOnElapsed
        hNS ht hEnd hTail)
    (hNorm :
      H3PreterminalCanonicalSpectralCoordinateNormContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalSpectralStateContinuousOnElapsed
      hNS ht hEnd hTail := by
  unfold H3PreterminalCanonicalSpectralStateContinuousOnElapsed

  apply continuous_pi
  intro j

  exact
    continuous_of_weakRealPairings_of_norm
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q j)
      (hWeak j)
      (hNorm j)

/-- Bundled weak-plus-norm form of the same local implication. -/
theorem h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_weakNorm
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hWeakNorm :
      H3PreterminalCanonicalSpectralWeakNormContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalSpectralStateContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_weak_of_norm
      hNS ht hEnd hTail
      hWeakNorm.1
      hWeakNorm.2

/-- Restart-radius weak-plus-norm spectral continuity frontier. -/
def H3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontierOnRestartRadius
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E),
    ∀ hqPos : 0 < (q : ℝ),
      ∀ hEnd : t + (q : ℝ) < T,
        H3PreterminalCanonicalSpectralWeakNormContinuousOnElapsed
          hNS ht hEnd hTail

/-- Radius-wide weak-plus-norm continuity closes the radius-wide strong spectral
continuity frontier. -/
theorem h3PreterminalTailUnitViscositySpectralContinuityFrontierOnRestartRadius_of_weakNorm
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hWeakNorm :
      H3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3PreterminalTailUnitViscositySpectralContinuityFrontierOnRestartRadius
      E u T t hNS ht hE hTail := by
  intro q hqPos hEnd

  exact
    h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_weakNorm
      hNS ht hEnd hTail
      (hWeakNorm q hqPos hEnd)

/-- Global weak-plus-norm weighted H³ spectral continuity frontier. -/
def H3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- The global weak-plus-norm frontier closes the global strong spectral
continuity frontier. -/
theorem h3PreterminalTailUnitViscositySpectralContinuityFrontier_of_weakNorm
    (hWeakNorm :
      H3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontier) :
    H3PreterminalTailUnitViscositySpectralContinuityFrontier := by
  intro E hE u T t hNS ht hTail

  exact
    h3PreterminalTailUnitViscositySpectralContinuityFrontierOnRestartRadius_of_weakNorm
      hNS ht hE hTail
      (hWeakNorm E hE u T t hNS ht hTail)

/-- The global weak-plus-norm frontier therefore closes the existing global
ordered-third physical `L²` continuity frontier. -/
theorem h3PreterminalTailUnitViscosityThirdContinuityFrontier_of_weakNorm
    (hWeakNorm :
      H3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontier) :
    H3PreterminalTailUnitViscosityThirdContinuityFrontier := by
  exact
    h3PreterminalTailUnitViscosityThirdContinuityFrontier_of_spectral
      (h3PreterminalTailUnitViscositySpectralContinuityFrontier_of_weakNorm
        hWeakNorm)

/-- Current continuation theorem with the remaining fronts stated as:

* old preterminal pressure-gradient mass for the zeroth-order route;
* weak-plus-coordinate-norm continuity of the weighted H³ spectral state.
-/
theorem h3ControlProducesExtension_of_unitViscosityZeroOldPressureSpectralWeakNormClosed
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    (hWeakNorm :
      H3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroOldPressureSpectralContinuityClosed
      hOld
      (h3PreterminalTailUnitViscositySpectralContinuityFrontier_of_weakNorm
        hWeakNorm)

end

end Euclidean
end Bridge
end PrimeTensor
