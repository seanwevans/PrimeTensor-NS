import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Weak.Norm
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.RHSBound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Density

/-!
# Ordered-third endpoint continuity: reduce weak H³ continuity to Schwartz tests

`WeakNorm` reduced strong weighted H³ spectral continuity to:

1. weak continuity of every fixed spectral pairing;
2. continuity of each spectral coordinate norm.

The weak half can itself be reduced to a dense smooth test class.

The weighted spectral scalar state is just complex `L²` on the Fourier carrier,
and `Spectral.Density` already proves that Schwartz frequency functions are
dense in that exact space.  On the retained old tail we also have the uniform
bound

    ‖U(q)‖ ≤ 2E.

Hence, if the weak real pairing

    q ↦ Re ⟪U_j(q), ψ⟫

is continuous for every Schwartz `ψ`, then it is continuous for every
`L²` spectral test `Φ`: approximate `Φ` by one Schwartz test and control the
two approximation errors uniformly by Cauchy--Schwarz and the `2E` bound.

This file is purely functional analytic.  It introduces no PDE estimate.

After this reduction the ordered-third branch requires only:

* Schwartz-test weak spectral continuity; and
* spectral coordinate-norm continuity.

The next bridge can attack the Schwartz-test pairing directly from the already
available zeroth physical `L²` continuity, because multiplying a Schwartz test
by the polynomial H³ weight stays in `L²`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  ComplexConjugate SchwartzMap

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityThirdWeakSchwartz
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Real-part pairing perturbation in the test vector is controlled by the
Hilbert norms. -/
theorem dist_re_inner_right_le_norm_mul_norm_sub
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (x y z : H) :
    dist
        (inner ℂ x y).re
        (inner ℂ x z).re
      ≤
    ‖x‖ * ‖y - z‖ := by
  rw [Real.dist_eq]

  have hRe :
      (inner ℂ x y).re - (inner ℂ x z).re
        =
      (inner ℂ x (y - z)).re := by
    rw [inner_sub_right]
    rfl

  rw [hRe]

  exact
    (Complex.abs_re_le_norm
      (inner ℂ x (y - z))).trans
      (norm_inner_le_norm x (y - z))

/-- A uniformly bounded spectral path whose real weak pairings are continuous
against every Schwartz test is weakly continuous against every spectral `L²`
test. -/
theorem continuous_re_inner_of_schwartz_of_uniform_bound
    {α : Type*}
    [PseudoMetricSpace α]
    (F : α → H3SpectralScalarState)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hBound : ∀ q : α, ‖F q‖ ≤ B)
    (hSchwartz :
      ∀ ψ : SchwartzMap H3FourierPoint3 ℂ,
        Continuous
          (fun q : α =>
            (inner ℂ
              (F q)
              (ψ.toLp 2
                (volume : Measure H3FourierPoint3))).re))
    (Φ : H3SpectralScalarState) :
    Continuous
      (fun q : α =>
        (inner ℂ (F q) Φ).re) := by
  rw [continuous_iff_continuousAt]
  intro q₀

  rw [Metric.continuousAt_iff]
  intro ε hε

  have hB1 :
      0 < B + 1 := by
    linarith

  let η : ℝ :=
    ε / (4 * (B + 1))

  have hη :
      0 < η := by
    dsimp only [η]
    positivity

  obtain ⟨ψ, hψ⟩ :=
    exists_h3Schwartz_spectralApprox_norm
      Φ hη

  let Ψ : H3SpectralScalarState :=
    ψ.toLp 2
      (volume : Measure H3FourierPoint3)

  have hψ' :
      ‖Φ - Ψ‖ < η := by
    simpa only [Ψ] using hψ

  have hApprox :
      ∀ q : α,
        dist
            (inner ℂ (F q) Φ).re
            (inner ℂ (F q) Ψ).re
          <
        ε / 4 := by
    intro q

    have hPair :=
      dist_re_inner_right_le_norm_mul_norm_sub
        (F q) Φ Ψ

    have hNormMul :
        ‖F q‖ * ‖Φ - Ψ‖
          ≤
        B * ‖Φ - Ψ‖ := by
      exact
        mul_le_mul_of_nonneg_right
          (hBound q)
          (norm_nonneg (Φ - Ψ))

    have hBLe :
        B ≤ B + 1 := by
      linarith

    have hBPlus :
        B * ‖Φ - Ψ‖
          ≤
        (B + 1) * ‖Φ - Ψ‖ := by
      exact
        mul_le_mul_of_nonneg_right
          hBLe
          (norm_nonneg (Φ - Ψ))

    have hApproxMul :
        (B + 1) * ‖Φ - Ψ‖
          <
        (B + 1) * η := by
      exact
        mul_lt_mul_of_pos_left
          hψ'
          hB1

    have hEtaEq :
        (B + 1) * η
          =
        ε / 4 := by
      dsimp only [η]
      field_simp

    exact
      lt_of_le_of_lt
        hPair
        (lt_of_le_of_lt
          hNormMul
          (lt_of_le_of_lt
            hBPlus
            (by
              rw [hEtaEq] at hApproxMul
              exact hApproxMul)))

  have hΨCont :
      Continuous
        (fun q : α =>
          (inner ℂ (F q) Ψ).re) := by
    dsimp only [Ψ]
    exact hSchwartz ψ

  have hΨAt :=
    Metric.continuousAt_iff.mp
      (hΨCont.continuousAt (x := q₀))
      (ε / 2)
      (by linarith)

  obtain ⟨δ, hδ, hδprop⟩ :=
    hΨAt

  refine ⟨δ, hδ, ?_⟩
  intro q hq

  have hMid :
      dist
          (inner ℂ (F q) Ψ).re
          (inner ℂ (F q₀) Ψ).re
        <
      ε / 2 :=
    hδprop hq

  have hLeft :
      dist
          (inner ℂ (F q) Φ).re
          (inner ℂ (F q) Ψ).re
        <
      ε / 4 :=
    hApprox q

  have hRight :
      dist
          (inner ℂ (F q₀) Ψ).re
          (inner ℂ (F q₀) Φ).re
        <
      ε / 4 := by
    rw [dist_comm]
    exact hApprox q₀

  calc
    dist
        (inner ℂ (F q) Φ).re
        (inner ℂ (F q₀) Φ).re
        ≤
      dist
          (inner ℂ (F q) Φ).re
          (inner ℂ (F q) Ψ).re
        +
      dist
          (inner ℂ (F q) Ψ).re
          (inner ℂ (F q₀) Φ).re :=
      dist_triangle _ _ _
    _ ≤
      dist
          (inner ℂ (F q) Φ).re
          (inner ℂ (F q) Ψ).re
        +
      (dist
          (inner ℂ (F q) Ψ).re
          (inner ℂ (F q₀) Ψ).re
        +
       dist
          (inner ℂ (F q₀) Ψ).re
          (inner ℂ (F q₀) Φ).re) := by
      have hTri :
          dist
              (inner ℂ (F q) Ψ).re
              (inner ℂ (F q₀) Φ).re
            ≤
          dist
              (inner ℂ (F q) Ψ).re
              (inner ℂ (F q₀) Ψ).re
            +
          dist
              (inner ℂ (F q₀) Ψ).re
              (inner ℂ (F q₀) Φ).re :=
        dist_triangle _ _ _
      linarith
    _ <
      ε / 4 + (ε / 2 + ε / 4) := by
      exact
        add_lt_add
          hLeft
          (add_lt_add hMid hRight)
    _ = ε := by
      ring

/-- Weak spectral continuity tested only against Schwartz frequency states. -/
def H3PreterminalCanonicalSpectralSchwartzWeakContinuousOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀
    (j : Fin 3)
    (ψ : SchwartzMap H3FourierPoint3 ℂ),
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          (inner ℂ
            (h3PreterminalTailCanonicalSpectralStateOnElapsed
              hNS ht hEnd hTail q j)
            (ψ.toLp 2
              (volume : Measure H3FourierPoint3))).re)

/-- Schwartz-test weak continuity extends to arbitrary weighted spectral `L²`
tests using the retained uniform H³ tail bound. -/
theorem h3PreterminalCanonicalSpectralWeakContinuousOnElapsed_of_schwartz
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hSchwartz :
      H3PreterminalCanonicalSpectralSchwartzWeakContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalSpectralWeakContinuousOnElapsed
      hNS ht hEnd hTail := by
  intro j Φ

  let F :
      Set.Icc (0 : ℝ) tau →
        H3SpectralScalarState :=
    fun q =>
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q j

  have hTwoE :
      0 ≤ 2 * E := by
    linarith

  have hBound :
      ∀ q : Set.Icc (0 : ℝ) tau,
        ‖F q‖ ≤ 2 * E := by
    intro q

    exact
      (h3SpectralVelocity_coordinate_norm_le
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q)
        j).trans
        (norm_h3PreterminalTailCanonicalSpectralStateOnElapsed_le_twoE
          hNS ht hEnd hE hTail q)

  exact
    continuous_re_inner_of_schwartz_of_uniform_bound
      F
      (2 * E)
      hTwoE
      hBound
      (hSchwartz j)
      Φ

/-- Local weak-plus-norm package can therefore be formed from Schwartz weak
continuity and coordinate-norm continuity. -/
theorem h3PreterminalCanonicalSpectralWeakNormContinuousOnElapsed_of_schwartz_of_norm
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hSchwartz :
      H3PreterminalCanonicalSpectralSchwartzWeakContinuousOnElapsed
        hNS ht hEnd hTail)
    (hNorm :
      H3PreterminalCanonicalSpectralCoordinateNormContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalSpectralWeakNormContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    ⟨
      h3PreterminalCanonicalSpectralWeakContinuousOnElapsed_of_schwartz
        hNS ht hEnd hE hTail hSchwartz,
      hNorm
    ⟩

/-- Restart-radius frontier phrased with only Schwartz weak tests plus scalar
spectral-coordinate norm continuity. -/
def H3PreterminalTailUnitViscositySpectralSchwartzWeakNormContinuityFrontierOnRestartRadius
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
        H3PreterminalCanonicalSpectralSchwartzWeakContinuousOnElapsed
            hNS ht hEnd hTail
          ∧
        H3PreterminalCanonicalSpectralCoordinateNormContinuousOnElapsed
            hNS ht hEnd hTail

/-- Radius-wide Schwartz weak plus norm continuity implies the existing
weak-plus-norm frontier. -/
theorem h3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontierOnRestartRadius_of_schwartz
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hSchwartz :
      H3PreterminalTailUnitViscositySpectralSchwartzWeakNormContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontierOnRestartRadius
      E u T t hNS ht hE hTail := by
  intro q hqPos hEnd

  have hLocal :=
    hSchwartz q hqPos hEnd

  exact
    h3PreterminalCanonicalSpectralWeakNormContinuousOnElapsed_of_schwartz_of_norm
      hNS ht hEnd hE hTail
      hLocal.1
      hLocal.2

/-- Global Schwartz-test weak plus coordinate-norm continuity frontier. -/
def H3PreterminalTailUnitViscositySpectralSchwartzWeakNormContinuityFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscositySpectralSchwartzWeakNormContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- Global Schwartz weak plus norm continuity closes the global weak-plus-norm
frontier. -/
theorem h3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontier_of_schwartz
    (hSchwartz :
      H3PreterminalTailUnitViscositySpectralSchwartzWeakNormContinuityFrontier) :
    H3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontier := by
  intro E hE u T t hNS ht hTail

  exact
    h3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontierOnRestartRadius_of_schwartz
      hNS ht hE hTail
      (hSchwartz E hE u T t hNS ht hTail)

/-- Current continuation theorem with the third-order branch reduced to
Schwartz weak spectral pairings plus scalar spectral-coordinate norm
continuity. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroOldPressureSpectralSchwartzWeakNormClosed
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    (hSchwartz :
      H3PreterminalTailUnitViscositySpectralSchwartzWeakNormContinuityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroOldPressureSpectralWeakNormClosed
      hOld
      (h3PreterminalTailUnitViscositySpectralWeakNormContinuityFrontier_of_schwartz
        hSchwartz)

end

end Euclidean
end Bridge
end PrimeTensor
