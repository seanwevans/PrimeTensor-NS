import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.WeakCompactZero

/-!
# Ordered-third endpoint continuity: reduce the strong topology to scalar H³ energy continuity

`WeakCompactZero` closes weak weighted-H³ continuity from the zeroth physical
`L²` branch under the old-pressure frontier.

The remaining coordinate-norm formulation can be sharpened further.  The
project's solver state uses the finite sup norm

    H3SpectralVelocityState = Fin 3 → H3SpectralScalarState,

so we do not treat the complete velocity state itself as a Hilbert space.
Instead use the already-defined Hilbert square-energy observable

    h3SpectralVelocitySquareEnergy U = ∑ j, ‖U j‖².

For a fixed base time `q₀`, weak continuity gives continuity of

    ∑ j Re ⟪U_j(q), U_j(q₀)⟫,

and scalar square-energy continuity gives continuity of `∑ j ‖U_j(q)‖²`.
Hence the exact finite identity

    ∑ j ‖U_j(q) - U_j(q₀)‖²
      =
    E(q)
      - 2 ∑ j Re ⟪U_j(q), U_j(q₀)⟫
      + E(q₀)

forces the total squared coordinate distance to zero.  Every coordinate norm,
and therefore the finite sup norm, is bounded by the square root of this
quantity.  Thus the full weighted spectral state is strongly continuous.

Finally, the encoder already proves the exact snapshot identity

    1 + h3SpectralVelocitySquareEnergy U(q)
      = velocityH3EnergyAt u (t+q).

Therefore ordinary scalar continuity of the physical H³ energy profile closes
the remaining strong-topology input.

After this file the current continuation boundary consists of exactly two
independent analytic fronts:

* old preterminal pressure-gradient mass;
* scalar physical H³ energy continuity on the retained old tail.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityThirdEnergyContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Continuity of the finite Hilbert square-energy observable of the weighted
spectral velocity state. -/
def H3PreterminalCanonicalSpectralSquareEnergyContinuousOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  Continuous
    (fun q : Set.Icc (0 : ℝ) tau =>
      h3SpectralVelocitySquareEnergy
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q))

/-- Coordinatewise weak continuity plus continuity of the single total
square-energy observable implies strong continuity in the project's finite sup
norm. -/
theorem h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_weak_of_squareEnergy
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
    (hEnergy :
      H3PreterminalCanonicalSpectralSquareEnergyContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalSpectralStateContinuousOnElapsed
      hNS ht hEnd hTail := by
  unfold H3PreterminalCanonicalSpectralStateContinuousOnElapsed

  rw [continuous_iff_continuousAt]
  intro q₀

  apply tendsto_iff_norm_sub_tendsto_zero.2

  let U :
      Set.Icc (0 : ℝ) tau →
        H3SpectralVelocityState :=
    fun q =>
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q

  let P :
      Set.Icc (0 : ℝ) tau → ℝ :=
    fun q =>
      ∑ j : Fin 3,
        (inner ℂ (U q j) (U q₀ j)).re

  let D :
      Set.Icc (0 : ℝ) tau → ℝ :=
    fun q =>
      ∑ j : Fin 3,
        ‖U q j - U q₀ j‖ ^ 2

  have hP :
      Continuous P := by
    dsimp only [P]
    apply continuous_finset_sum
    intro j hj
    exact hWeak j (U q₀ j)

  have hDFormula :
      ∀ q : Set.Icc (0 : ℝ) tau,
        D q
          =
        h3SpectralVelocitySquareEnergy (U q)
          -
        2 * P q
          +
        h3SpectralVelocitySquareEnergy (U q₀) := by
    intro q

    dsimp only [D, P]
    unfold h3SpectralVelocitySquareEnergy

    calc
      (∑ j : Fin 3, ‖U q j - U q₀ j‖ ^ 2)
          =
        ∑ j : Fin 3,
          (‖U q j‖ ^ 2
            -
           2 * (inner ℂ (U q j) (U q₀ j)).re
            +
           ‖U q₀ j‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact norm_sub_sq (𝕜 := ℂ) (U q j) (U q₀ j)
      _ =
        (∑ j : Fin 3, ‖U q j‖ ^ 2)
          -
        2 * (∑ j : Fin 3,
          (inner ℂ (U q j) (U q₀ j)).re)
          +
        (∑ j : Fin 3, ‖U q₀ j‖ ^ 2) := by
        rw [Finset.sum_add_distrib]
        rw [Finset.sum_sub_distrib]
        rw [← Finset.mul_sum]

  have hD :
      Continuous D := by
    have hEq :
        D
          =
        (fun q : Set.Icc (0 : ℝ) tau =>
          h3SpectralVelocitySquareEnergy (U q)
            -
          2 * P q
            +
          h3SpectralVelocitySquareEnergy (U q₀)) := by
      funext q
      exact hDFormula q

    rw [hEq]

    exact
      ((hEnergy.sub
          (continuous_const.mul hP)).add
        continuous_const)

  have hDZero :
      D q₀ = 0 := by
    dsimp only [D]
    simp

  have hDTendstoRaw :
      Tendsto D
        (𝓝 q₀)
        (𝓝 (D q₀)) :=
    hD.continuousAt

  have hDTendsto :
      Tendsto D
        (𝓝 q₀)
        (𝓝 0) := by
    rw [hDZero] at hDTendstoRaw
    exact hDTendstoRaw

  have hSqrtAt :
      Tendsto
        Real.sqrt
        (𝓝 (0 : ℝ))
        (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt

  have hSqrt :
      Tendsto
        (fun q : Set.Icc (0 : ℝ) tau =>
          Real.sqrt (D q))
        (𝓝 q₀)
        (𝓝 0) := by
    have hComp :
        Tendsto
          (fun q : Set.Icc (0 : ℝ) tau =>
            Real.sqrt (D q))
          (𝓝 q₀)
          (𝓝 (Real.sqrt 0)) :=
      hSqrtAt.comp hDTendsto

    simpa only [Real.sqrt_zero] using hComp

  have hNormBound :
      ∀ q : Set.Icc (0 : ℝ) tau,
        ‖U q - U q₀‖
          ≤
        Real.sqrt (D q) := by
    intro q

    have hDNonneg :
        0 ≤ D q := by
      dsimp only [D]
      exact
        Finset.sum_nonneg
          (fun j hj => sq_nonneg _)

    apply
      (pi_norm_le_iff_of_nonneg
        (Real.sqrt_nonneg (D q))).2

    intro j

    have hCoordSq :
        ‖U q j - U q₀ j‖ ^ 2
          ≤
        D q := by
      dsimp only [D]
      exact
        Finset.single_le_sum
          (fun k hk =>
            sq_nonneg
              ‖U q k - U q₀ k‖)
          (Finset.mem_univ j)

    have hSqrtSq :
        (Real.sqrt (D q)) ^ 2
          =
        D q :=
      Real.sq_sqrt hDNonneg

    have hCoord :
        ‖U q j - U q₀ j‖
          ≤
        Real.sqrt (D q) := by
      have hLeft :
          0 ≤ ‖U q j - U q₀ j‖ :=
        norm_nonneg _
      have hRight :
          0 ≤ Real.sqrt (D q) :=
        Real.sqrt_nonneg _
      nlinarith

    simpa only [Pi.sub_apply] using hCoord

  have hNormNonneg :
      ∀ q : Set.Icc (0 : ℝ) tau,
        0 ≤ ‖U q - U q₀‖ :=
    fun q => norm_nonneg _

  have hNormTendsto :
      Tendsto
        (fun q : Set.Icc (0 : ℝ) tau =>
          ‖U q - U q₀‖)
        (𝓝 q₀)
        (𝓝 0) :=
    squeeze_zero
      hNormNonneg
      hNormBound
      hSqrt

  exact hNormTendsto

/-- The local old-pressure frontier supplies weak H³ continuity; total
square-energy continuity then closes strong weighted spectral continuity. -/
theorem h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_oldPressure_of_squareEnergy
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hOld :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail)
    (hEnergy :
      H3PreterminalCanonicalSpectralSquareEnergyContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalSpectralStateContinuousOnElapsed
      hNS ht hEnd hTail := by
  have hCompact :
      H3PreterminalCanonicalSpectralSmoothCompactWeakContinuousOnElapsed
        hNS ht hEnd hTail :=
    h3PreterminalCanonicalSpectralSmoothCompactWeakContinuousOnElapsed_of_oldPressure
      hNS ht htau hEnd hE hTail hOld

  have hWeak :
      H3PreterminalCanonicalSpectralWeakContinuousOnElapsed
        hNS ht hEnd hTail :=
    h3PreterminalCanonicalSpectralWeakContinuousOnElapsed_of_smoothCompact
      hNS ht hEnd hE hTail hCompact

  exact
    h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_weak_of_squareEnergy
      hNS ht hEnd hTail hWeak hEnergy

/-- Continuity of the ordinary scalar physical H³ energy profile on one
elapsed interval. -/
def H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  Continuous
    (fun q : Set.Icc (0 : ℝ) tau =>
      velocityH3EnergyAt
        u
        (t + (q : ℝ)))

/-- The encoder's exact energy identity turns physical H³ energy continuity
into weighted spectral square-energy continuity. -/
theorem h3PreterminalCanonicalSpectralSquareEnergyContinuousOnElapsed_of_physicalEnergy
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPhysical :
      H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalSpectralSquareEnergyContinuousOnElapsed
      hNS ht hEnd hTail := by
  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3SpectralVelocitySquareEnergy
          (h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail q))
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        velocityH3EnergyAt
            u
            (t + (q : ℝ))
          -
        1) := by
    funext q

    have hExact :
        1
            +
          h3SpectralVelocitySquareEnergy
            (h3PreterminalTailCanonicalSpectralStateOnElapsed
              hNS ht hEnd hTail q)
          =
        velocityH3EnergyAt
          u
          (t + (q : ℝ)) := by
      unfold h3PreterminalTailCanonicalSpectralStateOnElapsed

      exact
        one_add_h3SpectralVelocitySquareEnergy_velocityH3SpectralStateAt_eq
          (h3PreterminalTailFourierCompatibleOnElapsed
            hNS ht hEnd hTail q)

    linarith

  unfold H3PreterminalCanonicalSpectralSquareEnergyContinuousOnElapsed

  rw [hEq]

  exact hPhysical.sub continuous_const

/-- Radius-wide scalar physical-H³-energy continuity frontier. -/
def H3PreterminalTailUnitViscosityPhysicalH3EnergyContinuityFrontierOnRestartRadius
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
        H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed
          hNS ht hEnd hTail

/-- Global scalar physical-H³-energy continuity frontier. -/
def H3PreterminalTailUnitViscosityPhysicalH3EnergyContinuityFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityPhysicalH3EnergyContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- Old-pressure control plus scalar physical H³ energy continuity closes the
global strong spectral-continuity frontier. -/
theorem h3PreterminalTailUnitViscositySpectralContinuityFrontier_of_oldPressure_of_physicalH3Energy
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    (hEnergy :
      H3PreterminalTailUnitViscosityPhysicalH3EnergyContinuityFrontier) :
    H3PreterminalTailUnitViscositySpectralContinuityFrontier := by
  intro E hE u T t hNS ht hTail
  intro q hqPos hEnd

  have hOldLocal :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail :=
    hOld E hE u T t hNS ht hTail q hqPos hEnd

  have hPhysical :
      H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed
        hNS ht hEnd hTail :=
    hEnergy E hE u T t hNS ht hTail q hqPos hEnd

  have hSquare :
      H3PreterminalCanonicalSpectralSquareEnergyContinuousOnElapsed
        hNS ht hEnd hTail :=
    h3PreterminalCanonicalSpectralSquareEnergyContinuousOnElapsed_of_physicalEnergy
      hNS ht hEnd hTail hPhysical

  exact
    h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_oldPressure_of_squareEnergy
      hNS ht hqPos hEnd hE hTail hOldLocal hSquare

/-- Current continuation theorem with the third-order topology reduced to one
scalar physical H³ energy-continuity frontier. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroOldPressurePhysicalH3EnergyClosed
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    (hEnergy :
      H3PreterminalTailUnitViscosityPhysicalH3EnergyContinuityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroOldPressureSpectralContinuityClosed
      hOld
      (h3PreterminalTailUnitViscositySpectralContinuityFrontier_of_oldPressure_of_physicalH3Energy
        hOld hEnergy)

end

end Euclidean
end Bridge
end PrimeTensor
