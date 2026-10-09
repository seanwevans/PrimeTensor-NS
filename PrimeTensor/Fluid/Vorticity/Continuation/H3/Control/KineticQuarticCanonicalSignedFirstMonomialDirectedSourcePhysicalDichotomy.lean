import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceCriticalClocks

/-!
# Physical dichotomy for a fixed signed directed H³ terminal source

The ten-source cofinal obstruction has one gradient-excess source (index zero)
and nine concrete ordered first-monomial velocity channels.  The preceding
critical-clock theorem synchronizes the chosen fixed index with a single
physical sequence `τ(n) → T` and three proven terminal PDE clocks.

This file resolves the *identity* of the signed source without an unproved
gradient-absorption hypothesis. Under hypothetical nonextension, one of the
following alternatives holds on exactly that same selected sequence:

* gradient: (24 C₁ sqrt(E) E₃ - D)/(9 E) → +∞;
* velocity: for one fixed ordered pair `(j,r)`, `(-2 Q(j,r))/E → +∞`.

The factor two treats all nine channels uniformly: diagonal components have
weight nine and off-diagonal components weight eighteen in the source.

Both alternatives retain divergence of the top characteristic frequency and
the three critical-time bounds.  No sign is assumed on a velocity component,
and neither alternative is declared impossible by this theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- The ordered physical velocity axes associated with any nonzero member of
the fixed ten-source index.  Index zero is assigned an arbitrary pair only so
the map is total; it is excluded in all subsequent velocity statements. -/
private def h3PathCanonicalDirectedSourcePair
    (i : Fin 10) :
    PrimeTensor.Axis Depth.three × PrimeTensor.Axis Depth.three :=
  match i.val with
  | 1 => (xAxis, xAxis)
  | 2 => (yAxis, yAxis)
  | 3 => (zAxis, zAxis)
  | 4 => (xAxis, yAxis)
  | 5 => (yAxis, xAxis)
  | 6 => (xAxis, zAxis)
  | 7 => (zAxis, xAxis)
  | 8 => (yAxis, zAxis)
  | _ => (zAxis, yAxis)

/-- The exact nine weights convert an arbitrarily adverse normalized fixed
source into a uniformly weighted *physical* ordered monomial deficit.
No symmetry or additional PDE sign estimate is used. -/
private theorem h3PathCanonical_directedSource_large_forces_orderedDeficit
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) (i : Fin 10) (hi : i ≠ 0) (R : ℝ)
    (hR : 0 ≤ R)
    (hLarge :
      9 * R * velocityH3EnergyAt u t <
        h3PathCanonicalJointDirectedTenSourceAt u t i) :
    R * velocityH3EnergyAt u t <
      -(2 * h3PathCanonicalFirstMonomialComponentAt u t
        (h3PathCanonicalDirectedSourcePair i).1
        (h3PathCanonicalDirectedSourcePair i).2) := by
  have hRE : 0 ≤ R * velocityH3EnergyAt u t :=
    mul_nonneg hR
      (le_trans zero_le_one (one_le_velocityH3EnergyAt u t))
  fin_cases i
  · exact (hi rfl).elim
  all_goals
    -- `dsimp` alone leaves the natural-number `match` opaque.  Full `simp`
    -- reduces each concrete Fin index and its ordered axis pair.
    simp [h3PathCanonicalJointDirectedTenSourceAt,
      h3PathCanonicalDirectedSourcePair] at hLarge ⊢ <;>
      nlinarith only [hLarge, hRE]

/-- If the selected fixed source is an ordered velocity channel, the actual
negative signed velocity monomial grows without bound relative to full H³
energy on exactly the source's original time sequence. -/
private theorem h3PathCanonical_directedSource_velocityDeficit_tendsto
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (i : Fin 10) (hi : i ≠ 0) (τ : ℕ → ℝ)
    (hSourceT :
      Tendsto
        (fun n : ℕ =>
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n))) atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n)
          (h3PathCanonicalDirectedSourcePair i).1
          (h3PathCanonicalDirectedSourcePair i).2) /
            velocityH3EnergyAt u (τ n)) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro M
  let R : ℝ := max M 0
  have hR : 0 ≤ R := le_max_right M 0
  have hBig : ∀ᶠ n : ℕ in atTop,
      R + 1 ≤
        h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
          (9 * velocityH3EnergyAt u (τ n)) :=
    (tendsto_atTop.1 hSourceT) (R + 1)
  filter_upwards [hBig] with n hn
  have hE : 0 < velocityH3EnergyAt u (τ n) :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u (τ n))
  have hDen : 0 < 9 * velocityH3EnergyAt u (τ n) := by
    positivity
  have hRatio : R <
      h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
        (9 * velocityH3EnergyAt u (τ n)) := by
    linarith only [hn]
  have hScaled := (lt_div_iff₀ hDen).mp hRatio
  have hRaw :
      9 * R * velocityH3EnergyAt u (τ n) <
        h3PathCanonicalJointDirectedTenSourceAt u (τ n) i := by
    calc
      9 * R * velocityH3EnergyAt u (τ n) =
          R * (9 * velocityH3EnergyAt u (τ n)) := by ring
      _ < _ := hScaled
  have hNegative :=
    h3PathCanonical_directedSource_large_forces_orderedDeficit
      u (τ n) i hi R hR hRaw
  have hDiv : R <
      -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n)
        (h3PathCanonicalDirectedSourcePair i).1
        (h3PathCanonicalDirectedSourcePair i).2) /
          velocityH3EnergyAt u (τ n) :=
    (lt_div_iff₀ hE).2 hNegative
  exact le_trans (le_max_left M 0) (le_of_lt hDiv)

/-- A fixed source, the same physical terminal times, and the three verified
critical clocks admit a genuine two-way signed alternative.  The gradient
excess or one fixed *ordered* velocity monomial has an unbounded normalized
adverse contribution; neither case is assumed or excluded. -/
theorem h3PathCanonical_fixedDirectedSource_physicalDichotomy_criticalClocks
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ (i : Fin 10) (τ : ℕ → ℝ),
      (∀ n : ℕ, τ n ∈ Set.Ioo
        (T - (1 : ℝ) / ((n : ℝ) + 1)) T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      Tendsto
        (fun n : ℕ =>
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n))) atTop atTop ∧
      Tendsto (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ n))
        atTop atTop ∧
      (∀ᶠ n : ℕ in atTop,
        h3PathCanonicalDirectedCriticalClocksAt u T b (τ n)) ∧
      ((i = 0 ∧
          Tendsto
            (fun n : ℕ =>
              (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
                Real.sqrt (velocityH3EnergyAt u (τ n))) *
                velocityH3Energy3At u (τ n) -
                velocityH3DissipationAt u (τ n)) /
                (9 * velocityH3EnergyAt u (τ n))) atTop atTop) ∨
        (i ≠ 0 ∧
          ∃ j r : PrimeTensor.Axis Depth.three,
            Tendsto
              (fun n : ℕ =>
                -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
                  velocityH3EnergyAt u (τ n)) atTop atTop)) := by
  obtain ⟨i, τ, hNear, hτT, hSourceT, hFreqT, hClocks⟩ :=
    h3PathCanonical_fixedDirectedSource_criticalClocks_sameSequence
      hH3 hNoExtension hClass hb
  refine ⟨i, τ, hNear, hτT, hSourceT, hFreqT, hClocks, ?_⟩
  by_cases hi : i = 0
  · left
    refine ⟨hi, ?_⟩
    subst i
    -- Evaluate the closed index-zero match, not just unfold its definition.
    simpa [h3PathCanonicalJointDirectedTenSourceAt] using hSourceT
  · right
    refine ⟨hi,
      (h3PathCanonicalDirectedSourcePair i).1,
      (h3PathCanonicalDirectedSourcePair i).2, ?_⟩
    exact h3PathCanonical_directedSource_velocityDeficit_tendsto
      u i hi τ hSourceT

end
end Euclidean
end Bridge
end PrimeTensor
