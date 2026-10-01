import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Enstrophy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Native.Residual.Spatial.Escape.Dichotomy

/-!
# Spatial geometry of the pure physical vorticity/enstrophy escape sequence

The pure physical terminal sequence already carries

* shrinking localization toward `T`;
* minimal-vorticity-envelope escape;
* one fixed actual vorticity component with one fixed orientation;
* quadratic pointwise-enstrophy growth.

This file classifies the spatial behavior of the selected points without
changing that quantitative sequence.  If their range is bounded, properness of
`Point3` gives a cofinal subsequence converging to one finite spatial cluster
point.  If their range is unbounded, the existing selected-point escape theorem
gives a cofinal refinement whose distance from the origin tends to infinity.

Thus the physical vorticity/enstrophy obstruction has a clean geometric
alternative: finite-core concentration or spatial escape.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalMinimalVorticityPhysicalSpatialGeometry
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A selected spatial sequence has a finite spatial cluster point on a cofinal
refinement. -/
def H3TerminalSelectedPointHasFiniteCluster
    (z : ℕ → Point3) : Prop :=
  ∃ y : Point3,
    ∃ k : ℕ → ℕ,
      Tendsto k atTop atTop
        ∧
      Tendsto
        (fun n : ℕ => z (k n))
        atTop
        (𝓝 y)

/-- Pure physical terminal vorticity/enstrophy escape together with the
spatial alternative for its selected points.  The quantitative bounds remain
on the original sequence; the geometry is read on a cofinal refinement. -/
def H3TerminalMinimalVorticityPhysicalSpatialGeometry
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) : Prop :=
  ∃ i : Fin 3,
    ∃ s : H3TerminalOrientation,
      ∃ τ : ℕ → ℝ,
        ∃ z : ℕ → Point3,
          (∀ n : ℕ,
            τ n ∈
                Set.Ioo
                  (T - (1 : ℝ) / ((n : ℝ) + 1))
                  T
              ∧
            (n : ℝ) < h3MinimalVorticityEnvelopeAt u (τ n))
            ∧
          Tendsto τ atTop (𝓝 T)
            ∧
          Tendsto
            (fun n : ℕ => h3MinimalVorticityEnvelopeAt u (τ n))
            atTop atTop
            ∧
          (∀ n : ℕ,
            (n : ℝ) <
              h3TerminalOrientedValue
                s
                (h3NativeActualVorticityComponentAt u i (τ n) (z n)))
            ∧
          Tendsto
            (fun n : ℕ =>
              h3TerminalOrientedValue
                s
                (h3NativeActualVorticityComponentAt u i (τ n) (z n)))
            atTop atTop
            ∧
          (∀ n : ℕ,
            (n : ℝ) ^ 2 <
              realEnstrophyDensity
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                (τ n) (z n))
            ∧
          Tendsto
            (fun n : ℕ =>
              realEnstrophyDensity
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                (τ n) (z n))
            atTop atTop
            ∧
          (
            H3TerminalSelectedPointHasFiniteCluster z
              ∨
            H3TerminalSelectedPointEscapesToInfinity z
          )

/-- Every physical enstrophy escape sequence admits the finite-cluster versus
spatial-infinity dichotomy. -/
theorem h3TerminalMinimalVorticityPhysicalSpatialGeometry_of_enstrophyEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hEscape :
      H3TerminalMinimalVorticityPhysicalEnstrophyEscapeSequence u T) :
    H3TerminalMinimalVorticityPhysicalSpatialGeometry u T := by
  classical

  obtain
    ⟨
      i,
      s,
      τ,
      z,
      hData,
      hTauTendsto,
      hEnvelopeTendsto,
      hOrientedLower,
      hOrientedTendsto,
      hEnstrophyLower,
      hEnstrophyTendsto
    ⟩ :=
    hEscape

  by_cases hBounded :
      Bornology.IsBounded (Set.range z)

  · have hZMem :
        ∀ n : ℕ,
          z n ∈ Set.range z := by
      intro n
      exact ⟨n, rfl⟩

    obtain
      ⟨
        y,
        _hyMem,
        k,
        hKStrict,
        hSpatialLimit
      ⟩ :=
      tendsto_subseq_of_bounded
        hBounded
        hZMem

    exact
      ⟨
        i,
        s,
        τ,
        z,
        hData,
        hTauTendsto,
        hEnvelopeTendsto,
        hOrientedLower,
        hOrientedTendsto,
        hEnstrophyLower,
        hEnstrophyTendsto,
        Or.inl
          ⟨
            y,
            k,
            hKStrict.tendsto_atTop,
            hSpatialLimit
          ⟩
      ⟩

  · exact
      ⟨
        i,
        s,
        τ,
        z,
        hData,
        hTauTendsto,
        hEnvelopeTendsto,
        hOrientedLower,
        hOrientedTendsto,
        hEnstrophyLower,
        hEnstrophyTendsto,
        Or.inr
          (selectedPointEscapesToInfinity_of_unbounded hBounded)
      ⟩

/-- Hypothetical nonextension forces the physical vorticity/enstrophy escape
sequence into the finite-core versus spatial-infinity geometric alternative. -/
theorem exists_terminal_minimalVorticityPhysicalSpatialGeometry_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalMinimalVorticityPhysicalSpatialGeometry u T := by
  exact
    h3TerminalMinimalVorticityPhysicalSpatialGeometry_of_enstrophyEscape
      (exists_terminal_minimalVorticityPhysicalEnstrophyEscapeSequence_of_noH3PathExtension
        hH3 hNoExtension hClass)

/-- Neutral formulation: either the H³ path continues smoothly, or the pure
physical vorticity/enstrophy escape sequence has finite-cluster or
spatial-infinity geometry. -/
theorem smoothContinuationExtension_or_terminal_minimalVorticityPhysicalSpatialGeometry
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    H3TerminalMinimalVorticityPhysicalSpatialGeometry u T := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact
      Or.inr
        (exists_terminal_minimalVorticityPhysicalSpatialGeometry_of_noH3PathExtension
          hH3 hExtension hClass)

end

end Euclidean
end Bridge
end PrimeTensor
