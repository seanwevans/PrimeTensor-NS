import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeGlobalFixedActualVorticity

/-!
# Physical endpoint escape of one actual vorticity component

The globally fixed native component has actual space-time values above
the indexed lower bound in each near-terminal window. In particular,
the same component is unbounded on every strict terminal subtail.
The conclusion concerns pointwise spatial values, not a time integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- One actual vorticity component has indexed pointwise lower values
arbitrarily close to the endpoint, and is unbounded on every strict
terminal subtail. The component index does not depend on the subtail. -/
def H3TerminalFixedActualVorticityEndpointEscape
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  ∃ i : Fin 3,
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      (∀ n : ℕ,
        ∃ t : ℝ, ∃ x : Point3,
          t ∈ Set.Ioo b T ∧
          t ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
          (n : ℝ) - 2 <
            |h3NativeActualVorticityComponentAt u i t x|) ∧
      (∀ M : ℝ,
        ∃ t : ℝ, ∃ x : Point3,
          t ∈ Set.Ioo b T ∧
          M < |h3NativeActualVorticityComponentAt u i t x|)

/-- Discarding the native auxiliary data yields a physical pointwise
endpoint escape with the same component on every terminal subtail. -/
theorem fixedActualVorticity_endpointEscape_of_globalNativeRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hGlobal :
      H3TerminalPositiveGrowthGlobalFixedActualVorticityRateData u a T) :
    H3TerminalFixedActualVorticityEndpointEscape u a T := by
  obtain ⟨p, sCurl, sGradient, i, hEvery⟩ := hGlobal
  refine ⟨i, ?_⟩
  intro b hb
  obtain ⟨τ, y, z, hData, hBound, hTop⟩ := hEvery b hb
  constructor
  · intro n
    exact ⟨τ n, z n, (hData.1 n).1,
      (hData.1 n).2.1, hBound n⟩
  · intro M
    obtain ⟨n, hn⟩ :=
      (hTop.eventually (eventually_gt_atTop M)).exists
    exact ⟨τ n, z n, (hData.1 n).1, hn⟩

/-- With a raw dissipation ceiling on one chosen strict subtail,
hypothetical nonextension forces one actual vorticity component to
escape pointwise on every terminal subtail. -/
theorem positiveGrowth_fixedActualVorticity_endpointEscape_of_rawCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b₀ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb₀ : b₀ ∈ Set.Ioo a T)
    (hRawCeiling : H3TerminalNativeUniformRawSubexponentialCeiling u b₀ T) :
    H3TerminalFixedActualVorticityEndpointEscape u a T := by
  exact fixedActualVorticity_endpointEscape_of_globalNativeRate
    (positiveGrowth_globalFixedActualVorticity_of_rawCeiling_on_one_subtail
      hH3 hNoExtension hClass hb₀ hRawCeiling)

/-- Endpoint escape rules out a uniform space-time bound for the
selected component on any strict terminal subtail. -/
theorem fixedActualVorticity_noUniformTailCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hEscape : H3TerminalFixedActualVorticityEndpointEscape u a T) :
    ∃ i : Fin 3,
      ∀ b : ℝ, b ∈ Set.Ioo a T →
        ¬ ∃ C : ℝ,
          ∀ t : ℝ, t ∈ Set.Ioo b T →
            ∀ x : Point3,
              |h3NativeActualVorticityComponentAt u i t x| ≤ C := by
  obtain ⟨i, hEvery⟩ := hEscape
  refine ⟨i, ?_⟩
  intro b hb hCeiling
  obtain ⟨C, hC⟩ := hCeiling
  obtain ⟨t, x, ht, hLower⟩ := (hEvery b hb).2 C
  exact (not_lt_of_ge (hC t ht x)) hLower

/-- Neutral alternative: smooth continuation or physical endpoint
escape of one fixed actual vorticity component under the stated raw
dissipation ceiling. -/
theorem smoothContinuationExtension_or_fixedActualVorticity_endpointEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b₀ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb₀ : b₀ ∈ Set.Ioo a T)
    (hRawCeiling : H3TerminalNativeUniformRawSubexponentialCeiling u b₀ T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    H3TerminalFixedActualVorticityEndpointEscape u a T := by
  rcases
      smoothContinuationExtension_or_globalFixedActualVorticity_of_rawCeiling
        hH3 hClass hb₀ hRawCeiling with hExtension | hGlobal
  · exact Or.inl hExtension
  · exact Or.inr
      (fixedActualVorticity_endpointEscape_of_globalNativeRate hGlobal)

end

end Euclidean
end Bridge
end PrimeTensor
