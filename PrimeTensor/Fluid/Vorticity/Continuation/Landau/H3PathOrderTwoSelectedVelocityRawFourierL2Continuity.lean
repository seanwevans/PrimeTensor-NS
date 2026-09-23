import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderTwoSelectedVelocityRadialL2Difference
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Raw.Approximation
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Time.Continuity

/-!
# Selected raw Fourier L² continuity

The fourth-radial frequency-splitting estimate has two inputs:

* continuity of the unweighted raw Fourier `L²` selected state;
* local boundedness of the fifth-radial selected state.

The first input is purely formal.  Deweighting the native H³ spectral state is
an `L²` contraction:

    ‖rawL2(F) - rawL2(G)‖ ≤ ‖F - G‖.

Therefore every continuous spectral path remains continuous after raw Fourier
deweighting.  The selected mild physical extension is already globally
continuous in the native H³ spectral state, hence every selected coordinate is
strongly continuous in raw Fourier `L²`.

After this file, the only remaining input to the fourth-radial continuity
argument is a local uniform fifth-radial bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedVelocityRawFourierL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Contractive deweighting preserves continuity of arbitrary H³ spectral
scalar paths. -/
theorem continuous_h3SpectralScalarRawFourierL2_comp
    {α : Type*}
    [TopologicalSpace α]
    (F : α → H3SpectralScalarState)
    (hF : Continuous F) :
    Continuous
      (fun x : α =>
        h3SpectralScalarRawFourierL2 (F x)) := by
  rw [continuous_iff_continuousAt]
  intro x

  change
    Tendsto
      (fun y : α =>
        h3SpectralScalarRawFourierL2 (F y))
      (𝓝 x)
      (𝓝 (h3SpectralScalarRawFourierL2 (F x)))

  rw [tendsto_iff_norm_sub_tendsto_zero]

  have hBase :
      Tendsto
        (fun y : α => ‖F y - F x‖)
        (𝓝 x)
        (𝓝 0) := by
    exact
      tendsto_iff_norm_sub_tendsto_zero.1
        hF.continuousAt

  apply squeeze_zero'
  · exact
      Filter.Eventually.of_forall
        (fun y : α =>
          norm_nonneg
            (h3SpectralScalarRawFourierL2 (F y)
              -
            h3SpectralScalarRawFourierL2 (F x)))
  · exact
      Filter.Eventually.of_forall
        (fun y : α =>
          norm_h3SpectralScalarRawFourierL2_sub_le
            (F y) (F x))
  · exact hBase

/-- Every coordinate of the selected restart mild solution is strongly
continuous in unweighted raw Fourier `L²` on all real elapsed times. -/
theorem continuous_h3SelectedRestartVelocityRawFourierL2
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (j : Fin 3) :
    Continuous
      (fun q : ℝ =>
        h3SpectralScalarRawFourierL2
          ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ q)
            j)) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hW :
      Continuous W :=
    continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hCoord :
      Continuous
        (fun q : ℝ => W q j) :=
    (continuous_apply j).comp hW

  dsimp only [W] at hCoord ⊢

  exact
    continuous_h3SpectralScalarRawFourierL2_comp
      (fun q : ℝ =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ q) j)
      hCoord

/-- Specialized selected-path form used by the order-two fourth-radial
difference estimate. -/
theorem continuous_h3PreterminalSelectedVelocityRawFourierL2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j : Fin 3) :
    Continuous
      (fun q : ℝ =>
        h3SpectralScalarRawFourierL2
          ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              (one_pos : (0 : ℝ) < 1)
              (h3PreterminalSelectedDecoderAnchorState
                hNS ht₀ hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalSelectedDecoderAnchorState_le
                hNS ht₀ hE hTail)
              q)
            j)) := by
  exact
    continuous_h3SelectedRestartVelocityRawFourierL2
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNS ht₀ hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNS ht₀ hE hTail)
      j

/-- Restriction of the selected raw Fourier `L²` path to the strict restart
interval. -/
theorem continuous_h3PreterminalSelectedVelocityRawFourierL2OnRestartRadius
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j : Fin 3) :
    Continuous
      (fun q :
        Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
        h3SpectralScalarRawFourierL2
          ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              (one_pos : (0 : ℝ) < 1)
              (h3PreterminalSelectedDecoderAnchorState
                hNS ht₀ hTail)
              (lt_of_lt_of_le zero_lt_one hE)
              (norm_h3PreterminalSelectedDecoderAnchorState_le
                hNS ht₀ hE hTail)
              (q : ℝ))
            j)) := by
  exact
    (continuous_h3PreterminalSelectedVelocityRawFourierL2
      hNS ht₀ hE hTail j).comp
      continuous_subtype_val

end

end Euclidean
end Bridge
end PrimeTensor
