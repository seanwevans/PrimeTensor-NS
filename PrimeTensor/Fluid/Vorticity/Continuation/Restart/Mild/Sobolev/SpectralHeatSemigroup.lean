import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SpectralHeatCLM

/-!
# Semigroup law for spectral H³ heat evolution

The heat action on the weighted spectral solver state has now been packaged as
a contractive real continuous linear map.  This file records the exact
nonnegative-time semigroup law in three equivalent forms:

* scalar weighted Fourier state;
* three-component spectral velocity state;
* composition of the bundled continuous linear maps.

This is the algebraic input needed for the Duhamel restart identity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SpectralHeatSemigroup
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Scalar semigroup law -/

/--
Nonnegative-time semigroup law on one weighted Fourier H³ scalar state.
-/
theorem h3SpectralScalarHeatApplyNN_add_time
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (a b : ℝ≥0)
    (F : H3SpectralScalarState) :
    h3SpectralScalarHeatApplyNN ν hν (a + b) F
      =
    h3SpectralScalarHeatApplyNN ν hν b
      (h3SpectralScalarHeatApplyNN ν hν a F) := by
  unfold h3SpectralScalarHeatApplyNN
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3HeatFrequencyApplyNN_coeFn
      ν hν (a + b) F,
    h3HeatFrequencyApplyNN_coeFn
      ν hν b (h3HeatFrequencyApplyNN ν hν a F),
    h3HeatFrequencyApplyNN_coeFn
      ν hν a F
  ] with ξ hab hb ha
  rw [hab, hb, ha]
  have hsym :
      h3HeatFourierSymbol ν ((a + b : ℝ≥0) : ℝ) ξ
        =
      h3HeatFourierSymbol ν (b : ℝ) ξ *
        h3HeatFourierSymbol ν (a : ℝ) ξ := by
    simpa only [NNReal.coe_add] using
      h3HeatFourierSymbol_add
        ν (a : ℝ) (b : ℝ) ξ
  rw [hsym]
  ring

/-! ## Velocity semigroup law -/

/--
Nonnegative-time semigroup law on the three-component spectral H³ velocity
state.
-/
theorem h3SpectralVelocityHeatApplyNN_add_time
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (a b : ℝ≥0)
    (U : H3SpectralVelocityState) :
    h3SpectralVelocityHeatApplyNN ν hν (a + b) U
      =
    h3SpectralVelocityHeatApplyNN ν hν b
      (h3SpectralVelocityHeatApplyNN ν hν a U) := by
  funext j
  exact
    h3SpectralScalarHeatApplyNN_add_time
      ν hν a b (U j)

/-! ## Continuous-linear semigroup law -/

/--
The bundled spectral velocity heat operators compose according to time
addition.
-/
theorem h3SpectralVelocityHeatCLM_add_time
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (a b : ℝ≥0) :
    h3SpectralVelocityHeatCLM ν hν (a + b)
      =
    (h3SpectralVelocityHeatCLM ν hν b).comp
      (h3SpectralVelocityHeatCLM ν hν a) := by
  apply ContinuousLinearMap.ext
  intro U
  simp only [
    ContinuousLinearMap.comp_apply,
    h3SpectralVelocityHeatCLM_apply
  ]
  exact
    h3SpectralVelocityHeatApplyNN_add_time
      ν hν a b U

end

end Euclidean
end Bridge
end PrimeTensor
