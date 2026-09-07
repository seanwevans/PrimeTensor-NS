import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Evolution.IntegralEquation
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Heat.Intertwining
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.Heat.Semigroup

/-!
# Physical L² temporal admissibility: quotient-safe Fourier L² heat semigroup

The endpoint integral equation now lives entirely in raw Fourier `L²`.  The
next semigroup step should therefore stay in the quotient space rather than
return to fixed-frequency representatives.

This file gives the existing heat multiplier a raw-Fourier-`L²` interface:

* a three-component raw `L²` state;
* fixed-time heat evolution and its bundled real continuous linear map;
* strong continuity and the nonnegative-time semigroup law;
* exact commutation of H³ deweighting with heat evolution.

The last identity is the key bridge.  It says that whenever a weighted H³
spectral state is available as generator-domain data, evolving it first and
then stripping the H³ weight is exactly the same as evolving its raw `L²`
class by the quotient-safe heat semigroup.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2HeatSemigroup
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Three-component quotient-safe raw Fourier `L²` state. -/
abbrev H3RawFourierL2FinVectorState : Type :=
  Fin 3 → H3FourierComplexL2

/-- Coordinatewise removal of the exact H³ Sobolev weight. -/
noncomputable def h3SpectralFinVectorRawFourierL2
    (U : H3SpectralFinVectorState) :
    H3RawFourierL2FinVectorState :=
  fun i : Fin 3 => h3SpectralScalarRawFourierL2 (U i)

@[simp]
theorem h3SpectralFinVectorRawFourierL2_apply
    (U : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3SpectralFinVectorRawFourierL2 U i
      =
    h3SpectralScalarRawFourierL2 (U i) :=
  rfl

/-- Raw Fourier `L²` heat evolution, coordinatewise on velocity. -/
noncomputable def h3RawFourierL2HeatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U : H3RawFourierL2FinVectorState) :
    H3RawFourierL2FinVectorState :=
  h3SpectralVelocityHeatApplyNN ν hν t U

@[simp]
theorem h3RawFourierL2HeatApplyNN_apply
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U : H3RawFourierL2FinVectorState)
    (i : Fin 3) :
    h3RawFourierL2HeatApplyNN ν hν t U i
      =
    h3HeatFrequencyApplyNN ν hν t (U i) :=
  rfl

/-- Fixed-time raw Fourier `L²` heat evolution as a contractive real CLM. -/
noncomputable def h3RawFourierL2HeatCLM
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0) :
    H3RawFourierL2FinVectorState →L[ℝ]
      H3RawFourierL2FinVectorState :=
  h3SpectralVelocityHeatCLM ν hν t

@[simp]
theorem h3RawFourierL2HeatCLM_apply
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U : H3RawFourierL2FinVectorState) :
    h3RawFourierL2HeatCLM ν hν t U
      =
    h3RawFourierL2HeatApplyNN ν hν t U :=
  rfl

/-- Strong continuity in nonnegative time for every fixed raw Fourier `L²`
velocity state. -/
theorem continuous_h3RawFourierL2HeatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (U : H3RawFourierL2FinVectorState) :
    Continuous
      (fun t : ℝ≥0 => h3RawFourierL2HeatApplyNN ν hν t U) := by
  exact continuous_h3SpectralVelocityHeatApplyNN ν hν U

/-- Nonnegative-time semigroup law on raw Fourier `L²` velocity states. -/
theorem h3RawFourierL2HeatApplyNN_add_time
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (a b : ℝ≥0)
    (U : H3RawFourierL2FinVectorState) :
    h3RawFourierL2HeatApplyNN ν hν (a + b) U
      =
    h3RawFourierL2HeatApplyNN ν hν b
      (h3RawFourierL2HeatApplyNN ν hν a U) := by
  exact h3SpectralVelocityHeatApplyNN_add_time ν hν a b U

/-- Bundled continuous-linear semigroup law on raw Fourier `L²`. -/
theorem h3RawFourierL2HeatCLM_add_time
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (a b : ℝ≥0) :
    h3RawFourierL2HeatCLM ν hν (a + b)
      =
    (h3RawFourierL2HeatCLM ν hν b).comp
      (h3RawFourierL2HeatCLM ν hν a) := by
  exact h3SpectralVelocityHeatCLM_add_time ν hν a b

/-- H³ deweighting commutes exactly with the quotient-safe heat semigroup. -/
theorem h3SpectralFinVectorRawFourierL2_heatApplyNN
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U : H3SpectralFinVectorState) :
    h3SpectralFinVectorRawFourierL2
        (h3SpectralVelocityHeatApplyNN ν hν t U)
      =
    h3RawFourierL2HeatApplyNN ν hν t
      (h3SpectralFinVectorRawFourierL2 U) := by
  funext i
  exact
    h3SpectralScalarRawFourierL2_heatApplyNN
      ν hν t (U i)

end

end Euclidean
end Bridge
end PrimeTensor
