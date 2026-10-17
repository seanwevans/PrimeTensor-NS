import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzH3CrossEnergyInvariant244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Density
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Genuine three-component weighted H³ spectral Schwartz density

The previously proved `h3Schwartz_denseRange_toSpectralScalar` is a scalar
density statement for the actual complex weighted spectral L² carrier.
Here `DenseRange.piMap` extends it to the complete THREE-component
`H3SpectralVelocityState`, with no finite-dimensional surrogate norm.

For any spectral velocity state U, a full Schwartz-vector sequence Φₙ is
constructed with

  ‖U - Φₙ.toLp‖ < 1 / (n + 1),

so the encoded Schwartz vectors converge strongly to U in the genuine
weighted H³ Hilbert state and are Cauchy there.

The field Φₙ is Schwartz in the WEIGHTED FREQUENCY carrier. We do NOT
assert that it is the Fourier transform of a real divergence-free physical
Schwartz velocity: deweighting, Fourier reality, solenoidal projection,
and matching the physical E₂/E₃ energies are separate analytic bridges.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped ENNReal SchwartzMap

noncomputable section

noncomputable local instance axisFintypeSpectralVelocityDensity244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Coordinatewise realization of THREE genuine complex spectral Schwartz
functions as a complete weighted H³ spectral velocity state. -/
noncomputable def h3SchwartzSpectralVelocityRealization244 :
    (Fin 3 → SchwartzMap H3FourierPoint3 ℂ) →
      H3SpectralVelocityState :=
  Pi.map (fun _ : Fin 3 =>
    (fun φ : SchwartzMap H3FourierPoint3 ℂ =>
      φ.toLp 2 (volume : Measure H3FourierPoint3)))

@[simp]
theorem h3SchwartzSpectralVelocityRealization_apply244
    (Φ : Fin 3 → SchwartzMap H3FourierPoint3 ℂ) (j : Fin 3) :
    h3SchwartzSpectralVelocityRealization244 Φ j =
      (Φ j).toLp 2 (volume : Measure H3FourierPoint3) := by
  rfl

/-- The entire finite velocity state, not merely one scalar coordinate,
has dense realisation by weighted spectral Schwartz vectors. -/
theorem h3SchwartzSpectralVelocityRealization_denseRange244 :
    DenseRange h3SchwartzSpectralVelocityRealization244 := by
  unfold h3SchwartzSpectralVelocityRealization244
  exact DenseRange.piMap
    (fun _ : Fin 3 => h3Schwartz_denseRange_toSpectralScalar)

/-- Arbitrarily small approximation of an arbitrary weighted spectral
H³ velocity, measured in its actual product-space norm. -/
theorem exists_h3SchwartzSpectralVelocityApprox_norm244
    (U : H3SpectralVelocityState)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Φ : Fin 3 → SchwartzMap H3FourierPoint3 ℂ,
      ‖U - h3SchwartzSpectralVelocityRealization244 Φ‖ < ε := by
  simpa only [dist_eq_norm] using
    (h3SchwartzSpectralVelocityRealization_denseRange244.exists_dist_lt U hε)

/-- A full sequence of three-component spectral Schwartz approximants is
constructed from density using the explicit reciprocal-N error threshold.
No Cauchy or convergence hypothesis is postulated. -/
theorem exists_h3SchwartzSpectralVelocityApprox_sequence244
    (U : H3SpectralVelocityState) :
    ∃ Φ : ℕ → Fin 3 → SchwartzMap H3FourierPoint3 ℂ,
      Tendsto (fun n =>
          h3SchwartzSpectralVelocityRealization244 (Φ n))
        atTop (𝓝 U) ∧
      CauchySeq (fun n =>
          h3SchwartzSpectralVelocityRealization244 (Φ n)) := by
  classical
  have hRadiusPos (n : ℕ) :
      0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  have hApprox :
      ∀ n : ℕ,
        ∃ φ : Fin 3 → SchwartzMap H3FourierPoint3 ℂ,
          dist U (h3SchwartzSpectralVelocityRealization244 φ) <
            (1 : ℝ) / ((n : ℝ) + 1) := by
    intro n
    exact h3SchwartzSpectralVelocityRealization_denseRange244.exists_dist_lt
      U (hRadiusPos n)
  choose Φ hΦ using hApprox
  have hRadiusTendsto :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hConverges :
      Tendsto (fun n =>
          h3SchwartzSpectralVelocityRealization244 (Φ n))
        atTop (𝓝 U) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hRadiusTendsto) ε hε
    refine ⟨N, ?_⟩
    intro n hn
    have hRadiusSmall :
        (1 : ℝ) / ((n : ℝ) + 1) < ε := by
      have h := hN n hn
      simpa only [Real.dist_eq, sub_zero, abs_of_pos (hRadiusPos n)] using h
    calc
      dist (h3SchwartzSpectralVelocityRealization244 (Φ n)) U =
          dist U (h3SchwartzSpectralVelocityRealization244 (Φ n)) :=
        dist_comm _ _
      _ < (1 : ℝ) / ((n : ℝ) + 1) := hΦ n
      _ < ε := hRadiusSmall
  exact ⟨Φ, hConverges, hConverges.cauchySeq⟩

end
end PrimeTensor.FirstMonomialTriad
