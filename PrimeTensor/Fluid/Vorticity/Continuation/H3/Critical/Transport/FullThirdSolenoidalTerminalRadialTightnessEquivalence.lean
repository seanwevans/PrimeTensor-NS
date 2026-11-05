import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalUnconditionalTerminalLowBandFTC
import Mathlib.Tactic

/-!
# Terminal H³ convergence is exactly endpoint-uniform radial tightness

Every fixed weighted H³ Fourier low band already has a strong terminal limit
from the actual physical Hilbert FTC and integrability of the projected
low-pass momentum source. Thus the only remaining functional-analytic
obstruction to a full terminal H³ spectral trace is the loss of a single
endpoint-uniform high-frequency cutoff.

The necessity direction follows from contraction of the high-radial Fourier
projector and vanishing high-radial mass of any fixed H³ state. Together with
the sufficient direction, this gives an iff statement and a quantified,
cofinal high-radial escape characterization of failure of an H³ trace.

Endpoint-uniform tightness is NOT established here. Neither an unconditional
H³ trace nor continuation of a Navier-Stokes solution is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeTerminalRadialEquivalence244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Any strong H³ limit forces one radius and one terminal time width
on which the high-radial Fourier tail is small for *all* late times.
This direction is purely functional analytic. -/
theorem thirdFullTerminalTrace_implies_uniformHighRadialTight244
    (U : ℝ → H3SpectralVelocityState) (a T : ℝ)
    (L : H3SpectralVelocityState)
    (hTrace : Tendsto U (𝓝[<] T) (𝓝 L)) :
    ThirdFullTerminalUniformHighRadialTightOn244 U a T := by
  intro ε hε
  have hHalf : 0 < ε / 2 := by linarith
  have hTail := thirdFullSpectralVelocityHighRadialApply_norm_tendsto_zero244 L
  obtain ⟨R, hR⟩ := (Metric.tendsto_atTop.mp hTail) (ε / 2) hHalf
  have hLimitTail :
      ‖thirdFullSpectralVelocityHighRadialApply244 R L‖ < ε / 2 := by
    have h := hR R le_rfl
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (norm_nonneg _)] using h
  obtain ⟨δ, hδ, hNear⟩ :=
    (Metric.tendsto_nhdsWithin_nhds.mp hTrace) (ε / 2) hHalf
  refine ⟨R, δ, hδ, ?_⟩
  intro t ht htNear
  have htDist : dist t T < δ := by
    simpa only [Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr ht.2.le), neg_sub] using htNear
  have hClose : ‖U t - L‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hNear ht.2 htDist
  calc
    ‖thirdFullSpectralVelocityHighRadialApply244 R (U t)‖ =
        ‖thirdFullSpectralVelocityHighRadialApply244 R ((U t - L) + L)‖ := by
          rw [sub_add_cancel]
    _ = ‖thirdFullSpectralVelocityHighRadialApply244 R (U t - L) +
          thirdFullSpectralVelocityHighRadialApply244 R L‖ := by
            rw [thirdFullSpectralVelocityHighRadialApply_add244]
    _ ≤ ‖thirdFullSpectralVelocityHighRadialApply244 R (U t - L)‖ +
          ‖thirdFullSpectralVelocityHighRadialApply244 R L‖ := norm_add_le _ _
    _ ≤ ‖U t - L‖ +
          ‖thirdFullSpectralVelocityHighRadialApply244 R L‖ := by
            exact add_le_add
              (thirdFullSpectralVelocityHighRadialApply_norm_le244 R (U t - L))
              le_rfl
    _ < ε := by linarith only [hClose, hLimitTail]

/-- Sharp terminal compactness criterion for the ORIGINAL physical velocity:
given the existing H³ path/energy class, strong H³ endpoint convergence is
equivalent to endpoint-uniform high-frequency Fourier tightness. Every fixed
low-frequency terminal Cauchy condition has already been discharged. -/
theorem thirdFullPhysical_terminalH3Trace_iff_uniformHighRadialTight244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    (∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L)) ↔
      ThirdFullTerminalUniformHighRadialTightOn244
        (h3AuditActualSpectralVelocityTotal hH3) b T := by
  constructor
  · rintro ⟨L, hTrace⟩
    exact thirdFullTerminalTrace_implies_uniformHighRadialTight244
      (h3AuditActualSpectralVelocityTotal hH3) b T L hTrace
  · intro hTight
    exact thirdFullPhysical_terminalH3Trace_of_radialTight244
      hH3 hClass b hb hTight

/-- The failure of a physical H³ terminal trace is EQUIVALENT to cofinal
high-frequency H³ mass escape beyond every finite radial ball, with a
single positive threshold chosen before the cutoff and terminal window. -/
theorem thirdFullPhysical_noH3Trace_iff_cofinalHighRadialEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    (¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L)) ↔
    (∃ ε : ℝ, 0 < ε ∧
      ∀ (R : ℕ) (δ : ℝ), 0 < δ →
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧ T - t < δ ∧
          ε ≤ ‖thirdFullSpectralVelocityHighRadialApply244 R
            (h3AuditActualSpectralVelocityTotal hH3 t)‖) := by
  constructor
  · intro hNoTrace
    exact thirdFullPhysical_noH3Trace_cofinalHighRadialEscape_automaticLow244
      hH3 hClass b hb hNoTrace
  · rintro ⟨ε, hε, hEscape⟩ ⟨L, hTrace⟩
    have hTight := thirdFullTerminalTrace_implies_uniformHighRadialTight244
      (h3AuditActualSpectralVelocityTotal hH3) b T L hTrace
    obtain ⟨R, δ, hδ, hSmall⟩ := hTight ε hε
    obtain ⟨t, ht, htNear, hLarge⟩ := hEscape R δ hδ
    exact (not_lt_of_ge hLarge) (hSmall t ht htNear)

/-- Exact endpoint alternative: the actual H³ spectral state either has a
terminal trace or its high-frequency mass escapes cofinally at one fixed
positive threshold. No terminal trace is asserted unconditionally. -/
theorem thirdFullPhysical_terminalH3Trace_or_cofinalHighRadialEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    (∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L)) ∨
    (∃ ε : ℝ, 0 < ε ∧
      ∀ (R : ℕ) (δ : ℝ), 0 < δ →
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧ T - t < δ ∧
          ε ≤ ‖thirdFullSpectralVelocityHighRadialApply244 R
            (h3AuditActualSpectralVelocityTotal hH3 t)‖) := by
  classical
  by_cases hTrace : ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L)
  · exact Or.inl hTrace
  · exact Or.inr
      ((thirdFullPhysical_noH3Trace_iff_cofinalHighRadialEscape244
        hH3 hClass b hb).mp hTrace)

end
end PrimeTensor.FirstMonomialTriad
