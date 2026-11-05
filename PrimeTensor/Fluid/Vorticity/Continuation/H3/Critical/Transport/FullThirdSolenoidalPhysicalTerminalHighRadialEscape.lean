import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalRadialCauchyCriterion
import Mathlib.Tactic

/-!
# Terminal physical H³ trace or cofinal weighted high-radial escape

This file instantiates the sharp low-band/high-tail closure criterion for the
original preterminal weighted Fourier state, not a separately chosen model.

The current physical theory already proves fixed-radius physical projected
source Bochner-L¹ on strict terminal tails; converting that PDE statement
into *weighted low-frequency state Cauchy* is the outstanding separate
Fourier/FTC identification. We therefore retain that exact premise rather
than implicitly claiming that continuity on (0,T) extends to T.

Under that low-band premise, failure of a terminal H³ trace forces a
single positive weighted H³ high-radial tail lower bound arbitrarily close
to T, for every fixed natural cutoff R. This is a necessary obstruction;
it does not on its own establish Navier–Stokes continuation or exclude a
terminal singularity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators ENNReal Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypePhysicalTerminalHighRadialEscape244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Genuine physical spectral H³ trace from terminal low-band Cauchy
and a single ε-dependent common high-radial cutoff. -/
theorem thirdFullPhysicalTerminalSpectralTrace_of_lowAndTight244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (haT : a < T)
    (hLow : ThirdFullTerminalLowRadialCauchyOn244
      (h3AuditActualSpectralVelocityTotal hH3) a T)
    (hTight : ThirdFullTerminalUniformHighRadialTightOn244
      (h3AuditActualSpectralVelocityTotal hH3) a T) :
    ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L) :=
  thirdFullTerminalSpectralTrace_of_lowAndTight244
    (h3AuditActualSpectralVelocityTotal hH3) a T haT hLow hTight

/-- With fixed-band Cauchy control, nonconvergence in weighted H³
precludes terminal-uniform high-radial tightness. -/
theorem thirdFullPhysical_noH3Trace_notUniformHighRadialTight244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (haT : a < T)
    (hLow : ThirdFullTerminalLowRadialCauchyOn244
      (h3AuditActualSpectralVelocityTotal hH3) a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L)) :
    ¬ ThirdFullTerminalUniformHighRadialTightOn244
      (h3AuditActualSpectralVelocityTotal hH3) a T := by
  intro hTight
  exact hNoTrace
    (thirdFullPhysicalTerminalSpectralTrace_of_lowAndTight244
      hH3 haT hLow hTight)

/-- Quantified failure of tightness: some positive amount of actual
weighted Fourier H³ square-root mass persists beyond EVERY fixed cutoff,
arbitrarily close to the physical terminal time. The threshold is selected
BEFORE the radius and the terminal neighborhood. -/
theorem thirdFullPhysical_noH3Trace_cofinalHighRadialEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (haT : a < T)
    (hLow : ThirdFullTerminalLowRadialCauchyOn244
      (h3AuditActualSpectralVelocityTotal hH3) a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (R : ℕ) (δ : ℝ), 0 < δ →
        ∃ t : ℝ, t ∈ Set.Ioo a T ∧ T - t < δ ∧
          ε ≤ ‖thirdFullSpectralVelocityHighRadialApply244 R
            (h3AuditActualSpectralVelocityTotal hH3 t)‖ := by
  have hNotTight := thirdFullPhysical_noH3Trace_notUniformHighRadialTight244
    hH3 haT hLow hNoTrace
  unfold ThirdFullTerminalUniformHighRadialTightOn244 at hNotTight
  push_neg at hNotTight
  obtain ⟨ε, hε, hEscape⟩ := hNotTight
  refine ⟨ε, hε, ?_⟩
  intro R δ hδ
  exact hEscape R δ hδ

end
end PrimeTensor.FirstMonomialTriad
