import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralKineticRadialEscape244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Bounded.Radial.Uniform.Absolute.Continuity
import Mathlib.Tactic

/-!
# Complementary Fourier integral equals the actual high-radial H³ mass

The previous physical-kinetic reduction obtains cofinal unboundedness of

  HighRemainder(ρ,G) = SpectralSquareEnergy(G) - LowSquareMass(ρ,G)

on every terminal subtail, under the explicitly retained condition that the
physical kinetic L² velocity has no strong terminal trace. This file closes
the remaining *measure-theoretic* normalization.

The three-component density of the weighted Fourier state is integrable.
The difference-from-zero density used to define LowSquareMass coincides
pointwise with that amplitude. Plancherel's L² norm identity identifies the
whole-space integral with SpectralSquareEnergy. Therefore the exact set-
integral complement theorem gives

  HighRemainder(ρ,G)
    = ∫_{h3TerminalRadialFrequencyBelow(ρ)ᶜ} Σ_j |G_j(ξ)|² dξ.

In particular this mass is nonnegative. The terminal escape theorem is now
an assertion about a genuine integrated Fourier tail, not a subtraction of
unnormalized quantities. It does NOT identify H³ nonextension with failure
of the strong physical kinetic L² terminal trace.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3PhysicalSpectralHighRadialIntegral244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalSpectralHighRadialIntegral244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Comparing a weighted spectral state to zero in the earlier radial
square-defect construction recovers its pointwise three-component energy
density, without selecting representatives at individual frequencies. -/
theorem h3Path_actualSpectralDifferenceFromZero_density_eq244
    (G : H3SpectralVelocityState) (ξ : H3FourierPoint3) :
    h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity G 0 ξ =
      h3TerminalSpectralStateSquareAmplitude G ξ := by
  simp [h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity,
    h3TerminalSpectralStateSquareAmplitude,
    h3TerminalSpectralDifferenceAt]

/-- The complete three-coordinate weighted Fourier square energy is the
integral of its actual nonnegative spectral amplitude. Unlike the product
sup norm, this is an exact Hilbert square-energy identity. -/
theorem h3Path_spectralSquareEnergy_eq_totalFourierIntegral244
    (G : H3SpectralVelocityState) :
    h3SpectralVelocitySquareEnergy G =
      ∫ ξ : H3FourierPoint3,
        h3TerminalSpectralStateSquareAmplitude G ξ ∂volume := by
  have h0 : Integrable
      (fun ξ : H3FourierPoint3 => ‖G 0 ξ‖ ^ 2) volume :=
    (MeasureTheory.Lp.memLp (G 0)).norm.integrable_sq
  have h1 : Integrable
      (fun ξ : H3FourierPoint3 => ‖G 1 ξ‖ ^ 2) volume :=
    (MeasureTheory.Lp.memLp (G 1)).norm.integrable_sq
  have h2 : Integrable
      (fun ξ : H3FourierPoint3 => ‖G 2 ξ‖ ^ 2) volume :=
    (MeasureTheory.Lp.memLp (G 2)).norm.integrable_sq
  calc
    h3SpectralVelocitySquareEnergy G =
        ‖G 0‖ ^ 2 + ‖G 1‖ ^ 2 + ‖G 2‖ ^ 2 := by
          simp only [h3SpectralVelocitySquareEnergy, Fin.sum_univ_three]
    _ = (∫ ξ : H3FourierPoint3, ‖G 0 ξ‖ ^ 2 ∂volume) +
          (∫ ξ : H3FourierPoint3, ‖G 1 ξ‖ ^ 2 ∂volume) +
          (∫ ξ : H3FourierPoint3, ‖G 2 ξ‖ ^ 2 ∂volume) := by
          rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq,
            h3FourierComplexL2_norm_sq_eq_integral_norm_sq,
            h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
    _ = ∫ ξ : H3FourierPoint3,
          h3TerminalSpectralStateSquareAmplitude G ξ ∂volume := by
          unfold h3TerminalSpectralStateSquareAmplitude
          -- `integral_add` is stated for pointwise function addition.  Its
          -- Pi.add notation needs normalization before rewriting this lambda.
          have h012 := integral_add (h0.add h1) h2
          have h01 := integral_add h0 h1
          simp only [Pi.add_apply] at h012 h01
          rw [h012, h01]

/-- The existing radial comparison with the zero spectral state is literally
integration of the weighted H³ square amplitude on the low radial ball. -/
theorem h3Path_actualSpectralLowRadialSquareMass_eq_integral244
    (ρ : ℝ) (G : H3SpectralVelocityState) :
    h3PathActualSpectralLowRadialSquareMass244 ρ G =
      ∫ ξ in h3TerminalRadialFrequencyBelow ρ,
        h3TerminalSpectralStateSquareAmplitude G ξ ∂volume := by
  change
    (∫ ξ in h3TerminalRadialFrequencyBelow ρ,
      h3TerminalWeightedSpectralVelocityTotalSquareDifferenceDensity G 0 ξ
      ∂volume) =
    (∫ ξ in h3TerminalRadialFrequencyBelow ρ,
      h3TerminalSpectralStateSquareAmplitude G ξ ∂volume)
  apply integral_congr_ae
  filter_upwards with ξ
  exact h3Path_actualSpectralDifferenceFromZero_density_eq244 G ξ

/-- Exact complementary Fourier-mass identification of the formerly
algebraic high-radial remainder, at every cutoff and for every weighted H³
state. No terminal or dynamical hypotheses are needed for this identity. -/
theorem h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244
    (ρ : ℝ) (G : H3SpectralVelocityState) :
    h3PathActualSpectralHighRadialRemainder244 ρ G =
      ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        h3TerminalSpectralStateSquareAmplitude G ξ ∂volume := by
  unfold h3PathActualSpectralHighRadialRemainder244
  rw [h3Path_spectralSquareEnergy_eq_totalFourierIntegral244,
    h3Path_actualSpectralLowRadialSquareMass_eq_integral244]
  exact (setIntegral_compl
    (measurableSet_h3TerminalRadialFrequencyBelow ρ)
    (h3TerminalSpectralStateSquareAmplitude_integrable G)).symm

/-- The normalized high-radial spectral mass cannot be negative. -/
theorem h3Path_actualSpectralHighRadialRemainder_nonneg244
    (ρ : ℝ) (G : H3SpectralVelocityState) :
    0 ≤ h3PathActualSpectralHighRadialRemainder244 ρ G := by
  rw [h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244]
  apply integral_nonneg
  intro ξ
  exact h3TerminalSpectralStateSquareAmplitude_nonneg G ξ

/-- If a positive-terminal-kinetic-mass path has no strong physical L²
endpoint trace, then the *integrated* actual weighted H³ mass outside every
fixed radial ball is cofinally unbounded. The earlier fixed-coordinate
escape and actual kinetic ceiling are the substantive hypotheses. -/
theorem h3Path_physicalNoL2Trace_forces_highRadialFourierIntegralEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ c : ℝ, c ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo c T ∧
        M < ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
          h3TerminalSpectralStateSquareAmplitude
            (h3AuditActualSpectralVelocityTotal hH3 r) ξ ∂volume := by
  intro c hc M
  obtain ⟨r, hr, hLarge⟩ :=
    h3Path_physicalNoL2Trace_forces_highRadialRemainder_kinetic244
      hH3 hClass hL hNoTrace ρ hρ c hc M
  refine ⟨r, hr, ?_⟩
  simpa only [h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244]
    using hLarge

/-- Final normalized kinetic-trace alternative: either the old physical
velocity converges strongly in kinetic L² with the canonical terminal mass,
or that mass is positive and every fixed Fourier radial complement has
cofinally unbounded *integrated* weighted H³ mass. -/
theorem h3Path_physicalL2Trace_or_allHighRadialFourierIntegralEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U) ∧
        ‖U‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T) ∨
      (0 < h3PathCanonicalTerminalKineticEnergyAt u a T ∧
        ∀ ρ : ℝ, 0 ≤ ρ →
          ∀ c : ℝ, c ∈ Set.Ioo a T → ∀ M : ℝ,
            ∃ r : ℝ, r ∈ Set.Ioo c T ∧
              M < ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
                h3TerminalSpectralStateSquareAmplitude
                  (h3AuditActualSpectralVelocityTotal hH3 r) ξ ∂volume) := by
  rcases h3Path_physicalL2Trace_or_allHighRadialRemainderEscape244
    hH3 hClass with hTrace | hEscape
  · exact Or.inl hTrace
  · refine Or.inr ⟨hEscape.1, ?_⟩
    intro ρ hρ c hc M
    obtain ⟨r, hr, hLarge⟩ := hEscape.2 ρ hρ c hc M
    refine ⟨r, hr, ?_⟩
    simpa only [h3Path_actualSpectralHighRadialRemainder_eq_complementIntegral244]
      using hLarge

end
end PrimeTensor.FirstMonomialTriad
