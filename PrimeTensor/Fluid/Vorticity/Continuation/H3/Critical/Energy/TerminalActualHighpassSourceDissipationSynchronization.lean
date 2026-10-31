import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassFourierMassEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalFixedRadialHighDissipation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.FiniteDissipationPointwise
import Mathlib.Tactic

/-!
# Same-time high-frequency source and H³ dissipation escape

The committed actual high-pass Fourier mass obstruction already supplies one
fixed projected-source coordinate with unbounded high-frequency L² mass on
all strict terminal subintervals, under an explicit failure of the physical
L² terminal trace. The separately proved fixed-radius high-H³-dissipation
obstruction gives spikes but does not couple their TIMES.

Here the exact complementary Fourier indicator is shown contractive. The
actual source bound, the anchored interpolation estimate, and the kinetic
bound for low-radial H³ dissipation give, for arbitrary INDEPENDENT fixed
source and dissipation radii ρ and σ,

  ‖1_{Sρᶜ} R̂ᵢ(t)‖₂ ≤ (3+C_L) [1+6 E₀(b)+3(Cσ+HighDσ(t))],
  Cσ = σ² W₃(σ)² E₀(b).

Thus the same terminal time chosen by sufficiently large *source* highpass
mass necessarily has high-H³ dissipation above any prescribed threshold.
The source coordinate is selected once, before both radii and thresholds.
This is a synchronized necessary obstruction, NOT a finite-time singularity
construction nor an estimate of dissipation by source mass from below.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1600000

noncomputable local instance axisFintypeH3ActualHighpassSourceDissSync
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ActualHighpassSourceDissSync :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The Fourier high-pass complement is a contraction, without a factor 2:
its almost-everywhere representative is exactly an indicator. -/
theorem h3Critical_fourierSharpHighpass_norm_le
    (ρ : ℝ) (F : H3FourierComplexL2) :
    ‖F - h3CriticalFourierSharpLowCutoffCLM ρ F‖ ≤ ‖F‖ := by
  apply MeasureTheory.Lp.norm_le_norm_of_ae_le
  filter_upwards [h3Critical_fourierSharpHighpass_ae ρ F] with ξ hAt
  rw [hAt]
  by_cases hξ : ξ ∈ (h3TerminalRadialFrequencyBelow ρ)ᶜ
  · simpa only [Set.indicator_of_mem hξ] using (le_refl (‖F ξ‖))
  · simpa only [Set.indicator_of_notMem hξ, norm_zero] using
      (norm_nonneg (F ξ))

/-- A fixed Fourier high-pass coordinate of the genuine projected momentum
source cannot exceed the full physical vector source norm. -/
theorem h3Critical_actualHighpassFourierSource_norm_le_physicalSource
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ : ℝ) (i : Fin 3) (t : ℝ) :
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ ≤
      ‖h3PathActualProjectedMomentumSource244 hH3 t‖ := by
  calc
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ ≤
        ‖h3CriticalActualProjectedFourierSource hH3 i t‖ :=
      h3Critical_fourierSharpHighpass_norm_le ρ _
    _ = ‖(h3PathActualProjectedMomentumSource244 hH3 t).ofLp i‖ :=
      norm_h3ScalarFourierL2 _
    _ ≤ ‖h3PathActualProjectedMomentumSource244 hH3 t‖ :=
      PiLp.norm_apply_le _ i

/-- The exact high-pass source is controlled at each actual kinetic-anchored
time by the full physical H³ dissipation, without any extra Fourier premise. -/
theorem h3Critical_actualHighpassFourierSource_norm_le_fullDissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (i : Fin 3)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) :
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ ≤
      (3 + h3AuditInitialLerayEnergyCoefficient) *
        (1 + 6 * velocityH3Energy0At u b +
          3 * velocityH3DissipationAt u t) := by
  exact
    (h3Critical_actualHighpassFourierSource_norm_le_physicalSource
      hH3 ρ i t).trans
      (h3Critical_projected_source_le_kinetic_anchor_add_dissipation
        hH3 hClass hb ht)

/-- Quantitative SAME-TIME coupling. The source cutoff ρ and the
H³-dissipation cutoff σ need not agree. -/
theorem h3Critical_actualHighpassFourierSource_norm_le_highRadialDissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ σ : ℝ) (hσ : 0 ≤ σ) (i : Fin 3)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) :
    ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ ≤
      (3 + h3AuditInitialLerayEnergyCoefficient) *
        (1 + 6 * velocityH3Energy0At u b +
          3 * (σ ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling σ *
                velocityH3Energy0At u b) +
              h3PathActualHighRadialDissipation244 σ
                (h3AuditActualSpectralVelocityTotal hH3 t))) := by
  have hPart := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ⟨lt_trans hb.1 ht.1, ht.2⟩ σ
  have hLow := h3Path_actualLowRadialDissipation_le_kineticAnchor244
    hH3 hClass b hb σ hσ t ht
  have hCoeff : 0 ≤ 3 + h3AuditInitialLerayEnergyCoefficient := by
    have h := h3AuditInitialLerayEnergyCoefficient_nonneg
    linarith only [h]
  have hUpper :
      1 + 6 * velocityH3Energy0At u b +
        3 * velocityH3DissipationAt u t ≤
      1 + 6 * velocityH3Energy0At u b +
        3 * (σ ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling σ *
              velocityH3Energy0At u b) +
            h3PathActualHighRadialDissipation244 σ
              (h3AuditActualSpectralVelocityTotal hH3 t)) := by
    linarith only [hPart, hLow]
  exact
    (h3Critical_actualHighpassFourierSource_norm_le_fullDissipation
      hH3 hClass b hb ρ i t ht).trans
      (mul_le_mul_of_nonneg_left hUpper hCoeff)

/-- One fixed projected-source coordinate exhibits simultaneous cofinal
high-pass Fourier mass and high-H³ dissipation escape. The two arbitrary
fixed frequency cutoffs may be chosen independently, and the witness t is
THE SAME for the two strict inequalities. The only terminal hypothesis is
absence of a strong physical L² velocity trace. -/
theorem h3Critical_noL2Trace_actualHighpassSourceMass_and_highDissipation_sameTime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ i : Fin 3,
      ∀ (ρ σ : ℝ), 0 ≤ ρ → 0 ≤ σ →
        ∀ (c : ℝ), c ∈ Set.Ioo b T → ∀ (K M : ℝ),
          ∃ t : ℝ, t ∈ Set.Ioo c T ∧
            (K < ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
              ‖h3CriticalActualProjectedFourierSource hH3 i t ξ‖ ^ 2 ∂volume) ∧
            (M < h3PathActualHighRadialDissipation244 σ
              (h3AuditActualSpectralVelocityTotal hH3 t)) := by
  obtain ⟨i, hi⟩ :=
    h3Critical_noL2Trace_actualHighpassFourierMass_escape
      hH3 hClass b hb hNoTrace
  refine ⟨i, ?_⟩
  intro ρ σ hρ hσ c hc K M
  let C : ℝ := σ ^ 2 *
    (h3TerminalRadialSobolevWeightSquareCeiling σ * velocityH3Energy0At u b)
  let Q : ℝ := (3 + h3AuditInitialLerayEnergyCoefficient) *
    (1 + 6 * velocityH3Energy0At u b + 3 * (C + M))
  let B : ℝ := max Q 0
  obtain ⟨t, ht, hLarge⟩ := hi ρ hρ c hc (max K (B ^ 2))
  refine ⟨t, ht, ?_, ?_⟩
  · exact (le_max_left K (B ^ 2)).trans_lt hLarge
  · by_contra hNot
    have hDle :
        h3PathActualHighRadialDissipation244 σ
          (h3AuditActualSpectralVelocityTotal hH3 t) ≤ M :=
      le_of_not_gt hNot
    have hCoeff : 0 ≤ 3 + h3AuditInitialLerayEnergyCoefficient := by
      have h := h3AuditInitialLerayEnergyCoefficient_nonneg
      linarith only [h]
    have hPoint :=
      h3Critical_actualHighpassFourierSource_norm_le_highRadialDissipation
        hH3 hClass b hb ρ σ hσ i t
        ⟨lt_trans hc.1 ht.1, ht.2⟩
    have hInner :
        1 + 6 * velocityH3Energy0At u b +
          3 * (C + h3PathActualHighRadialDissipation244 σ
            (h3AuditActualSpectralVelocityTotal hH3 t)) ≤
        1 + 6 * velocityH3Energy0At u b + 3 * (C + M) := by
      linarith only [hDle]
    have hNormUpper :
        ‖h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t‖ ≤ Q := by
      exact hPoint.trans
        (mul_le_mul_of_nonneg_left hInner hCoeff)
    let H : H3FourierComplexL2 :=
      h3CriticalActualProjectedHighpassFourierSource hH3 ρ i t
    have hBound : ‖H‖ ≤ B :=
      hNormUpper.trans (le_max_left Q 0)
    have hBNonneg : 0 ≤ B := le_max_right Q 0
    have hSquareBound : ‖H‖ ^ 2 ≤ B ^ 2 :=
      (sq_le_sq₀ (norm_nonneg H) hBNonneg).2 hBound
    have hMass : ‖H‖ ^ 2 =
        ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
          ‖h3CriticalActualProjectedFourierSource hH3 i t ξ‖ ^ 2 ∂volume :=
      h3Critical_fourierSharpHighpass_norm_sq_eq_integral ρ _
    have hAbove : B ^ 2 < ‖H‖ ^ 2 := by
      rw [hMass]
      exact (le_max_right K (B ^ 2)).trans_lt hLarge
    exact (not_lt_of_ge hSquareBound) hAbove

end
end PrimeTensor.Bridge.Euclidean
