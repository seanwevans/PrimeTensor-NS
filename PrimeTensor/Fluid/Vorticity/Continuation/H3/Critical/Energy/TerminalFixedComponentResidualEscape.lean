import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalFixedSpatialComponentNonintegrability
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Tactic

/-!
# Terminal non-L¹ obstruction survives every integrable correction

The fixed physical scalar-L² source component obtained from failure of the
strong physical L² terminal trace stays non-L¹ on every terminal tail after
subtracting a Bochner-L¹ correction. If both the component and correction are
continuous at positive times, the residual also has cofinal L²-norm spikes.

For a family of bounded linear maps P ρ acting on physical scalar L², this
applies to F - (P ρ) F for EVERY ρ, provided (P ρ) F is L¹ on each terminal
tail. This is a CONDITIONAL frequency-cutoff interface: it does not prove
that the Fourier low-frequency projection of the actual PDE source is L¹.
No terminal kinetic mass or finite full H³ dissipation premise is added.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped Topology Interval

noncomputable section
set_option maxHeartbeats 800000

/-- A scalar-L² source that is non-L¹ on every terminal subinterval remains
non-L¹ after subtraction of any correction that is L¹ on each such tail. -/
theorem h3Critical_scalarL2_terminal_nonintegrability_survives_L1_correction
    (F B : ℝ → H3ScalarL2)
    {T : ℝ}
    (hNonInt : ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
      ¬ IntervalIntegrable F volume b T)
    (hBInt : ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
      IntervalIntegrable B volume b T) :
    ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
      ¬ IntervalIntegrable (fun t : ℝ => F t - B t) volume b T := by
  intro b hb hResidual
  have hSum := hResidual.add (hBInt b hb)
  have hF : IntervalIntegrable F volume b T := by
    simpa only [sub_add_cancel] using hSum
  exact (hNonInt b hb) hF

/-- A continuous scalar-L² source with persistent non-L¹ cannot have a
bounded norm on any terminal tail, even after a continuous L¹ correction. -/
theorem h3Critical_scalarL2_terminal_residual_cofinal_spikes
    (F B : ℝ → H3ScalarL2)
    {T : ℝ}
    (hFCont : ContinuousOn F (Set.Ioo (0 : ℝ) T))
    (hBCont : ContinuousOn B (Set.Ioo (0 : ℝ) T))
    (hNonInt : ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
      ¬ IntervalIntegrable F volume b T)
    (hBInt : ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
      IntervalIntegrable B volume b T) :
    ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T → ∀ M : ℝ,
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧ M < ‖F t - B t‖ := by
  have hRCont : ContinuousOn (fun t : ℝ => F t - B t)
      (Set.Ioo (0 : ℝ) T) := hFCont.sub hBCont
  have hRNonInt :=
    h3Critical_scalarL2_terminal_nonintegrability_survives_L1_correction
      F B hNonInt hBInt
  exact h3Critical_continuous_scalarL2_nonintegrable_forces_spikes
    (fun t : ℝ => F t - B t) hRCont hRNonInt

/-- In the actual projected physical momentum source, there is ONE fixed
coordinate that stays non-L¹ after EVERY chosen integrable correction.
This holds simultaneously for an arbitrary family of correction paths. -/
theorem h3Critical_noL2Trace_fixed_coordinate_survives_L1_correction_family
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    {ι : Type*}
    (B : ι → Fin 3 → ℝ → H3ScalarL2)
    (hBInt : ∀ (i : ι) (j : Fin 3) (b : ℝ),
      b ∈ Set.Ioo (0 : ℝ) T →
      IntervalIntegrable (B i j) volume b T) :
    ∃ j : Fin 3,
      ∀ (i : ι) (b : ℝ), b ∈ Set.Ioo (0 : ℝ) T →
        ¬ IntervalIntegrable
          (fun t : ℝ =>
            (h3PathActualProjectedMomentumSource244 hH3 t).ofLp j - B i j t)
          volume b T := by
  obtain ⟨j, hj, _⟩ :=
    h3Critical_noL2Trace_fixed_projected_coordinate_nonintegrable_and_spikes
      hH3 hNoTrace
  refine ⟨j, ?_⟩
  intro i b hb
  exact
    (h3Critical_scalarL2_terminal_nonintegrability_survives_L1_correction
      (fun t : ℝ => (h3PathActualProjectedMomentumSource244 hH3 t).ofLp j)
      (B i j) hj (hBInt i j)) b hb

/-- Conditional high-pass escape for a FAMILY of bounded linear cutoffs.
The single coordinate is selected before the radius. The essential
unproved Fourier step is supplied explicitly as hLow: every cutoff output
of the actual component is time-integrable on every terminal subinterval. -/
theorem h3Critical_noL2Trace_fixed_coordinate_highpass_escape_of_lowpass_L1
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (P : ℝ → H3ScalarL2 →L[ℝ] H3ScalarL2)
    (hLow : ∀ (ρ : ℝ) (j : Fin 3) (b : ℝ),
      b ∈ Set.Ioo (0 : ℝ) T →
      IntervalIntegrable
        (fun t : ℝ => (P ρ) ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp j))
        volume b T) :
    ∃ j : Fin 3, ∀ ρ : ℝ,
      (∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
        ¬ IntervalIntegrable
          (fun t : ℝ =>
            (h3PathActualProjectedMomentumSource244 hH3 t).ofLp j -
              (P ρ) ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp j))
          volume b T) ∧
      (∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T → ∀ M : ℝ,
        ∃ t : ℝ, t ∈ Set.Ioo b T ∧
          M < ‖(h3PathActualProjectedMomentumSource244 hH3 t).ofLp j -
            (P ρ) ((h3PathActualProjectedMomentumSource244 hH3 t).ofLp j)‖) := by
  obtain ⟨j, hj, _⟩ :=
    h3Critical_noL2Trace_fixed_projected_coordinate_nonintegrable_and_spikes
      hH3 hNoTrace
  let F : ℝ → H3ScalarL2 :=
    fun t => (h3PathActualProjectedMomentumSource244 hH3 t).ofLp j
  have hFNonInt : ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
      ¬ IntervalIntegrable F volume b T := hj
  have hSourceCont : ContinuousOn
      (h3PathActualProjectedMomentumSource244 hH3)
      (Set.Ioo (0 : ℝ) T) := by
    change ContinuousOn
      (fun t : ℝ => h3AuditInitialActualSpectralLaplacianTotal hH3 t -
        h3AuditInitialActualSpectralLerayTotal hH3 t)
      (Set.Ioo (0 : ℝ) T)
    exact h3Audit_initialActualProjectedRHS_continuousOn_positiveTime hH3
  have hEval : Continuous
      (fun V : H3PhysicalRealFinVectorL2Hilbert => V.ofLp j) :=
    PiLp.continuous_apply
      (2 : ENNReal) (fun _ : Fin 3 => H3ScalarL2) j
  have hFCont : ContinuousOn F (Set.Ioo (0 : ℝ) T) :=
    hEval.comp_continuousOn hSourceCont
  refine ⟨j, ?_⟩
  intro ρ
  let B : ℝ → H3ScalarL2 := fun t => (P ρ) (F t)
  have hBCont : ContinuousOn B (Set.Ioo (0 : ℝ) T) :=
    (P ρ).continuous.comp_continuousOn hFCont
  have hBInt : ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
      IntervalIntegrable B volume b T := by
    intro b hb
    exact hLow ρ j b hb
  have hResidual : ∀ b : ℝ, b ∈ Set.Ioo (0 : ℝ) T →
      ¬ IntervalIntegrable (fun t : ℝ => F t - B t) volume b T :=
    h3Critical_scalarL2_terminal_nonintegrability_survives_L1_correction
      F B hFNonInt hBInt
  refine ⟨hResidual, ?_⟩
  exact h3Critical_scalarL2_terminal_residual_cofinal_spikes
    F B hFCont hBCont hFNonInt hBInt

end
end PrimeTensor.Bridge.Euclidean
