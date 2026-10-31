import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDissipationSynchronization
import Mathlib.Tactic

/-!
# Moving-cutoff simultaneous source and H³ dissipation escape

The preceding theorem selects one actual projected-momentum coordinate and,
for every pair of fixed radii, gives arbitrarily large high-frequency Fourier
source mass and high-radial physical H³ dissipation at the same late time.

This file diagonalizes that exact quantifier order.  Arbitrary sequences of
nonnegative radii and real thresholds can be prescribed *in advance*. Given
any sequence of lower temporal anchors converging to T from a fixed strict
tail, one can select a SINGLE sequence of common witnesses converging to T,
meeting both spectral inequalities at the n-th prescribed radii/thresholds.

In particular, at radii n+1 for BOTH channels, the actual projected-source
mass and high-H³ dissipation both exceed n and tend to +∞ along the SAME
sequence of times tending to T.  These are *moving*-frequency cutoffs, not
merely fixed-cutoff escape on separately selected times.

All conclusions remain conditional on lack of a strong physical L² terminal
velocity trace. No lower bound or noncompression estimate is assumed.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1600000

noncomputable local instance axisFintypeH3MovingHighpassSourceDiss
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3MovingHighpassSourceDiss :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Diagonal selection across any prescribed moving source and dissipation
frequency cutoffs and any prescribed spike thresholds. All witnesses belong
to one time sequence converging to the physical terminal time. -/
theorem h3Critical_noL2Trace_actualHighpassSourceDissipation_movingDiagonal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ K M : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n) :
    ∃ i : Fin 3, ∃ t : ℕ → ℝ,
      Tendsto t atTop (𝓝 T) ∧
      ∀ n : ℕ,
        t n ∈ Set.Ioo (c n) T ∧
        K n < ∫ ξ in (h3TerminalRadialFrequencyBelow (ρ n))ᶜ,
          ‖h3CriticalActualProjectedFourierSource hH3 i (t n) ξ‖ ^ 2 ∂volume ∧
        M n < h3PathActualHighRadialDissipation244 (σ n)
          (h3AuditActualSpectralVelocityTotal hH3 (t n)) := by
  classical
  obtain ⟨i, hi⟩ :=
    h3Critical_noL2Trace_actualHighpassSourceMass_and_highDissipation_sameTime
      hH3 hClass b hb hNoTrace
  have hWitness : ∀ n : ℕ, ∃ t : ℝ,
      t ∈ Set.Ioo (c n) T ∧
      K n < ∫ ξ in (h3TerminalRadialFrequencyBelow (ρ n))ᶜ,
        ‖h3CriticalActualProjectedFourierSource hH3 i t ξ‖ ^ 2 ∂volume ∧
      M n < h3PathActualHighRadialDissipation244 (σ n)
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
    intro n
    exact hi (ρ n) (σ n) (hρ n) (hσ n) (c n) (hc n) (K n) (M n)
  choose t ht hMass hDiss using hWitness
  refine ⟨i, t, ?_, ?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      hcLimit tendsto_const_nhds
      (fun n => (ht n).1.le)
      (fun n => (ht n).2.le)
  · intro n
    exact ⟨ht n, hMass n, hDiss n⟩

/-- At the growing radii n+1, one fixed actual source coordinate has both
high-pass Fourier square mass and physical high-H³ dissipation above n at
the SAME physical times, converging to the terminal time. -/
theorem h3Critical_noL2Trace_actualHighpassSourceDissipation_natDiagonal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T)) :
    ∃ i : Fin 3, ∃ t : ℕ → ℝ,
      Tendsto t atTop (𝓝 T) ∧
      ∀ n : ℕ,
        t n ∈ Set.Ioo (c n) T ∧
        (n : ℝ) < ∫ ξ in
            (h3TerminalRadialFrequencyBelow ((n : ℝ) + 1))ᶜ,
          ‖h3CriticalActualProjectedFourierSource hH3 i (t n) ξ‖ ^ 2 ∂volume ∧
        (n : ℝ) < h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (t n)) := by
  exact h3Critical_noL2Trace_actualHighpassSourceDissipation_movingDiagonal
    hH3 hClass b hb hNoTrace
    c (fun n => (n : ℝ) + 1) (fun n => (n : ℝ) + 1)
    (fun n => (n : ℝ)) (fun n => (n : ℝ))
    hc hcLimit (fun n => by positivity) (fun n => by positivity)

/-- Both moving-frequency escape observables diverge on one common terminal
sequence, not simply along two unrelated subsequences. -/
theorem h3Critical_noL2Trace_actualHighpassSourceDissipation_commonDivergence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T)) :
    ∃ i : Fin 3, ∃ t : ℕ → ℝ,
      Tendsto t atTop (𝓝 T) ∧
      (∀ n : ℕ, t n ∈ Set.Ioo (c n) T) ∧
      Tendsto (fun n : ℕ =>
        ∫ ξ in (h3TerminalRadialFrequencyBelow ((n : ℝ) + 1))ᶜ,
          ‖h3CriticalActualProjectedFourierSource hH3 i (t n) ξ‖ ^ 2 ∂volume)
        atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (t n)))
        atTop atTop := by
  obtain ⟨i, t, htLimit, hSpike⟩ :=
    h3Critical_noL2Trace_actualHighpassSourceDissipation_natDiagonal
      hH3 hClass b hb hNoTrace c hc hcLimit
  refine ⟨i, t, htLimit, (fun n => (hSpike n).1), ?_, ?_⟩
  · exact tendsto_atTop_mono
      (fun n => (hSpike n).2.1.le)
      tendsto_natCast_atTop_atTop
  · exact tendsto_atTop_mono
      (fun n => (hSpike n).2.2.le)
      tendsto_natCast_atTop_atTop

end
end PrimeTensor.Bridge.Euclidean
