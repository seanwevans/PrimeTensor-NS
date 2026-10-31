import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDissipationTemporalWindows
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointWindows244
import Mathlib.Tactic

/-!
# Pairwise-separated actual Fourier-source / H³ dissipation windows

The common physical-time persistence theorem at the preceding checkpoint gives
one projected-source coordinate and cofinal right-hand physical-time windows.
The previously proved terminal-window extraction selects a strictly increasing
subsequence whose closed windows are pairwise separated, without touching the
Fourier cutoffs, source mass, high-H³ dissipation, or their individual costs.

The finite-sum conclusions preserve both time-integrated height times width
bounds on that SAME disjoint family. They do not assert a divergent cost sum,
an a priori width bound, finite H³ dissipation up to T, or the existence of the
no-strong-L²-trace branch. Full H³ dissipation continuity remains explicit.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3ActualHighpassDisjointWindows
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ActualHighpassDisjointWindows :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A single actual source coordinate and a strictly increasing subsequence
of the already-proved common highpass-source/high-H³-dissipation windows.
The CLOSED windows are strictly separated in time. The two finite partial
integral sums both dominate the same sum of selected height times width.
Neither sum is asserted to diverge. -/
theorem h3Critical_noL2Trace_actualHighpassSourceDissipation_disjointWindows
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
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hDCont : ContinuousOn (velocityH3DissipationAt u) (Set.Ioo a T)) :
    ∃ i : Fin 3, ∃ t δ : ℕ → ℝ, ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ,
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < δ (v k) ∧ t (v k) + δ (v k) < T ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ (v k)) →
          (v k : ℝ) < ∫ ξ in
              (h3TerminalRadialFrequencyBelow ((v k : ℝ) + 1))ᶜ,
              ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume ∧
          (v k : ℝ) < h3PathActualHighRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        δ (v k) * (v k : ℝ) ≤ ∫ s in t (v k)..(t (v k) + δ (v k)),
          (∫ ξ in (h3TerminalRadialFrequencyBelow ((v k : ℝ) + 1))ᶜ,
            ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume) ∧
        δ (v k) * (v k : ℝ) ≤ ∫ s in t (v k)..(t (v k) + δ (v k)),
          h3PathActualHighRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m, δ (v k) * (v k : ℝ)) ≤
          ∑ k ∈ Finset.range m,
            ∫ s in t (v k)..(t (v k) + δ (v k)),
              (∫ ξ in (h3TerminalRadialFrequencyBelow ((v k : ℝ) + 1))ᶜ,
                ‖h3CriticalActualProjectedFourierSource hH3 i s ξ‖ ^ 2 ∂volume) ∧
        (∑ k ∈ Finset.range m, δ (v k) * (v k : ℝ)) ≤
          ∑ k ∈ Finset.range m,
            ∫ s in t (v k)..(t (v k) + δ (v k)),
              h3PathActualHighRadialDissipation244 ((v k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  obtain ⟨i, t, δ, htLimit, hWindow⟩ :=
    h3Critical_noL2Trace_actualHighpassSourceDissipation_integratedWindows
      hH3 hClass b hb hNoTrace c hc hcLimit hDCont
  have hWidth (n : ℕ) : 0 < δ n := (hWindow n).2.1
  have hEnd (n : ℕ) : t n + δ n < T := (hWindow n).2.2.1
  obtain ⟨v, hMono, hCofinal, hSeparated⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      t δ T htLimit hWidth hEnd
  refine ⟨i, t, δ, v, hMono, hCofinal, hSeparated, ?_, ?_⟩
  · intro k
    exact hWindow (v k)
  · intro m
    constructor
    · exact Finset.sum_le_sum (fun k _ => (hWindow (v k)).2.2.2.2.1)
    · exact Finset.sum_le_sum (fun k _ => (hWindow (v k)).2.2.2.2.2)

end
end PrimeTensor.Bridge.Euclidean
