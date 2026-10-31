import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDrivenWindows
import Mathlib.Tactic

/-!
# Extended time-integral costs for source-driven high-H³ windows

The source-driven theorem supplies common physical-time windows on which the
actual high-radial H³ dissipation exceeds an arbitrary prescribed threshold,
without assuming continuity of full dissipation. The preceding real-valued
interval-integral lower bound required interval integrability of the high
channel. Here we instead use the nonnegative extended Lebesgue integral.

By monotonicity of the extended integral on each Ioc window, the integral of
the constant threshold is below that of ENNReal.ofReal of the genuine high-H³
dissipation. This needs neither temporal measurability nor finite L¹ cost.
The finite-sum result retains the original strictly separated windows.

It does NOT establish measurability, finite H³ dissipation, an ordinary Bochner
integral, a lower bound on the window widths, or a divergent series of costs.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A pointwise lower bound on a closed time window yields an extended
Lebesgue-integral lower bound on its half-open interior. The function need
not be interval-integrable or even known to be measurable. -/
theorem h3Critical_extendedWindowCost_of_pointwiseFloor
    (f : ℝ → ℝ) (t δ M : ℝ)
    (hFloor : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) → M ≤ f s) :
    (∫⁻ _s in Set.Ioc t (t + δ), ENNReal.ofReal M ∂volume) ≤
      ∫⁻ s in Set.Ioc t (t + δ), ENNReal.ofReal (f s) ∂volume := by
  apply setLIntegral_mono' measurableSet_Ioc
  intro s hs
  exact ENNReal.ofReal_le_ofReal (hFloor s ⟨hs.1.le, hs.2⟩)

/-- The no-trace source-driven witnesses provide simultaneously separated
nonnegative extended H³ dissipation costs, without any high-channel
interval-integrability or continuity assumption. The constant integral on
each selected window is its actual length times ENNReal.ofReal of its height.
The same witnesses retain the source bounds established by the imported
source-driven disjoint-window theorem. -/
theorem h3Critical_noL2Trace_sourceDriven_disjointExtendedDissipationCosts
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
    ∃ i : Fin 3, ∃ t δ : ℕ → ℝ, ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ,
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < δ (v k) ∧ t (v k) + δ (v k) < T ∧
        ∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ (v k)) →
          M (v k) < h3PathActualHighRadialDissipation244 (σ (v k))
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ∫⁻ _s in Set.Ioc (t (v k)) (t (v k) + δ (v k)),
            ENNReal.ofReal (M (v k)) ∂volume) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ (v k)),
            ENNReal.ofReal
              (h3PathActualHighRadialDissipation244 (σ (v k))
                (h3AuditActualSpectralVelocityTotal hH3 s)) ∂volume) := by
  obtain ⟨i, t, δ, v, hMono, hLimit, hSeparate, hWindows,
      _hSourceCosts, _hConditionalDissipationCosts⟩ :=
    h3Critical_noL2Trace_sourceDriven_profileDisjointWindows
      hH3 hClass b hb hNoTrace c ρ σ K M hc hcLimit hρ hσ
  refine ⟨i, t, δ, v, hMono, hLimit, hSeparate, ?_, ?_⟩
  · intro k
    exact ⟨(hWindows k).1, (hWindows k).2.1,
      (hWindows k).2.2.1,
      fun s hs => ((hWindows k).2.2.2.1 s hs).2⟩
  · intro m
    apply Finset.sum_le_sum
    intro k _hk
    apply h3Critical_extendedWindowCost_of_pointwiseFloor
    intro s hs
    exact (((hWindows k).2.2.2.1 s hs).2).le

end
end PrimeTensor.Bridge.Euclidean
