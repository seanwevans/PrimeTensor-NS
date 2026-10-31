import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassSourceDrivenExtendedCosts
import Mathlib.Tactic

/-!
# Transfer source-driven extended window costs to full physical H³ dissipation

The actual physical H³ dissipation equals the sum of its nonnegative
low-radial and high-radial parts at each strict energy-class time. Hence
the high-radial channel lies below the full physical dissipation pointwise.

The source-driven no-terminal-trace branch already provides strictly
separated windows and extended high-radial cost inequalities. Transfer them
to the genuine full physical H³ dissipation, with the SAME moving radii,
heights, coordinate, times and windows, without assuming time continuity,
measurability or finite L¹ of the full dissipation.

This controls individual and finite-sum extended integrals from below. It
does not provide an upper bound on the full terminal integral, a divergent
cost sum, an ordinary finite integral, or a noncompression estimate.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Actual high-radial H³ dissipation is below the full physical H³
viscous dissipation at each strict energy-class time. No sign assumption
on the radial cutoff is required by the exact partition. -/
theorem h3Critical_actualHighRadialDissipation_le_full
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (σ : ℝ) :
    h3PathActualHighRadialDissipation244 σ
      (h3AuditActualSpectralVelocityTotal hH3 t) ≤
      velocityH3DissipationAt u t := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  have hLow : 0 ≤ h3PathActualLowRadialDissipation244 σ G := by
    unfold h3PathActualLowRadialDissipation244
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg G ξ
  have hPartition :
      h3PathActualLowRadialDissipation244 σ G +
        h3PathActualHighRadialDissipation244 σ G =
          velocityH3DissipationAt u t :=
    h3Path_actualRadialDissipation_partition244 hH3 hClass t ht σ
  change h3PathActualHighRadialDissipation244 σ G ≤
    velocityH3DissipationAt u t
  linarith only [hLow, hPartition]

/-- Monotonicity of extended window costs needs only a pointwise inequality
on the physical time window; it does not presume measurability of either
real-valued density. -/
theorem h3Critical_extendedWindowCost_mono
    (f g : ℝ → ℝ) (t δ : ℝ)
    (hDom : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) → f s ≤ g s) :
    (∫⁻ s in Set.Ioc t (t + δ), ENNReal.ofReal (f s) ∂volume) ≤
      ∫⁻ s in Set.Ioc t (t + δ), ENNReal.ofReal (g s) ∂volume := by
  apply setLIntegral_mono' measurableSet_Ioc
  intro s hs
  exact ENNReal.ofReal_le_ofReal (hDom s ⟨hs.1.le, hs.2⟩)

/-- On the SAME source-driven, strictly separated physical windows, the
full physical H³ dissipation dominates the moving high-radial floor.
Both extended high-radial and full physical finite-sum costs dominate the
prescribed constant extended window costs. The high-radial extended finite
sum itself is bounded above by the full physical extended finite sum.

No full-H³ temporal continuity, local integrability, or terminal L¹ bound
is assumed. The no-strong-terminal-physical-L²-trace branch is explicit. -/
theorem h3Critical_noL2Trace_sourceDriven_disjointExtendedFullDissipationCosts
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
          M (v k) < velocityH3DissipationAt u s) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ∫⁻ _s in Set.Ioc (t (v k)) (t (v k) + δ (v k)),
            ENNReal.ofReal (M (v k)) ∂volume) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ (v k)),
            ENNReal.ofReal
              (h3PathActualHighRadialDissipation244 (σ (v k))
                (h3AuditActualSpectralVelocityTotal hH3 s)) ∂volume) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ (v k)),
            ENNReal.ofReal
              (h3PathActualHighRadialDissipation244 (σ (v k))
                (h3AuditActualSpectralVelocityTotal hH3 s)) ∂volume) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ (v k)),
            ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) := by
  obtain ⟨i, t, δ, v, hMono, hLimit, hSeparate, hWindows, hCosts⟩ :=
    h3Critical_noL2Trace_sourceDriven_disjointExtendedDissipationCosts
      hH3 hClass b hb hNoTrace c ρ σ K M hc hcLimit hρ hσ
  have hClassTime (k : ℕ) (s : ℝ)
      (hs : s ∈ Set.Icc (t (v k)) (t (v k) + δ (v k))) :
      s ∈ Set.Ioo a T := by
    have hStart : a < t (v k) :=
      lt_trans hb.1 (lt_trans (hc (v k)).1 ((hWindows k).1).1)
    exact ⟨lt_of_lt_of_le hStart hs.1,
      lt_of_le_of_lt hs.2 ((hWindows k).2.2.1)⟩
  have hFullFloor (k : ℕ) (s : ℝ)
      (hs : s ∈ Set.Icc (t (v k)) (t (v k) + δ (v k))) :
      M (v k) < velocityH3DissipationAt u s := by
    exact lt_of_lt_of_le ((hWindows k).2.2.2 s hs)
      (h3Critical_actualHighRadialDissipation_le_full
        hH3 hClass s (hClassTime k s hs) (σ (v k)))
  refine ⟨i, t, δ, v, hMono, hLimit, hSeparate, ?_, hCosts, ?_⟩
  · intro k
    exact ⟨(hWindows k).1, (hWindows k).2.1,
      (hWindows k).2.2.1, hFullFloor k⟩
  · intro m
    apply Finset.sum_le_sum
    intro k _hk
    apply h3Critical_extendedWindowCost_mono
    intro s hs
    exact h3Critical_actualHighRadialDissipation_le_full
      hH3 hClass s (hClassTime k s hs) (σ (v k))

end
end PrimeTensor.Bridge.Euclidean
