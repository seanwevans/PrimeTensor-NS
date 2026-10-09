import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceFullTailTopShareLimitOne
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Fourier.Identification

/-!
# Full-terminal concentration of physical H³ viscous dissipation

The exact physical block identities give

  D = D₀ + D₁ + D₂ + D₃ = E₁ + E₂ + E₃ + D₃.

Under hypothetical nonextension, the previous full-terminal theorem gives
E₁+E₂ = o(E₃), and the established characteristic frequency cascade gives
D₃/E₃ -> +infinity on the entire left terminal filter. Combining these
independent conclusions proves, without new PDE sign assumptions,

  D₀ + D₁ + D₂ = o(D₃),   D₃ / D -> 1,     as t approaches T from below.

Both fixed directed-source alternatives remain open. This is a necessary
condition under hypothetical nonextension, not evidence of an actual
singularity, a transport estimate, or unconditional continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Full H³ viscous dissipation consists exactly of the next three physical
energy moments and the fourth-order viscous block. -/
theorem h3PathCanonical_fullDissipation_eq_lowerEnergies_add_topDissipation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    velocityH3DissipationAt u t =
      (velocityH3Energy1At u t + velocityH3Energy2At u t +
        velocityH3Energy3At u t) + velocityH3Dissipation3At u t := by
  unfold velocityH3DissipationAt
  rw [velocityH3Dissipation0At_eq_energy1 u t,
    velocityH3Dissipation1At_eq_energy2 u t,
    velocityH3Dissipation2At_eq_energy3 u t]

/-- The fourth-order viscous block is always bounded by full physical
viscous dissipation, independently of a terminal-time hypothesis. -/
theorem h3PathCanonical_topDissipation_le_fullDissipation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    velocityH3Dissipation3At u t ≤ velocityH3DissipationAt u t := by
  have h1 := velocityH3Energy1At_nonneg u t
  have h2 := velocityH3Energy2At_nonneg u t
  have h3 := velocityH3Energy3At_nonneg u t
  rw [h3PathCanonical_fullDissipation_eq_lowerEnergies_add_topDissipation]
  linarith only [h1, h2, h3]

/-- Every positive epsilon eventually bounds the full physical viscous
energy by `(1+epsilon) D₃` on the entire left terminal neighborhood. -/
theorem h3PathCanonical_eventually_fullDissipation_le_one_add_epsilon_top_nhdsLT
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      velocityH3DissipationAt u t ≤
        (1 + ε) * velocityH3Dissipation3At u t := by
  have hLower : ∀ᶠ t : ℝ in 𝓝[<] T,
      velocityH3Energy1At u t + velocityH3Energy2At u t ≤
        velocityH3Energy3At u t := by
    simpa only [one_mul] using
      h3PathCanonical_eventually_lowerOrders_le_epsilon_top_nhdsLT
        hH3 hNoExtension hClass hb 1 (by norm_num)
  have hTopT : Tendsto (velocityH3Energy3At u) (𝓝[<] T) atTop :=
    velocityH3Energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hTopPositive : ∀ᶠ t : ℝ in 𝓝[<] T,
      1 ≤ velocityH3Energy3At u t :=
    (tendsto_atTop.1 hTopT) 1
  have hDissRate : Tendsto
      (fun t : ℝ => velocityH3Dissipation3At u t /
        velocityH3Energy3At u t) (𝓝[<] T) atTop :=
    velocityH3Dissipation3At_div_energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hDissLarge : ∀ᶠ t : ℝ in 𝓝[<] T,
      2 / ε ≤ velocityH3Dissipation3At u t /
        velocityH3Energy3At u t :=
    (tendsto_atTop.1 hDissRate) (2 / ε)
  filter_upwards [hLower, hTopPositive, hDissLarge] with t hLowerAt hThirdOne hRateAt
  have hE3 : 0 < velocityH3Energy3At u t :=
    lt_of_lt_of_le zero_lt_one hThirdOne
  have hRateScaled :
      (2 / ε) * velocityH3Energy3At u t ≤
        velocityH3Dissipation3At u t :=
    (le_div_iff₀ hE3).mp hRateAt
  have hTwoTop :
      2 * velocityH3Energy3At u t ≤
        ε * velocityH3Dissipation3At u t := by
    calc
      2 * velocityH3Energy3At u t =
          ε * ((2 / ε) * velocityH3Energy3At u t) := by
        field_simp [ne_of_gt hε]
      _ ≤ ε * velocityH3Dissipation3At u t :=
        mul_le_mul_of_nonneg_left hRateScaled hε.le
  have hExact :=
    h3PathCanonical_fullDissipation_eq_lowerEnergies_add_topDissipation u t
  have hBound :
      velocityH3DissipationAt u t ≤
        2 * velocityH3Energy3At u t + velocityH3Dissipation3At u t := by
    rw [hExact]
    linarith only [hLowerAt]
  linarith only [hBound, hTwoTop]

/-- All three lower viscous blocks are negligible compared with the genuine
fourth-derivative dissipation, uniformly on a sufficiently late tail. -/
theorem h3PathCanonical_eventually_lowerDissipation_le_epsilon_top_nhdsLT
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      velocityH3Dissipation0At u t + velocityH3Dissipation1At u t +
        velocityH3Dissipation2At u t ≤
          ε * velocityH3Dissipation3At u t := by
  have hUpper :=
    h3PathCanonical_eventually_fullDissipation_le_one_add_epsilon_top_nhdsLT
      hH3 hNoExtension hClass hb ε hε
  filter_upwards [hUpper] with t ht
  unfold velocityH3DissipationAt at ht
  linarith only [ht]

/-- In a hypothetical nonextendible H³ path the fourth-derivative viscous
energy carries asymptotically all the full dissipation, not only the
third-derivative energy. This is a full-left-filter limit. -/
theorem h3PathCanonical_dissipationTopShare_tendsto_one_nhdsLT_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    Tendsto (fun t : ℝ =>
      velocityH3Dissipation3At u t / velocityH3DissipationAt u t)
      (𝓝[<] T) (𝓝 1) := by
  have hD3T : Tendsto (velocityH3Dissipation3At u) (𝓝[<] T) atTop :=
    velocityH3Dissipation3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hD3One : ∀ᶠ t : ℝ in 𝓝[<] T,
      1 ≤ velocityH3Dissipation3At u t :=
    (tendsto_atTop.1 hD3T) 1
  have hDPos : ∀ᶠ t : ℝ in 𝓝[<] T,
      0 < velocityH3DissipationAt u t := by
    filter_upwards [hD3One] with t ht
    exact lt_of_lt_of_le zero_lt_one
      (le_trans ht (h3PathCanonical_topDissipation_le_fullDissipation u t))
  have hUpper (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        velocityH3DissipationAt u t ≤
          (1 + ε) * velocityH3Dissipation3At u t :=
    h3PathCanonical_eventually_fullDissipation_le_one_add_epsilon_top_nhdsLT
      hH3 hNoExtension hClass hb ε hε
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro c hc
    let ε : ℝ := (1 - c) / 2
    have hε : 0 < ε := by
      dsimp only [ε]
      linarith only [hc]
    have hCoeff : 0 < 1 + ε := by linarith only [hε]
    have hFactor : 0 < (1 - c) * (2 - c) :=
      mul_pos (by linarith only [hc]) (by linarith only [hc])
    have hcBelow : c < 1 / (1 + ε) := by
      apply (lt_div_iff₀ hCoeff).2
      dsimp only [ε]
      nlinarith only [hFactor]
    filter_upwards [hUpper ε hε, hDPos] with t ht hD
    have hDivide : velocityH3DissipationAt u t / (1 + ε) ≤
        velocityH3Dissipation3At u t :=
      (div_le_iff₀ hCoeff).2 (by
        calc
          velocityH3DissipationAt u t ≤
              (1 + ε) * velocityH3Dissipation3At u t := ht
          _ = velocityH3Dissipation3At u t * (1 + ε) := by ring)
    have hShare : 1 / (1 + ε) ≤
        velocityH3Dissipation3At u t / velocityH3DissipationAt u t := by
      apply (le_div_iff₀ hD).2
      calc
        (1 / (1 + ε)) * velocityH3DissipationAt u t =
            velocityH3DissipationAt u t / (1 + ε) := by ring
        _ ≤ velocityH3Dissipation3At u t := hDivide
    exact lt_of_lt_of_le hcBelow hShare
  · intro c hc
    filter_upwards [hDPos] with t hD
    have hTop := h3PathCanonical_topDissipation_le_fullDissipation u t
    exact lt_of_le_of_lt
      ((div_le_iff₀ hD).2 (by simpa using hTop)) hc

end
end Euclidean
end Bridge
end PrimeTensor
