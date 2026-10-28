import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorCriticalWidthEscape244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointCostSum244
import Mathlib.Tactic

/-!
# Canonical anchor dissipation escape and physical energy-normalized spectral rate

The exact three-quarter cubic crossing gives a physical H³ dissipation height
strictly greater than 3 R³ / 4 at every original canonical anchor, WITHOUT
assuming a ninth/eighth annular-width bound. The same disjoint windows have
summable cubic-weighted dissipation charges, hence delta_k R_k³ -> 0.

If the previously conditional critical annular-width cap additionally holds,
the prior exact-anchor result yields K_k -> infinity and D_k/K_k² -> infinity.
The exact three-component spectral energy comparison
  1 <= E_k <= 1 + 3 K_k²
upgrades this to the genuinely physical ratio D_k/E_k -> infinity, and
eventually M E_k <= D_k for each fixed real M. These statements concern
the same physical anchors tau(v k), not reselected spectral source maxima.

Pointwise dissipation heights need not have nonvanishing time exposure.
No terminal H³ continuation or unconditional critical-width cap is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A cubic annular dissipation floor over an escaping inner radius
forces unbounded physical H³ dissipation at the very same anchors. -/
theorem h3Path_scalar_cubicFloor_forces_dissipationEscape244
    (R D : ℕ → ℝ)
    (hRadius : Tendsto (fun k => (R k) ^ 3) atTop atTop)
    (hFloor : ∀ k, 3 * (R k) ^ 3 / 4 < D k) :
    Tendsto D atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  let B : ℝ := max M 0 + 1
  have hMB : M ≤ B := by
    dsimp only [B]
    have hm := le_max_left M 0
    linarith only [hm]
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hm := le_max_right M 0
    linarith only [hm]
  have hLarge : ∀ᶠ k : ℕ in atTop, 4 * B ≤ (R k) ^ 3 :=
    hRadius.eventually (eventually_ge_atTop (4 * B))
  filter_upwards [hLarge] with k hk
  have hD := hFloor k
  linarith only [hMB, hB, hk, hD]

/-- Nonnegative physical energy bounded above by the three-component
spectral sup norm inherits its *normalized dissipation frequency escape*.
The exact normalized energy E is not equal to one plus K squared. -/
theorem h3Path_scalar_spectralRateEscape_forces_physicalEnergyRate244
    (D E K : ℕ → ℝ)
    (hEpos : ∀ k, 0 < E k)
    (hUpper : ∀ k, E k ≤ 1 + 3 * (K k) ^ 2)
    (hKescape : Tendsto K atTop atTop)
    (hSpectralRate : Tendsto (fun k => D k / (K k) ^ 2) atTop atTop) :
    Tendsto (fun k => D k / E k) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  let B : ℝ := max M 0
  have hMB : M ≤ B := le_max_left _ _
  have hB : 0 ≤ B := le_max_right _ _
  have hRate : ∀ᶠ k : ℕ in atTop, 4 * B ≤ D k / (K k) ^ 2 :=
    hSpectralRate.eventually (eventually_ge_atTop (4 * B))
  have hNorm : ∀ᶠ k : ℕ in atTop, 1 ≤ K k :=
    hKescape.eventually (eventually_ge_atTop 1)
  filter_upwards [hRate, hNorm] with k hr hk
  have hSqRaw : (1 : ℝ) ^ 2 ≤ (K k) ^ 2 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hk 2
  have hSq : 1 ≤ (K k) ^ 2 := by
    simpa only [one_pow] using hSqRaw
  have hSqPos : 0 < (K k) ^ 2 := lt_of_lt_of_le (by norm_num) hSq
  have hBound : E k ≤ 4 * (K k) ^ 2 := by
    linarith only [hUpper k, hSq]
  have hCost : (4 * B) * (K k) ^ 2 ≤ D k :=
    (le_div_iff₀ hSqPos).1 hr
  have hMSmall : M * E k ≤ B * E k :=
    mul_le_mul_of_nonneg_right hMB (hEpos k).le
  have hScaled : B * E k ≤ B * (4 * (K k) ^ 2) :=
    mul_le_mul_of_nonneg_left hBound hB
  have hME : M * E k ≤ D k := by
    calc
      _ ≤ B * E k := hMSmall
      _ ≤ B * (4 * (K k) ^ 2) := hScaled
      _ = (4 * B) * (K k) ^ 2 := by ring
      _ ≤ D k := hCost
  exact (le_div_iff₀ (hEpos k)).2 hME

/-- A summable family of original disjoint cubic persistence charges has
vanishing cubic-weighted widths, with no pointwise energy boundedness. -/
theorem h3Path_scalar_summableCubicWindowCost_forces_clockCollapse244
    (v : ℕ → ℕ) (δ : ℕ → ℝ)
    (hCost : Summable (fun k =>
      δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2))) :
    Tendsto (fun k => δ (v k) * ((v k : ℝ) + 1) ^ 3)
      atTop (𝓝 0) := by
  have hTwice := hCost.tendsto_atTop_zero.const_mul (2 : ℝ)
  have hEq : (fun k : ℕ => δ (v k) * ((v k : ℝ) + 1) ^ 3) =
      (fun k : ℕ => 2 * (δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2))) := by
    funext k
    ring
  rw [hEq]
  simpa only [mul_zero] using hTwice

/-- The ORIGINAL exact-anchor minimal cubic first crossings have physically
unbounded D₃ at their anchors even with no critical ninth/eighth width cap.
Simultaneously their exact disjoint persistence charges shrink to zero.
Under the additional (explicit) ninth/eighth cap, the same anchors also
exhibit D₃/E₃ -> infinity, hence eventually M*E₃ <= D₃ for every M. -/
theorem h3Path_noL2Trace_exactAnchor_unconditionalDissipationEscape_conditionalRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k,
        K (v k) = ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∧
        K (v k) ^ 2 ≤ velocityH3EnergyAt u (τ (v k)) ∧
        v k ≤ N (v k) ∧
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        (∃ s : ℝ, s ∈ Set.Icc (τ (v k))
            (τ (v k) + (T - τ (v k)) / 2) ∧
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C (v k))) ∧
      (∀ k, 3 * (((v k : ℝ) + 1) ^ 3) / 4 <
        velocityH3DissipationAt u (τ (v k))) ∧
      Tendsto (fun k => velocityH3DissipationAt u (τ (v k))) atTop atTop ∧
      Tendsto (fun k => δ (v k) * ((v k : ℝ) + 1) ^ 3)
        atTop (𝓝 0) ∧
      (∀ V : ℝ, 0 ≤ V →
        (∀ᶠ k : ℕ in atTop,
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            V * (((v k : ℝ) + 1) ^ 9)) →
        Tendsto (fun k => velocityH3EnergyAt u (τ (v k))) atTop atTop ∧
        Tendsto (fun k => K (v k)) atTop atTop ∧
        Tendsto (fun k => velocityH3DissipationAt u (τ (v k)) /
          (velocityH3EnergyAt u (τ (v k)))) atTop atTop ∧
        (∀ M : ℝ, ∀ᶠ k : ℕ in atTop,
          M * velocityH3EnergyAt u (τ (v k)) ≤
            velocityH3DissipationAt u (τ (v k)))) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, hSummable, hAll, hCap⟩ :=
    h3Path_noL2Trace_exactAnchorCriticalWidth_anchorAmplification244
      hH3 hClass hMass hNoTrace hDInt
  have hRadius := h3Path_strictMono_canonicalRadiusCube_escape244 v hv
  have hFloor (k : ℕ) :
      3 * (((v k : ℝ) + 1) ^ 3) / 4 <
        velocityH3DissipationAt u (τ (v k)) := by
    obtain ⟨_, _, _, hg, _, _⟩ := hAll k
    have hCross : 3 * (((v k : ℝ) + 1) ^ 3) / 4 <
        h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
        h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
      dsimp only [h3PathCubicAnnulusActualGap244] at hg
      linarith only [hg]
    exact lt_of_lt_of_le hCross
      (h3Path_actualFiniteAnnulusDissipation_le_fullAt244
        hH3 hClass (τ (v k)) (hTime (v k))
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1))
  have hDivergent := h3Path_scalar_cubicFloor_forces_dissipationEscape244
    (fun k => (v k : ℝ) + 1)
    (fun k => velocityH3DissipationAt u (τ (v k))) hRadius hFloor
  have hCollapse := h3Path_scalar_summableCubicWindowCost_forces_clockCollapse244
    v δ hSummable
  have hEpos (k : ℕ) : 0 < velocityH3EnergyAt u (τ (v k)) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u (τ (v k)))
  have hUpper (k : ℕ) :
      velocityH3EnergyAt u (τ (v k)) ≤ 1 + 3 * (K (v k)) ^ 2 := by
    have ht : τ (v k) ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 (hTime (v k)).1,
        (hTime (v k)).2⟩
    have hExact := h3AuditActualSpectralVelocityTotal_energy_exact
      hH3 (τ (v k)) ht
    have hSup := h3Path_spectralSquareEnergy_le_threeSupSquare244
      (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))
    rw [(hAll k).1]
    linarith only [hExact, hSup]
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
    hSeparate, hSummable, hAll, hFloor, hDivergent, hCollapse, ?_⟩
  intro V hV hWidth
  obtain ⟨hEnergy, hSpectral, hSpectralRatio⟩ := hCap V hV hWidth
  have hPhysicalRatio := h3Path_scalar_spectralRateEscape_forces_physicalEnergyRate244
    (fun k => velocityH3DissipationAt u (τ (v k)))
    (fun k => velocityH3EnergyAt u (τ (v k)))
    (fun k => K (v k))
    hEpos hUpper hSpectral hSpectralRatio
  refine ⟨hEnergy, hSpectral, hPhysicalRatio, ?_⟩
  intro M
  have hLarge : ∀ᶠ k : ℕ in atTop,
      M ≤ velocityH3DissipationAt u (τ (v k)) /
        velocityH3EnergyAt u (τ (v k)) :=
    hPhysicalRatio.eventually (eventually_ge_atTop M)
  filter_upwards [hLarge] with k hk
  exact (le_div_iff₀ (hEpos k)).1 hk

end
end PrimeTensor.FirstMonomialTriad
