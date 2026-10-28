import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorEnergyFourth244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakFrequencyAmplification244
import Mathlib.Tactic

/-!
# Conditional critical annular width forces H³ escape at the SAME disjoint anchors

The exact-anchor canonical sequence already contains a strict three-quarter-
cubic annular first crossing and pairwise-disjoint physical dissipation windows.
A conditional ninth/eighth bound on its minimal annulus implies

  R_k³ < 65536 (V+1) E₃(τ(v k))⁴.

Because v is strictly increasing, R_k = v k + 1 tends to infinity. Thus
E₃(τ(v k)) tends to infinity without a geometric-noncompression or linear-rate
hypothesis. The exact energy/spectral identity E₃ ≤ 1+3 K² then forces
K(v k) = ‖U₃(τ(v k))‖ to infinity. Existing fixed-radius physical Fourier
coercivity consequently forces D₃(τ(v k))/K(v k)² to infinity.

These are pointwise anchor observations, not integrated lower bounds on a
uniform-width interval. The width cap itself is not derived here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Strictly increasing natural-number index selectors force the cubic
radial scale (v k + 1)³ to escape. -/
theorem h3Path_strictMono_canonicalRadiusCube_escape244
    (v : ℕ → ℕ) (hv : StrictMono v) :
    Tendsto (fun k : ℕ => ((v k : ℝ) + 1) ^ 3) atTop atTop := by
  have hLower (k : ℕ) : k ≤ v k := by
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hStep : v k < v (k + 1) := hv (Nat.lt_succ_self k)
      omega
  apply Filter.tendsto_atTop.2
  intro M
  obtain ⟨n, hn⟩ := exists_nat_gt M
  filter_upwards [eventually_ge_atTop n] with k hk
  have hIndex : n ≤ v k := hk.trans (hLower k)
  have hCast : (n : ℝ) ≤ (v k : ℝ) := by exact_mod_cast hIndex
  let R : ℝ := (v k : ℝ) + 1
  have hR : 1 ≤ R := by
    dsimp only [R]
    have hCast0 : 0 ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hCast0]
  have hRNonneg : 0 ≤ R := by linarith only [hR]
  have hSqRaw : (1 : ℝ) ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hR 2
  have hSq : 1 ≤ R ^ 2 := by simpa only [one_pow] using hSqRaw
  have hCube : R ≤ R ^ 3 := by
    calc
      R = R * 1 := by ring
      _ ≤ R * R ^ 2 := mul_le_mul_of_nonneg_left hSq hRNonneg
      _ = R ^ 3 := by ring
  change M ≤ R ^ 3
  dsimp only [R] at hCube ⊢
  linarith only [hn, hCast, hCube]

/-- An unbounded cubic cutoff with a fourth-power energy lower bound
forces the nonnegative physical energy sequence to infinity. -/
theorem h3Path_scalar_cubicFourthCost_forces_energyEscape244
    (R E : ℕ → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hE : ∀ k, 0 ≤ E k)
    (hRadial : Tendsto (fun k => (R k) ^ 3) atTop atTop)
    (hCost : ∀ᶠ k : ℕ in atTop, (R k) ^ 3 < D * (E k) ^ 4) :
    Tendsto E atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  let B : ℝ := max M 0 + 1
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hMax : 0 ≤ max M 0 := le_max_right _ _
    linarith only [hMax]
  have hMB : M ≤ B := by
    dsimp only [B]
    have hMax : M ≤ max M 0 := le_max_left _ _
    linarith only [hMax]
  have hLarge : ∀ᶠ k : ℕ in atTop, D * B ^ 4 + 1 ≤ (R k) ^ 3 :=
    hRadial.eventually (eventually_ge_atTop (D * B ^ 4 + 1))
  filter_upwards [hCost, hLarge] with k hk hBig
  by_contra hNot
  have hEUpper : E k ≤ B := by
    have hSmall : E k < M := lt_of_not_ge hNot
    linarith only [hSmall, hMB]
  have hPower : (E k) ^ 4 ≤ B ^ 4 :=
    pow_le_pow_left₀ (hE k) hEUpper 4
  have hScaled := mul_le_mul_of_nonneg_left hPower hD
  linarith only [hk, hBig, hScaled]

/-- Escape of the exact physical H³ energy forces the actual three-component
weighted Fourier sup norm to escape; no equality E₃ = 1+K² is assumed. -/
theorem h3Path_scalar_energyEscape_forces_threeSpectralEscape244
    (E K : ℕ → ℝ)
    (hEnergy : Tendsto E atTop atTop)
    (hK : ∀ k, 0 ≤ K k)
    (hUpper : ∀ k, E k ≤ 1 + 3 * (K k) ^ 2) :
    Tendsto K atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  let B : ℝ := max M 0 + 1
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hMax : 0 ≤ max M 0 := le_max_right _ _
    linarith only [hMax]
  have hMB : M ≤ B := by
    dsimp only [B]
    have hMax : M ≤ max M 0 := le_max_left _ _
    linarith only [hMax]
  have hLarge : ∀ᶠ k : ℕ in atTop,
      1 + 3 * B ^ 2 + 1 ≤ E k :=
    hEnergy.eventually (eventually_ge_atTop (1 + 3 * B ^ 2 + 1))
  filter_upwards [hLarge] with k hk
  by_contra hNot
  have hKUpper : K k ≤ B := by
    have hSmall : K k < M := lt_of_not_ge hNot
    linarith only [hSmall, hMB]
  have hSquare : (K k) ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ (hK k) hB).2 hKUpper
  have hEstimate := hUpper k
  linarith only [hk, hSquare, hEstimate]

/-- The SAME exact-anchor, disjoint canonical PDE windows now carry a
conditional pointwise physical energy escape, spectral sup-norm escape,
and arbitrarily large physical H³ dissipation per spectral norm-square.
Only the ninth/eighth width cap is assumed eventually; neither geometric
noncompression nor a sixth-order linear source-rate bound is required. -/
theorem h3Path_noL2Trace_exactAnchorCriticalWidth_anchorAmplification244
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
      (∀ V : ℝ, 0 ≤ V →
        (∀ᶠ k : ℕ in atTop,
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            V * (((v k : ℝ) + 1) ^ 9)) →
        Tendsto (fun k => velocityH3EnergyAt u (τ (v k))) atTop atTop ∧
        Tendsto (fun k => K (v k)) atTop atTop ∧
        Tendsto (fun k =>
          velocityH3DissipationAt u (τ (v k)) / (K (v k)) ^ 2)
          atTop atTop) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, hSummable, hAll, _hBarrier, _hPeaks⟩ :=
    h3Path_noL2Trace_finiteDissipation_exactAnchorCanonicalThreeScale244
      hH3 hClass hMass hNoTrace hDInt
  have hN (k : ℕ) : v k ≤ N (v k) := by
    rcases hAll k with ⟨_, _, _, hn, _, _, _, _, _, _, _, _⟩
    exact hn
  have hGap (k : ℕ) : ((v k : ℝ) + 1) ^ 3 / 4 <
      h3PathCubicAnnulusActualGap244 hH3 τ N (v k) := by
    rcases hAll k with ⟨_, _, _, _, _, _, _, _, _, _, hg, _⟩
    exact hg
  have hKE (k : ℕ) :
      K (v k) = ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ :=
    (hAll k).1
  have hAnchor (k : ℕ) :
      velocityH3EnergyAt u (τ (v k)) ≤ 1 + 3 * K (v k) ^ 2 := by
    have ht : τ (v k) ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 (hTime (v k)).1,
        (hTime (v k)).2⟩
    have hExact := h3AuditActualSpectralVelocityTotal_energy_exact
      hH3 (τ (v k)) ht
    have hSup := h3Path_spectralSquareEnergy_le_threeSupSquare244
      (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))
    rw [hKE k]
    linarith only [hExact, hSup]
  have hKnonneg (k : ℕ) : 0 ≤ K (v k) := by
    rw [hKE k]
    exact norm_nonneg _
  have hRadial := h3Path_strictMono_canonicalRadiusCube_escape244 v hv
  let b : ℝ := (a + T) / 2
  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    have hAT := hClass.terminal_start.2
    constructor <;> linarith only [hAT]
  have hLate : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hCofinal.eventually (Ioi_mem_nhds hb.2)
  have hInside : ∀ᶠ k : ℕ in atTop, τ (v k) ∈ Set.Ioo b T := by
    filter_upwards [hLate] with k hk
    exact ⟨hk, (hTime (v k)).2⟩
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
    hSeparate, hSummable, ?_, ?_⟩
  · intro k
    rcases hAll k with ⟨hk, he, _, hn, hc, hp, _, _, _, _, hg, _⟩
    exact ⟨hk, he, hn, hg, hc, hp⟩
  · intro V hV hWidth
    have hFourth := h3Path_exactAnchorCanonicalWidth_forces_eventualEnergyFourth244
      hH3 hClass τ N v hTime hN hGap V hV hWidth
    have hEpos (k : ℕ) : 0 ≤ velocityH3EnergyAt u (τ (v k)) :=
      le_trans zero_le_one (one_le_velocityH3EnergyAt u (τ (v k)))
    have hEescape := h3Path_scalar_cubicFourthCost_forces_energyEscape244
      (fun k => (v k : ℝ) + 1)
      (fun k => velocityH3EnergyAt u (τ (v k)))
      (65536 * (V + 1))
      (by positivity) hEpos hRadial
      (by simpa only [mul_assoc] using hFourth)
    have hKescape := h3Path_scalar_energyEscape_forces_threeSpectralEscape244
      (fun k => velocityH3EnergyAt u (τ (v k)))
      (fun k => K (v k)) hEescape hKnonneg hAnchor
    have hActualEscape : Tendsto (fun k =>
        ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖) atTop atTop := by
      convert hKescape using 1
      funext k
      exact (hKE k).symm
    have hRatio := h3Path_cofinalSpectralPeaks_dissipationOverSquare_escape244
      hH3 hClass b hb (fun k => τ (v k)) hInside hActualEscape
    have hEqRatio : (fun k =>
        velocityH3DissipationAt u (τ (v k)) / K (v k) ^ 2) =
      (fun k => velocityH3DissipationAt u (τ (v k)) /
        ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ^ 2) := by
      funext k
      rw [hKE k]
    refine ⟨hEescape, hKescape, ?_⟩
    rw [hEqRatio]
    exact hRatio

end
end PrimeTensor.FirstMonomialTriad
