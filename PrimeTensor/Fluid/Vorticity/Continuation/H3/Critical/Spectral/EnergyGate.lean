import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.RadialMoments.AllOrdersSharpEnergy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorCriticalWidthEscape244
import Mathlib.Tactic

/-!
# Actual spectral H3 energy gate for arbitrary-order radial budgets

The existing fourth-power inequality on original critical canonical annuli is
transferred to the actual three-component spectral Fourier norm. An abstract
cofinal argument turns the polynomial radial cost into terminal H3 energy
escape, then the established exact spectral-energy identity forces the actual
spectral sup norm to escape at the *same selected anchors*.

All higher-moment, intrinsic source, critical-width and terminal-time
noncompression assumptions are explicitly retained; no derivative bound,
positive-growth-rate integrability or regularity is inferred.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Substitute the genuine physical Fourier H3 energy ceiling into the
all-orders fourth-power cost without changing the canonical cutoff. -/
theorem h3Path_higherBudget_energyFourth_to_spectralFourth244
    (R E K S D ε : ℝ) (m : ℕ)
    (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hEnergy : E ≤ 1 + 3 * K ^ 2)
    (hCost : R ^ (16 * m + 3) ≤
      (512 * ε ^ 2) ^ 4 * (2304 * E * S ^ 2 + 1) ^ 4 * D ^ 5) :
    R ^ (16 * m + 3) ≤
      (512 * ε ^ 2) ^ 4 *
        (2304 * (1 + 3 * K ^ 2) * S ^ 2 + 1) ^ 4 * D ^ 5 := by
  have hScaled := mul_le_mul_of_nonneg_left hEnergy
    (show 0 ≤ 2304 * S ^ 2 by positivity)
  have hAdd : 2304 * E * S ^ 2 + 1 ≤
      2304 * (1 + 3 * K ^ 2) * S ^ 2 + 1 := by
    calc
      2304 * E * S ^ 2 + 1 = (2304 * S ^ 2) * E + 1 := by ring
      _ ≤ (2304 * S ^ 2) * (1 + 3 * K ^ 2) + 1 := by
        linarith only [hScaled]
      _ = 2304 * (1 + 3 * K ^ 2) * S ^ 2 + 1 := by ring
  have hPow : (2304 * E * S ^ 2 + 1) ^ 4 ≤
      (2304 * (1 + 3 * K ^ 2) * S ^ 2 + 1) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hAdd 4
  have hNonneg : 0 ≤ (512 * ε ^ 2) ^ 4 * D ^ 5 := by positivity
  have hBound := mul_le_mul_of_nonneg_left hPow hNonneg
  calc
    R ^ (16 * m + 3) ≤
        (512 * ε ^ 2) ^ 4 * (2304 * E * S ^ 2 + 1) ^ 4 * D ^ 5 := hCost
    _ = ((512 * ε ^ 2) ^ 4 * D ^ 5) *
          (2304 * E * S ^ 2 + 1) ^ 4 := by ring
    _ ≤ ((512 * ε ^ 2) ^ 4 * D ^ 5) *
          (2304 * (1 + 3 * K ^ 2) * S ^ 2 + 1) ^ 4 := hBound
    _ = (512 * ε ^ 2) ^ 4 *
          (2304 * (1 + 3 * K ^ 2) * S ^ 2 + 1) ^ 4 * D ^ 5 := by ring

/-- A cofinal radial scale and any fourth-power energy bill with exponent
16m+3 force the nonnegative H3 energy sequence to escape every fixed bound.
The fixed coefficient B can even vanish; then the hypotheses are inconsistent. -/
theorem h3Path_scalar_higherSharpEnergyCost_forces_energyEscape244
    (R E : ℕ → ℝ) (m : ℕ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hR : ∀ k, 1 ≤ R k) (hE : ∀ k, 0 ≤ E k)
    (hRadial : Tendsto (fun k => (R k) ^ 3) atTop atTop)
    (hCost : ∀ᶠ k : ℕ in atTop,
      (R k) ^ (16 * m + 3) ≤ A * (B * E k + 1) ^ 4) :
    Tendsto E atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  let H : ℝ := max M 0 + 1
  have hH : 0 ≤ H := by
    dsimp only [H]
    have hh : 0 ≤ max M 0 := le_max_right _ _
    linarith only [hh]
  have hMH : M ≤ H := by
    dsimp only [H]
    have hh : M ≤ max M 0 := le_max_left _ _
    linarith only [hh]
  have hLarge : ∀ᶠ k : ℕ in atTop,
      A * (B * H + 1) ^ 4 + 1 ≤ (R k) ^ 3 :=
    hRadial.eventually (eventually_ge_atTop (A * (B * H + 1) ^ 4 + 1))
  filter_upwards [hCost, hLarge] with k hk hBig
  by_contra hNot
  have hEUpper : E k ≤ H := by
    have hSmall : E k < M := lt_of_not_ge hNot
    linarith only [hSmall, hMH]
  have hMul := mul_le_mul_of_nonneg_left hEUpper hB
  have hCoeff : B * E k + 1 ≤ B * H + 1 := by
    linarith only [hMul]
  have hCoeffNonneg : 0 ≤ B * E k + 1 := by
    have hp := mul_nonneg hB (hE k)
    linarith only [hp]
  have hFourth : (B * E k + 1) ^ 4 ≤ (B * H + 1) ^ 4 :=
    pow_le_pow_left₀ hCoeffNonneg hCoeff 4
  have hScaled := mul_le_mul_of_nonneg_left hFourth hA
  have hRpow : 1 ≤ (R k) ^ (16 * m) := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (hR k) (16 * m))
  have hRcube : (R k) ^ 3 ≤ (R k) ^ (16 * m + 3) := by
    calc
      (R k) ^ 3 = 1 * (R k) ^ 3 := by ring
      _ ≤ (R k) ^ (16 * m) * (R k) ^ 3 :=
        mul_le_mul_of_nonneg_right hRpow
          (pow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) (hR k)) 3)
      _ = (R k) ^ (16 * m + 3) := by rw [pow_add]
  linarith only [hk, hBig, hScaled, hRcube]

/-- Same actual canonical anchors: the polynomial fourth-power cost is
carried by the genuine Fourier H3 norm, and both physical energy and that
norm escape. No integration of the positive energy derivative is asserted. -/
theorem h3Path_noL2Trace_exactAnchor_allOrdersCriticalBudget_spectralEnergyGate244
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
    ∃ hτ : (∀ n, τ n ∈ Set.Ioo a T),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2)) ∧
      (∀ m : ℕ, ∀ F : ℝ → ℝ,
        (∀ s : ℝ, 0 ≤ F s) →
        IntervalIntegrable F volume a T →
        (∀ s : ℝ, ∀ hs : s ∈ Set.Ioo a T,
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass m s hs ≤ ENNReal.ofReal (F s)) →
        ∀ S D η ε : ℝ,
          0 ≤ S → 0 ≤ D → 0 < η → 0 < ε → ε < η →
          16 * ε ^ 2 * (36 * S ^ 2 * (D + 256) + 1) < 1 →
          (∀ᶠ k : ℕ in atTop, C (v k) ≤ S) →
          (∀ᶠ k : ℕ in atTop,
            ((N (v k) : ℝ) + 2) ^ 8 ≤ D * ((v k : ℝ) + 1) ^ 9) →
          (∀ᶠ k : ℕ in atTop,
            η ≤ ((v k : ℝ) + 1) ^ (2 * m + 3) * ((T - τ (v k)) / 4)) →
          (∀ᶠ k : ℕ in atTop,
            ((v k : ℝ) + 1) ^ (16 * m + 3) ≤
              (512 * ε ^ 2) ^ 4 *
              (2304 * (1 + 3 *
                ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ^ 2) *
                S ^ 2 + 1) ^ 4 * D ^ 5) ∧
          Tendsto (fun k => velocityH3EnergyAt u (τ (v k))) atTop atTop ∧
          Tendsto (fun k =>
            ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖)
            atTop atTop) := by
  obtain ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
      hSeparate, hAnchor, hHigher⟩ :=
    h3Path_noL2Trace_exactAnchor_anyHigherBudget_criticalOuter_sharpEnergyFourth244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
    hSeparate, hAnchor, ?_⟩
  intro m F hF hFInt hUpper S D η ε hS hD hη hε hεη hSmall hCeil hCap hGeom
  have hCost := hHigher m F hF hFInt hUpper
    S D η ε hS hD hη hε hεη hSmall hCeil hCap hGeom
  let R : ℕ → ℝ := fun k => (v k : ℝ) + 1
  let E : ℕ → ℝ := fun k => velocityH3EnergyAt u (τ (v k))
  let Spectral : ℕ → ℝ := fun k =>
    ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖
  have hRadial : Tendsto (fun k => (R k) ^ 3) atTop atTop := by
    simpa only [R] using h3Path_strictMono_canonicalRadiusCube_escape244 v hv
  have hR (k : ℕ) : 1 ≤ R k := by
    dsimp only [R]
    have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hn]
  have hE (k : ℕ) : 0 ≤ E k := by
    dsimp only [E]
    exact le_trans zero_le_one (one_le_velocityH3EnergyAt u (τ (v k)))
  have hSpectralNonneg (k : ℕ) : 0 ≤ Spectral k := norm_nonneg _
  have hEnergyUpper (k : ℕ) : E k ≤ 1 + 3 * (Spectral k) ^ 2 := by
    have ht : τ (v k) ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 (hτ (v k)).1,
        (hτ (v k)).2⟩
    have hExact := h3AuditActualSpectralVelocityTotal_energy_exact
      hH3 (τ (v k)) ht
    have hSup := h3Path_spectralSquareEnergy_le_threeSupSquare244
      (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))
    dsimp only [E, Spectral]
    linarith only [hExact, hSup]
  have hCost' : ∀ᶠ k : ℕ in atTop,
      (R k) ^ (16 * m + 3) ≤
        ((512 * ε ^ 2) ^ 4 * D ^ 5) *
        ((2304 * S ^ 2) * E k + 1) ^ 4 := by
    filter_upwards [hCost] with k hk
    calc
      (R k) ^ (16 * m + 3) ≤
          (512 * ε ^ 2) ^ 4 *
          (2304 * E k * S ^ 2 + 1) ^ 4 * D ^ 5 := by
            simpa only [R, E] using hk
      _ = ((512 * ε ^ 2) ^ 4 * D ^ 5) *
          ((2304 * S ^ 2) * E k + 1) ^ 4 := by ring
  have hEnergyEscape : Tendsto E atTop atTop :=
    h3Path_scalar_higherSharpEnergyCost_forces_energyEscape244
      R E m ((512 * ε ^ 2) ^ 4 * D ^ 5) (2304 * S ^ 2)
      (by positivity) (by positivity)
      hR hE hRadial hCost'
  have hSpectralEscape : Tendsto Spectral atTop atTop :=
    h3Path_scalar_energyEscape_forces_threeSpectralEscape244
      E Spectral hEnergyEscape hSpectralNonneg hEnergyUpper
  have hSpectralCost : ∀ᶠ k : ℕ in atTop,
      (R k) ^ (16 * m + 3) ≤
        (512 * ε ^ 2) ^ 4 *
        (2304 * (1 + 3 * (Spectral k) ^ 2) * S ^ 2 + 1) ^ 4 * D ^ 5 := by
    filter_upwards [hCost] with k hk
    exact h3Path_higherBudget_energyFourth_to_spectralFourth244
      (R k) (E k) (Spectral k) S D ε m
      (hE k) hD (hEnergyUpper k)
      (by simpa only [R, E] using hk)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [R, Spectral] using hSpectralCost
  · simpa only [E] using hEnergyEscape
  · simpa only [Spectral] using hSpectralEscape

end
end PrimeTensor.FirstMonomialTriad
