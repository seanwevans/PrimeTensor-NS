import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudgetNormalizedSignedOvershoot244
import Mathlib.Tactic

/-!
# Quantitative signed H³ transport growth required by all-orders canonical radii

The exact physical H³ logarithmic secant between any two strict times b < t
is realized at an intermediate time s. The exact signed energy balance then
gives the one-point energy ceiling

  E₃(t) ≤ E₃(b) exp((t-b) max(0,(-Transport₃(s)-2D₃(s))/E₃(s))).

Substitution into the already-proved arbitrary-order fourth-power critical
annular cost yields an explicit logarithmic/physical-rate gate for the original
canonical first-crossing anchors. This does not control the signed rate or
prove any higher-moment, source, cutoff, or noncompression assumption.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- At an intermediate physical time, the exact full-dissipation signed
transport rate controls the complete positive logarithmic secant and hence
the energy at the later time. This uses genuine physical H³ derivatives. -/
theorem h3Path_physicalH3_signedLogSecant_exponentialCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b t : ℝ)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo a T)
    (hbt : b < t) :
    ∃ s : ℝ, s ∈ Set.Ioo b t ∧
      velocityH3EnergyAt u t ≤
        velocityH3EnergyAt u b *
          Real.exp ((t - b) * h3PathFullDissipationTransportExcessRate u s) := by
  let L : ℝ → ℝ := fun x => Real.log (velocityH3EnergyAt u x)
  have hInside (x : ℝ) (hx : x ∈ Set.Icc b t) :
      x ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hb.1 hx.1, lt_of_le_of_lt hx.2 ht.2⟩
  have hPos (x : ℝ) : 0 < velocityH3EnergyAt u x :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u x)
  have hLogDeriv (x : ℝ) (hx : x ∈ Set.Ioo a T) :
      HasDerivAt L (deriv L x) x := by
    have hEnergyDeriv : HasDerivAt (velocityH3EnergyAt u)
        (deriv (velocityH3EnergyAt u) x) x :=
      h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_orderEnergyDerivativeIdentities
        h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
        u T hH3 a hClass x hx
    have hHas : HasDerivAt L
        (deriv (velocityH3EnergyAt u) x / velocityH3EnergyAt u x) x := by
      change HasDerivAt (fun y : ℝ => Real.log (velocityH3EnergyAt u y))
        (deriv (velocityH3EnergyAt u) x / velocityH3EnergyAt u x) x
      exact hEnergyDeriv.log (ne_of_gt (hPos x))
    rw [hHas.deriv]
    exact hHas
  have hContinuous : ContinuousOn L (Set.Icc b t) := by
    intro x hx
    exact (hLogDeriv x (hInside x hx)).continuousAt.continuousWithinAt
  have hDifferentiable : DifferentiableOn ℝ L (Set.Ioo b t) := by
    intro x hx
    exact (hLogDeriv x (hInside x ⟨hx.1.le, hx.2.le⟩)).differentiableAt.differentiableWithinAt
  obtain ⟨s, hs, hSlope⟩ :=
    exists_deriv_eq_slope L hbt hContinuous hDifferentiable
  have hsClass : s ∈ Set.Ioo a T :=
    hInside s ⟨hs.1.le, hs.2.le⟩
  have hRateEq :=
    h3PathFullDissipationTransportExcessRate_eq_positiveLogEnergyGrowthRate
      hH3 hClass hsClass
  have hRateUpper : deriv L s ≤
      h3PathFullDissipationTransportExcessRate u s := by
    rw [hRateEq]
    change deriv L s ≤ max 0 (deriv L s)
    exact le_max_right _ _
  have hGap : 0 < t - b := sub_pos.mpr hbt
  have hSecant : deriv L s * (t - b) = L t - L b := by
    rw [hSlope]
    exact div_mul_cancel₀ _ (ne_of_gt hGap)
  have hScaled := mul_le_mul_of_nonneg_right hRateUpper hGap.le
  rw [hSecant] at hScaled
  have hLogUpper : L t ≤ L b +
      (t - b) * h3PathFullDissipationTransportExcessRate u s := by
    linarith only [hScaled]
  have hExp := Real.exp_le_exp.mpr hLogUpper
  refine ⟨s, hs, ?_⟩
  calc
    velocityH3EnergyAt u t = Real.exp (L t) := by
      dsimp only [L]
      exact (Real.exp_log (hPos t)).symm
    _ ≤ Real.exp (L b +
        (t - b) * h3PathFullDissipationTransportExcessRate u s) := hExp
    _ = velocityH3EnergyAt u b *
        Real.exp ((t - b) * h3PathFullDissipationTransportExcessRate u s) := by
      rw [Real.exp_add]
      dsimp only [L]
      rw [Real.exp_log (hPos b)]

/-- An energy ceiling converts the critical fourth-power cost into a
quantitative exponential constraint on signed physical transport. -/
theorem h3Path_higherBudget_energyFourth_to_signedExponentialFourth244
    (R E E₀ S D ε x : ℝ) (m : ℕ)
    (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hEnergy : E ≤ E₀ * Real.exp x)
    (hCost : R ^ (16 * m + 3) ≤
      (512 * ε ^ 2) ^ 4 * (2304 * E * S ^ 2 + 1) ^ 4 * D ^ 5) :
    R ^ (16 * m + 3) ≤
      (512 * ε ^ 2) ^ 4 *
        (2304 * (E₀ * Real.exp x) * S ^ 2 + 1) ^ 4 * D ^ 5 := by
  have hScaled := mul_le_mul_of_nonneg_left hEnergy
    (show 0 ≤ 2304 * S ^ 2 by positivity)
  have hAdd : 2304 * E * S ^ 2 + 1 ≤
      2304 * (E₀ * Real.exp x) * S ^ 2 + 1 := by
    calc
      2304 * E * S ^ 2 + 1 = (2304 * S ^ 2) * E + 1 := by ring
      _ ≤ (2304 * S ^ 2) * (E₀ * Real.exp x) + 1 := by
        linarith only [hScaled]
      _ = 2304 * (E₀ * Real.exp x) * S ^ 2 + 1 := by ring
  have hPow : (2304 * E * S ^ 2 + 1) ^ 4 ≤
      (2304 * (E₀ * Real.exp x) * S ^ 2 + 1) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hAdd 4
  have hCoefficient : 0 ≤ (512 * ε ^ 2) ^ 4 * D ^ 5 := by positivity
  have hBound := mul_le_mul_of_nonneg_left hPow hCoefficient
  calc
    R ^ (16 * m + 3) ≤
        (512 * ε ^ 2) ^ 4 * (2304 * E * S ^ 2 + 1) ^ 4 * D ^ 5 := hCost
    _ = ((512 * ε ^ 2) ^ 4 * D ^ 5) *
        (2304 * E * S ^ 2 + 1) ^ 4 := by ring
    _ ≤ ((512 * ε ^ 2) ^ 4 * D ^ 5) *
        (2304 * (E₀ * Real.exp x) * S ^ 2 + 1) ^ 4 := hBound
    _ = (512 * ε ^ 2) ^ 4 *
        (2304 * (E₀ * Real.exp x) * S ^ 2 + 1) ^ 4 * D ^ 5 := by ring

/-- The SAME canonical first-crossing anchors carry a quantitative
R^(16m+3) signed-transport exponential gate. Every higher-moment, attained
source ceiling, eighth-power cutoff, small-tolerance and weighted
terminal-clock assumption from the existing all-orders theorem remains explicit. -/
theorem h3Path_noL2Trace_exactAnchor_higherBudget_signedExponentialSecantGate244
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
          ∀ b : ℝ, b ∈ Set.Ioo a T →
          ∀ᶠ k : ℕ in atTop,
            ∃ s : ℝ, s ∈ Set.Ioo b (τ (v k)) ∧
              ((v k : ℝ) + 1) ^ (16 * m + 3) ≤
                (512 * ε ^ 2) ^ 4 *
                  (2304 * (velocityH3EnergyAt u b *
                    Real.exp ((τ (v k) - b) *
                      h3PathFullDissipationTransportExcessRate u s)) *
                      S ^ 2 + 1) ^ 4 * D ^ 5) := by
  obtain ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
      hSeparate, hAnchor, hHigher⟩ :=
    h3Path_noL2Trace_exactAnchor_anyHigherBudget_criticalOuter_sharpEnergyFourth244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
    hSeparate, hAnchor, ?_⟩
  intro m F hF hFInt hUpper S D η ε hS hD hη hε hεη
    hSmall hCeil hCap hGeom b hb
  have hCost := hHigher m F hF hFInt hUpper
    S D η ε hS hD hη hε hεη hSmall hCeil hCap hGeom
  have hLate : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hCofinal.eventually (Ioi_mem_nhds hb.2)
  filter_upwards [hCost, hLate] with k hk hkLate
  obtain ⟨s, hs, hEnergyCeiling⟩ :=
    h3Path_physicalH3_signedLogSecant_exponentialCeiling244
      hH3 hClass b (τ (v k)) hb (hτ (v k)) hkLate
  refine ⟨s, hs, ?_⟩
  exact h3Path_higherBudget_energyFourth_to_signedExponentialFourth244
    ((v k : ℝ) + 1)
    (velocityH3EnergyAt u (τ (v k)))
    (velocityH3EnergyAt u b) S D ε
    ((τ (v k) - b) * h3PathFullDissipationTransportExcessRate u s) m
    (le_trans zero_le_one (one_le_velocityH3EnergyAt u (τ (v k))))
    hD hEnergyCeiling hk

end
end PrimeTensor.FirstMonomialTriad
