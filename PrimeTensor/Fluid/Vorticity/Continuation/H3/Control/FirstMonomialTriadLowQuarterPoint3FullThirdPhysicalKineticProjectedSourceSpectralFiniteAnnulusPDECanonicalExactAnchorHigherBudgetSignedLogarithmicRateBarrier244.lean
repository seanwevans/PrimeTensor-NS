import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudgetSignedLogarithmicRadiusGate244
import Mathlib.Tactic

/-!
# Critical all-orders H3 signed logarithmic rate barrier

The existing physical logarithmic-radius gate gives, for every sufficiently late
canonical radius R_k, an intermediate time s between a fixed physical b and
the canonical anchor with

  p log R_k <= log C_b + 4 (T-b) g(s),     p=16m+3.

The canonical logarithmic radius escapes to +infinity. The finite constant
log C_b can therefore absorb at most half the radius term eventually:

  p log R_k <= 8 (T-b) g(s).

A separate sharp scalar obstruction excludes a proposed envelope
  g(s) <= c log R_k   on all intermediate physical times
whenever 4 (T-b)c < p. No such envelope is established by this module.
All high-moment, source, annular-cutoff and terminal-clock assumptions remain
explicit in the canonical theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- The logarithm of the canonical first-crossing radius escapes on every
strictly increasing natural selector. -/
theorem h3Path_strictMono_canonicalLogRadius_escape244
    (v : ℕ → ℕ) (hv : StrictMono v) :
    Tendsto (fun k : ℕ => Real.log ((v k : ℝ) + 1)) atTop atTop := by
  have hLower (k : ℕ) : k ≤ v k := by
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hStep : v k < v (k + 1) := hv (Nat.lt_succ_self k)
      omega
  apply Filter.tendsto_atTop.2
  intro M
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp M)
  filter_upwards [eventually_ge_atTop n] with k hk
  have hIndex : n ≤ v k := hk.trans (hLower k)
  have hCast : (n : ℝ) ≤ (v k : ℝ) := by exact_mod_cast hIndex
  have hRadius : Real.exp M ≤ (v k : ℝ) + 1 := by
    linarith only [hn, hCast]
  rw [← Real.log_exp M]
  exact Real.log_le_log (Real.exp_pos M) hRadius

/-- A constant-offset logarithmic budget gives an eventual explicit lower
physical rate at the SAME selected intermediate times. -/
theorem h3Path_scalar_logBudget_forces_halfSharpRate244
    (R : ℕ → ℝ) (G : ℝ → ℝ) (I : ℕ → Set ℝ)
    (p C d : ℝ)
    (hp : 0 < p) (_hd : 0 < d)
    (hLogTop : Tendsto (fun k => Real.log (R k)) atTop atTop)
    (hBudget : ∀ᶠ k : ℕ in atTop,
      ∃ s : ℝ, s ∈ I k ∧
        p * Real.log (R k) ≤ Real.log C + 4 * d * G s) :
    ∀ᶠ k : ℕ in atTop,
      ∃ s : ℝ, s ∈ I k ∧
        p * Real.log (R k) ≤ 8 * d * G s := by
  have hHalf : 0 < p / 2 := by positivity
  have hLarge : ∀ᶠ k : ℕ in atTop,
      (max (Real.log C) 0 + 1) / (p / 2) ≤ Real.log (R k) :=
    hLogTop.eventually
      (eventually_ge_atTop ((max (Real.log C) 0 + 1) / (p / 2)))
  filter_upwards [hBudget, hLarge] with k hk hLogLarge
  obtain ⟨s, hs, hCost⟩ := hk
  have hScaled : max (Real.log C) 0 + 1 ≤
      (p / 2) * Real.log (R k) := by
    calc
      _ ≤ Real.log (R k) * (p / 2) :=
        (div_le_iff₀ hHalf).1 hLogLarge
      _ = (p / 2) * Real.log (R k) := by ring
  have hMax : Real.log C ≤ max (Real.log C) 0 :=
    le_max_left _ _
  refine ⟨s, hs, ?_⟩
  nlinarith only [hCost, hScaled, hMax]

/-- The sharp subcritical logarithmic upper-rate coefficient is incompatible
with an eventual annular logarithmic radius budget. This is a conditional
exclusion of the proposed upper cap, not a physical PDE estimate. -/
theorem h3Path_scalar_logBudget_excludes_subcriticalRateEnvelope244
    (R : ℕ → ℝ) (G : ℝ → ℝ) (I : ℕ → Set ℝ)
    (p C d c : ℝ)
    (hd : 0 < d)
    (hSmall : 4 * d * c < p)
    (hLogTop : Tendsto (fun k => Real.log (R k)) atTop atTop)
    (hBudget : ∀ᶠ k : ℕ in atTop,
      ∃ s : ℝ, s ∈ I k ∧
        p * Real.log (R k) ≤ Real.log C + 4 * d * G s) :
    ¬ (∀ᶠ k : ℕ in atTop,
      ∀ s : ℝ, s ∈ I k → G s ≤ c * Real.log (R k)) := by
  intro hCap
  have hDelta : 0 < p - 4 * d * c := by linarith only [hSmall]
  have hLarge : ∀ᶠ k : ℕ in atTop,
      (max (Real.log C) 0 + 1) / (p - 4 * d * c) ≤
        Real.log (R k) :=
    hLogTop.eventually
      (eventually_ge_atTop
        ((max (Real.log C) 0 + 1) / (p - 4 * d * c)))
  obtain ⟨k, hkBudget, hkCap, hkLarge⟩ :=
    (hBudget.and (hCap.and hLarge)).exists
  obtain ⟨s, hs, hCost⟩ := hkBudget
  have hUpper := hkCap s hs
  have hScale : 4 * d * G s ≤ 4 * d * (c * Real.log (R k)) :=
    mul_le_mul_of_nonneg_left hUpper (by positivity)
  have hRadial : max (Real.log C) 0 + 1 ≤
      (p - 4 * d * c) * Real.log (R k) := by
    calc
      _ ≤ Real.log (R k) * (p - 4 * d * c) :=
        (div_le_iff₀ hDelta).1 hkLarge
      _ = (p - 4 * d * c) * Real.log (R k) := by ring
  have hMax : Real.log C ≤ max (Real.log C) 0 :=
    le_max_left _ _
  nlinarith only [hCost, hScale, hRadial, hMax]

/-- The original disjoint canonical exact-anchor witnesses carry an
EVENTUAL logarithmic lower rate and exclude any subcritical logarithmic
upper envelope on their physical intermediate intervals. -/
theorem h3Path_noL2Trace_exactAnchor_higherBudget_signedLogRateBarrier244
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
            (∀ᶠ k : ℕ in atTop,
              ∃ s : ℝ, s ∈ Set.Ioo b (τ (v k)) ∧
                ((16 * m + 3 : ℕ) : ℝ) *
                  Real.log ((v k : ℝ) + 1) ≤
                  8 * (T - b) *
                    h3PathFullDissipationTransportExcessRate u s) ∧
            (∀ c : ℝ, 4 * (T - b) * c < ((16 * m + 3 : ℕ) : ℝ) →
              ¬ (∀ᶠ k : ℕ in atTop,
                ∀ s : ℝ, s ∈ Set.Ioo b (τ (v k)) →
                  h3PathFullDissipationTransportExcessRate u s ≤
                    c * Real.log ((v k : ℝ) + 1)))) := by
  obtain ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
      hSeparate, hAnchor, hHigher⟩ :=
    h3Path_noL2Trace_exactAnchor_higherBudget_signedLogRadiusGate244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
    hSeparate, hAnchor, ?_⟩
  intro m F hF hFInt hUpper S D η ε hS hD hη hε hεη
    hSmall hCeil hCap hGeom b hb
  let R : ℕ → ℝ := fun k => (v k : ℝ) + 1
  let G : ℝ → ℝ := h3PathFullDissipationTransportExcessRate u
  let I : ℕ → Set ℝ := fun k => Set.Ioo b (τ (v k))
  let p : ℝ := ((16 * m + 3 : ℕ) : ℝ)
  let d : ℝ := T - b
  let Cb : ℝ := ((512 * ε ^ 2) ^ 4 * D ^ 5) *
    (2304 * velocityH3EnergyAt u b * S ^ 2 + 1) ^ 4
  have hp : 0 < p := by dsimp only [p]; positivity
  have hd : 0 < d := by dsimp only [d]; exact sub_pos.mpr hb.2
  have hLogTop : Tendsto (fun k => Real.log (R k)) atTop atTop := by
    simpa only [R] using h3Path_strictMono_canonicalLogRadius_escape244 v hv
  have hBudget : ∀ᶠ k : ℕ in atTop,
      ∃ s : ℝ, s ∈ I k ∧
        p * Real.log (R k) ≤ Real.log Cb + 4 * d * G s := by
    have hOriginal := hHigher m F hF hFInt hUpper
      S D η ε hS hD hη hε hεη hSmall hCeil hCap hGeom b hb
    filter_upwards [hOriginal] with k hk
    obtain ⟨s, hs, _, hTerminal⟩ := hk
    refine ⟨s, hs, ?_⟩
    simpa only [p, R, Cb, d, G, I] using hTerminal
  constructor
  · have hRate := h3Path_scalar_logBudget_forces_halfSharpRate244
      R G I p Cb d hp hd hLogTop hBudget
    simpa only [p, R, d, G, I] using hRate
  · intro c hc
    have hForbidden := h3Path_scalar_logBudget_excludes_subcriticalRateEnvelope244
      R G I p Cb d c hd hc hLogTop hBudget
    simpa only [p, R, d, G, I] using hForbidden

end
end PrimeTensor.FirstMonomialTriad
