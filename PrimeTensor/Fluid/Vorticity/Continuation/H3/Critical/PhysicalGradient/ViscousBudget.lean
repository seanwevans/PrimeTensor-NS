import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.RiccatiBarrier
import Mathlib.Tactic

/-!
# A physical viscosity-inclusive gradient budget for critical H³ annuli

The committed all-orders log-radius theorem forces the exact positive signed
full-dissipation rate g(s) to exceed a logarithmic radial cost at an actual
intermediate time. On times where g(s)>0, the full positive-part definition
can be removed and the exact physical transport identity gives

  g(s) + 2 D₃(s)/E₃(s) = -Transport₃(s)/E₃(s).

The complete H³ PDE commutator controls this latter quantity by
4422*(1+|h(s)|), for the proven canonical C¹-gradient upper envelope h.
Consequently both the radius and the full positive viscous share must be
paid for by the same physical gradient envelope at the selected intermediate
time. We do NOT claim that this h majorant is a lower bound for the actual
gradient supremum, or that the conditional higher-budget assumptions follow
from the Navier–Stokes PDE without further proof.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- On a positive-growth physical slice, the full normalized signed excess
PLUS both copies of the actual viscous expenditure is paid by the already
closed nonlinear H³ gradient commutator. No dissipation term is dropped. -/
theorem h3Path_positiveFullExcess_add_viscousShare_le_gradientEnvelope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hPositive : 0 < h3PathFullDissipationTransportExcessRate u s) :
    h3PathFullDissipationTransportExcessRate u s +
        (2 * velocityH3DissipationAt u s) / velocityH3EnergyAt u s ≤
      4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|) := by
  let h : ℝ → ℝ := h3PathCanonicalSqrtEnergyGradientEnvelope u
  let E : ℝ := velocityH3EnergyAt u s
  let D : ℝ := velocityH3DissipationAt u s
  let Tr : ℝ := velocityH3TransportDerivativeAt u s
  let z : ℝ := (-Tr - 2 * D) / E
  have hE : 0 < E := by
    dsimp only [E]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u s)
  have hTransport : H3TransportCommutatorBoundAt u h 4422 s :=
    (h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3 hClass
      (fun t ht => h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass ht)
      s hs).2
  have hNeg : -Tr ≤ (4422 * (1 + |h s|)) * E := by
    dsimp only [Tr, E]
    exact neg_transport_le_of_commutatorBound hTransport
  have hDiv : (-Tr) / E ≤ 4422 * (1 + |h s|) :=
    (div_le_iff₀ hE).2 hNeg
  have hzPositive : 0 < z := by
    by_contra hn
    have hzNonpos : z ≤ 0 := le_of_not_gt hn
    have hZero : h3PathFullDissipationTransportExcessRate u s = 0 := by
      change max 0 z = 0
      exact max_eq_left hzNonpos
    rw [hZero] at hPositive
    exact (not_lt_of_ge (le_refl (0 : ℝ))) hPositive
  have hRateEq : h3PathFullDissipationTransportExcessRate u s = z := by
    change max 0 z = z
    exact max_eq_right hzPositive.le
  calc
    h3PathFullDissipationTransportExcessRate u s +
        (2 * velocityH3DissipationAt u s) / velocityH3EnergyAt u s =
        (-Tr) / E := by
          rw [hRateEq]
          dsimp only [z, Tr, D, E]
          ring
    _ ≤ 4422 * (1 + |h s|) := hDiv
    _ = 4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|) := rfl

/-- Algebraic transfer of an actual logarithmic radial-rate floor to a
viscosity-inclusive H³ gradient upper budget, retaining the exact 2D/E term. -/
theorem h3Path_scalar_logRate_viscousShare_budget244
    (L p d g z A : ℝ)
    (hd : 0 ≤ d)
    (hRate : p * L ≤ 8 * d * g)
    (hPDE : g + 2 * z ≤ A) :
    p * L + 16 * d * z ≤ 8 * d * A := by
  have hCoeff : 0 ≤ 8 * d := mul_nonneg (by norm_num) hd
  have hScaled := mul_le_mul_of_nonneg_left hPDE hCoeff
  nlinarith only [hRate, hScaled]

/-- At precisely the SAME disjoint canonical first-crossing witnesses, the
physical gradient envelope pays both the logarithmic critical annulus cost
and the two-copy viscous expenditure. The higher radial moment majorant,
source ceiling, eighth-power cutoff, small tolerance and noncompressed
terminal clock all remain explicit premises of this implication. -/
theorem h3Path_noL2Trace_exactAnchor_higherBudget_physicalViscousGradientBudget244
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
                0 < h3PathFullDissipationTransportExcessRate u s ∧
                ((16 * m + 3 : ℕ) : ℝ) *
                  Real.log ((v k : ℝ) + 1) +
                  16 * (T - b) *
                    (velocityH3DissipationAt u s /
                      velocityH3EnergyAt u s) ≤
                  8 * (T - b) *
                    (4422 * (1 +
                      |h3PathCanonicalSqrtEnergyGradientEnvelope u s|))) := by
  obtain ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
      hSeparate, hAnchor, hHigher⟩ :=
    h3Path_noL2Trace_exactAnchor_higherBudget_signedLogRateBarrier244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
    hSeparate, hAnchor, ?_⟩
  intro m F hF hFInt hUpper S D η ε hS hD hη hε hεη
    hSmall hCeil hCap hGeom b hb
  obtain ⟨hRateLate, _hForbidden⟩ :=
    hHigher m F hF hFInt hUpper S D η ε hS hD hη hε
      hεη hSmall hCeil hCap hGeom b hb
  have hLogTop : Tendsto
      (fun k : ℕ => Real.log ((v k : ℝ) + 1)) atTop atTop :=
    h3Path_strictMono_canonicalLogRadius_escape244 v hv
  have hPositiveLog : ∀ᶠ k : ℕ in atTop,
      1 ≤ Real.log ((v k : ℝ) + 1) :=
    hLogTop.eventually (eventually_ge_atTop 1)
  have hp : 0 < ((16 * m + 3 : ℕ) : ℝ) := by positivity
  have hd : 0 ≤ T - b := sub_nonneg.mpr hb.2.le
  have hCoeff : 0 ≤ 8 * (T - b) := mul_nonneg (by norm_num) hd
  filter_upwards [hRateLate, hPositiveLog] with k hk hkLog
  obtain ⟨s, hs, hRate⟩ := hk
  have hPL : 0 < ((16 * m + 3 : ℕ) : ℝ) *
      Real.log ((v k : ℝ) + 1) :=
    lt_of_lt_of_le (mul_pos hp (by linarith only [hkLog])) (le_refl _)
  have hGPos : 0 < h3PathFullDissipationTransportExcessRate u s := by
    by_contra hn
    have hGNonpos : h3PathFullDissipationTransportExcessRate u s ≤ 0 :=
      le_of_not_gt hn
    have hBound : 8 * (T - b) *
        h3PathFullDissipationTransportExcessRate u s ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hCoeff hGNonpos
    exact (not_lt_of_ge (le_trans hRate hBound)) hPL
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, lt_trans hs.2 (hτ (v k)).2⟩
  have hPDE := h3Path_positiveFullExcess_add_viscousShare_le_gradientEnvelope244
    hH3 hClass hsClass hGPos
  have hViscous := h3Path_scalar_logRate_viscousShare_budget244
    (Real.log ((v k : ℝ) + 1))
    (((16 * m + 3 : ℕ) : ℝ)) (T - b)
    (h3PathFullDissipationTransportExcessRate u s)
    (velocityH3DissipationAt u s / velocityH3EnergyAt u s)
    (4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|))
    hd hRate
    (by convert hPDE using 1 <;> ring)
  exact ⟨s, hs, hGPos, hViscous⟩

end
end PrimeTensor.FirstMonomialTriad
