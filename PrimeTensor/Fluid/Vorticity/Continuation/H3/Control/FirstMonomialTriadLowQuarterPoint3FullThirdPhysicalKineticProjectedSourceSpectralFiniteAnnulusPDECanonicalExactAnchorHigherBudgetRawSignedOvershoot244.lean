import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudgetPointwiseSignedTransport244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Integrability
import Mathlib.Tactic

/-!
# Cofinal H³ energy escape forces unbounded raw signed PDE transport margins

A cofinal sequence of physical H³ energies escaping to +∞ on a finite
terminal interval cannot have a uniformly upper-bounded time derivative
on any terminal subinterval. This is a one-dimensional comparison theorem:
apply the mean-value theorem directly between an interior midpoint and a
later canonical time with energy exceeding M times the terminal gap.

Using the exact signed physical balance E' + 2 D = -Transport, every terminal
tail therefore contains points where -Transport - 2 D exceeds ANY fixed M.
Equivalently the RAW positive full-dissipation transport excess has no finite
pointwise ceiling on any terminal tail. This is not an L¹ estimate and says
nothing about the pointwise normalized ratio being unbounded.

The canonical theorem retains the same original disjoint first-crossing
anchors and ALL the explicit conditional higher-moment, source, critical
outer-cutoff, and weighted terminal-clock hypotheses.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Any real energy with a differentiable strict tail and cofinal escape has
arbitrarily large positive *raw time derivatives* somewhere on every terminal
subinterval. Choose a late high-energy secant whose slope exceeds M; no shifted function is differentiated. -/
theorem h3Path_scalar_cofinalEscape_forces_unboundedDerivativeEveryTail244
    {E : ℝ → ℝ} {a T : ℝ} (t : ℕ → ℝ)
    (hDeriv : ∀ s : ℝ, s ∈ Set.Ioo a T →
      HasDerivAt E (deriv E s) s)
    (ht : ∀ k, t k ∈ Set.Ioo a T)
    (hCofinal : Tendsto t atTop (𝓝 T))
    (hEscape : Tendsto (fun k => E (t k)) atTop atTop) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ M : ℝ, 0 ≤ M →
        ∃ s : ℝ, s ∈ Set.Ioo b T ∧ M < deriv E s := by
  intro b hb M hM
  let s₀ : ℝ := (b + T) / 2
  have hs₀ : s₀ ∈ Set.Ioo b T := by
    dsimp only [s₀]
    constructor <;> linarith only [hb.2]
  have hLate : ∀ᶠ k : ℕ in atTop, s₀ < t k :=
    hCofinal.eventually (Ioi_mem_nhds hs₀.2)
  have hLarge : ∀ᶠ k : ℕ in atTop,
      E s₀ + M * (T - s₀) + 1 ≤ E (t k) :=
    hEscape.eventually
      (eventually_ge_atTop (E s₀ + M * (T - s₀) + 1))
  obtain ⟨k, hkLate, hkLarge⟩ := (hLate.and hLarge).exists
  have hInside (x : ℝ) (hx : x ∈ Set.Icc s₀ (t k)) :
      x ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le (lt_trans hb.1 hs₀.1) hx.1,
      lt_of_le_of_lt hx.2 (ht k).2⟩
  have hContinuous : ContinuousOn E (Set.Icc s₀ (t k)) := by
    intro x hx
    exact (hDeriv x (hInside x hx)).continuousAt.continuousWithinAt
  have hDifferentiable : DifferentiableOn ℝ E (Set.Ioo s₀ (t k)) := by
    intro x hx
    exact (hDeriv x (hInside x ⟨hx.1.le, hx.2.le⟩)).differentiableAt.differentiableWithinAt
  obtain ⟨s, hs, hSlope⟩ :=
    exists_deriv_eq_slope E hkLate hContinuous hDifferentiable
  have hGap : 0 < t k - s₀ := sub_pos.mpr hkLate
  have hGapLe : t k - s₀ ≤ T - s₀ := by
    linarith only [(ht k).2]
  have hScaledGap : M * (t k - s₀) ≤ M * (T - s₀) :=
    mul_le_mul_of_nonneg_left hGapLe hM
  have hNumerator : M * (t k - s₀) < E (t k) - E s₀ := by
    linarith only [hkLarge, hScaledGap]
  have hRate : M < (E (t k) - E s₀) / (t k - s₀) :=
    (lt_div_iff₀ hGap).2 hNumerator
  have hDerivLarge : M < deriv E s := by
    rw [hSlope]
    exact hRate
  exact ⟨s,
    ⟨lt_trans hs₀.1 hs.1, lt_trans hs.2 (ht k).2⟩,
    hDerivLarge⟩

/-- Physical cofinal H³ escape forces the signed H³ transport to exceed
BOTH copies of viscous dissipation by an arbitrarily prescribed raw amount
at some time on each terminal subinterval. -/
theorem h3Path_cofinalPhysicalEnergyEscape_forces_arbitrarySignedTransportMargin244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℕ → ℝ)
    (ht : ∀ k, t k ∈ Set.Ioo a T)
    (hCofinal : Tendsto t atTop (𝓝 T))
    (hEscape : Tendsto (fun k => velocityH3EnergyAt u (t k)) atTop atTop) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ M : ℝ, 0 ≤ M →
        ∃ s : ℝ, s ∈ Set.Ioo b T ∧
          M + 2 * velocityH3DissipationAt u s <
            - velocityH3TransportDerivativeAt u s := by
  have hDeriv (s : ℝ) (hs : s ∈ Set.Ioo a T) :
      HasDerivAt (velocityH3EnergyAt u)
        (deriv (velocityH3EnergyAt u) s) s := by
    have hIds : H3OrderEnergyDerivativeIdentities u s :=
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
        u T hH3 a hClass s hs
    rw [deriv_velocityH3EnergyAt hIds]
    exact hasDerivAt_velocityH3EnergyAt hIds
  intro b hb M hM
  obtain ⟨s, hs, hLarge⟩ :=
    h3Path_scalar_cofinalEscape_forces_unboundedDerivativeEveryTail244
      t hDeriv ht hCofinal hEscape b hb M hM
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, hs.2⟩
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass hsClass
  refine ⟨s, hs, ?_⟩
  linarith only [hLarge, hBalance]

/-- The raw positive full-dissipation transport excess exceeds M whenever
the signed transport margin exceeds M. No normalization is introduced. -/
theorem h3Path_arbitrarySignedTransportMargin_forces_rawPositiveExcess244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (s M : ℝ)
    (hMargin : M + 2 * velocityH3DissipationAt u s <
      - velocityH3TransportDerivativeAt u s) :
    M < h3PathRawFullDissipationTransportExcessPart u s := by
  have hRaw : M < - velocityH3TransportDerivativeAt u s -
      2 * velocityH3DissipationAt u s := by
    linarith only [hMargin]
  unfold h3PathRawFullDissipationTransportExcessPart
  exact lt_of_lt_of_le hRaw (le_max_right _ _)

/-- The *same* canonical first-crossing witnesses yield an arbitrarily large
raw signed H³ transport margin on every terminal subinterval, provided the
original higher-radial envelope, source ceiling, cutoff cap and noncompressed
weighted clock hypotheses hold. The positive NORMALIZED excess need not be
unbounded: it is the raw numerator that is forced to escape pointwise. -/
theorem h3Path_noL2Trace_exactAnchor_higherBudget_unboundedRawSignedTransport244
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
            ∀ M : ℝ, 0 ≤ M →
              ∃ s : ℝ, s ∈ Set.Ioo b T ∧
                M + 2 * velocityH3DissipationAt u s <
                  - velocityH3TransportDerivativeAt u s ∧
                M < h3PathRawFullDissipationTransportExcessPart u s) := by
  obtain ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
      hSeparate, hAnchor, hHigher⟩ :=
    h3Path_noL2Trace_exactAnchor_allOrdersCriticalBudget_spectralEnergyGate244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal,
    hτ, hSeparate, hAnchor, ?_⟩
  intro m F hF hFInt hUpper S D η ε hS hD hη hε hεη
    hSmall hCeil hCap hGeom b hb M hM
  obtain ⟨_hCost, hEnergyEscape, _hSpectralEscape⟩ :=
    hHigher m F hF hFInt hUpper S D η ε hS hD hη hε
      hεη hSmall hCeil hCap hGeom
  obtain ⟨s, hs, hMargin⟩ :=
    (h3Path_cofinalPhysicalEnergyEscape_forces_arbitrarySignedTransportMargin244
      hH3 hClass (fun k => τ (v k))
      (fun k => hτ (v k)) hCofinal hEnergyEscape) b hb M hM
  refine ⟨s, hs, hMargin, ?_⟩
  exact h3Path_arbitrarySignedTransportMargin_forces_rawPositiveExcess244
    u s M hMargin

end
end PrimeTensor.FirstMonomialTriad
