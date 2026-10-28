import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakIntegratedTransportResidual244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopAutomaticLogClock244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalMeasurability
import Mathlib.Tactic

/-!
# Canonical peak half-loss: automatic compact-time signed transport integrability

A compact preterminal interval supports a continuous canonical scalar energy
E(t) and the continuous Landau majorant
 M(t) = 4422 * (1 + |C₁ sqrt(E(t))|) * E(t).
The exact physical PDE implies E'(t) <= M(t) since D(t) >= 0.
The previous one-sided derivative integrability lemma then makes E' integrable
on every compact interior interval, without requiring continuity of E'.
With the given finite global dissipation budget, the exact PDE identity
Tr(t) = -E'(t) - 2D(t) provides the interval integrability of the signed
transport channel, not just a formal energy residual.

The cofinal theorem transports this identity to the same canonical source
maximizers and half-loss witnesses under unchanged conditional critical-width
hypotheses. It does not establish an upper transport bound or a contradiction.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Finite global viscous expenditure and the existing local Landau control
make the actual physical H³ energy derivative Lebesgue integrable on any
compact strict preterminal interval. The bound is one-sided, so derivative
continuity is not used. -/
theorem h3Path_canonicalEnergyDerivative_intervalIntegrable_automatic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (s r : ℝ) (hs : s ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo a T)
    (hsr : s ≤ r) :
    IntervalIntegrable (deriv (velocityH3EnergyAt u)) volume s r := by
  let F : ℝ → ℝ := velocityH3EnergyAt u
  let M : ℝ → ℝ := fun t =>
    (4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u t|)) *
      velocityH3EnergyAt u t
  have hSubset : Set.Icc s r ⊆ Set.Ioo a T := by
    intro t ht
    exact ⟨lt_of_lt_of_le hs.1 ht.1, lt_of_le_of_lt ht.2 hr.2⟩
  have hEnergyCont : ContinuousOn F (Set.Ioo a T) :=
    continuousOn_velocityH3EnergyAt_on_energyClassTail hH3 hClass
  have hCoefCont : ContinuousOn
      (fun t : ℝ =>
        4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u t|))
      (Set.Ioo a T) :=
    continuousOn_h3PathCanonicalSqrtEnergyGradientCoefficient_on_energyClassTail
      hH3 hClass
  have hMCont : ContinuousOn M (Set.Icc s r) :=
    (hCoefCont.mul hEnergyCont).mono hSubset
  obtain ⟨t₀, _ht₀, hMax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hsr) hMCont
  have hHasDeriv (t : ℝ) (ht : t ∈ Set.Icc s r) :
      HasDerivAt F (deriv F t) t :=
    h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_orderEnergyDerivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      u T hH3 a hClass t (hSubset ht)
  have hCont : ContinuousOn F (Set.Icc s r) :=
    hEnergyCont.mono hSubset
  have hDeriv : ∀ t, t ∈ Set.Ioo s r →
      HasDerivAt F (deriv F t) t := by
    intro t ht
    exact hHasDeriv t ⟨ht.1.le, ht.2.le⟩
  have hBound : ∀ t, t ∈ Set.Ioo s r → deriv F t ≤ M t₀ := by
    intro t ht
    have htClosed : t ∈ Set.Icc s r := ⟨ht.1.le, ht.2.le⟩
    have htClass : t ∈ Set.Ioo a T := hSubset htClosed
    have hTransport :
        |velocityH3TransportDerivativeAt u t| ≤ M t := by
      exact (h3TransportControlledOnTail_of_h3Path_exactPDEPairing
        h3PathEnergyClassProducesPDEPairingIntegrability_closed
        hH3 hClass
        (fun q hq => h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass hq)
        t htClass).2
    have hBal := deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass htClass
    have hD := velocityH3DissipationAt_nonneg u t
    have hUpper : deriv F t ≤ M t := by
      have hNeg : -velocityH3TransportDerivativeAt u t ≤
          |velocityH3TransportDerivativeAt u t| := neg_le_abs _
      dsimp only [F]
      linarith only [hBal, hD, hTransport, hNeg]
    exact hUpper.trans (hMax htClosed)
  exact h3_scalar_signedRate_intervalIntegrable_of_upperDerivative244
    F (deriv F) s r (M t₀) hsr hCont hDeriv hBound

/-- The true signed physical H³ transport is automatically interval-integrable
as the difference of the actual integrable energy derivative and viscosity.
The equality is used on the open interval, avoiding endpoint assumptions. -/
theorem h3Path_canonicalSignedTransport_intervalIntegrable_automatic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (s r : ℝ) (hs : s ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo a T)
    (hsr : s ≤ r) :
    IntervalIntegrable (velocityH3TransportDerivativeAt u) volume s r := by
  have hDerivativeInt :=
    h3Path_canonicalEnergyDerivative_intervalIntegrable_automatic244
      hH3 hClass s r hs hr hsr
  have hDIntLocal : IntervalIntegrable
      (velocityH3DissipationAt u) volume s r := by
    apply hDInt.mono_set
    rw [Set.uIcc_of_le hsr, Set.uIcc_of_le hClass.terminal_start.2.le]
    exact Set.Icc_subset_Icc hs.1.le hr.2.le
  have hExpr : IntervalIntegrable
      (fun t : ℝ => -deriv (velocityH3EnergyAt u) t -
        2 * velocityH3DissipationAt u t) volume s r :=
    hDerivativeInt.neg.sub (hDIntLocal.const_mul 2)
  have hEq : Set.EqOn
      (fun t : ℝ => -deriv (velocityH3EnergyAt u) t -
        2 * velocityH3DissipationAt u t)
      (velocityH3TransportDerivativeAt u) (Set.uIoo s r) := by
    intro t ht
    rw [Set.uIoo_of_le hsr] at ht
    have htClass : t ∈ Set.Ioo a T :=
      ⟨lt_trans hs.1 ht.1, lt_trans ht.2 hr.2⟩
    have hBalance := deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass htClass
    dsimp
    linarith only [hBalance]
  exact hExpr.congr_uIoo hEq

/-- With no added local temporal regularity premises, the exact signed
physical transport expenditure equals the canonical H³ energy residual. -/
theorem h3Path_canonicalSignedTransportResidual_eq_integral_automatic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (s r : ℝ) (hs : s ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo a T)
    (hsr : s < r) :
    velocityH3EnergyAt u s - velocityH3EnergyAt u r -
        2 * (∫ t in s..r, velocityH3DissipationAt u t) =
      ∫ t in s..r, velocityH3TransportDerivativeAt u t := by
  exact h3Path_physicalSignedTransportResidual_eq_integral244
    hH3 hClass hDInt s r hs hr hsr
    (h3Path_canonicalEnergyDerivative_intervalIntegrable_automatic244
      hH3 hClass s r hs hr hsr.le)
    (h3Path_canonicalSignedTransport_intervalIntegrable_automatic244
      hH3 hClass hDInt s r hs hr hsr.le)

/-- If the canonical H³ peak loses half-amplitude beyond the viscous budget,
its true signed transport integral is positive and exceeds A²/8. There are
no new assumptions on temporal transport or energy-derivative integrability. -/
theorem h3Path_physicalHalfLoss_positiveIntegratedTransport_automatic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (s r : ℝ) (hs : s ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo a T)
    (hsr : s < r)
    (hHalf : ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2)
    (hThreshold :
      16 * (∫ t in a..T, velocityH3DissipationAt u t) ≤
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2) :
    ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 / 8 <
      ∫ t in s..r, velocityH3TransportDerivativeAt u t := by
  exact h3Path_physicalHalfLoss_positiveIntegratedTransport244
    hH3 hClass hDInt s r hs hr hsr hHalf hThreshold
    (h3Path_canonicalEnergyDerivative_intervalIntegrable_automatic244
      hH3 hClass s r hs hr hsr.le)
    (h3Path_canonicalSignedTransport_intervalIntegrable_automatic244
      hH3 hClass hDInt s r hs hr hsr.le)

/-- Pointwise optimized peak clock upgraded to actual integrated signed
transport without any temporal integrability assumptions beyond the
existing finite physical viscous budget. -/
theorem h3Path_optimizedPeak_terminalCompression_or_integratedTransport_automatic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (s : ℝ) (hs : s ∈ Set.Ioo b T)
    (hTwo : 2 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 s‖)
    (hLarge : 32 * (velocityH3Energy0At u b + 1) ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2)
    (hThreshold : 16 * (∫ t in a..T, velocityH3DissipationAt u t) ≤
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2) :
    ∃ H : ℝ, 0 < H ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 8 =
        16384 * (velocityH3Energy0At u b + 1) * H ^ 3 ∧
      let B := ∫ t in a..T, velocityH3DissipationAt u t
      T - s ≤ (B + 1) / H ∨
        ∃ r : ℝ,
          r ∈ Set.Icc s (s + (B + 1) / H) ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
            ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2 ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 / 8 <
            ∫ t in s..r, velocityH3TransportDerivativeAt u t := by
  obtain ⟨H, hH, hIdentity, hAlternative⟩ :=
    h3Path_optimizedPeak_terminalCompression_or_integratedTransportResidual244
      hH3 hClass hDInt b hb s hs hTwo hLarge hThreshold
  let B : ℝ := ∫ t in a..T, velocityH3DissipationAt u t
  refine ⟨H, hH, hIdentity, ?_⟩
  change T - s ≤ (B + 1) / H ∨
    ∃ r : ℝ,
      r ∈ Set.Icc s (s + (B + 1) / H) ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
        ‖h3AuditActualSpectralVelocityTotal hH3 s‖ / 2 ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ^ 2 / 8 <
        velocityH3EnergyAt u s - velocityH3EnergyAt u r -
          2 * (∫ t in s..r, velocityH3DissipationAt u t) at hAlternative
  rcases hAlternative with hCompression | ⟨r, hr, hHalf, hResidual⟩
  · exact Or.inl hCompression
  · by_cases hCompression : T - s ≤ (B + 1) / H
    · exact Or.inl hCompression
    · right
      have hEnd : s + (B + 1) / H < T := by
        have hShort := lt_of_not_ge hCompression
        linarith only [hShort]
      have hsr : s < r := by
        rcases lt_or_eq_of_le hr.1 with hlt | heq
        · exact hlt
        · subst r
          linarith only [hTwo, hHalf]
      have hsClass : s ∈ Set.Ioo a T :=
        ⟨lt_trans hb.1 hs.1, hs.2⟩
      have hrClass : r ∈ Set.Ioo a T :=
        ⟨lt_of_lt_of_le hsClass.1 hr.1, lt_of_le_of_lt hr.2 hEnd⟩
      have hIdentityTransport :=
        h3Path_canonicalSignedTransportResidual_eq_integral_automatic244
          hH3 hClass hDInt s r hsClass hrClass hsr
      rw [hIdentityTransport] at hResidual
      exact ⟨r, hr, hHalf, hResidual⟩


/-- Preserve the exact canonical source-maximizing times and quadratic-sharp
annulus witnesses. The positive rate is the actual Lebesgue time integral of
the signed full physical transport, without extra FTC assumptions. -/
theorem h3Path_noL2Trace_canonicalWidth_sourcePeakIntegratedTransport_automatic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTerminalMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ) (s : ℕ → ℝ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k, v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2)) ∧
      (∀ k, s k ∈ Set.Icc (τ (v k))
          (τ (v k) + (T - τ (v k)) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 (s k)‖ = C (v k)) ∧
      (∀ η U V : ℝ, 0 < η → 0 ≤ U → 0 ≤ V →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            U * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            V * (((v k : ℝ) + 1) ^ 9)) →
        ∀ b : ℝ, b ∈ Set.Ioo a T →
        ∀ᶠ k : ℕ in atTop,
          ∃ H : ℝ, 0 < H ∧
            ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 8 =
              16384 * (velocityH3Energy0At u b + 1) * H ^ 3 ∧
            let Budget := ∫ t in a..T, velocityH3DissipationAt u t
            T - s k ≤ (Budget + 1) / H ∨
              ∃ r : ℝ,
                r ∈ Set.Icc (s k) (s k + (Budget + 1) / H) ∧
                ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
                  ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ / 2 ∧
                ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 / 8 <
                  ∫ t in (s k)..r, velocityH3TransportDerivativeAt u t) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, hJoint⟩ :=
    h3Path_noL2Trace_canonicalWidth_sourcePeakIntegratedTransportResidual244
      hH3 hClass hTerminalMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, ?_⟩
  intro η U V hη hU hV hRegime b hb
  have hLate := hJoint η U V hη hU hV hRegime b hb
  filter_upwards [hLate] with k hk
  obtain ⟨H, hH, hIdentity, hAlternative⟩ := hk
  let Budget : ℝ := ∫ t in a..T, velocityH3DissipationAt u t
  refine ⟨H, hH, hIdentity, ?_⟩
  change T - s k ≤ (Budget + 1) / H ∨
    ∃ r : ℝ,
      r ∈ Set.Icc (s k) (s k + (Budget + 1) / H) ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 r‖ <
        ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ / 2 ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 (s k)‖ ^ 2 / 8 <
        velocityH3EnergyAt u (s k) - velocityH3EnergyAt u r -
          2 * (∫ t in (s k)..r, velocityH3DissipationAt u t)
      at hAlternative
  rcases hAlternative with hCompression | ⟨r, hr, hHalf, hResidual⟩
  · exact Or.inl hCompression
  · by_cases hCompression : T - s k ≤ (Budget + 1) / H
    · exact Or.inl hCompression
    · right
      have hEnd : s k + (Budget + 1) / H < T := by
        have hShort := lt_of_not_ge hCompression
        linarith only [hShort]
      have hsr : s k < r := by
        rcases lt_or_eq_of_le hr.1 with hlt | heq
        · exact hlt
        · subst r
          have hNonnegative := norm_nonneg (h3AuditActualSpectralVelocityTotal hH3 (s k))
          linarith only [hHalf, hNonnegative]
      have hsClass : s k ∈ Set.Ioo a T := by
        have hLeft := (hPeak k).1.1
        have hRight := (hPeak k).1.2
        have hTau := (hTime (v k)).1
        have hEndMid : τ (v k) + (T - τ (v k)) / 2 < T := by
          linarith only [(hTime (v k)).2]
        exact ⟨lt_of_lt_of_le hTau hLeft, lt_of_le_of_lt hRight hEndMid⟩
      have hrClass : r ∈ Set.Ioo a T :=
        ⟨lt_of_lt_of_le hsClass.1 hr.1, lt_of_le_of_lt hr.2 hEnd⟩
      have hTransport :=
        h3Path_canonicalSignedTransportResidual_eq_integral_automatic244
          hH3 hClass hDInt (s k) r hsClass hrClass hsr
      rw [hTransport] at hResidual
      exact ⟨r, hr, hHalf, hResidual⟩

end
end PrimeTensor.FirstMonomialTriad
