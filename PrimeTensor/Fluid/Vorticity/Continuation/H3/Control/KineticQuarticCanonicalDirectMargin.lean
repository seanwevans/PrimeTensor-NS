import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalDirectExcessIntegral

/-!
# Integrable dissipation-margin frontiers on exactly direct-selected H³ times

The exact energy identity is E' + 2D = -transport.  The earlier terminal
Riccati clock ensures that, under hypothetical nonextension, the exact kinetic
selection is the direct branch at every sufficiently late time whenever a
fixed anchor has strictly positive kinetic energy.

This file tests a genuinely stronger *analytic premise* than a uniform
transport-defect ceiling: an arbitrary temporally integrable remainder r,
with any fixed nonnegative dissipation margin ε, may bound the transport as

    -transport(t) ≤ (2-ε) D(t) + r(t) E(t)

on the exactly direct-selected times of one late tail.  The exact energy
balance then gives E' ≤ r E, and the existing logarithmic continuation
criterion applies.  Consequently nonextension forces violations of every
such integrable-remainder estimate arbitrarily late in the direct regime.

The new theorem does NOT assert that the requisite transport estimate holds
for an arbitrary Navier--Stokes solution, nor that nonextension occurs.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

/-- Spending at least two copies of H³ dissipation, with any nonnegative
extra margin, leaves ordinary scalar linear H³-energy growth. -/
theorem h3PathCanonical_energyGrowth_le_of_dissipationMargin
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t ε : ℝ} {r : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hε : 0 ≤ ε)
    (hTransport :
      - velocityH3TransportDerivativeAt u t ≤
        (2 - ε) * velocityH3DissipationAt u t +
          r t * velocityH3EnergyAt u t) :
    deriv (velocityH3EnergyAt u) t ≤
      r t * velocityH3EnergyAt u t := by
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht
  have hDNonneg := velocityH3DissipationAt_nonneg u t
  have hPenalty : 0 ≤ ε * velocityH3DissipationAt u t :=
    mul_nonneg hε hDNonneg
  nlinarith only [hBalance, hTransport, hPenalty]

/-- An L¹ transport remainder that pays the full dissipation (and optionally
more) on late exact-direct times forces continuation at a positive kinetic
anchor. The estimate is a hypothesis, not an asserted PDE bound. -/
theorem h3PathCanonical_extension_of_integrable_direct_dissipation_margin
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c ε : ℝ} {r : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b)
    (hc : c ∈ Set.Ioo a T)
    (hε : 0 ≤ ε)
    (hr : IntegrableOn r (Set.Ioo c T))
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo c T →
      h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t =
          h3PathCanonicalKineticTransportCoefficient u t →
      - velocityH3TransportDerivativeAt u t ≤
        (2 - ε) * velocityH3DissipationAt u t +
          r t * velocityH3EnergyAt u t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨e, he, hDirect⟩ :=
    h3PathCanonical_eventually_direct_of_noExtension_positive_mass
      hH3 hNoExtension hClass hMass
  let d : ℝ := max c e
  have hd : d ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hc.1 (le_max_left c e), max_lt hc.2 he.2⟩
  have hClassD : PreterminalH3EnergyClass u d T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hd.1) hd.2
  have hrD : IntegrableOn r (Set.Ioo d T) := by
    apply hr.mono_set
    intro t ht
    exact ⟨lt_of_le_of_lt (le_max_left c e) ht.1, ht.2⟩
  have hGrowth : ∀ t : ℝ, t ∈ Set.Ioo d T →
      deriv (velocityH3EnergyAt u) t ≤
        r t * velocityH3EnergyAt u t := by
    intro t ht
    have htClass : t ∈ Set.Ioo a T :=
      ⟨lt_trans hd.1 ht.1, ht.2⟩
    have htC : t ∈ Set.Ioo c T :=
      ⟨lt_of_le_of_lt (le_max_left c e) ht.1, ht.2⟩
    have htE : t ∈ Set.Ioo e T :=
      ⟨lt_of_le_of_lt (le_max_right c e) ht.1, ht.2⟩
    exact h3PathCanonical_energyGrowth_le_of_dissipationMargin
      hH3 hClass htClass hε (hTransport t htC (hDirect t htE).1)
  exact hNoExtension
    (h3PathExtension_of_integrableLinearEnergyGrowthMajorantOnTail
      hH3 hClassD hrD hGrowth)

/-- Under hypothetical nonextension, *every* integrable temporal envelope
fails to absorb the adverse transport after paying `(2-ε) D` at some
strictly later exactly direct-selected time. The envelope need not be
nonnegative; only temporal integrability and `ε ≥ 0` are assumed. -/
theorem h3PathCanonical_direct_margin_exceeds_integrable_remainder_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c ε : ℝ} (r : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b)
    (hc : c ∈ Set.Ioo a T)
    (hε : 0 ≤ ε)
    (hr : IntegrableOn r (Set.Ioo c T)) :
    ∃ t : ℝ, t ∈ Set.Ioo c T ∧
      h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t =
          h3PathCanonicalKineticTransportCoefficient u t ∧
      (2 - ε) * velocityH3DissipationAt u t +
        r t * velocityH3EnergyAt u t <
          - velocityH3TransportDerivativeAt u t := by
  by_contra hNoWitness
  have hBound : ∀ t : ℝ, t ∈ Set.Ioo c T →
      h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t =
          h3PathCanonicalKineticTransportCoefficient u t →
      - velocityH3TransportDerivativeAt u t ≤
        (2 - ε) * velocityH3DissipationAt u t +
          r t * velocityH3EnergyAt u t := by
    intro t ht hSelected
    by_contra hNotLe
    exact hNoWitness ⟨t, ht, hSelected, lt_of_not_ge hNotLe⟩
  exact hNoExtension
    (h3PathCanonical_extension_of_integrable_direct_dissipation_margin
      hH3 hClass hMass hc hε hr hBound)

/-- Constant temporal rates are L¹ on every finite strict terminal interval.
In particular, any fixed dissipation margin cannot make the remaining signed
transport excess uniformly `M E`-bounded at late direct-selected times
under hypothetical nonextension. -/
theorem h3PathCanonical_direct_margin_exceeds_every_constant_energy_rate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c ε : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b)
    (hc : c ∈ Set.Ioo a T)
    (hε : 0 ≤ ε) :
    ∃ t : ℝ, t ∈ Set.Ioo c T ∧
      h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t =
          h3PathCanonicalKineticTransportCoefficient u t ∧
      (2 - ε) * velocityH3DissipationAt u t +
        M * velocityH3EnergyAt u t <
          - velocityH3TransportDerivativeAt u t := by
  have hr : IntegrableOn (fun _ : ℝ => M) (Set.Ioo c T) :=
    integrableOn_const measure_Ioo_lt_top.ne
  exact h3PathCanonical_direct_margin_exceeds_integrable_remainder_of_noExtension
    (r := fun _ : ℝ => M) hH3 hNoExtension hClass hMass hc hε hr

/-- Neutral terminal alternative: either continuation, or at each positive
kinetic anchor every L¹ dissipation-margin envelope is violated in the exact
direct regime, on every strict terminal tail. -/
theorem h3PathCanonical_extension_or_direct_margin_defeats_every_integrable_remainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, 0 < velocityH3Energy0At u b →
      ∀ c : ℝ, c ∈ Set.Ioo a T →
      ∀ ε : ℝ, 0 ≤ ε →
      ∀ r : ℝ → ℝ, IntegrableOn r (Set.Ioo c T) →
        ∃ t : ℝ, t ∈ Set.Ioo c T ∧
          h3ExactAdaptiveSelectedDirectCoefficient u
            (h3PathCanonicalKineticTransportCoefficient u) b t =
              h3PathCanonicalKineticTransportCoefficient u t ∧
          (2 - ε) * velocityH3DissipationAt u t +
            r t * velocityH3EnergyAt u t <
              - velocityH3TransportDerivativeAt u t := by
  by_cases hExtension : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · right
    intro b hMass c hc ε hε r hr
    exact h3PathCanonical_direct_margin_exceeds_integrable_remainder_of_noExtension
      r hH3 hExtension hClass hMass hc hε hr

end Euclidean
end Bridge
end PrimeTensor
