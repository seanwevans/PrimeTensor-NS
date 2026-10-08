import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalMarginExcess

/-!
# Canonical spectral transport envelope minus a retained dissipation margin

The existing H3 commutator estimate bounds adverse transport by the explicit
canonical coefficient `B(t) E(t)` where `B(t) = 4422 (1 + C1 sqrt E(t))`.
The exact balance `E' + 2 D = -transport` permits a more quantitative
sufficient continuation criterion: the positive spectral dissipation gap

  gap_epsilon(t) = max 0 (B(t) - (2-epsilon) D(t) / E(t))

is an explicit scalar envelope of the *minimal* normalized transport margin
excess. Integrability of this gap on any energy-class terminal tail implies
smooth continuation, without kinetic mass assumptions.

Conversely, on a hypothetical nonextendible path the gap cannot be bounded
throughout any strict terminal tail by *any* integrable scalar envelope:
there must be a late time at which the gap strictly exceeds that envelope.
For each positive-mass kinetic anchor the violating time can additionally
be chosen where the exact selected direct branch is active and absorption
vanishes. These are conditional necessary conditions, not new PDE bounds.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

/-- The full existing commutator bound with no artificial addition of a
positive dissipation term. -/
theorem h3PathCanonical_neg_transport_le_kineticCoefficient_mul_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    - velocityH3TransportDerivativeAt u t ≤
      h3PathCanonicalKineticTransportCoefficient u t *
        velocityH3EnergyAt u t := by
  let h : ℝ → ℝ := h3PathCanonicalSqrtEnergyGradientEnvelope u
  have hGradient :
      ∀ s : ℝ, s ∈ Set.Ioo a T → VelocityGradientEnvelope u h s := by
    intro s hs
    exact h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass hs
  have hTransport :=
    neg_transport_le_of_commutatorBound
      ((h3TransportControlledOnTail_of_h3Path_exactPDEPairing
        h3PathEnergyClassProducesPDEPairingIntegrability_closed
        hH3 hClass hGradient) t ht).2
  dsimp only [h] at hTransport
  simpa only [h3PathCanonicalKineticTransportCoefficient] using hTransport

/-- Explicit nonnegative spectral envelope for the transport margin excess.
The actual normalized nonlinear excess can be strictly smaller because of
cancellation in the PDE transport pairing. -/
noncomputable def h3PathCanonicalSpectralDissipationGap
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (ε : ℝ) : ℝ → ℝ :=
  fun t => max 0
    (h3PathCanonicalKineticTransportCoefficient u t -
      (2 - ε) * velocityH3DissipationAt u t /
        velocityH3EnergyAt u t)

/-- The spectral envelope of each fixed margin is pointwise nonnegative. -/
theorem h3PathCanonicalSpectralDissipationGap_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (ε t : ℝ) :
    0 ≤ h3PathCanonicalSpectralDissipationGap u ε t := by
  unfold h3PathCanonicalSpectralDissipationGap
  exact le_max_left _ _

/-- The existing commutator estimate bounds the *actual* minimal
normalized margin excess by the spectral dissipation gap. -/
theorem h3PathCanonicalMarginExcessRate_le_spectralDissipationGap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ} (ε : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathCanonicalMarginExcessRate u ε t ≤
      h3PathCanonicalSpectralDissipationGap u ε t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hTransport :=
    h3PathCanonical_neg_transport_le_kineticCoefficient_mul_energy
      hH3 hClass ht
  have hNumerator :=
    sub_le_sub_right hTransport
      ((2 - ε) * velocityH3DissipationAt u t)
  have hDiv :
      (- velocityH3TransportDerivativeAt u t -
        (2 - ε) * velocityH3DissipationAt u t) /
          velocityH3EnergyAt u t ≤
      h3PathCanonicalKineticTransportCoefficient u t -
        (2 - ε) * velocityH3DissipationAt u t /
          velocityH3EnergyAt u t := by
    calc
      _ ≤ (h3PathCanonicalKineticTransportCoefficient u t *
        velocityH3EnergyAt u t -
          (2 - ε) * velocityH3DissipationAt u t) /
            velocityH3EnergyAt u t :=
        (div_le_div_iff_of_pos_right hEPos).2 hNumerator
      _ = _ := by
        field_simp [ne_of_gt hEPos]
        <;> ring
  unfold h3PathCanonicalMarginExcessRate
    h3PathCanonicalSpectralDissipationGap
  exact max_le_max_left 0 hDiv

/-- The spectral gap itself gives a retained-dissipation transport envelope,
without an assumption that the PDE transport inequality is sharp. -/
theorem h3PathCanonical_neg_transport_le_dissipation_add_spectralGap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ} (ε : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    - velocityH3TransportDerivativeAt u t ≤
      (2 - ε) * velocityH3DissipationAt u t +
        h3PathCanonicalSpectralDissipationGap u ε t *
          velocityH3EnergyAt u t := by
  have hActual := h3PathCanonicalMarginExcessRate_transport_bound u ε t
  have hGap := h3PathCanonicalMarginExcessRate_le_spectralDissipationGap
    ε hH3 hClass ht
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  have hScaled := mul_le_mul_of_nonneg_right hGap hE
  linarith only [hActual, hScaled]

/-- If an explicit spectral dissipation gap is integrable for a fixed
nonnegative margin on one terminal tail, smooth continuation follows. -/
theorem h3PathCanonical_extension_of_integrable_spectralDissipationGap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hε : 0 ≤ ε)
    (hGap : IntegrableOn (h3PathCanonicalSpectralDissipationGap u ε)
      (Set.Ioo a T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  apply h3PathExtension_of_integrableLinearEnergyGrowthMajorantOnTail
    hH3 hClass hGap
  intro t ht
  exact h3PathCanonical_energyGrowth_le_of_dissipationMargin
    hH3 hClass ht hε
      (h3PathCanonical_neg_transport_le_dissipation_add_spectralGap
        ε hH3 hClass ht)

/-- Hypothetical nonextension makes the explicit commutator/dissipation
gap nonintegrable on every energy-class tail for all ε >= 0. -/
theorem h3PathCanonicalSpectralDissipationGap_nonintegrable_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hε : 0 ≤ ε) :
    ¬ IntegrableOn (h3PathCanonicalSpectralDissipationGap u ε)
      (Set.Ioo a T) := by
  intro hGap
  exact hNoExtension
    (h3PathCanonical_extension_of_integrable_spectralDissipationGap
      hH3 hClass hε hGap)

/-- Every integrable real-valued scalar comparison envelope is strictly
exceeded by the explicit spectral dissipation gap at some terminal time,
conditionally on nonextension and for every nonnegative margin. -/
theorem h3PathCanonicalSpectralDissipationGap_exceeds_integrable_envelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d ε : ℝ} (r : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hε : 0 ≤ ε)
    (hr : IntegrableOn r (Set.Ioo d T)) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      r t < h3PathCanonicalSpectralDissipationGap u ε t := by
  by_contra hNoWitness
  have hPointwise : ∀ t : ℝ, t ∈ Set.Ioo d T →
      h3PathCanonicalSpectralDissipationGap u ε t ≤ r t := by
    intro t ht
    by_contra hNotLe
    exact hNoWitness ⟨t, ht, lt_of_not_ge hNotLe⟩
  have hClassD : PreterminalH3EnergyClass u d T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hd.1) hd.2
  have hGrowth : ∀ t : ℝ, t ∈ Set.Ioo d T →
      deriv (velocityH3EnergyAt u) t ≤
        r t * velocityH3EnergyAt u t := by
    intro t ht
    have hTransport :=
      h3PathCanonical_neg_transport_le_dissipation_add_spectralGap
        ε hH3 hClassD ht
    have hScaled := mul_le_mul_of_nonneg_right (hPointwise t ht)
      (le_trans zero_le_one (one_le_velocityH3EnergyAt u t))
    have hTransportR : - velocityH3TransportDerivativeAt u t ≤
        (2 - ε) * velocityH3DissipationAt u t +
          r t * velocityH3EnergyAt u t := by
      linarith only [hTransport, hScaled]
    exact h3PathCanonical_energyGrowth_le_of_dissipationMargin
      hH3 hClassD ht hε hTransportR
  exact hNoExtension
    (h3PathExtension_of_integrableLinearEnergyGrowthMajorantOnTail
      hH3 hClassD hr hGrowth)

/-- The spectral gap witness can be synchronized with *exact direct selection*
at each positive-mass anchor: on the hypothetical nonextension branch, for
all late tails, all margins and all integrable envelopes. -/
theorem h3PathCanonicalSpectralDissipationGap_exceeds_envelope_in_direct_regime
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d ε : ℝ} (r : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b)
    (hd : d ∈ Set.Ioo a T)
    (hε : 0 ≤ ε)
    (hr : IntegrableOn r (Set.Ioo d T)) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t =
          h3PathCanonicalKineticTransportCoefficient u t ∧
      h3ExactAdaptiveSelectedAbsorbedCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t = 0 ∧
      r t < h3PathCanonicalSpectralDissipationGap u ε t := by
  obtain ⟨c, hc, hDirect⟩ :=
    h3PathCanonical_eventually_direct_of_noExtension_positive_mass
      hH3 hNoExtension hClass hMass
  let e : ℝ := max d c
  have he : e ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hd.1 (le_max_left d c), max_lt hd.2 hc.2⟩
  have hrE : IntegrableOn r (Set.Ioo e T) := by
    apply hr.mono_set
    intro t ht
    exact ⟨lt_of_le_of_lt (le_max_left d c) ht.1, ht.2⟩
  obtain ⟨t, ht, hGap⟩ :=
    h3PathCanonicalSpectralDissipationGap_exceeds_integrable_envelope
      r hH3 hNoExtension hClass he hε hrE
  have htD : t ∈ Set.Ioo d T :=
    ⟨lt_of_le_of_lt (le_max_left d c) ht.1, ht.2⟩
  have htC : t ∈ Set.Ioo c T :=
    ⟨lt_of_le_of_lt (le_max_right d c) ht.1, ht.2⟩
  exact ⟨t, htD, (hDirect t htC).1, (hDirect t htC).2, hGap⟩

/-- Neutral structural alternative: continuation, or every nonnegative
margin has a nonintegrable spectral dissipation gap on every late tail. -/
theorem h3PathCanonical_extension_or_spectralDissipationGap_nonintegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ ε : ℝ, 0 ≤ ε →
    ∀ d : ℝ, d ∈ Set.Ioo a T →
      ¬ IntegrableOn (h3PathCanonicalSpectralDissipationGap u ε)
        (Set.Ioo d T) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro ε hε d hd
    have hClassD : PreterminalH3EnergyClass u d T :=
      preterminalH3EnergyClass_restrict_left hClass (le_of_lt hd.1) hd.2
    exact h3PathCanonicalSpectralDissipationGap_nonintegrable_of_noExtension
      hH3 hExt hClassD hε

end Euclidean
end Bridge
end PrimeTensor
