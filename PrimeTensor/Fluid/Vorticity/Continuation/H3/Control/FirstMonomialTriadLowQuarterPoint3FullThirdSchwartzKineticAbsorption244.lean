import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzEndpointTransport244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedTopSpectralCorridor
import Mathlib.Tactic

/-!
# Kinetic absorption and signed Schwartz top-order obstruction

The physical H3 program has already absorbed both lower commutators with a
fixed kinetic anchor, leaving one unit of full dissipation and the signed
top transport. This file transfers those strong physical results to an
actual real-Schwartz realization. Unlike the earlier endpoint-ceiling
alternative, the nonextension conclusion needs no assumed endpoint ceiling.

The Schwartz realization of each selected physical slice remains an explicit
hypothesis. There is no implication that an arbitrary solenoidal Schwartz
packet is attained by a Navier--Stokes trajectory.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdKineticAbsorption244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Kinetic-anchored Young absorption replaces the unbounded lower-order
Schwartz transport budget by one unit of dissipation, an anchored sqrt-energy
term and an anchored *linear* energy term. -/
theorem h3Path_realSchwartz_anchorKineticAbsorbedBalance244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    deriv (velocityH3EnergyAt u) t +
      lowNormalRealSchwartzH3FullDissipation244 f ≤
      3 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
        velocityH3Energy0At u b +
      (21 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f))) ^ 2 *
        velocityH3Energy0At u b -
      fullSchwartzThirdCommutator244 f := by
  have hBound := h3PathCanonical_deriv_add_oneDissipation_le_signedTop_only
    hH3 hClass hb ht
  rw [thirdFullSchwartz_pathFullDissipation_eq244 u t f hRealization,
    lowNormalRealSchwartz_pathEnergy_eq u t f hRealization,
    h3Path_fullThirdTransport_eq_realSchwartz_of_realization244
      hH3 hClass ⟨lt_trans hb.1 ht.1, ht.2⟩ f hRealization] at hBound
  simpa only [lowNormalRealSchwartzH3FullDissipation244] using hBound

/-- The complete lower-order absorption produces a signed *top* cubic
surplus at any sufficiently high normalized H3 growth instant. -/
theorem h3Path_realSchwartz_anchoredHighGrowthForcesTopAdversity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hM : 0 ≤ M)
    (hHigh : M < h3PathCanonicalUnabsorbedRiccatiRate u t) :
    (4422 + M -
      441 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient ^ 2 *
        velocityH3Energy0At u b) * lowNormalRealSchwartzH3Energy f +
        lowNormalRealSchwartzH3FullDissipation244 f <
      3 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
        velocityH3Energy0At u b -
      fullSchwartzThirdCommutator244 f := by
  have hBound := h3PathCanonical_highUnabsorbed_forces_signedTopBeyondLowOrders
    hH3 hClass hb ht hM hHigh
  rw [thirdFullSchwartz_pathFullDissipation_eq244 u t f hRealization,
    lowNormalRealSchwartz_pathEnergy_eq u t f hRealization,
    h3Path_fullThirdTransport_eq_realSchwartz_of_realization244
      hH3 hClass ⟨lt_trans hb.1 ht.1, ht.2⟩ f hRealization] at hBound
  simpa only [lowNormalRealSchwartzH3FullDissipation244] using hBound

/-- A genuinely adverse signed Schwartz cubic forces a Fourier top-jet
corridor in the actual velocity, including the complete fourth-derivative
viscosity mass. The growth allowance M is not discarded. -/
theorem h3Path_realSchwartz_topDissipationGrowthCorridor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hAdverse :
      M * lowNormalRealSchwartzH3Energy f +
        lowNormalRealSchwartzH3FullDissipation244 f <
      -fullSchwartzThirdCommutator244 f) :
    lowNormalRealSchwartzH3TopDissipation f +
      M * lowNormalRealSchwartzH3Energy f <
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f))) *
        lowNormalRealSchwartzH3Energy3 f := by
  have hPhysical :
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t := by
    rw [lowNormalRealSchwartz_pathEnergy_eq u t f hRealization,
      thirdFullSchwartz_pathFullDissipation_eq244 u t f hRealization,
      h3Path_fullThirdTransport_eq_realSchwartz_of_realization244
        hH3 hClass ht f hRealization]
    simpa only [lowNormalRealSchwartzH3FullDissipation244] using hAdverse
  have hCorridor := h3PathCanonical_topDissipation_add_growth_lt_LandauTopCeiling
    hH3 hClass ht hPhysical
  rw [lowNormalRealSchwartz_pathTopDissipation_eq u t f hRealization,
    lowNormalRealSchwartz_pathEnergy_eq u t f hRealization,
    lowNormalRealSchwartz_pathEnergy3_eq u t f hRealization] at hCorridor
  exact hCorridor

/-- The same adverse growth corridor forces a nonzero real-Schwartz third jet. -/
theorem h3Path_realSchwartz_topEnergy_pos_of_signedAdversity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hM : 0 ≤ M)
    (hAdverse :
      M * lowNormalRealSchwartzH3Energy f +
        lowNormalRealSchwartzH3FullDissipation244 f <
      -fullSchwartzThirdCommutator244 f) :
    0 < lowNormalRealSchwartzH3Energy3 f := by
  have hPhysical :
      M * velocityH3EnergyAt u t + velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t := by
    rw [lowNormalRealSchwartz_pathEnergy_eq u t f hRealization,
      thirdFullSchwartz_pathFullDissipation_eq244 u t f hRealization,
      h3Path_fullThirdTransport_eq_realSchwartz_of_realization244
        hH3 hClass ht f hRealization]
    simpa only [lowNormalRealSchwartzH3FullDissipation244] using hAdverse
  have hPos := h3PathCanonical_topEnergy_pos_of_signedTransportDominance
    hH3 hClass ht hM hPhysical
  rw [lowNormalRealSchwartz_pathEnergy3_eq u t f hRealization] at hPos
  exact hPos

/-- Hypothetical nonextension forces arbitrarily large normalized signed
Schwartz third-order adversity on *every* strict subtail, if the selected
time slices have real-Schwartz representatives. No endpoint ceiling is used. -/
theorem h3Path_noExtension_realSchwartzTopAdverse_onEverySubtail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hM : 0 ≤ M)
    (hRealizedTail : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∃ f : A3 → SchwartzMap V3 ℝ,
        ∀ j : A3,
          loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      ∃ f : A3 → SchwartzMap V3 ℝ,
        (∀ j : A3,
          loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) ∧
        M * lowNormalRealSchwartzH3Energy f +
          lowNormalRealSchwartzH3FullDissipation244 f <
        -fullSchwartzThirdCommutator244 f := by
  obtain ⟨t, ht, hSigned⟩ :=
    h3PathCanonical_signedTopDominatesDissipation_on_every_subtail
      hH3 hNoExtension hClass hb hd hM
  obtain ⟨f, hRealization⟩ := hRealizedTail t ht
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  rw [lowNormalRealSchwartz_pathEnergy_eq u t f hRealization,
    thirdFullSchwartz_pathFullDissipation_eq244 u t f hRealization,
    h3Path_fullThirdTransport_eq_realSchwartz_of_realization244
      hH3 hClass htClass f hRealization] at hSigned
  refine ⟨t, ht, f, hRealization, ?_⟩
  simpa only [lowNormalRealSchwartzH3FullDissipation244] using hSigned

/-- On every strict terminal subtail, nonextension and Schwartz realization
force a *single* field with arbitrary normalized top-cubic excess, positive
third-order energy and a strict physical fourth-order frequency corridor. -/
theorem h3Path_noExtension_realSchwartzTopFrequencyCorridor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hM : 0 ≤ M)
    (hRealizedTail : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∃ f : A3 → SchwartzMap V3 ℝ,
        ∀ j : A3,
          loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      ∃ f : A3 → SchwartzMap V3 ℝ,
        (∀ j : A3,
          loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) ∧
        0 < lowNormalRealSchwartzH3Energy3 f ∧
        M * lowNormalRealSchwartzH3Energy f +
          lowNormalRealSchwartzH3FullDissipation244 f <
            -fullSchwartzThirdCommutator244 f ∧
        lowNormalRealSchwartzH3TopDissipation f +
          M * lowNormalRealSchwartzH3Energy f <
        (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (lowNormalRealSchwartzH3Energy f))) *
          lowNormalRealSchwartzH3Energy3 f := by
  obtain ⟨t, ht, f, hRealization, hSigned⟩ :=
    h3Path_noExtension_realSchwartzTopAdverse_onEverySubtail244
      hH3 hNoExtension hClass hb hd hM hRealizedTail
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  have hPos := h3Path_realSchwartz_topEnergy_pos_of_signedAdversity244
    hH3 hClass htClass f hRealization hM hSigned
  have hCorridor := h3Path_realSchwartz_topDissipationGrowthCorridor244
    hH3 hClass htClass f hRealization hSigned
  exact ⟨t, ht, f, hRealization, hPos, hSigned, hCorridor⟩

/-- A genuine Schwartz spectral dominance criterion: if all strict-tail
velocity slices have real-Schwartz representatives and their 243-slot
fourth-order viscous mass dominates the canonical Landau allowance, the
actual H3 solution extends. This is conditional, not a general dominance
claim about Navier--Stokes solutions. -/
theorem h3Path_extension_of_realSchwartzTopSpectralDominance244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hDominance : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∃ f : A3 → SchwartzMap V3 ℝ,
        (∀ j : A3,
          loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) ∧
        (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (lowNormalRealSchwartzH3Energy f))) *
          lowNormalRealSchwartzH3Energy3 f ≤
        lowNormalRealSchwartzH3TopDissipation f) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  apply h3PathCanonical_extension_of_eventual_topSpectralDissipationDominance
    hH3 hClass hb hd
  intro t ht
  obtain ⟨f, hRealization, hBound⟩ := hDominance t ht
  rw [lowNormalRealSchwartz_pathEnergy_eq u t f hRealization,
    lowNormalRealSchwartz_pathEnergy3_eq u t f hRealization,
    lowNormalRealSchwartz_pathTopDissipation_eq u t f hRealization]
  exact hBound


/-- A finite *pathwise* bound on the signed top cubic after reserving one
unit of complete viscosity suffices for H3 continuation. Unlike uniform
static absorption, the hypothesis is restricted to actual solution slices. -/
theorem h3Path_extension_of_realSchwartzTopCubicEnvelope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hB : 0 ≤ B)
    (hEnvelope : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∃ f : A3 → SchwartzMap V3 ℝ,
        (∀ j : A3,
          loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) ∧
        -fullSchwartzThirdCommutator244 f ≤
          B * lowNormalRealSchwartzH3Energy f +
            lowNormalRealSchwartzH3FullDissipation244 f) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨t, ht, hAdverse⟩ :=
    h3PathCanonical_signedTopDominatesDissipation_on_every_subtail
      hH3 hNoExtension hClass hb hd hB
  obtain ⟨f, hRealization, hBound⟩ := hEnvelope t ht
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hd.1 ht.1), ht.2⟩
  rw [lowNormalRealSchwartz_pathEnergy_eq u t f hRealization,
    thirdFullSchwartz_pathFullDissipation_eq244 u t f hRealization,
    h3Path_fullThirdTransport_eq_realSchwartz_of_realization244
      hH3 hClass htClass f hRealization] at hAdverse
  have hStrict :
      B * lowNormalRealSchwartzH3Energy f +
        lowNormalRealSchwartzH3FullDissipation244 f <
        -fullSchwartzThirdCommutator244 f := by
    simpa only [lowNormalRealSchwartzH3FullDissipation244] using hAdverse
  exact (not_lt_of_ge hBound) hStrict

end
end PrimeTensor.FirstMonomialTriad
