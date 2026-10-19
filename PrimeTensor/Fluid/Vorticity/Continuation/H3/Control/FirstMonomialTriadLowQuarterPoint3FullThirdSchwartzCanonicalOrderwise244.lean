import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzLowerTransportBudget244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalLowerOrderSignedTransport
import Mathlib.Tactic

/-!
# Canonical orderwise Schwartz transport and physical high-growth alternative

The preceding lower-transport bridge retained explicit zero/first/second
flux, integrability and gradient-envelope hypotheses. Those hypotheses
are ALREADY discharged along an admissible H³ path by the canonical
square-root energy gradient envelope and the existing energy-class
integration-by-parts theorems.

This module transfers the stronger, already proved path estimate

    |T₁+T₂| <= C₁ sqrt(E) (6 E₁ + 18 E₂)

to an actually realized real-Schwartz slice, identifies the complete
viscous dissipation and signed top cubic, and obtains a sufficient
positive-slope criterion with no manually supplied flux or pairing contract.

A second bridge translates the established unabsorbed high-growth
dichotomy to the same Schwartz quantities. A conditional no-extension
witness theorem makes the time-slice realization premise explicit:
no arbitrary Schwartz packet is asserted to evolve along NS, and
no global regularity or singularity claim is made here.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdCanonicalOrderwise244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The kinetic-flux cancellation needed in the exact Schwartz identity
is automatic for an admissible NS path: H³ integrability and the
canonical gradient envelope supply the energy-class IBP theorem. -/
theorem h3Path_exactEnergyBalance_fullThirdSchwartz_noFluxAssumption244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    deriv (velocityH3EnergyAt u) t +
      2 * lowNormalRealSchwartzH3FullDissipation244 f =
      -(velocityH3TransportDerivative1At u t +
        velocityH3TransportDerivative2At u t +
        fullSchwartzThirdCommutator244 f) := by
  have htNS : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hH3At : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htNS
  have hGradient :
      VelocityGradientEnvelope u
        (h3PathCanonicalSqrtEnergyGradientEnvelope u) t :=
    h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass ht
  have hIBP : H3TransportEnergyIntegrationByPartsAt u t :=
    h3TransportEnergyIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradient
  have hFlux : H3TransportEnergyFluxVanishesAt u t :=
    h3TransportEnergyFluxVanishesAt_of_integrationByParts hIBP
  exact h3Path_exactEnergyBalance_fullThirdSchwartz_noT0_244
    hH3 hClass ht f hRealization hFlux

/-- The exact orderwise path commutator bound, transferred without loss to
Schwartz energies of a realized time slice. No explicit flux or pairing
assumptions remain. -/
theorem h3Path_lowerTransport_abs_le_realSchwartzOrderwise244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    |velocityH3TransportDerivative1At u t +
      velocityH3TransportDerivative2At u t| ≤
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
          (6 * lowNormalRealSchwartzH3Energy1 f +
            18 * lowNormalRealSchwartzH3Energy2 f) := by
  have hBound := h3PathCanonical_lowerTransport_abs_le_orderwiseEnergy
    hH3 hClass ht
  rw [lowNormalRealSchwartz_pathEnergy_eq u t f hRealization,
    lowNormalRealSchwartz_pathEnergy1_eq u t f hRealization,
    lowNormalRealSchwartz_pathEnergy2_eq u t f hRealization] at hBound
  exact hBound

/-- Exact full viscosity and signed top-order Schwartz cubic, with the
separately weighted lower-order energies rather than the coarser 24 h E. -/
theorem h3Path_deriv_add_completeSchwartzDissipation_le_orderwise244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    deriv (velocityH3EnergyAt u) t +
      2 * lowNormalRealSchwartzH3FullDissipation244 f ≤
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
          (6 * lowNormalRealSchwartzH3Energy1 f +
            18 * lowNormalRealSchwartzH3Energy2 f) -
      fullSchwartzThirdCommutator244 f := by
  have hBound :=
    h3PathCanonical_deriv_add_dissipation_le_lowerOrderSignedTop
      hH3 hClass ht
  rw [thirdFullSchwartz_pathFullDissipation_eq244 u t f hRealization,
    lowNormalRealSchwartz_pathEnergy_eq u t f hRealization,
    lowNormalRealSchwartz_pathEnergy1_eq u t f hRealization,
    lowNormalRealSchwartz_pathEnergy2_eq u t f hRealization,
    h3Path_fullThirdTransport_eq_realSchwartz_of_realization244
      hH3 hClass ht f hRealization] at hBound
  simpa only [lowNormalRealSchwartzH3FullDissipation244] using hBound

/-- A physical positive-slope criterion at a realized NS slice. All lower
transport hypotheses are discharged by the established energy-class theory;
only the genuinely quantitative adverse Schwartz budget remains. -/
theorem h3Path_energySlope_pos_of_realSchwartzOrderwiseBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hAdverse :
      2 * lowNormalRealSchwartzH3FullDissipation244 f +
        (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
          (6 * lowNormalRealSchwartzH3Energy1 f +
            18 * lowNormalRealSchwartzH3Energy2 f) <
      -fullSchwartzThirdCommutator244 f) :
    0 < deriv (velocityH3EnergyAt u) t := by
  have hExact :=
    h3Path_exactEnergyBalance_fullThirdSchwartz_noFluxAssumption244
      hH3 hClass ht f hRealization
  have hLower := h3Path_lowerTransport_abs_le_realSchwartzOrderwise244
    hH3 hClass ht f hRealization
  have hUpper :
      velocityH3TransportDerivative1At u t +
        velocityH3TransportDerivative2At u t ≤
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
          (6 * lowNormalRealSchwartzH3Energy1 f +
            18 * lowNormalRealSchwartzH3Energy2 f) :=
    le_trans (le_abs_self _) hLower
  linarith only [hExact, hUpper, hAdverse]

/-- Conversely, any positive actual H³ slope forces the adverse third-order
Schwartz cubic to exceed twice viscosity minus the orderwise lower budget.
This necessary condition does not infer a sign for the top cubic alone. -/
theorem h3Path_realSchwartzOrderwiseNecessary_of_energySlope_pos244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hPositive : 0 < deriv (velocityH3EnergyAt u) t) :
    2 * lowNormalRealSchwartzH3FullDissipation244 f <
      -fullSchwartzThirdCommutator244 f +
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
          (6 * lowNormalRealSchwartzH3Energy1 f +
            18 * lowNormalRealSchwartzH3Energy2 f) := by
  have hBound :=
    h3Path_deriv_add_completeSchwartzDissipation_le_orderwise244
      hH3 hClass ht f hRealization
  linarith only [hPositive, hBound]

/-- The established high unabsorbed Riccati-rate alternative has an exact
real-Schwartz formulation whenever the actual NS slice is represented by f.
Its two branches remain alternatives, neither is claimed impossible. -/
theorem h3Path_highUnabsorbed_realSchwartzOrderwiseAlternative244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hM : 0 ≤ M)
    (hHigh : M < h3PathCanonicalUnabsorbedRiccatiRate u t) :
    (4422 + M) * lowNormalRealSchwartzH3Energy f <
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
          (6 * lowNormalRealSchwartzH3Energy1 f +
            18 * lowNormalRealSchwartzH3Energy2 f) ∨
      2 * lowNormalRealSchwartzH3FullDissipation244 f <
        -fullSchwartzThirdCommutator244 f := by
  have hPhysical :=
    h3PathCanonical_highUnabsorbed_lowerOrderOrTopAdversity
      hH3 hClass ht hM hHigh
  rw [lowNormalRealSchwartz_pathEnergy_eq u t f hRealization,
    lowNormalRealSchwartz_pathEnergy1_eq u t f hRealization,
    lowNormalRealSchwartz_pathEnergy2_eq u t f hRealization,
    thirdFullSchwartz_pathFullDissipation_eq244 u t f hRealization,
    h3Path_fullThirdTransport_eq_realSchwartz_of_realization244
      hH3 hClass ht f hRealization] at hPhysical
  simpa only [lowNormalRealSchwartzH3FullDissipation244] using hPhysical

/-- Under the explicitly stated Schwartz-realization-on-subtail contract,
nonextension forces a genuinely realized time and Schwartz velocity with
either high lower-order transport cost or adverse top cubic. No static packet
is identified with an NS solution by fiat. -/
theorem h3Path_noExtension_realSchwartzOrderwiseWitness244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hM : 0 ≤ M)
    (hRealizedTail : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∃ f : A3 → SchwartzMap V3 ℝ,
        ∀ j : A3,
          loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      ∃ f : A3 → SchwartzMap V3 ℝ,
        (∀ j : A3,
          loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) ∧
        ((4422 + M) * lowNormalRealSchwartzH3Energy f <
          (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
              (6 * lowNormalRealSchwartzH3Energy1 f +
                18 * lowNormalRealSchwartzH3Energy2 f) ∨
          2 * lowNormalRealSchwartzH3FullDissipation244 f <
            -fullSchwartzThirdCommutator244 f) := by
  obtain ⟨t, ht, hPhysical⟩ :=
    h3PathCanonical_lowerOrderOrTopAdversity_witness_of_noExtension
      hH3 hNoExtension hClass hd hM
  obtain ⟨f, hRealization⟩ := hRealizedTail t ht
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  have hSchwartz :
      (4422 + M) * lowNormalRealSchwartzH3Energy f <
        (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (lowNormalRealSchwartzH3Energy f)) *
            (6 * lowNormalRealSchwartzH3Energy1 f +
              18 * lowNormalRealSchwartzH3Energy2 f) ∨
        2 * lowNormalRealSchwartzH3FullDissipation244 f <
          -fullSchwartzThirdCommutator244 f := by
    rw [lowNormalRealSchwartz_pathEnergy_eq u t f hRealization,
      lowNormalRealSchwartz_pathEnergy1_eq u t f hRealization,
      lowNormalRealSchwartz_pathEnergy2_eq u t f hRealization,
      thirdFullSchwartz_pathFullDissipation_eq244 u t f hRealization,
      h3Path_fullThirdTransport_eq_realSchwartz_of_realization244
        hH3 hClass htClass f hRealization] at hPhysical
    simpa only [lowNormalRealSchwartzH3FullDissipation244] using hPhysical
  exact ⟨t, ht, f, hRealization, hSchwartz⟩

end
end PrimeTensor.FirstMonomialTriad
