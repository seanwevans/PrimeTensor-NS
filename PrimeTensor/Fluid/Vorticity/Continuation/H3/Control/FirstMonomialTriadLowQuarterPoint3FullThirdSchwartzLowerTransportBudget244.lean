import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzDissipationBalance244
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Cancellation
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.One.Total.Bound
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Two.Total.Bound
import Mathlib.Tactic

/-!
# Full viscous static obstruction and physical lower-transport budget

This checkpoint separates TWO logically different results.

(1) Static: The already-constructed fixed-kinetic solenoidal Schwartz seed
    defeats the ENTIRE physical viscosity mass, not merely the top D4 block.
    Indeed E1+E2+E3 ≤ E = 1+E0+E1+E2+E3, so the old arbitrary coefficient K
    absorbs all three missing dissipative blocks. This does NOT produce an
    admissible NS slice, and makes no claim about finite-time blowup.

(2) Actual paths: If the previously proved zero-order flux cancellation and
    first- and second-order flux/pairing/gradient hypotheses hold, then
    |T1+T2| ≤ (6+18) h(t) E(t) = 24 h(t) E(t).
    Combining this with the exact unforced Schwartz-realized identity yields
    an explicit sufficient condition for positive H3 energy slope. This does
    NOT establish the needed gradient-envelope inequality for a constructed
    static profile or its realization on a solution.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

-- A Schwartz map on the Fourier carrier requires the normed additive
-- structure of its finite coordinate PiLp space. As in the neighboring
-- full-third modules, install the finite-axis instance locally.
noncomputable local instance axisFintypeFullThirdLowerTransport244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- All four dissipative orders of the real Schwartz H3 energy. -/
noncomputable def lowNormalRealSchwartzH3FullDissipation244
    (f : A3 → SchwartzMap V3 ℝ) : ℝ :=
  lowNormalRealSchwartzH3Energy1 f +
    lowNormalRealSchwartzH3Energy2 f +
    lowNormalRealSchwartzH3Energy3 f +
    lowNormalRealSchwartzH3TopDissipation f

/-- The complete lower viscous mass is dominated by normalized H3 energy.
This is an unconditional inequality on any real Schwartz three-vector. -/
theorem thirdFullSchwartz_lowerDissipation_le_energy244
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3Energy1 f +
      lowNormalRealSchwartzH3Energy2 f +
      lowNormalRealSchwartzH3Energy3 f ≤
    lowNormalRealSchwartzH3Energy f := by
  have h0 := lowNormalRealSchwartzH3Energy0_nonneg f
  rw [lowNormalRealSchwartzH3Energy_eq_one_add_quadratic,
    lowNormalRealSchwartzH3EnergyQuadratic_eq_sum]
  linarith

/-- The full viscous quantity is at most top viscosity plus normalized energy.
Finite energy blocks are NOT incorrectly identified with the top one. -/
theorem thirdFullSchwartz_fullDissipation_le_top_add_energy244
    (f : A3 → SchwartzMap V3 ℝ) :
    lowNormalRealSchwartzH3FullDissipation244 f ≤
      lowNormalRealSchwartzH3TopDissipation f +
        lowNormalRealSchwartzH3Energy f := by
  have hLower := thirdFullSchwartz_lowerDissipation_le_energy244 f
  dsimp [lowNormalRealSchwartzH3FullDissipation244]
  linarith

/-- The prior fixed-kinetic witness defeats the *complete* viscous mass at
its physical coefficient 2, plus ANY finite multiple of normalized H3 energy.
This result is static: the witness is not postulated to be a solution slice. -/
theorem thirdFullSchwartz_fixedKinetic_completeViscousAdverse244 :
    ∃ E₀ : ℝ, ∀ K : ℝ,
      ∃ g : A3 → SchwartzMap V3 ℝ,
        lowNormalRealSchwartz_Point3Solenoidal g ∧
        lowNormalRealSchwartzH3Energy0 g = E₀ ∧
        fullSchwartzThirdCommutator244 g < 0 ∧
        2 * lowNormalRealSchwartzH3FullDissipation244 g +
          K * lowNormalRealSchwartzH3Energy g <
          -fullSchwartzThirdCommutator244 g := by
  obtain ⟨E₀, hAll⟩ := thirdFullSchwartz_fixedKinetic_unforcedAdverse244
  refine ⟨E₀, ?_⟩
  intro K
  obtain ⟨g, hDiv, hMass, hNegative, hEscape⟩ := hAll 2 (K + 2)
  refine ⟨g, hDiv, hMass, hNegative, ?_⟩
  have hLower := thirdFullSchwartz_lowerDissipation_le_energy244 g
  dsimp [lowNormalRealSchwartzH3FullDissipation244]
  nlinarith

/-- Uniform static absorption of the adverse third-order cubic by complete
viscosity and normalized H3 energy, restricted to solenoidal Schwartz fields. -/
def FullThirdUnforcedCompleteStaticCoercivity244 (C K : ℝ) : Prop :=
  ∀ f : A3 → SchwartzMap V3 ℝ,
    lowNormalRealSchwartz_Point3Solenoidal f →
      -fullSchwartzThirdCommutator244 f ≤
        C * lowNormalRealSchwartzH3FullDissipation244 f +
          K * lowNormalRealSchwartzH3Energy f

/-- No nonnegative coefficient C on COMPLETE dissipation admits such a
uniform static absorption, even after an arbitrary energy compensation K.
The quantifiers are static and must not be transferred to NS time slices. -/
theorem thirdFullSchwartz_no_completeStaticCoercivity244
    (C K : ℝ) (hC : 0 ≤ C) :
    ¬ FullThirdUnforcedCompleteStaticCoercivity244 C K := by
  intro hUniversal
  obtain ⟨E₀, hAll⟩ := thirdFullSchwartz_fixedKinetic_unforcedAdverse244
  obtain ⟨g, hDiv, hMass, hNegative, hEscape⟩ := hAll C (K + C)
  have hFull := thirdFullSchwartz_fullDissipation_le_top_add_energy244 g
  have hScale := mul_le_mul_of_nonneg_left hFull hC
  have hBound := hUniversal g hDiv
  nlinarith

/-- Remove precisely the kinetic transport term from the full exact physical
Schwartz balance. The flux condition is NOT silently inferred from an energy
class or a static seed. -/
theorem h3Path_exactEnergyBalance_fullThirdSchwartz_noT0_244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hFlux0 : H3TransportEnergyFluxVanishesAt u t) :
    deriv (velocityH3EnergyAt u) t +
      2 * lowNormalRealSchwartzH3FullDissipation244 f =
      -(velocityH3TransportDerivative1At u t +
        velocityH3TransportDerivative2At u t +
        fullSchwartzThirdCommutator244 f) := by
  have hBalance := h3Path_exactEnergyBalance_fullThirdSchwartz244
    hH3 hClass ht f hRealization
  have hZero := velocityH3TransportDerivative0At_eq_zero_of_energyClass
    hClass ht hFlux0
  rw [hZero] at hBalance
  dsimp [lowNormalRealSchwartzH3FullDissipation244]
  simpa only [zero_add] using hBalance

/-- The two remaining lower physical transport orders cost no more than 24
units of gradient envelope times actual H3 energy. The exact Schwartz slice
realization then identifies the latter with Schwartz energy. -/
theorem h3Path_lowerTransport_abs_le_schwartzEnergy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ} {h : ℝ → ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hFlux1 : H3FirstDerivativeTransportFluxVanishesAt u t)
    (hPairing1 : H3OrderOneTransportPairingIntegrableAt u t)
    (hFlux2 : H3SecondDerivativeTransportFluxVanishesAt u t)
    (hPairing2 : H3OrderTwoTransportPairingIntegrableAt u t)
    (hH3 : VelocityH3IntegrableAt u t)
    (hGradient : VelocityGradientEnvelope u h t) :
    |velocityH3TransportDerivative1At u t +
      velocityH3TransportDerivative2At u t| ≤
      24 * h t * lowNormalRealSchwartzH3Energy f := by
  have h1 := velocityH3TransportDerivative1At_le_totalEnergy
    hClass ht hFlux1 hPairing1 hH3 hGradient
  have h2 := velocityH3TransportDerivative2At_le_totalEnergy
    hClass ht hFlux2 hPairing2 hH3 hGradient
  have hEnergy := lowNormalRealSchwartz_pathEnergy_eq u t f hRealization
  rw [hEnergy] at h1 h2
  calc
    |velocityH3TransportDerivative1At u t +
      velocityH3TransportDerivative2At u t| ≤
      |velocityH3TransportDerivative1At u t| +
        |velocityH3TransportDerivative2At u t| := abs_add_le _ _
    _ ≤ 6 * h t * lowNormalRealSchwartzH3Energy f +
        18 * h t * lowNormalRealSchwartzH3Energy f := add_le_add h1 h2
    _ = 24 * h t * lowNormalRealSchwartzH3Energy f := by ring

/-- Conditional, fully quantitative positive energy-slope result. The
hypothesis compares the *whole* adverse top cubic against complete viscosity
and the known 24 h E lower-transport envelope. No chosen static Schwartz
profile is asserted to have the required NS evolution or gradient envelope. -/
theorem h3Path_energySlope_pos_of_completeSchwartzGradientBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ} {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hFlux0 : H3TransportEnergyFluxVanishesAt u t)
    (hFlux1 : H3FirstDerivativeTransportFluxVanishesAt u t)
    (hPairing1 : H3OrderOneTransportPairingIntegrableAt u t)
    (hFlux2 : H3SecondDerivativeTransportFluxVanishesAt u t)
    (hPairing2 : H3OrderTwoTransportPairingIntegrableAt u t)
    (hEnergy : VelocityH3IntegrableAt u t)
    (hGradient : VelocityGradientEnvelope u h t)
    (hAdverse :
      2 * lowNormalRealSchwartzH3FullDissipation244 f +
        24 * h t * lowNormalRealSchwartzH3Energy f <
      -fullSchwartzThirdCommutator244 f) :
    0 < deriv (velocityH3EnergyAt u) t := by
  have hBalance := h3Path_exactEnergyBalance_fullThirdSchwartz_noT0_244
    hH3 hClass ht f hRealization hFlux0
  have hLower := h3Path_lowerTransport_abs_le_schwartzEnergy244
    hClass ht f hRealization hFlux1 hPairing1 hFlux2 hPairing2
    hEnergy hGradient
  have hLowerUpper :
      velocityH3TransportDerivative1At u t +
        velocityH3TransportDerivative2At u t ≤
      24 * h t * lowNormalRealSchwartzH3Energy f := by
    exact le_trans (le_abs_self _) hLower
  linarith

end
end PrimeTensor.FirstMonomialTriad
