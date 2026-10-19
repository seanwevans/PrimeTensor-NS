import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientIntegrability244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzPathEnergyIdentification244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Balance.Exact
import Mathlib.Tactic

/-!
# Exact complete viscous dissipation of a real-Schwartz NS slice

The preceding checkpoint closed the exact top-order physical transport
identity `T₃(u(t)) = G₃(f) + 3 M(f)` for a real Schwartz realization.
The *top* physical dissipation was already identified with the 243-term
fourth-order Schwartz mass in `SchwartzPathEnergyIdentification244`.

Here we identify the remaining THREE physical viscous blocks. They are
exactly the canonical energy masses one order higher:

    D₀ = E₁, D₁ = E₂, D₂ = E₃.

The latter two equalities exchange only FINITE-SUM bound axes, not mixed
partial derivatives. Combining them with the existing top identification
gives the full, not merely highest-order, physical dissipative mass.

Finally the already-proved exact UNFORCED NS balance becomes

    E'(t) + 2(E₁(f)+E₂(f)+E₃(f)+D₄(f))
        = -(T₀(u,t)+T₁(u,t)+T₂(u,t)+G₃(f)+3 M(f)).

The three lower-order transports are kept explicit. A real Schwartz slice
realization of an already-admissible NS path is still a hypothesis: no
arbitrary static Schwartz packet is asserted to occur at a positive time.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdSchwartzDissipation244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The physical zeroth-order viscous mass is exactly first-jet energy.
This identity is definitional; no time regularity or IBP is required. -/
theorem thirdFullPhysicalDissipation0_eq_energy1_244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    velocityH3Dissipation0At u t = velocityH3Energy1At u t := by
  rfl

/-- Order-one viscous mass is the complete second-jet square mass.
The exterior differentiation axis moves OUTSIDE the finite sum, without
commuting any two spatial differential operators. -/
theorem thirdFullPhysicalDissipation1_eq_energy2_244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    velocityH3Dissipation1At u t = velocityH3Energy2At u t := by
  unfold velocityH3Dissipation1At velocityH3Energy2At
  apply Finset.sum_congr rfl
  intro j _
  let F : A3 → A3 → ℝ := fun r i =>
    spatialSquareEnergy (spatial3.d r (spatial3.d i
      (loggedVelocityComponent u t j)))
  change (∑ i : A3, ∑ r : A3, F r i) =
    ∑ r : A3, ∑ i : A3, F r i
  exact Finset.sum_comm

/-- Order-two viscous mass is the complete third-jet square mass.
The only operation is a cyclic reindexing of the three finite sums; the
order `d r (d i (d k u))` remains literally unchanged. -/
theorem thirdFullPhysicalDissipation2_eq_energy3_244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    velocityH3Dissipation2At u t = velocityH3Energy3At u t := by
  unfold velocityH3Dissipation2At velocityH3Energy3At
  apply Finset.sum_congr rfl
  intro j _
  let F : A3 → A3 → A3 → ℝ := fun r i k =>
    spatialSquareEnergy (spatial3.d r (spatial3.d i
      (spatial3.d k (loggedVelocityComponent u t j))))
  change (∑ i : A3, ∑ k : A3, ∑ r : A3, F r i k) =
    ∑ r : A3, ∑ i : A3, ∑ k : A3, F r i k
  calc
    _ = ∑ i : A3, ∑ r : A3, ∑ k : A3, F r i k := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- For ANY physical velocity slice, its full fourth-order NS dissipation
is the sum of the first three positive H³ energies and the top dissipation.
No Schwartz realization, solenoidality, or PDE hypothesis is needed. -/
theorem thirdFullPhysicalDissipation_eq_lowerEnergies_add_top244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    velocityH3DissipationAt u t =
      velocityH3Energy1At u t + velocityH3Energy2At u t +
        velocityH3Energy3At u t + velocityH3Dissipation3At u t := by
  unfold velocityH3DissipationAt
  rw [thirdFullPhysicalDissipation0_eq_energy1_244,
    thirdFullPhysicalDissipation1_eq_energy2_244,
    thirdFullPhysicalDissipation2_eq_energy3_244]

/-- The complete REAL Schwarz viscous mass (all four dissipative orders),
not only its top D4 term, is exactly the physical PDE dissipation. -/
theorem thirdFullSchwartz_pathFullDissipation_eq244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    velocityH3DissipationAt u t =
      lowNormalRealSchwartzH3Energy1 f +
      lowNormalRealSchwartzH3Energy2 f +
      lowNormalRealSchwartzH3Energy3 f +
      lowNormalRealSchwartzH3TopDissipation f := by
  rw [thirdFullPhysicalDissipation_eq_lowerEnergies_add_top244,
    lowNormalRealSchwartz_pathEnergy1_eq u t f hRealization,
    lowNormalRealSchwartz_pathEnergy2_eq u t f hRealization,
    lowNormalRealSchwartz_pathEnergy3_eq u t f hRealization,
    lowNormalRealSchwartz_pathTopDissipation_eq u t f hRealization]

/-- Exact UNFORCED Navier-Stokes H³ energy balance on a realized Schwartz
slice. The top commutator is now fully represented by the real Schwartz
cubic, and ALL viscous blocks have precisely the matching Schwartz masses.
The unaddressed lower-order transports T0,T1,T2 are displayed explicitly. -/
theorem h3Path_exactEnergyBalance_fullThirdSchwartz244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    deriv (velocityH3EnergyAt u) t +
      2 * (lowNormalRealSchwartzH3Energy1 f +
        lowNormalRealSchwartzH3Energy2 f +
        lowNormalRealSchwartzH3Energy3 f +
        lowNormalRealSchwartzH3TopDissipation f) =
      -(velocityH3TransportDerivative0At u t +
        velocityH3TransportDerivative1At u t +
        velocityH3TransportDerivative2At u t +
        fullSchwartzThirdCommutator244 f) := by
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht
  rw [thirdFullSchwartz_pathFullDissipation_eq244
    u t f hRealization] at hBalance
  unfold velocityH3TransportDerivativeAt at hBalance
  rw [h3Path_fullThirdTransport_eq_realSchwartz_of_realization244
    hH3 hClass ht f hRealization] at hBalance
  exact hBalance

/-- A precise, local sufficient condition for a positive instantaneous H³
slope along an ACTUAL solution. The lower-order transports cannot be
omitted: the adverse static top cubic alone does not imply this condition. -/
theorem h3Path_energySlope_pos_of_realSchwartzFullBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j))
    (hAdverse :
      2 * (lowNormalRealSchwartzH3Energy1 f +
        lowNormalRealSchwartzH3Energy2 f +
        lowNormalRealSchwartzH3Energy3 f +
        lowNormalRealSchwartzH3TopDissipation f) +
      (velocityH3TransportDerivative0At u t +
        velocityH3TransportDerivative1At u t +
        velocityH3TransportDerivative2At u t) <
      -fullSchwartzThirdCommutator244 f) :
    0 < deriv (velocityH3EnergyAt u) t := by
  have hBalance := h3Path_exactEnergyBalance_fullThirdSchwartz244
    hH3 hClass ht f hRealization
  linarith

end
end PrimeTensor.FirstMonomialTriad
