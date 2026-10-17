import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzPhysicalPathCriticalHalf244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Dissipation

/-!
# Identify the actual physical H³ path energies of a Schwartz-realized slice

The previous signed 243-slot theorem had a real Schwartz realization but
still expressed its critical-half bound with Schwartz energies. Here we
identify the zero- and first-order masses exactly with the canonical path
energies, and identify the full 243-slot fourth derivative mass with the
TOP (order-three) canonical dissipation. The order of the four derivative
indices changes only by FINITE SUM REINDEXING, not by assuming that mixed
partials commute.

The resulting top-transport estimate uses only genuine physical path energy
terms, and can enlarge the top dissipation to full canonical dissipation.
No assumption that a general H³ slice is Schwartz is introduced or erased.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeSchwartzPathEnergy244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact real square integral after the physical Point3 pullback. -/
private theorem schwartzPath_squareEnergy_eq
    (g : SchwartzMap V3 ℝ) :
    spatialSquareEnergy (h3SchwartzPoint3Scalar g) =
      ∫ x : V3, (g x) ^ 2 := by
  unfold spatialSquareEnergy h3SchwartzPoint3Scalar
  exact h3Point3ToFourier_integral (fun x : V3 => (g x) ^ 2)

/-- Physical kinetic energy and the complete three-component Schwartz mass. -/
theorem lowNormalRealSchwartz_pathEnergy0_eq
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    velocityH3Energy0At u t = lowNormalRealSchwartzH3Energy0 f := by
  classical
  unfold velocityH3Energy0At lowNormalRealSchwartzH3Energy0
  apply Finset.sum_congr rfl
  intro j _
  rw [hRealization j]
  exact schwartzPath_squareEnergy_eq (f j)

/-- The nine physical first-jet slots equal the nine Schwartz slots. -/
theorem lowNormalRealSchwartz_pathEnergy1_eq
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    velocityH3Energy1At u t = lowNormalRealSchwartzH3Energy1 f := by
  classical
  unfold velocityH3Energy1At lowNormalRealSchwartzH3Energy1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hRealization j, h3SchwartzPoint3Scalar_spatial_d]
  exact schwartzPath_squareEnergy_eq
    (∂_{h3FourierAxisDirection i} (f j))

/-- The 27 physical second-jet slots agree with the 27 Schwartz slots. -/
theorem lowNormalRealSchwartz_pathEnergy2_eq
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    velocityH3Energy2At u t = lowNormalRealSchwartzH3Energy2 f := by
  classical
  unfold velocityH3Energy2At lowNormalRealSchwartzH3Energy2
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [hRealization j, h3SchwartzPoint3Scalar_spatial_d,
    h3SchwartzPoint3Scalar_spatial_d]
  exact schwartzPath_squareEnergy_eq
    (∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection k} (f j)))

/-- The 81 physical third-jet slots agree with the Schwartz slots. -/
theorem lowNormalRealSchwartz_pathEnergy3_eq
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    velocityH3Energy3At u t = lowNormalRealSchwartzH3Energy3 f := by
  classical
  unfold velocityH3Energy3At lowNormalRealSchwartzH3Energy3
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hRealization j, h3SchwartzPoint3Scalar_spatial_d,
    h3SchwartzPoint3Scalar_spatial_d,
    h3SchwartzPoint3Scalar_spatial_d]
  exact schwartzPath_squareEnergy_eq
    (∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection k}
        (∂_{h3FourierAxisDirection l} (f j))))

/-- Rotate the fourth derivative's SUM indices. Derivatives themselves are
not commuted. This remains true for an arbitrary, non-symmetric function. -/
private theorem schwartzPath_rotate_four_sums
    (F : A3 → A3 → A3 → A3 → ℝ) :
    (∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
      F r i k l) =
    ∑ r : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
      F r i k l := by
  classical
  calc
    _ = ∑ i : A3, ∑ k : A3, ∑ r : A3, ∑ l : A3,
          F r i k l := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = ∑ i : A3, ∑ r : A3, ∑ k : A3, ∑ l : A3,
          F r i k l := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The true physical top viscous mass and the 243-slot Schwartz mass
are equal; no selected factor and no derivative commutation is used. -/
theorem lowNormalRealSchwartz_pathTopDissipation_eq
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    velocityH3Dissipation3At u t =
      lowNormalRealSchwartzH3TopDissipation f := by
  classical
  let F : A3 → A3 → A3 → A3 → A3 → ℝ := fun j r i k l =>
    ∫ x : V3,
      ((∂_{h3FourierAxisDirection r}
        (∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection k}
            (∂_{h3FourierAxisDirection l} (f j))))) x) ^ 2
  have hSlot (j i k l r : A3) :
      spatialSquareEnergy
        (spatial3.d r
          (spatial3.d i
            (spatial3.d k
              (spatial3.d l (loggedVelocityComponent u t j))))) =
        F j r i k l := by
    dsimp only [F]
    rw [hRealization j, h3SchwartzPoint3Scalar_spatial_d,
      h3SchwartzPoint3Scalar_spatial_d,
      h3SchwartzPoint3Scalar_spatial_d,
      h3SchwartzPoint3Scalar_spatial_d]
    exact schwartzPath_squareEnergy_eq _
  change (∑ j : A3, ∑ i : A3, ∑ k : A3,
    ∑ l : A3, ∑ r : A3,
      spatialSquareEnergy
        (spatial3.d r (spatial3.d i (spatial3.d k
          (spatial3.d l (loggedVelocityComponent u t j)))))) =
    ∑ j : A3, ∑ r : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
      F j r i k l
  calc
    _ = ∑ j : A3, ∑ i : A3, ∑ k : A3,
          ∑ l : A3, ∑ r : A3, F j r i k l := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro r _
      exact hSlot j i k l r
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact schwartzPath_rotate_four_sums (F j)

/-- Top fourth-order viscous energy is one nonnegative block of the entire
canonical dissipation. -/
theorem schwartzPath_topDissipation_le_full
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    velocityH3Dissipation3At u t ≤ velocityH3DissipationAt u t := by
  have h0 := velocityH3Dissipation0At_nonneg u t
  have h1 := velocityH3Dissipation1At_nonneg u t
  have h2 := velocityH3Dissipation2At_nonneg u t
  unfold velocityH3DissipationAt
  linarith

/-- Complete path H³ energy is exactly the normalized Schwartz energy
under a real Schwartz realization. No auxiliary scalar envelope. -/
theorem lowNormalRealSchwartz_pathEnergy_eq
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    velocityH3EnergyAt u t = lowNormalRealSchwartzH3Energy f := by
  unfold velocityH3EnergyAt lowNormalRealSchwartzH3Energy
  rw [lowNormalRealSchwartz_pathEnergy0_eq u t f hRealization,
    lowNormalRealSchwartz_pathEnergy1_eq u t f hRealization,
    lowNormalRealSchwartz_pathEnergy2_eq u t f hRealization,
    lowNormalRealSchwartz_pathEnergy3_eq u t f hRealization]

/-- The full signed top transport estimate with canonical path energies,
not a separate Schwartz-mass proxy. The realization premise remains exact. -/
theorem lowNormalRealSchwartz_pathThirdTransport_physicalEnergies244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    |velocityH3TransportDerivative3At u t| ≤
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t +
      3 * lowNormalRealSchwartz_holder244CriticalConstant *
        Real.sqrt (Real.sqrt
          (velocityH3Energy0At u t * velocityH3Energy1At u t)) *
        velocityH3DissipationAt u t := by
  have hBound := lowNormalRealSchwartz_pathThirdTransport_criticalHalf244
    hH3 hClass ht f hRealization
  have h0 := lowNormalRealSchwartz_pathEnergy0_eq u t f hRealization
  have h1 := lowNormalRealSchwartz_pathEnergy1_eq u t f hRealization
  have hD := lowNormalRealSchwartz_pathTopDissipation_eq u t f hRealization
  rw [← h0, ← h1, ← hD] at hBound
  have hK := lowNormalRealSchwartz_holder244CriticalConstant_nonneg
  have hCoeff :
      0 ≤ 3 * lowNormalRealSchwartz_holder244CriticalConstant *
        Real.sqrt (Real.sqrt
          (velocityH3Energy0At u t * velocityH3Energy1At u t)) := by
    positivity
  have hTop := schwartzPath_topDissipation_le_full u t
  calc
    |velocityH3TransportDerivative3At u t| ≤
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t +
        3 * lowNormalRealSchwartz_holder244CriticalConstant *
          Real.sqrt (Real.sqrt
            (velocityH3Energy0At u t * velocityH3Energy1At u t)) *
          velocityH3Dissipation3At u t := hBound
    _ ≤ 24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t +
        3 * lowNormalRealSchwartz_holder244CriticalConstant *
          Real.sqrt (Real.sqrt
            (velocityH3Energy0At u t * velocityH3Energy1At u t)) *
          velocityH3DissipationAt u t := by
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hTop hCoeff)

end
end PrimeTensor.FirstMonomialTriad
