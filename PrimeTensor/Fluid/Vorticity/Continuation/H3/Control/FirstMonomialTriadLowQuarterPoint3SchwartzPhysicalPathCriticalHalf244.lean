import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzCriticalHalfFromHolder244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadPhysicalShell

/-!
# Transport the physical Schwartz critical-half estimate to canonical H³ slices

The unconditional real-Schwartz bound of the previous module controls the
complete signed 243-slot first monomial M(f). An already-proved physical
realization identity identifies M(f) with the canonical signed type-0
aggregate A₀(u,t) whenever the path slice is represented by a REAL Schwartz
family f. Separately the established mixed-partial reindexing proves
I₃(u,t) = 3 A₀(u,t), and the canonical gradient bound controls G₃.

This module assembles these results with their exact constants:

  |I₃| ≤ 3 K (E₀(f) E₁(f))^(1/4) D(f),
  |T₃| ≤ 24 C₁ sqrt(E(u,t)) E₃(u,t)
           + 3 K (E₀(f) E₁(f))^(1/4) D(f).

The H³ path assumptions and REAL Schwartz realization remain explicit.
In particular, this is NOT a proof that an arbitrary H³ slice is Schwartz,
not an identification of Schwartz energies with path energy, and not an
unconditional continuation theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypePhysicalPathCriticalHalf244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical type-0 signed physical path aggregate agrees EXACTLY with
our already bounded real 243-slot Schwartz monomial. Both include the factor
two from spatial energy pairing. -/
theorem lowNormalRealSchwartz_pathFirstMonomial_eq_schwartz244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    h3PathCanonicalFirstMonomialAggregateAt u t =
      lowNormalRealSchwartzPoint3Monomial f := by
  rw [h3PathCanonicalFirstMonomialAggregate_eq_complexSchwartz
    u t f hRealization,
    lowNormalRealSchwartzPoint3Monomial_eq_complex]

/-- The entire signed interpolation block, not a selected monomial, is THREE
copies of the real Schwartz monomial on a realized canonical H³ slice. -/
theorem lowNormalRealSchwartz_pathInterpolation_eq_three_schwartz244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    thirdOrderInterpolationTransportSum u t =
      3 * lowNormalRealSchwartzPoint3Monomial f := by
  rw [h3PathCanonical_interpolation_eq_three_firstMonomialAggregate
    hH3 hClass ht,
    lowNormalRealSchwartz_pathFirstMonomial_eq_schwartz244
      u t f hRealization]

/-- Homogeneous critical-half control of the full signed *interpolation*
commutator. The factor three is the proven physical cyclic multiplicity. -/
theorem lowNormalRealSchwartz_pathInterpolation_criticalHalf244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    |thirdOrderInterpolationTransportSum u t| ≤
      3 * lowNormalRealSchwartz_holder244CriticalConstant *
        Real.sqrt (Real.sqrt
          (lowNormalRealSchwartzH3Energy0 f *
            lowNormalRealSchwartzH3Energy1 f)) *
        lowNormalRealSchwartzH3TopDissipation f := by
  have hMonomial :=
    lowNormalRealSchwartz_firstMonomial_criticalHalfHomogeneous244 f
  calc
    |thirdOrderInterpolationTransportSum u t| =
        3 * |lowNormalRealSchwartzPoint3Monomial f| := by
      rw [lowNormalRealSchwartz_pathInterpolation_eq_three_schwartz244
        hH3 hClass ht f hRealization,
        abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    _ ≤ 3 * (lowNormalRealSchwartz_holder244CriticalConstant *
          Real.sqrt (Real.sqrt
            (lowNormalRealSchwartzH3Energy0 f *
              lowNormalRealSchwartzH3Energy1 f)) *
          lowNormalRealSchwartzH3TopDissipation f) :=
      mul_le_mul_of_nonneg_left hMonomial (by norm_num)
    _ = 3 * lowNormalRealSchwartz_holder244CriticalConstant *
          Real.sqrt (Real.sqrt
            (lowNormalRealSchwartzH3Energy0 f *
              lowNormalRealSchwartzH3Energy1 f)) *
          lowNormalRealSchwartzH3TopDissipation f := by ring

/-- Complete top-order H³ transport: the already proved physical gradient
estimate plus the now proved realized-Schwartz interpolation estimate.
This does not suppress the gradient term or identify the path energies with
the Schwartz energies without further proofs. -/
theorem lowNormalRealSchwartz_pathThirdTransport_criticalHalf244
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
          (lowNormalRealSchwartzH3Energy0 f *
            lowNormalRealSchwartzH3Energy1 f)) *
        lowNormalRealSchwartzH3TopDissipation f := by
  have hSplit :=
    h3PathCanonical_thirdTransport_eq_gradient_add_interpolation
      hH3 hClass ht
  have hGradient :=
    h3PathCanonical_abs_gradientTransport_le_topEnergy
      hH3 hClass ht
  have hInterp := lowNormalRealSchwartz_pathInterpolation_criticalHalf244
    hH3 hClass ht f hRealization
  calc
    |velocityH3TransportDerivative3At u t| =
        |thirdOrderGradientTransportSum u t +
          thirdOrderInterpolationTransportSum u t| := by rw [hSplit]
    _ ≤ |thirdOrderGradientTransportSum u t| +
          |thirdOrderInterpolationTransportSum u t| := abs_add_le _ _
    _ ≤ 24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t +
          3 * lowNormalRealSchwartz_holder244CriticalConstant *
            Real.sqrt (Real.sqrt
              (lowNormalRealSchwartzH3Energy0 f *
                lowNormalRealSchwartzH3Energy1 f)) *
            lowNormalRealSchwartzH3TopDissipation f :=
      add_le_add hGradient hInterp

end
end PrimeTensor.FirstMonomialTriad
