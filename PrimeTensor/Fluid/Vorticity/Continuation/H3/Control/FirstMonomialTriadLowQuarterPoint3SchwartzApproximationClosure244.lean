import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzPathEnergyIdentification244
import Mathlib.Topology.Algebra.Order.Field

/-!
# Schwartz 2-4-4 critical-half bound: precise sequential closure

The previous result applies when a canonical H3 path slice is *exactly* a real
Schwartz pullback. Here the inputs are instead a sequence of Schwartz
vectors whose signed first monomial, E0, E1, and full fourth-order top mass
converge to the *actual* canonical physical scalar quantities.

The conclusion has no Schwartz realization argument; it is valid on every
slice satisfying the explicitly declared approximation property. This is a
closedness statement and NOT a proof of the approximation property for every
H3 slice. The missing analytic issue is strong jet-density and continuity
of the 2-4-4 triple product; mere L2 density does not suffice.

All physical signs, the threefold cyclic multiplicity, and the separate
24*C1 gradient cost are retained. We keep D3 in the sharp version and then
allow D3 <= full D by the existing nonnegative-block lemma.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeApproximationClosure244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- An explicit, four-observable Schwartz approximation of a physical H3
slice. The signed monomial is NOT silently assumed continuous under L2
approximation: its convergence is a distinct component of this predicate. -/
def H3SchwartzCriticalHalfApproximable244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) : Prop :=
  ∃ f : ℕ → A3 → SchwartzMap V3 ℝ,
    Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial (f n)) atTop
      (𝓝 (h3PathCanonicalFirstMonomialAggregateAt u t)) ∧
    Tendsto (fun n => lowNormalRealSchwartzH3Energy0 (f n)) atTop
      (𝓝 (velocityH3Energy0At u t)) ∧
    Tendsto (fun n => lowNormalRealSchwartzH3Energy1 (f n)) atTop
      (𝓝 (velocityH3Energy1At u t)) ∧
    Tendsto (fun n => lowNormalRealSchwartzH3TopDissipation (f n)) atTop
      (𝓝 (velocityH3Dissipation3At u t))

/-- Nonlinear fourth roots and multiplication preserve the existing
Schwartz critical-half inequality under simultaneous convergence of all
four scalar observables. No positivity of the limiting energies is needed
for continuity, and no division by a possibly zero energy occurs. -/
theorem criticalHalf_Schwartz244_limit_closure
    (M E0 E1 D : ℝ)
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (hM : Tendsto (fun n => lowNormalRealSchwartzPoint3Monomial (f n))
      atTop (𝓝 M))
    (h0 : Tendsto (fun n => lowNormalRealSchwartzH3Energy0 (f n))
      atTop (𝓝 E0))
    (h1 : Tendsto (fun n => lowNormalRealSchwartzH3Energy1 (f n))
      atTop (𝓝 E1))
    (hD : Tendsto (fun n => lowNormalRealSchwartzH3TopDissipation (f n))
      atTop (𝓝 D)) :
    |M| ≤ lowNormalRealSchwartz_holder244CriticalConstant *
      Real.sqrt (Real.sqrt (E0 * E1)) * D := by
  have hProduct :
      Tendsto (fun n =>
        lowNormalRealSchwartzH3Energy0 (f n) *
          lowNormalRealSchwartzH3Energy1 (f n)) atTop
        (𝓝 (E0 * E1)) := h0.mul h1
  have hSqrt :
      Tendsto (fun n =>
        Real.sqrt (lowNormalRealSchwartzH3Energy0 (f n) *
          lowNormalRealSchwartzH3Energy1 (f n))) atTop
        (𝓝 (Real.sqrt (E0 * E1))) :=
    (Real.continuous_sqrt.tendsto _).comp hProduct
  have hFourthRoot :
      Tendsto (fun n =>
        Real.sqrt (Real.sqrt (lowNormalRealSchwartzH3Energy0 (f n) *
          lowNormalRealSchwartzH3Energy1 (f n)))) atTop
        (𝓝 (Real.sqrt (Real.sqrt (E0 * E1)))) :=
    (Real.continuous_sqrt.tendsto _).comp hSqrt
  have hAbs :
      Tendsto (fun n => |lowNormalRealSchwartzPoint3Monomial (f n)|)
        atTop (𝓝 |M|) :=
    (continuous_abs.tendsto M).comp hM
  have hRight :
      Tendsto (fun n =>
        lowNormalRealSchwartz_holder244CriticalConstant *
          Real.sqrt (Real.sqrt (lowNormalRealSchwartzH3Energy0 (f n) *
            lowNormalRealSchwartzH3Energy1 (f n))) *
          lowNormalRealSchwartzH3TopDissipation (f n))
        atTop
        (𝓝 (lowNormalRealSchwartz_holder244CriticalConstant *
          Real.sqrt (Real.sqrt (E0 * E1)) * D)) :=
    (tendsto_const_nhds.mul hFourthRoot).mul hD
  exact le_of_tendsto_of_tendsto hAbs hRight
    (Filter.Eventually.of_forall (fun n =>
      lowNormalRealSchwartz_firstMonomial_criticalHalfHomogeneous244 (f n)))

/-- The closed Schwartz estimate is an inequality for the actual canonical
signed physical first-monomial aggregate, without an exact Schwartz
realization hypothesis. The approximation predicate remains explicit. -/
theorem h3PathCanonical_firstMonomial_criticalHalf_of_approx244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (hApprox : H3SchwartzCriticalHalfApproximable244 u t) :
    |h3PathCanonicalFirstMonomialAggregateAt u t| ≤
      lowNormalRealSchwartz_holder244CriticalConstant *
        Real.sqrt (Real.sqrt
          (velocityH3Energy0At u t * velocityH3Energy1At u t)) *
        velocityH3Dissipation3At u t := by
  obtain ⟨f, hM, h0, h1, hD⟩ := hApprox
  exact criticalHalf_Schwartz244_limit_closure
    (h3PathCanonicalFirstMonomialAggregateAt u t)
    (velocityH3Energy0At u t) (velocityH3Energy1At u t)
    (velocityH3Dissipation3At u t) f hM h0 h1 hD

/-- An exact real Schwartz realization is a special case of our weaker
approximation predicate, witnessed by a constant Schwartz sequence. -/
theorem h3PathCanonical_exactSchwartz_implies_approximable244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    H3SchwartzCriticalHalfApproximable244 u t := by
  have hM := lowNormalRealSchwartz_pathFirstMonomial_eq_schwartz244
    u t f hRealization
  have hE0 := lowNormalRealSchwartz_pathEnergy0_eq u t f hRealization
  have hE1 := lowNormalRealSchwartz_pathEnergy1_eq u t f hRealization
  have hD := lowNormalRealSchwartz_pathTopDissipation_eq u t f hRealization
  refine ⟨fun _ => f, ?_, ?_, ?_, ?_⟩
  · simpa only [hM] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => lowNormalRealSchwartzPoint3Monomial f)
          atTop (𝓝 (lowNormalRealSchwartzPoint3Monomial f)))
  · simpa only [hE0] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => lowNormalRealSchwartzH3Energy0 f)
          atTop (𝓝 (lowNormalRealSchwartzH3Energy0 f)))
  · simpa only [hE1] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => lowNormalRealSchwartzH3Energy1 f)
          atTop (𝓝 (lowNormalRealSchwartzH3Energy1 f)))
  · simpa only [hD] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => lowNormalRealSchwartzH3TopDissipation f)
          atTop (𝓝 (lowNormalRealSchwartzH3TopDissipation f)))

/-- The THREE cyclically equivalent monomial types are controlled together
under the new approximation property. This is a signed physical PDE-facing
statement and includes the exact factor three. -/
theorem h3PathCanonical_interpolation_criticalHalf_of_approx244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hApprox : H3SchwartzCriticalHalfApproximable244 u t) :
    |thirdOrderInterpolationTransportSum u t| ≤
      3 * lowNormalRealSchwartz_holder244CriticalConstant *
        Real.sqrt (Real.sqrt
          (velocityH3Energy0At u t * velocityH3Energy1At u t)) *
        velocityH3Dissipation3At u t := by
  have hMonomial :=
    h3PathCanonical_firstMonomial_criticalHalf_of_approx244 u t hApprox
  calc
    |thirdOrderInterpolationTransportSum u t| =
        3 * |h3PathCanonicalFirstMonomialAggregateAt u t| := by
      rw [h3PathCanonical_interpolation_eq_three_firstMonomialAggregate
        hH3 hClass ht, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    _ ≤ 3 * (lowNormalRealSchwartz_holder244CriticalConstant *
          Real.sqrt (Real.sqrt
            (velocityH3Energy0At u t * velocityH3Energy1At u t)) *
          velocityH3Dissipation3At u t) :=
      mul_le_mul_of_nonneg_left hMonomial (by norm_num)
    _ = _ := by ring

/-- Entire top-order H3 transport bound under sequential Schwartz
approximation. The separate gradient cost is not dropped. The top
viscous term may be enlarged to all orders of physical dissipation. -/
theorem h3PathCanonical_thirdTransport_criticalHalf_of_approx244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hApprox : H3SchwartzCriticalHalfApproximable244 u t) :
    |velocityH3TransportDerivative3At u t| ≤
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t +
      3 * lowNormalRealSchwartz_holder244CriticalConstant *
        Real.sqrt (Real.sqrt
          (velocityH3Energy0At u t * velocityH3Energy1At u t)) *
        velocityH3DissipationAt u t := by
  have hSplit := h3PathCanonical_thirdTransport_eq_gradient_add_interpolation
    hH3 hClass ht
  have hGradient := h3PathCanonical_abs_gradientTransport_le_topEnergy
    hH3 hClass ht
  have hInterpolation := h3PathCanonical_interpolation_criticalHalf_of_approx244
    hH3 hClass ht hApprox
  have hCoeff :
      0 ≤ 3 * lowNormalRealSchwartz_holder244CriticalConstant *
        Real.sqrt (Real.sqrt
          (velocityH3Energy0At u t * velocityH3Energy1At u t)) := by
    have hK := lowNormalRealSchwartz_holder244CriticalConstant_nonneg
    positivity
  have hTop := schwartzPath_topDissipation_le_full u t
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
              (velocityH3Energy0At u t * velocityH3Energy1At u t)) *
            velocityH3Dissipation3At u t :=
      add_le_add hGradient hInterpolation
    _ ≤ 24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t +
          3 * lowNormalRealSchwartz_holder244CriticalConstant *
            Real.sqrt (Real.sqrt
              (velocityH3Energy0At u t * velocityH3Energy1At u t)) *
            velocityH3DissipationAt u t := by
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hTop hCoeff)

end
end PrimeTensor.FirstMonomialTriad
