import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSignedSlotIntegrability244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadPhysicalTransport
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Preterminal.Incompressibility
import Mathlib.Tactic

/-!
# Old physical spatial interpolation = actual 243-slot L²–L⁴–L⁴ aggregate

The preceding module constructs integrable signed products from genuine old
velocityH3L2JetAt classes and establishes their independence of the chosen
canonical L⁴ representatives.  Here we identify each integral with the OLD
spatialEnergyPairing of the original C³ physical derivatives.

Two pre-existing bridges suffice: the old concrete L² jet represents its
spatial derivative a.e., and the Point3/Euclidean change of carrier preserves
volume. No new Schwartz realization, transport cancellation or physical
nonextension hypothesis is introduced. In particular, this module does NOT
equate the old physical signed aggregate with the separate weighted-spectral
Schwartz-limit observable.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeSignedSpatial244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceSignedSpatial244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The ACTUAL old physical L² jet, transferred to the Euclidean carrier,
represents the original Point3 derivative evaluated at its inverse-volume
coordinate. This works for every semantic jet slot, not only 3–2–2. -/
theorem h3ActualPhysicalJetFourierCarrier_ae_eq_oldJetField244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (slot : H3JetIndex) :
    (h3ToFourierRealL2 (velocityH3L2JetAt u t hInt hMeas slot) : V3 → ℝ)
      =ᵐ[(volume : Measure V3)]
    (fun x : V3 => velocityH3JetFieldAt u t slot (WithLp.ofLp x)) := by
  have hTransport :=
    Lp.coeFn_compMeasurePreserving
      (velocityH3L2JetAt u t hInt hMeas slot)
      (PiLp.volume_preserving_ofLp A3)
  have hOld :=
    (PiLp.volume_preserving_ofLp A3).quasiMeasurePreserving.ae_eq_comp
      (velocityH3L2JetAt_ae_eq_jetField hInt hMeas slot)
  exact hTransport.trans hOld

/-- One fully ordered actual signed density, using ONLY the old physical
Point3 derivatives: j=component, r=contraction, i,k,l=derivative order. -/
noncomputable def h3OldPhysicalSignedFirstMonomialDensity244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (j r i k l : A3) : Point3 → ℝ :=
  fun x =>
    spatial3.d i (spatial3.d k (spatial3.d l
      (loggedVelocityComponent u t j))) x *
    ((spatial3.d k (spatial3.d l
        (loggedVelocityComponent u t r))) x *
     (spatial3.d i (spatial3.d r
        (loggedVelocityComponent u t j))) x)

/-- The three old L² jet representatives give exactly the original
physical derivative product a.e. after volume-preserving transport. -/
theorem h3ActualSignedFirstMonomialDensity_ae_eq_oldPhysical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j r i k l : A3) :
    (fun x : V3 =>
      (h3ActualThirdJetOnFourierCarrier244 hInt hMeas
        (h3ClassicalizationFinOfAxis j) i k l : V3 → ℝ) x *
      ((h3ActualSecondJetOnFourierCarrier244 hInt hMeas
          (h3ClassicalizationFinOfAxis r) k l : V3 → ℝ) x *
       (h3ActualSecondJetOnFourierCarrier244 hInt hMeas
          (h3ClassicalizationFinOfAxis j) i r : V3 → ℝ) x))
      =ᵐ[(volume : Measure V3)]
    (fun x : V3 =>
      h3OldPhysicalSignedFirstMonomialDensity244 u t j r i k l (WithLp.ofLp x)) := by
  have hA := h3ActualPhysicalJetFourierCarrier_ae_eq_oldJetField244
    hInt hMeas
    (h3JetSlot3 (h3ClassicalizationFinOfAxis j)
      (h3ClassicalizationFinOfAxis i) (h3ClassicalizationFinOfAxis k)
      (h3ClassicalizationFinOfAxis l))
  have hB := h3ActualPhysicalJetFourierCarrier_ae_eq_oldJetField244
    hInt hMeas
    (h3JetSlot2 (h3ClassicalizationFinOfAxis r)
      (h3ClassicalizationFinOfAxis k) (h3ClassicalizationFinOfAxis l))
  have hC := h3ActualPhysicalJetFourierCarrier_ae_eq_oldJetField244
    hInt hMeas
    (h3JetSlot2 (h3ClassicalizationFinOfAxis j)
      (h3ClassicalizationFinOfAxis i) (h3ClassicalizationFinOfAxis r))
  filter_upwards [hA, hB, hC] with x ha hb hc
  -- `ha`, `hb`, and `hc` identify the underlying `h3ToFourierRealL2`
  -- expressions. Expose those expressions before rewriting; a wildcard
  -- `change` does not unfold the three physical-jet wrappers.
  dsimp only [h3ActualThirdJetOnFourierCarrier244,
    h3ActualSecondJetOnFourierCarrier244]
  rw [ha, hb, hc]
  simp only [h3OldPhysicalSignedFirstMonomialDensity244,
    velocityH3JetFieldAt, h3JetSlot2, h3JetSlot3,
    h3AxisOfFin3_h3ClassicalizationFinOfAxis]

/-- The SAME 3–2–2 product has equal Euclidean and physical spatial
integrals. There is no Jacobian constant or (2π)-normalization. -/
theorem h3ActualSignedFirstMonomialSlotIntegral_eq_oldPhysicalIntegral244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j r i k l : A3) :
    h3ActualSignedFirstMonomialSlotIntegral244 hInt hMeas j r i k l =
      ∫ x : Point3, h3OldPhysicalSignedFirstMonomialDensity244 u t j r i k l x := by
  have hAE := h3ActualSignedFirstMonomialDensity_ae_eq_oldPhysical244
    hInt hMeas j r i k l
  have hEmb : MeasurableEmbedding (WithLp.ofLp : V3 → Point3) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : A3 => ℝ)).toHomeomorph.measurableEmbedding
  calc
    h3ActualSignedFirstMonomialSlotIntegral244 hInt hMeas j r i k l =
      ∫ x : V3, h3OldPhysicalSignedFirstMonomialDensity244
        u t j r i k l (WithLp.ofLp x) := by
      unfold h3ActualSignedFirstMonomialSlotIntegral244
      exact integral_congr_ae hAE
    _ = ∫ x : Point3,
      h3OldPhysicalSignedFirstMonomialDensity244 u t j r i k l x :=
        (PiLp.volume_preserving_ofLp A3).integral_comp hEmb _

/-- ACTUAL first physical interpolation monomial is exactly twice the
new integrable old-L² jet integral. All five indices retain their physical
ordering; the factor two is the energy-pairing normalization. -/
theorem h3PathCanonicalInterpolationMonomialPairing_eq_actualSignedSlot244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j r i k l : A3) :
    h3PathCanonicalInterpolationMonomialPairing u t j i k l r 0 =
      2 * h3ActualSignedFirstMonomialSlotIntegral244 hInt hMeas j r i k l := by
  rw [h3ActualSignedFirstMonomialSlotIntegral_eq_oldPhysicalIntegral244
    hInt hMeas j r i k l]
  unfold h3PathCanonicalInterpolationMonomialPairing
  simp only [ite_true]
  unfold spatialEnergyPairing thirdOrderInterpolationMonomial1
  rfl

/-- The complete ORIGINAL signed physical interpolation aggregate is
identical to the newly constructed 243-slot old-jet aggregate. No Schwartz
realization or L⁴ representative choice remains in this equality. -/
theorem h3PathCanonicalFirstMonomialAggregate_eq_actualSigned244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) :
    h3PathCanonicalFirstMonomialAggregateAt u t =
      h3ActualSignedFirstMonomialAggregate244 hInt hMeas := by
  unfold h3PathCanonicalFirstMonomialAggregateAt
    h3ActualSignedFirstMonomialAggregate244
  simp_rw [h3PathCanonicalInterpolationMonomialPairing_eq_actualSignedSlot244
    hInt hMeas]
  simp only [Finset.mul_sum]

/-- Combine the original physical pairing identification with the prior
canonical-L⁴ representative invariance; the result is an EXACT identity of
the old signed physical observable and its canonical second-jet integrals. -/
theorem h3PathCanonicalFirstMonomialAggregate_eq_canonicalSecondL4Integral244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    h3PathCanonicalFirstMonomialAggregateAt u t =
      h3CanonicalSignedFirstMonomialAggregate244 hFourier := by
  calc
    h3PathCanonicalFirstMonomialAggregateAt u t =
        h3ActualSignedFirstMonomialAggregate244 hInt hMeas :=
      h3PathCanonicalFirstMonomialAggregate_eq_actualSigned244 hInt hMeas
    _ = h3CanonicalSignedFirstMonomialAggregate244 hFourier :=
      h3ActualSignedFirstMonomialAggregate_eq_canonical244 hFourier

end
end PrimeTensor.FirstMonomialTriad
