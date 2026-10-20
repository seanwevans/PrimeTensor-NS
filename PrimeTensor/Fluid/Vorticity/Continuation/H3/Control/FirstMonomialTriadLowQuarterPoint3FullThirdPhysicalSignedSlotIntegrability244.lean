import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSecondL4Identification244
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-!
# Actual physical H³ signed 3–2–2 slots are integrable

The prior checkpoint identifies the canonical L⁴ second-derivative trace
almost everywhere with the OLD physical L² second derivative. This removes
the representative ambiguity in the signed 243-slot interpolation density.

The two physical second-order derivatives are genuine L⁴ functions; their
product is in L² by Hölder 4–4–2, and multiplying by the old L² third
spatial derivative is integrable by Hölder 2–2–1. No Schwartz realization
of the physical velocity slice is assumed.

We also show that replacing both old second-jet representatives by their
canonical L⁴ classes does not change any of the 243 actual integrals or the
complete physical-order finite sum. The separate identification of this
physical L²/L⁴ aggregate with the pre-existing `spatialEnergyPairing`
remains to be made; this module does not assert that identification.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypePhysicalSignedSlots244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

local instance h3PhysicalSignedFact2244 : Fact (1 ≤ (2 : ENNReal)) :=
  ⟨by norm_num⟩
local instance h3PhysicalSignedFact4244 : Fact (1 ≤ (4 : ENNReal)) :=
  ⟨by norm_num⟩

/-- Exactly 1/4 + 1/4 = 1/2 in extended-real Hölder exponents. -/
local instance h3PhysicalSignedHolder44244 :
    ENNReal.HolderTriple 4 4 2 := by
  refine ⟨?_⟩
  have hFour : (4 : ENNReal) = (2 : ENNReal) ^ 2 := by norm_num
  simp only [hFour, ENNReal.inv_pow]
  calc
    (2 : ENNReal)⁻¹ ^ 2 + (2 : ENNReal)⁻¹ ^ 2 =
        ((2 : ENNReal)⁻¹ + 2⁻¹) * 2⁻¹ := by ring
    _ = (2 : ENNReal)⁻¹ := by
      rw [ENNReal.inv_two_add_inv_two, one_mul]

/-- The actual old physical second jet, transported to the common Euclidean
carrier, before any canonical representative is substituted. -/
noncomputable def h3ActualSecondJetOnFourierCarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j : Fin 3) (a b : A3) : H3FourierRealL2 :=
  h3ToFourierRealL2
    (velocityH3L2JetAt u t hInt hMeas
      (h3JetSlot2 j (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b)))

/-- Exactly the physical third-order jet entering the old spatial H³
energy pairing, on the same volume-preserving carrier. -/
noncomputable def h3ActualThirdJetOnFourierCarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j : Fin 3) (a b c : A3) : H3FourierRealL2 :=
  h3ToFourierRealL2
    (velocityH3L2JetAt u t hInt hMeas
      (h3JetSlot3 j (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b)
        (h3ClassicalizationFinOfAxis c)))

/-- A genuine L⁴ integrability assertion for the original physical H³
second derivative, not merely its Schwartz or canonical substitute. -/
theorem h3ActualSecondJet_memLp_four244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) (a b : A3) :
    MemLp (h3ActualSecondJetOnFourierCarrier244 hInt hMeas j a b : V3 → ℝ)
      (4 : ENNReal) (volume : Measure V3) := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  have hAE :
      (weightedH3CanonicalSecondJetL4Trace244 U j a b : V3 → ℝ)
        =ᵐ[(volume : Measure V3)]
      (h3ActualSecondJetOnFourierCarrier244 hInt hMeas j a b : V3 → ℝ) := by
    exact weightedH3CanonicalSecondJetL4Trace_ae_eq_actualPhysical244
      hFourier j a b
  exact (memLp_congr_ae hAE).mp
    (Lp.memLp (weightedH3CanonicalSecondJetL4Trace244 U j a b))

/-- The actual physical 3–2–2 density at EVERY ordered five-axis slot
belongs to L¹. The proof uses only old physical L² jets and the canonical
L⁴ representative identification, with exact 4–4–2 and 2–2–1 Hölder. -/
theorem h3ActualSignedFirstMonomialSlot_integrable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j r i k l : A3) :
    Integrable (fun x : V3 =>
      (h3ActualThirdJetOnFourierCarrier244 hInt hMeas
        (h3ClassicalizationFinOfAxis j) i k l : V3 → ℝ) x *
      ((h3ActualSecondJetOnFourierCarrier244 hInt hMeas
          (h3ClassicalizationFinOfAxis r) k l : V3 → ℝ) x *
       (h3ActualSecondJetOnFourierCarrier244 hInt hMeas
          (h3ClassicalizationFinOfAxis j) i r : V3 → ℝ) x))
      (volume : Measure V3) := by
  let A : V3 → ℝ :=
    (h3ActualThirdJetOnFourierCarrier244 hInt hMeas
      (h3ClassicalizationFinOfAxis j) i k l : V3 → ℝ)
  let B : V3 → ℝ :=
    (h3ActualSecondJetOnFourierCarrier244 hInt hMeas
      (h3ClassicalizationFinOfAxis r) k l : V3 → ℝ)
  let C : V3 → ℝ :=
    (h3ActualSecondJetOnFourierCarrier244 hInt hMeas
      (h3ClassicalizationFinOfAxis j) i r : V3 → ℝ)
  have hA : MemLp A (2 : ENNReal) (volume : Measure V3) :=
    Lp.memLp _
  have hB : MemLp B (4 : ENNReal) (volume : Measure V3) :=
    h3ActualSecondJet_memLp_four244 hFourier
      (h3ClassicalizationFinOfAxis r) k l
  have hC : MemLp C (4 : ENNReal) (volume : Measure V3) :=
    h3ActualSecondJet_memLp_four244 hFourier
      (h3ClassicalizationFinOfAxis j) i r
  have hBC : MemLp (fun x : V3 => B x * C x)
      (2 : ENNReal) (volume : Measure V3) := by
    -- The project's PINNED mathlib (a021f70d) provides `MemLp.mul'`.
    -- Its arguments are (hf : MemLp f q μ) then (hφ : MemLp φ p μ),
    -- and it concludes the pointwise function `fun x => φ x * f x`.
    exact MemLp.mul' (r := (2 : ENNReal)) hC hB
  have hABC : Integrable (fun x : V3 => A x * (B x * C x))
      (volume : Measure V3) := by
    exact hA.integrable_mul hBC
  exact hABC

/-- The finite scalar value of one old physical 3–2–2 pairing after exact
volume-preserving transport to the Fourier carrier. -/
noncomputable def h3ActualSignedFirstMonomialSlotIntegral244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j r i k l : A3) : ℝ :=
  ∫ x : V3,
    (h3ActualThirdJetOnFourierCarrier244 hInt hMeas
      (h3ClassicalizationFinOfAxis j) i k l : V3 → ℝ) x *
    ((h3ActualSecondJetOnFourierCarrier244 hInt hMeas
        (h3ClassicalizationFinOfAxis r) k l : V3 → ℝ) x *
     (h3ActualSecondJetOnFourierCarrier244 hInt hMeas
        (h3ClassicalizationFinOfAxis j) i r : V3 → ℝ) x)

/-- The same physical slot, evaluated with the canonical L⁴ second jets.
The third factor in the energy pairing remains the OLD physical L² jet. -/
noncomputable def h3CanonicalSignedFirstMonomialSlotIntegral244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j r i k l : A3) : ℝ :=
  ∫ x : V3,
    (h3ActualThirdJetOnFourierCarrier244 hInt hMeas
      (h3ClassicalizationFinOfAxis j) i k l : V3 → ℝ) x *
    ((weightedH3CanonicalSecondJetL4Trace244
        (velocityH3SpectralStateAt u t hInt hMeas hFourier)
        (h3ClassicalizationFinOfAxis r) k l : V3 → ℝ) x *
     (weightedH3CanonicalSecondJetL4Trace244
        (velocityH3SpectralStateAt u t hInt hMeas hFourier)
        (h3ClassicalizationFinOfAxis j) i r : V3 → ℝ) x)

/-- Both actual second-jet representatives may be replaced in the spatial
integral by the canonical L⁴ traces, without changing its signed value. -/
theorem h3ActualSignedFirstMonomialSlotIntegral_eq_canonical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j r i k l : A3) :
    h3ActualSignedFirstMonomialSlotIntegral244 hInt hMeas j r i k l =
      h3CanonicalSignedFirstMonomialSlotIntegral244 hFourier j r i k l := by
  have hMiddle := weightedH3CanonicalSecondJetL4Trace_ae_eq_actualPhysical244
    hFourier (h3ClassicalizationFinOfAxis r) k l
  have hCross := weightedH3CanonicalSecondJetL4Trace_ae_eq_actualPhysical244
    hFourier (h3ClassicalizationFinOfAxis j) i r
  unfold h3ActualSignedFirstMonomialSlotIntegral244
    h3CanonicalSignedFirstMonomialSlotIntegral244
  apply integral_congr_ae
  filter_upwards [hMiddle, hCross] with x hm hc
  rw [hm, hc]
  rfl

/-- The FULL 243-slot physical-order aggregate, retaining the physical
energy-pairing factor two and all five ordered index sums. -/
noncomputable def h3ActualSignedFirstMonomialAggregate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t) : ℝ :=
  2 * (∑ j : A3, ∑ r : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
    h3ActualSignedFirstMonomialSlotIntegral244 hInt hMeas j r i k l)

/-- Finite old-physical 3–2–2 aggregate with the canonical L⁴ second jets. -/
noncomputable def h3CanonicalSignedFirstMonomialAggregate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) : ℝ :=
  2 * (∑ j : A3, ∑ r : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3,
    h3CanonicalSignedFirstMonomialSlotIntegral244 hFourier j r i k l)

/-- Replacing the L²-class representatives by the canonical L⁴ classes
commutes with the ENTIRE ordered signed 243-slot sum. No compensating
error term or extra combinatorial multiplicity appears. -/
theorem h3ActualSignedFirstMonomialAggregate_eq_canonical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    h3ActualSignedFirstMonomialAggregate244 hInt hMeas =
      h3CanonicalSignedFirstMonomialAggregate244 hFourier := by
  unfold h3ActualSignedFirstMonomialAggregate244
    h3CanonicalSignedFirstMonomialAggregate244
  simp_rw [h3ActualSignedFirstMonomialSlotIntegral_eq_canonical244 hFourier]

end
end PrimeTensor.FirstMonomialTriad
