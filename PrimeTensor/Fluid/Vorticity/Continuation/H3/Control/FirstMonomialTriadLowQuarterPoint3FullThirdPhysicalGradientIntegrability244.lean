import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalSignedCanonicalLimit244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientPathBridge244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Preterminal.Incompressibility
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-!
# Actual H³ 3–3–1 gradient integrability and the signed-gap reduction

The original physical signed interpolation now agrees with its canonical
Schwartz limit. Hence the complete third-order physical/canonical mismatch
is exactly the gradient mismatch, without a compensating scalar term.

For the gradient part, the original physical third derivatives are in L².
The first derivatives of a genuine Fourier-compatible interior Navier–Stokes
slice are bounded by the proven spectral H³-to-C¹ coefficient. Thus every
physical 3–3–1 density is integrable by the exact L²×L²×L∞ Holder rule.
This is an actual old-physical result, not a Schwartz-realization condition.
It is not yet an identification of the physical gradient integral with its
choice-independent weighted Schwartz completion; that is the next step.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three

noncomputable local instance axisFintypePhysicalGradient244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpacePhysicalGradient244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

local instance physicalGradientFact2244 : Fact (1 ≤ (2 : ENNReal)) :=
  ⟨by norm_num⟩

private abbrev physicalGradientThirdJet244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) (j a b c : A3) : Point3 → ℝ :=
  spatial3.d a (spatial3.d b (spatial3.d c
    (loggedVelocityComponent u t j)))

private abbrev physicalGradientFirstJet244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) (j a : A3) : Point3 → ℝ :=
  spatial3.d a (loggedVelocityComponent u t j)

/-- The original physical third-order derivative, not a Schwartz surrogate,
is an actual L² function at every ordered derivative slot. -/
theorem h3ActualPhysicalGradientThirdJet_memLp_two244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (j a b c : A3) :
    MemLp (physicalGradientThirdJet244 u t j a b c)
      (2 : ENNReal) (volume : Measure Point3) := by
  have h := velocityH3JetFieldAt_memLp2 hInt hMeas
    (h3JetSlot3 (h3ClassicalizationFinOfAxis j)
      (h3ClassicalizationFinOfAxis a)
      (h3ClassicalizationFinOfAxis b)
      (h3ClassicalizationFinOfAxis c))
  simpa only [physicalGradientThirdJet244, velocityH3JetFieldAt,
    h3JetSlot3, h3AxisOfFin3_h3ClassicalizationFinOfAxis] using h

/-- Physical first jets satisfy a uniform-in-space H³ spectral bound, not
just a representative almost-everywhere bound. -/
theorem h3ActualPhysicalGradientFirstJet_bound244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j a : A3) (x : Point3) :
    |physicalGradientFirstJet244 u t j a x| ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        ‖velocityH3SpectralScalarAt u t hInt hMeas hFourier
          (h3ClassicalizationFinOfAxis j)‖ := by
  have hPhysical :=
    h3SpectralScalarRealC1RepresentativeOnPoint3_velocityH3SpectralScalarAt_eq_loggedVelocityComponent
      hNS ht hFourier (h3ClassicalizationFinOfAxis j)
  have hBound :=
    norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_apply_le
      (velocityH3SpectralScalarAt u t hInt hMeas hFourier
        (h3ClassicalizationFinOfAxis j))
      (h3ClassicalizationFinOfAxis a) x
  rw [hPhysical] at hBound
  simpa only [physicalGradientFirstJet244,
    h3AxisOfFin3_h3ClassicalizationFinOfAxis, Real.norm_eq_abs] using hBound

/-- The original physical first jet is measurable and lies in L∞ with an
explicit Sobolev bound. Its measurability comes from the old H³ jet data;
the spectral representative supplies the uniform bound. -/
theorem h3ActualPhysicalGradientFirstJet_memLp_top244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j a : A3) :
    MemLp (physicalGradientFirstJet244 u t j a)
      (∞ : ENNReal) (volume : Measure Point3) := by
  have hMeasFirst : AEStronglyMeasurable
      (physicalGradientFirstJet244 u t j a)
      (volume : Measure Point3) := by
    exact (hMeas j).2.1 a
  apply memLp_top_of_bound hMeasFirst
    (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      ‖velocityH3SpectralScalarAt u t hInt hMeas hFourier
        (h3ClassicalizationFinOfAxis j)‖)
  filter_upwards with x
  simpa only [Real.norm_eq_abs] using
    h3ActualPhysicalGradientFirstJet_bound244
      hNS ht hFourier j a x

/-- Fundamental physical gradient triple: L²×L²×L∞ is L¹. This works
for any two distinct third derivative slots and any first derivative slot,
including all four genuine gradient-commutator orientations. -/
theorem h3ActualPhysicalGradientTriple_integrable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j p q a b c d e f r : A3) :
    Integrable (fun x : Point3 =>
      physicalGradientThirdJet244 u t j a b c x *
      (physicalGradientThirdJet244 u t p d e f x *
        physicalGradientFirstJet244 u t q r x))
      (volume : Measure Point3) := by
  let A : Point3 → ℝ := physicalGradientThirdJet244 u t j a b c
  let B : Point3 → ℝ := physicalGradientThirdJet244 u t p d e f
  let C : Point3 → ℝ := physicalGradientFirstJet244 u t q r
  have hA : MemLp A (2 : ENNReal) (volume : Measure Point3) :=
    h3ActualPhysicalGradientThirdJet_memLp_two244 hInt hMeas j a b c
  have hB : MemLp B (2 : ENNReal) (volume : Measure Point3) :=
    h3ActualPhysicalGradientThirdJet_memLp_two244 hInt hMeas p d e f
  have hAB : Integrable (fun x : Point3 => A x * B x)
      (volume : Measure Point3) := by
    exact hA.integrable_mul hB
  have hCMeas : AEStronglyMeasurable C
      (volume : Measure Point3) := (hMeas q).2.1 r
  have hCBound : ∀ᵐ x ∂(volume : Measure Point3),
      ‖C x‖ ≤
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          ‖velocityH3SpectralScalarAt u t hInt hMeas hFourier
            (h3ClassicalizationFinOfAxis q)‖ := by
    filter_upwards with x
    simpa only [C, Real.norm_eq_abs] using
      h3ActualPhysicalGradientFirstJet_bound244
        hNS ht hFourier q r x
  have hABC : Integrable (fun x : Point3 => (A x * B x) * C x)
      (volume : Measure Point3) :=
    hAB.mul_bdd hCMeas hCBound
  simpa only [mul_assoc] using hABC

/-- Every OLD physical gradient-axis density is integrable from genuine H³
L² jets and the physical H³→C¹ bound. This discharges the axis-integrability
contract without requiring the physical velocity to be Schwartz. -/
theorem h3ActualPhysicalGradientAxesIntegrable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    H3RealSchwartzGradientAxesIntegrable244 u t := by
  intro j i k l r
  let A := physicalGradientThirdJet244 u t j i k l
  let G₁ := physicalGradientThirdJet244 u t r i k l
  let H₁ := physicalGradientFirstJet244 u t j r
  let G₂ := physicalGradientThirdJet244 u t j i k r
  let H₂ := physicalGradientFirstJet244 u t r l
  let G₃ := physicalGradientThirdJet244 u t j i r l
  let H₃ := physicalGradientFirstJet244 u t r k
  let G₄ := physicalGradientThirdJet244 u t j r k l
  let H₄ := physicalGradientFirstJet244 u t r i
  have h₁ : Integrable (fun x : Point3 => A x * (G₁ x * H₁ x)) :=
    h3ActualPhysicalGradientTriple_integrable244 hNS ht hFourier
      j r j i k l i k l r
  have h₂ : Integrable (fun x : Point3 => A x * (G₂ x * H₂ x)) :=
    h3ActualPhysicalGradientTriple_integrable244 hNS ht hFourier
      j j r i k l i k r l
  have h₃ : Integrable (fun x : Point3 => A x * (G₃ x * H₃ x)) :=
    h3ActualPhysicalGradientTriple_integrable244 hNS ht hFourier
      j j r i k l i r l k
  have h₄ : Integrable (fun x : Point3 => A x * (G₄ x * H₄ x)) :=
    h3ActualPhysicalGradientTriple_integrable244 hNS ht hFourier
      j j r i k l r k l i
  have hCombined : Integrable (fun x : Point3 =>
      A x * (G₁ x * H₁ x + (G₂ x * H₂ x +
        (G₃ x * H₃ x + G₄ x * H₄ x)))) := by
    have hEq : (fun x : Point3 =>
        A x * (G₁ x * H₁ x + (G₂ x * H₂ x +
          (G₃ x * H₃ x + G₄ x * H₄ x)))) =
        (fun x : Point3 => A x * (G₁ x * H₁ x)) +
          ((fun x : Point3 => A x * (G₂ x * H₂ x)) +
            ((fun x : Point3 => A x * (G₃ x * H₃ x)) +
              (fun x : Point3 => A x * (G₄ x * H₄ x)))) := by
      funext x
      simp only [Pi.add_apply]
      ring
    rw [hEq]
    exact h₁.add (h₂.add (h₃.add h₄))
  have hComponent (q : A3) :
      (fun x : Point3 =>
        (PrimeTensor.Bridge.logSpaceTimeVectorField u t x).component q) =
      loggedVelocityComponent u t q := rfl
  have hEqDensity :
      (fun x : Point3 =>
        (spatial3.d i (spatial3.d k (spatial3.d l
          (loggedVelocityComponent u t j)))) x *
        (thirdTransportCommutatorAxisGradientBlock
          (PrimeTensor.Bridge.logSpaceTimeVectorField u) t i k l j r) x) =
      (fun x : Point3 => A x *
        (G₁ x * H₁ x + (G₂ x * H₂ x +
          (G₃ x * H₃ x + G₄ x * H₄ x)))) := by
    funext x
    dsimp only [A, G₁, H₁, G₂, H₂, G₃, H₃, G₄, H₄,
      physicalGradientThirdJet244, physicalGradientFirstJet244]
    simp only [thirdTransportCommutatorAxisGradientBlock]
    rw [hComponent j, hComponent r]
    ring
  rw [hEqDensity]
  exact hCombined

/-- With the signed 243-slot identification proved, the discrepancy of
physical top H³ transport from its weighted canonical completion is exactly
the OLD physical gradient discrepancy. No further signed term remains. -/
theorem h3PhysicalFullThird_discrepancy_eq_gradientOnly244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3TransportDerivative3At u t -
        h3PhysicalSnapshotCanonicalFullThird244 u t hFourier =
      thirdOrderGradientTransportSum u t -
        weightedH3CanonicalGradientTransport244
          (velocityH3SpectralStateAt u t hInt hMeas hFourier) := by
  rw [physicalFullThird_minus_canonical_eq_gradient_and_signed_gaps244
    hH3 hClass ht hFourier,
    h3PathCanonical_signedGap_eq_zero244 hFourier]
  ring

/-- The remaining PDE-facing full-third identity is equivalent to the one
precise 3–3–1 gradient identification. -/
theorem h3PhysicalFullThird_eq_canonical_iff_gradient_eq244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    velocityH3TransportDerivative3At u t =
        h3PhysicalSnapshotCanonicalFullThird244 u t hFourier ↔
      thirdOrderGradientTransportSum u t =
        weightedH3CanonicalGradientTransport244
          (velocityH3SpectralStateAt u t hInt hMeas hFourier) := by
  have h := h3PhysicalFullThird_discrepancy_eq_gradientOnly244
    hH3 hClass ht hFourier
  constructor
  · intro heq
    rw [heq, sub_self] at h
    exact sub_eq_zero.mp h.symm
  · intro heq
    rw [heq, sub_self] at h
    exact sub_eq_zero.mp h

end
end PrimeTensor.FirstMonomialTriad
