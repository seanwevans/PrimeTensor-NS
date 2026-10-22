import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopKineticL1EightMomentAlternative244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Bound.Forcing.Moment
import Mathlib.Tactic

/-!
# Inverse-Bessel reduction of the physical raw Fourier L¹ terminal branch

The exact three-dimensional Bessel weight (1+|ξ|²)⁻¹ in Fourier L² gives
    ‖û_j‖_{L¹} ≤ C_B (‖û_j‖_{L²} + ‖ |ξ|² û_j‖_{L²}).

The zeroth radial term is bounded by the physical kinetic anchor, without
any endpoint assumptions. Thus a uniform strict-tail second-radial Fourier
L² ceiling removes the last low-order alternative from the six-factor Young
corridor and forces cofinal order-eight velocity moments whenever physical
fourth-radial dissipation escapes.

The order-two representative is explicit: this module does not pretend that
kinetic L² alone controls Fourier L¹, nor does it infer an endpoint-uniform
second-radial norm from pointwise H³ smoothness.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section

-- Fourier three-space norm and product-volume instances require a finite axis.
noncomputable local instance axisFintypeH3PhysicalTopBesselSecondRadial244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/-- The exact inverse-Bessel p=0 estimate: one unweighted Fourier L²
representative and one radial-order-two L² representative control raw L¹.
The latter is a genuine, almost-everywhere Fourier representative. -/
theorem h3_rawFourierL1_le_bessel_rawL2_add_secondRadial244
    (F : H3SpectralScalarState)
    (G₂ : H3FourierComplexL2)
    (hG₂ :
      ((G₂ : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 2 : ℝ) : ℂ) * h3SpectralScalarRawFourier F ξ)) :
    h3SpectralScalarRawFourierL1Mass F ≤
      h3StandardInverseBesselWeightL2Factor *
        (‖h3SpectralScalarRawFourierL2 F‖ + ‖G₂‖) := by
  have hZero :
      (((h3SpectralScalarRawFourierL2 F : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ))
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 0 : ℝ) : ℂ) * h3SpectralScalarRawFourier F ξ) := by
    simpa only [pow_zero, Complex.ofReal_one, one_mul] using
      (h3SpectralScalarRawFourierL2_ae F)
  have hSecond :
      ((G₂ : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ (0 + 2) : ℝ) : ℂ) *
          h3SpectralScalarRawFourier F ξ) := by
    simpa only [zero_add] using hG₂
  have hBessel := integral_h3RawFourier_natMoment_le_bessel_mul_norms
    0 (h3SpectralScalarRawFourier F)
    (h3SpectralScalarRawFourierL2 F) G₂ hZero hSecond
  simpa [h3SpectralScalarRawFourierL1Mass] using hBessel

/-- At each later physical time, the zero-order term in the Bessel estimate
is bounded by the *anchored kinetic energy*, leaving only second radial L². -/
theorem h3Path_rawL1_le_kineticAnchor_add_secondRadial244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t) (j : Fin 3)
    (G₂ : H3FourierComplexL2)
    (hG₂ :
      let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
      let U : H3SpectralFinVectorState :=
        h3TerminalVelocitySpectralStateAt hH3 t htAbs
      ((G₂ : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
          h3SpectralScalarRawFourier (U j) ξ)) :
    h3PathVelocityRawFourierL1MassComponent244 hH3 hClass j t ≤
      h3StandardInverseBesselWeightL2Factor *
        (Real.sqrt (velocityH3Energy0At u s) + ‖G₂‖) := by
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  have hBessel := h3_rawFourierL1_le_bessel_rawL2_add_secondRadial244
    (U j) G₂ hG₂
  have hKinetic :
      ‖h3SpectralScalarRawFourierL2 (U j)‖ ≤
        Real.sqrt (velocityH3Energy0At u s) :=
    h3Path_rawVelocityFourierL2_le_sqrtKineticAnchor244
      hH3 hClass hs ht hst j
  have hC : 0 ≤ h3StandardInverseBesselWeightL2Factor :=
    h3StandardInverseBesselWeightL2Factor_nonneg
  calc
    h3PathVelocityRawFourierL1MassComponent244 hH3 hClass j t =
        h3SpectralScalarRawFourierL1Mass (U j) := by
      exact h3Path_velocityRawFourierL1MassComponent_eq244 hH3 hClass ht j
    _ ≤ h3StandardInverseBesselWeightL2Factor *
          (‖h3SpectralScalarRawFourierL2 (U j)‖ + ‖G₂‖) := hBessel
    _ ≤ h3StandardInverseBesselWeightL2Factor *
          (Real.sqrt (velocityH3Energy0At u s) + ‖G₂‖) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hKinetic _) hC

/-- An upper bound on the genuine order-two Fourier L² representatives,
combined with kinetic monotonicity, closes the residual raw L¹ premise
and forces *actual* order-eight velocity moment escape on every terminal subtail. -/
theorem h3Path_unboundedPhysicalTop_forces_eightMoment_of_secondRadialL2Ceiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t)
    (hMom : ∀ t (ht : t ∈ Set.Ioo a T),
      h3PathVelocityRawEightMomentsAt244 hH3 hClass ht)
    (hSecond : ∀ t (ht : t ∈ Set.Ioo a T), s < t →
      ∀ j : Fin 3, ∃ G₂ : H3FourierComplexL2,
        (let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
          ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
         let U : H3SpectralFinVectorState :=
          h3TerminalVelocitySpectralStateAt hH3 t htAbs
         ((G₂ : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
            =ᵐ[(volume : Measure H3FourierPoint3)]
         (fun ξ : H3FourierPoint3 =>
           ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
             h3SpectralScalarRawFourier (U j) ξ)) ∧
        ‖G₂‖ ≤ B) :
    ∀ σ, σ ∈ Set.Ioo s T → ∀ K : ℝ,
      ∃ r, r ∈ Set.Ioo σ T ∧ ∃ j : Fin 3,
        K < h3PathVelocityRawEightMomentComponent244 hH3 hClass j r := by
  apply h3Path_unboundedPhysicalTop_forces_eightMoment_of_rawFourierL1Ceiling244
    (B := h3StandardInverseBesselWeightL2Factor *
      (Real.sqrt (velocityH3Energy0At u s) + B))
    hH3 hClass hs hEscape hMom
  intro t ht hst j
  obtain ⟨G₂, hRep, hNorm⟩ := hSecond t ht hst j
  have hPoint := h3Path_rawL1_le_kineticAnchor_add_secondRadial244
    hH3 hClass hs ht hst.le j G₂ hRep
  have hC : 0 ≤ h3StandardInverseBesselWeightL2Factor :=
    h3StandardInverseBesselWeightL2Factor_nonneg
  have hUpper := mul_le_mul_of_nonneg_left
    (add_le_add_right hNorm (Real.sqrt (velocityH3Energy0At u s))) hC
  have hL1 : h3PathVelocityRawFourierL1MassComponent244 hH3 hClass j t ≤
      h3StandardInverseBesselWeightL2Factor *
        (Real.sqrt (velocityH3Energy0At u s) + B) :=
    hPoint.trans hUpper
  simpa only [h3Path_velocityRawFourierL1MassComponent_eq244
    hH3 hClass ht j] using hL1

end
end PrimeTensor.FirstMonomialTriad
