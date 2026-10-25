import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralHighEnergyRadialSynchronization244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedTopInterpolationFrontier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedTopYoungAbsorption
import Mathlib.Tactic

/-!
# The two signed H³ cubic channels synchronize with moving radial dissipation

Under failure of the physical kinetic terminal trace, the fixed cofinal
channel alternative includes negative canonical gradient and interpolation
channels. Cofinality of their separate witnesses alone would not imply
intersection with independently selected radial-frequency witnesses.

Here the physical Landau estimates furnish a genuinely pointwise bridge:

  |G₃| <= 24 C₁ sqrt(E) E,   |3 M₃| <= 4422 C₁ sqrt(E) E.

We obtain the second inequality by subtracting the first signed gradient
from the complete third transport, whose established bound is 4398.
Thus an arbitrarily large negative normalized cubic forces arbitrarily
large H³ energy AT THE SAME TIME. Before selecting a terminal witness,
we amplify the requested negative cubic threshold sufficiently to pay
for the fixed kinetic-anchor radial low-frequency ceiling. This yields
high radial concentration and the physical cubic dissipation clock on
one common witness for EITHER signed cubic channel. The fast-decay branch
remains separate. No two unrelated cofinal sets are intersected.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The physical top-energy block is dominated by the full H³ energy. -/
theorem h3Path_topEnergy_le_fullEnergy_signedRadial244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    velocityH3Energy3At u t ≤ velocityH3EnergyAt u t := by
  have h0 := velocityH3Energy0At_nonneg u t
  have h1 := velocityH3Energy1At_nonneg u t
  have h2 := velocityH3Energy2At_nonneg u t
  unfold velocityH3EnergyAt
  linarith only [h0, h1, h2]

/-- The exact physical/spectral gradient identity needs no Schwartz
realization assumption beyond the actual admissible H³ Fourier state. -/
theorem h3Path_weightedGradient_eq_physical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    weightedH3CanonicalGradientTransport244
        (h3PathWeightedSpectralState244 u T hH3 t) =
      thirdOrderGradientTransportSum u t := by
  have htNS : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htNS
  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htNS
  let hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htNS hInt
  have hPhysical := h3PhysicalGradient_eq_weightedCanonical244
    hH3.navier_stokes htNS hFourier
  rw [← h3PathWeightedSpectralState_eq_actual244 hH3 htNS hFourier]
    at hPhysical
  exact hPhysical.symm

/-- The canonical gradient itself inherits the *24* Landau coefficient
from the actual old physical H³ pairing, with E₃ <= full E. -/
theorem h3Path_weightedGradient_abs_le_sqrtFullEnergy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    |weightedH3CanonicalGradientTransport244
      (h3PathWeightedSpectralState244 u T hH3 t)| ≤
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t := by
  rw [h3Path_weightedGradient_eq_physical244 hH3 hClass ht]
  have hBound := h3PathCanonical_abs_gradientTransport_le_topEnergy
    hH3 hClass ht
  have hE3 := h3Path_topEnergy_le_fullEnergy_signedRadial244 u t
  have hCoeff : 0 ≤
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) := by
    exact mul_nonneg (by norm_num) (mul_nonneg
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _))
  exact hBound.trans (mul_le_mul_of_nonneg_left hE3 hCoeff)

/-- The exact interpolation part is the remainder after subtracting the
physical gradient from the complete physical top transport. -/
theorem h3Path_weightedInterpolation_eq_physical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    3 * weightedH3CanonicalSignedFirstMonomial244
        (h3PathWeightedSpectralState244 u T hH3 t) =
      thirdOrderInterpolationTransportSum u t := by
  have hFull := h3Path_weightedFullThird_eq_physical244
    hH3 hClass ht
  have hGradient := h3Path_weightedGradient_eq_physical244
    hH3 hClass ht
  have hSplit := h3PathCanonical_thirdTransport_eq_gradient_add_interpolation
    hH3 hClass ht
  unfold weightedH3CanonicalFullThirdCommutator244 at hFull
  rw [hGradient] at hFull
  linarith only [hFull, hSplit]

/-- The signed 243-slot canonical interpolation channel obeys an explicit
4422 coefficient: 4398 from full transport plus 24 from the gradient.
This is a pointwise absolute bound, not a favorable sign estimate. -/
theorem h3Path_weightedInterpolation_abs_le_sqrtFullEnergy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    |3 * weightedH3CanonicalSignedFirstMonomial244
      (h3PathWeightedSpectralState244 u T hH3 t)| ≤
      4422 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t := by
  rw [h3Path_weightedInterpolation_eq_physical244 hH3 hClass ht]
  have hSplit := h3PathCanonical_thirdTransport_eq_gradient_add_interpolation
    hH3 hClass ht
  have hTotal := h3PathCanonical_abs_thirdTransport_le_kineticGradientTopEnergy
    hH3 hClass ht
  have hGradient := h3PathCanonical_abs_gradientTransport_le_topEnergy
    hH3 hClass ht
  have hTriangle :
      |thirdOrderInterpolationTransportSum u t| ≤
        |velocityH3TransportDerivative3At u t| +
          |thirdOrderGradientTransportSum u t| := by
    have hEq : thirdOrderInterpolationTransportSum u t =
        velocityH3TransportDerivative3At u t -
          thirdOrderGradientTransportSum u t := by
      linarith only [hSplit]
    rw [hEq]
    simpa only [sub_eq_add_neg, abs_neg] using
      (abs_add_le (velocityH3TransportDerivative3At u t)
        (-thirdOrderGradientTransportSum u t))
  have hTop : velocityH3Energy3At u t ≤ velocityH3EnergyAt u t :=
    h3Path_topEnergy_le_fullEnergy_signedRadial244 u t
  have hCoeff : 0 ≤ 4422 *
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) := by
    exact mul_nonneg (by norm_num) (mul_nonneg
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _))
  calc
    |thirdOrderInterpolationTransportSum u t| ≤
        |velocityH3TransportDerivative3At u t| +
          |thirdOrderGradientTransportSum u t| := hTriangle
    _ ≤ (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) * velocityH3Energy3At u t +
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t :=
      add_le_add hTotal hGradient
    _ = 4422 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t := by ring
    _ ≤ 4422 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t :=
      mul_le_mul_of_nonneg_left hTop hCoeff

/-- Negative normalized cubic forcing cannot remain extreme with small
physical H³ energy. The factor 400 clears the worst 4422 coefficient and
the target 48 coefficient of the high-energy radial request. -/
theorem h3Path_largeNegativeCubic_forces_radialEnergyRequest244
    (E C S Q : ℝ)
    (hE : 0 < E) (hC : 0 ≤ C)
    (hBound : |S| ≤ 4422 * C * E)
    (hNegative : (400 * Q) * E < -(4 * S)) :
    Q ≤ 48 * C := by
  have hNegAbs : -S ≤ |S| := neg_le_abs S
  have hUpper : -(4 * S) ≤ (17688 * C) * E := by
    nlinarith only [hNegAbs, hBound]
  by_contra hNot
  have hQ : 48 * C < Q := lt_of_not_ge hNot
  have hScaled := mul_lt_mul_of_pos_right hQ hE
  have hCE : 0 ≤ C * E := mul_nonneg hC hE.le
  nlinarith only [hUpper, hNegative, hScaled, hCE]

/-- The physical, kinetically anchored radial request is nonnegative for
nonnegative cutoffs. -/
theorem h3Path_highEnergyRadialRequest_nonneg_signed244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b R : ℝ) (hR : 0 ≤ R) :
    0 ≤ h3PathHighEnergyRadialRequest244 u b R := by
  unfold h3PathHighEnergyRadialRequest244
  have hC : 0 ≤ h3TerminalRadialSobolevWeightSquareCeiling R *
      velocityH3Energy0At u b :=
    mul_nonneg (h3TerminalRadialSobolevWeightSquareCeiling_pos R).le
      (velocityH3Energy0At_nonneg u b)
  exact mul_nonneg (mul_nonneg (by norm_num)
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg)
    (by nlinarith only [hR, hC])

/-- Abstract fixed negative-cubic channel with an actual physical Landau
bound: select at each frequency cutoff a single time carrying BOTH the
negative signed cubic and the moving radial H³ concentration/dissipation
clock. There is no intersection of separately extracted sequences. -/
theorem h3Path_cofinalNegativeCubic_forces_jointRadialSequence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (S : ℝ → ℝ)
    (hBound : ∀ t : ℝ, t ∈ Set.Ioo a T →
      |S t| ≤ 4422 *
        (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t)
    (hNegative : ∀ c : ℝ, c ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        4 * S t < -(B * velocityH3EnergyAt u t)) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ, 4 * S (τ n) <
        -(((n : ℝ) + 1) * velocityH3EnergyAt u (τ n))) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 2) *
          h3PathActualSpectralHighRadialRemainder244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) >
          ((n : ℝ) + 1) * h3SpectralVelocitySquareEnergy
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) ^ 3 * velocityH3EnergyAt u (τ n) <
          ((n : ℝ) + 3) * velocityH3DissipationAt u (τ n)) := by
  let b : ℝ := (a + T) / 2
  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    constructor <;> linarith only [hClass.terminal_start.2]
  have hSelected : ∀ c : ℝ, c ∈ Set.Ioo b T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        4 * S t < -(B * velocityH3EnergyAt u t) ∧
        h3PathHighEnergyRadialRequest244 u b B ≤
          48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t) := by
    intro c hc B hB
    let Q : ℝ := h3PathHighEnergyRadialRequest244 u b B
    have hQ : 0 ≤ Q :=
      h3Path_highEnergyRadialRequest_nonneg_signed244 u b B hB
    let M : ℝ := 400 * (Q + B + 1)
    have hM : 0 ≤ M := by
      dsimp only [M]
      nlinarith only [hQ, hB]
    have hcClass : c ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 hc.1, hc.2⟩
    obtain ⟨t, ht, hBad⟩ := hNegative c hcClass M hM
    have htClass : t ∈ Set.Ioo a T :=
      ⟨lt_trans hcClass.1 ht.1, ht.2⟩
    let E : ℝ := velocityH3EnergyAt u t
    have hE : 0 < E := by
      dsimp only [E]
      exact lt_of_lt_of_le (by norm_num) (one_le_velocityH3EnergyAt u t)
    have hBM : B ≤ M := by
      dsimp only [M]
      nlinarith only [hQ, hB]
    have hQM : 400 * Q ≤ M := by
      dsimp only [M]
      nlinarith only [hQ, hB]
    have hBad' : M * E < -(4 * S t) := by
      dsimp only [E] at hBad ⊢
      linarith only [hBad]
    have hSignedB : B * E < -(4 * S t) :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hBM hE.le) hBad'
    have hSignedQ : (400 * Q) * E < -(4 * S t) :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hQM hE.le) hBad'
    have hC : 0 ≤ h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt E :=
      mul_nonneg h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
        (Real.sqrt_nonneg E)
    have hReq : Q ≤ 48 *
        (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt E) :=
      h3Path_largeNegativeCubic_forces_radialEnergyRequest244
        E _ (S t) Q hE hC (hBound t htClass) hSignedQ
    refine ⟨t, ht, ?_, ?_⟩
    · dsimp only [E] at hSignedB
      linarith only [hSignedB]
    · dsimp only [Q, E] at hReq
      convert hReq using 1 <;> ring
  obtain ⟨τ, hτ, hNear, hLimit, hPair⟩ :=
    h3Path_cofinalThreshold_diagonalPredicate244 hb.2
      (fun t B => 4 * S t < -(B * velocityH3EnergyAt u t) ∧
        h3PathHighEnergyRadialRequest244 u b B ≤
          48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t)) hSelected
  have hJoint (n : ℕ) :=
    h3Path_highEnergyRequest_forces_jointRadialClock244
      hH3 hClass b hb (τ n) (hτ n) n (hPair n).2
  exact ⟨τ, (fun n => ⟨lt_trans hb.1 (hτ n).1, (hτ n).2⟩),
    hNear, hLimit, (fun n => (hPair n).1),
    (fun n => (hJoint n).1), (fun n => (hJoint n).2)⟩

/-- A fixed cofinal negative canonical GRADIENT channel has a single
moving-radial physical witness with simultaneous signed negativity,
high-frequency dominance, and the physical cubic dissipation clock. -/
theorem h3Path_cofinalNegativeGradient_forces_jointRadialSequence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hGradient : ∀ c : ℝ, c ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        4 * weightedH3CanonicalGradientTransport244
          (h3PathWeightedSpectralState244 u T hH3 t) <
          -(B * velocityH3EnergyAt u t)) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        4 * weightedH3CanonicalGradientTransport244
          (h3PathWeightedSpectralState244 u T hH3 (τ n)) <
          -(((n : ℝ) + 1) * velocityH3EnergyAt u (τ n))) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 2) *
          h3PathActualSpectralHighRadialRemainder244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) >
          ((n : ℝ) + 1) * h3SpectralVelocitySquareEnergy
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) ^ 3 * velocityH3EnergyAt u (τ n) <
          ((n : ℝ) + 3) * velocityH3DissipationAt u (τ n)) := by
  apply h3Path_cofinalNegativeCubic_forces_jointRadialSequence244
    hH3 hClass (fun t => weightedH3CanonicalGradientTransport244
      (h3PathWeightedSpectralState244 u T hH3 t))
  · intro t ht
    have hGrad := h3Path_weightedGradient_abs_le_sqrtFullEnergy244
      hH3 hClass ht
    have hNonneg : 0 ≤
        (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t :=
      mul_nonneg
        (mul_nonneg h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
          (Real.sqrt_nonneg _))
        (le_trans zero_le_one (one_le_velocityH3EnergyAt u t))
    have hWiden : 24 *
        (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t ≤
        4422 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t := by
      nlinarith only [hNonneg]
    exact hGrad.trans hWiden
  · exact hGradient

/-- The same synchronization holds for a fixed cofinal negative signed
243-slot INTERPOLATION channel, with the proved factor three retained. -/
theorem h3Path_cofinalNegativeInterpolation_forces_jointRadialSequence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hInterpolation : ∀ c : ℝ, c ∈ Set.Ioo a T → ∀ B : ℝ, 0 ≤ B →
      ∃ t : ℝ, t ∈ Set.Ioo c T ∧
        4 * (3 * weightedH3CanonicalSignedFirstMonomial244
          (h3PathWeightedSpectralState244 u T hH3 t)) <
          -(B * velocityH3EnergyAt u t)) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        4 * (3 * weightedH3CanonicalSignedFirstMonomial244
          (h3PathWeightedSpectralState244 u T hH3 (τ n))) <
          -(((n : ℝ) + 1) * velocityH3EnergyAt u (τ n))) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 2) *
          h3PathActualSpectralHighRadialRemainder244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) >
          ((n : ℝ) + 1) * h3SpectralVelocitySquareEnergy
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) ^ 3 * velocityH3EnergyAt u (τ n) <
          ((n : ℝ) + 3) * velocityH3DissipationAt u (τ n)) := by
  apply h3Path_cofinalNegativeCubic_forces_jointRadialSequence244
    hH3 hClass (fun t => 3 * weightedH3CanonicalSignedFirstMonomial244
      (h3PathWeightedSpectralState244 u T hH3 t))
  · intro t ht
    exact h3Path_weightedInterpolation_abs_le_sqrtFullEnergy244 hH3 hClass ht
  · exact hInterpolation

end
end PrimeTensor.FirstMonomialTriad
