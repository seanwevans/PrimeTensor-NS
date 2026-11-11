import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalSharpYoungGapRigidity
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticTransverseSource244
import Mathlib.Tactic

/-!
# Physical kinetic rejection of global anti-heat saturation

The accepted exact sharp Young remainder vanishes for nonlinear Fourier
forcing `f = -2*q*z`. The physical Navier--Stokes PDE would then assign the
momentum source `R = -q*z-f = q*z`, i.e. anti-diffusive alignment.

At an actual positive PDE time the whole-space kinetic balance proves
`inner U R = -D0`, and `norm U ^ 2 = E0`. Consequently for EVERY scalar
`lambda >= 0` the exact real-Hilbert identity is

  norm (R-lambda*U)^2 = norm R^2 + lambda^2*E0 + 2*lambda*D0.

This is not a generic complex pointwise Young inequality: it uses the
actual Navier--Stokes kinetic cancellation and the true physical momentum
source. In the positive terminal kinetic branch it supplies the UNIFORM
lower bound `lambda^2*terminalKineticMass` at every strict tail time.

The conclusion excludes exact GLOBAL alignment with a fixed positive
anti-diffusive scalar. It does NOT rule out q-dependent high-frequency
saturation on a small moving spectral set. Such a claim requires an
additional spectral localization/flux argument, not supplied here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000

/-- General real-Hilbert identity behind the physical kinetic obstruction.
It is exact and works even if the energy or dissipation is zero. -/
theorem thirdFullKinetic_antiHeatResidual_exactSquare244
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U R : H) (D rate : ℝ) (hrate : 0 ≤ rate)
    (hPair : inner ℝ U R = -D) :
    ‖R - rate • U‖ ^ 2 =
      ‖R‖ ^ 2 + rate ^ 2 * ‖U‖ ^ 2 + 2 * rate * D := by
  have hReverse : inner ℝ R U = -D := by
    rw [real_inner_comm]
    exact hPair
  have hScaled : ‖rate • U‖ ^ 2 = rate ^ 2 * ‖U‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hrate, mul_pow]
  calc
    ‖R - rate • U‖ ^ 2 =
        ‖R‖ ^ 2 - 2 * inner ℝ R (rate • U) + ‖rate • U‖ ^ 2 :=
      norm_sub_sq_real R (rate • U)
    _ = ‖R‖ ^ 2 + rate ^ 2 * ‖U‖ ^ 2 + 2 * rate * D := by
      rw [real_inner_smul_right, hReverse, hScaled]
      ring

/-- An anti-diffusive source must have a quantitatively nonzero residual
whenever the kinetic energy is nonzero. -/
theorem thirdFullKinetic_antiHeatResidual_lowerSquare244
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U R : H) (D rate : ℝ) (hD : 0 ≤ D) (hrate : 0 ≤ rate)
    (hPair : inner ℝ U R = -D) :
    rate ^ 2 * ‖U‖ ^ 2 + 2 * rate * D ≤ ‖R - rate • U‖ ^ 2 := by
  have hExact :=
    thirdFullKinetic_antiHeatResidual_exactSquare244 U R D rate hrate hPair
  have hNonneg : 0 ≤ ‖R‖ ^ 2 := sq_nonneg _
  linarith only [hExact, hNonneg]

/-- Exact physical source/velocity anti-heat square expansion. The sign
comes from the Navier--Stokes kinetic balance, NOT an axiom of orthogonality. -/
theorem thirdFullPhysical_antiHeatKinetic_exactSquare244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (rate : ℝ) (hrate : 0 ≤ rate) :
    ‖h3PathActualProjectedMomentumSource244 hH3 t -
        rate • h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2 =
      ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ^ 2 +
        rate ^ 2 * velocityH3Energy0At u t +
        2 * rate * velocityH3Dissipation0At u t := by
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  let R : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3 t
  let D : ℝ := velocityH3Dissipation0At u t
  have hPair : inner ℝ U R = -D :=
    h3Path_physicalHilbertPairing_eq_negDissipation0_positiveTime244 hH3 t ht
  have hKinetic : ‖U‖ ^ 2 = velocityH3Energy0At u t :=
    h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy hH3 t ht
  have hExact :=
    thirdFullKinetic_antiHeatResidual_exactSquare244 U R D rate hrate hPair
  calc
    ‖h3PathActualProjectedMomentumSource244 hH3 t -
        rate • h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2 =
      ‖R‖ ^ 2 + rate ^ 2 * ‖U‖ ^ 2 + 2 * rate * D := hExact
    _ = ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ^ 2 +
        rate ^ 2 * velocityH3Energy0At u t +
        2 * rate * velocityH3Dissipation0At u t := by
      rw [hKinetic]

/-- Actual physical H3 paths repel positive scalar anti-heat alignment.
The viscous kinetic dissipation contributes a further positive margin. -/
theorem thirdFullPhysical_antiHeatKinetic_coercivity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (rate : ℝ) (hrate : 0 ≤ rate) :
    rate ^ 2 * velocityH3Energy0At u t +
        2 * rate * velocityH3Dissipation0At u t ≤
      ‖h3PathActualProjectedMomentumSource244 hH3 t -
        rate • h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2 := by
  have hExact := thirdFullPhysical_antiHeatKinetic_exactSquare244
    hH3 t ht rate hrate
  have hR : 0 ≤
      ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ^ 2 := sq_nonneg _
  linarith only [hExact, hR]

/-- A positive terminal kinetic infimum turns the source anti-heat
separation into a uniform-in-time lower bound on the physical tail. -/
theorem thirdFullPhysical_antiHeatKinetic_terminalFloor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (rate : ℝ) (hrate : 0 ≤ rate) :
    rate ^ 2 * h3PathCanonicalTerminalKineticEnergyAt u a T ≤
      ‖h3PathActualProjectedMomentumSource244 hH3 t -
        rate • h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2 := by
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hEnergyFloor :
      h3PathCanonicalTerminalKineticEnergyAt u a T ≤
        velocityH3Energy0At u t :=
    h3PathCanonical_terminalKineticEnergy_le_anchor (u := u) ht
  have hLower := thirdFullPhysical_antiHeatKinetic_coercivity244
    hH3 t htAbs rate hrate
  have hD : 0 ≤ velocityH3Dissipation0At u t :=
    velocityH3Dissipation0At_nonneg u t
  have hScaled :=
    mul_le_mul_of_nonneg_left hEnergyFloor (sq_nonneg rate)
  have hCross : 0 ≤ 2 * rate * velocityH3Dissipation0At u t := by
    positivity
  linarith only [hScaled, hLower, hCross]

/-- If terminal kinetic mass is positive, NO actual strict physical
source can equal a positive scalar times its own velocity. -/
theorem thirdFullPhysical_antiHeatKinetic_noAlignment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTerminal : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (rate : ℝ) (hrate : 0 < rate) :
    h3PathActualProjectedMomentumSource244 hH3 t ≠
      rate • h3AuditInitialOldPhysicalHilbertTotal hH3 t := by
  intro hEq
  have hBound := thirdFullPhysical_antiHeatKinetic_terminalFloor244
    hH3 hClass t ht rate hrate.le
  rw [hEq, sub_self, norm_zero] at hBound
  have hPositive :
      0 < rate ^ 2 * h3PathCanonicalTerminalKineticEnergyAt u a T :=
    mul_pos (pow_pos hrate 2) hTerminal
  nlinarith only [hBound, hPositive]


/-- Two-error gate for localizing the anti-heat obstruction. If `A` is
chosen as a positive-frequency viscous multiplier on a shell, the first
error measures Young-gap saturation and the second measures failure of
that multiplier to be constant on the shell. No such spectral choice of
`A` is made or assumed in this theorem. -/
theorem thirdFullPhysical_antiHeatKinetic_twoErrorGate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (rate : ℝ) (hrate : 0 ≤ rate)
    (A : H3PhysicalRealFinVectorL2Hilbert) :
    rate ^ 2 * velocityH3Energy0At u t +
        2 * rate * velocityH3Dissipation0At u t ≤
      (‖A - h3PathActualProjectedMomentumSource244 hH3 t‖ +
       ‖A - rate • h3AuditInitialOldPhysicalHilbertTotal hH3 t‖) ^ 2 := by
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  let R : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3 t
  have hLower :
      rate ^ 2 * velocityH3Energy0At u t +
          2 * rate * velocityH3Dissipation0At u t ≤
        ‖R - rate • U‖ ^ 2 :=
    thirdFullPhysical_antiHeatKinetic_coercivity244 hH3 t ht rate hrate
  have hRearrange : R - rate • U = (R - A) + (A - rate • U) := by
    abel
  have hTri : ‖R - rate • U‖ ≤ ‖A - R‖ + ‖A - rate • U‖ := by
    calc
      ‖R - rate • U‖ = ‖(R - A) + (A - rate • U)‖ := by
        rw [hRearrange]
      _ ≤ ‖R - A‖ + ‖A - rate • U‖ := norm_add_le _ _
      _ = ‖A - R‖ + ‖A - rate • U‖ := by
        rw [norm_sub_rev R A]
  have hSquared :
      ‖R - rate • U‖ ^ 2 ≤ (‖A - R‖ + ‖A - rate • U‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hTri 2
  exact hLower.trans hSquared

end
end PrimeTensor.FirstMonomialTriad
