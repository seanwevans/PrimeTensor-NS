import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralRadialMassEscape244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialRightKineticTraceReduction
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialPhysicalZeroJetL2
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.L2.Cauchy.Frontier
import Mathlib.Tactic

/-!
# The actual physical kinetic ceiling removes the raw-Fourier hypothesis

The previous radial-carrier theorem used an explicitly assumed uniform bound
on the zero-comparison raw Fourier square defect.  That bound is already a
consequence of the actual physical kinetic energy on *any fixed later subtail*.

At each strict time, Plancherel identifies the three raw Fourier scalar
coordinates with the Fourier transforms of the actual physical zero-order
velocity jets, while the physical PiLp norm-square is precisely E₀(t).
Therefore:

  RawSquare(S(t), 0) = E₀(t).

The already-closed physical kinetic monotonicity makes E₀(t) no larger
than E₀(b) whenever a < b < t < T.  The radial Sobolev-weight ceiling
then gives, for each fixed rho >= 0,

  LowSquare_rho(S(t)) <= K(rho) E₀(b),
  K(rho) = 1 + rho² + rho⁴ + rho⁶.

A fixed-coordinate spectral escape therefore yields cofinal unboundedness of
the algebraic complementary radial square mass *without any additional raw
Fourier ceiling assumption*.  For any requested terminal threshold c, choose
an earlier anchor b between a and c. Thus the endpoint assertion holds on
every strict subtail of (a,T).

This module does not infer failure of the physical L² terminal trace from
smooth nonextension.  Nor does it identify the algebraic complementary mass
with an integral on the complementary Fourier region: that measure-theoretic
normalization remains a separate obligation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The raw Fourier square mass of the *actual* strict-time velocity is
exactly its physical zeroth-order kinetic energy.  This uses physical
Plancherel, not an H³ norm estimate. -/
theorem h3Path_actualRawFourierSquareMass_eq_kinetic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3TerminalRawVelocityFourierTotalSquareDefect
        (h3AuditActualSpectralVelocityTotal hH3 t) 0 =
      velocityH3Energy0At u t := by
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  have hRaw (j : Fin 3) :
      h3TerminalRawVelocityFourierComponent G j =
        h3ScalarFourierL2 (U j) := by
    dsimp only [G, U]
    change h3SpectralScalarRawFourierL2
        (h3AuditActualSpectralVelocityTotal hH3 t j) =
      h3ScalarFourierL2
        (h3AuditActualPhysicalZeroJetL2Total hH3 j t)
    exact h3Audit_actualRawFourier_eq_fourierPhysicalZeroJetL2
      hH3 j t ht
  have hZero (j : Fin 3) :
      h3TerminalRawVelocityFourierComponent
          (0 : H3SpectralVelocityState) j = 0 := by
    change h3SpectralScalarRawFourierL2
        (0 : H3SpectralScalarState) = 0
    simp
  have hRawSquare :
      h3TerminalRawVelocityFourierTotalSquareDefect G 0 =
        ∑ j : Fin 3, ‖U j‖ ^ 2 := by
    rw [h3TerminalRawVelocityFourierTotalSquareDefect_eq_coordinate_norm_squares]
    rw [hRaw 0, hRaw 1, hRaw 2,
      hZero 0, hZero 1, hZero 2]
    simp only [sub_zero, norm_h3ScalarFourierL2, Fin.sum_univ_three]
  calc
    h3TerminalRawVelocityFourierTotalSquareDefect
        (h3AuditActualSpectralVelocityTotal hH3 t) 0 =
      ∑ j : Fin 3, ‖U j‖ ^ 2 := hRawSquare
    _ = ‖U‖ ^ 2 :=
      (PiLp.norm_sq_eq_of_L2
        (fun _ : Fin 3 => H3ScalarL2) U).symm
    _ = velocityH3Energy0At u t :=
      h3Audit_initialOldPhysicalHilbert_norm_sq_eq_kineticEnergy hH3 t ht

/-- Actual order-zero kinetic monotonicity gives a uniform raw Fourier
square ceiling after every fixed positive-time anchor. -/
theorem h3Path_actualRawFourierSquareMass_le_kineticAnchor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T) :
    ∀ r : ℝ, r ∈ Set.Ioo b T →
      h3TerminalRawVelocityFourierTotalSquareDefect
          (h3AuditActualSpectralVelocityTotal hH3 r) 0 ≤
        velocityH3Energy0At u b := by
  have hAnti :
      AntitoneOn (velocityH3Energy0At u) (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3 hClass
  intro r hr
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hr.1, hr.2⟩
  have hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hrClass.1, hrClass.2⟩
  rw [h3Path_actualRawFourierSquareMass_eq_kinetic244 hH3 r hrAbs]
  exact hAnti hb hrClass (le_of_lt hr.1)

/-- A genuine physical kinetic anchor supplies the fixed-radial weighted
H³ carrier ceiling. There is no arbitrary raw Fourier hypothesis. -/
theorem h3Path_actualSpectralLowRadialSquareMass_le_kineticAnchor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ r : ℝ, r ∈ Set.Ioo b T →
      h3PathActualSpectralLowRadialSquareMass244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 r) ≤
        h3TerminalRadialSobolevWeightSquareCeiling ρ *
          velocityH3Energy0At u b := by
  exact h3Path_actualSpectralLowRadialSquareMass_ceiling244
    (a := b) (T := T)
    (h3AuditActualSpectralVelocityTotal hH3)
    ρ (velocityH3Energy0At u b) hρ
    (h3Path_actualRawFourierSquareMass_le_kineticAnchor244
      hH3 hClass b hb)

/-- After removing the extra raw-ceiling assumption, failure of the strong
physical L² terminal trace forces cofinal high-radial *algebraic* remainder
escape outside any fixed radial carrier. -/
theorem h3Path_physicalNoL2Trace_forces_highRadialRemainder_kinetic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ c : ℝ, c ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo c T ∧
        M < h3PathActualSpectralHighRadialRemainder244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 r) := by
  obtain ⟨j, hj⟩ :=
    h3Path_physicalNoL2Trace_forces_fixedSpectralCoordinateEscape244
      hH3 hClass hL hNoTrace
  intro c hc M
  obtain ⟨b, hab, hbc⟩ := exists_between hc.1
  have hb : b ∈ Set.Ioo a T :=
    ⟨hab, lt_trans hbc hc.2⟩
  have hLow := h3Path_actualSpectralLowRadialSquareMass_le_kineticAnchor244
    hH3 hClass b hb ρ hρ
  have hFixed :
      ∃ i : Fin 3,
        ∀ d : ℝ, d ∈ Set.Ioo b T → ∀ N : ℝ,
          ∃ s : ℝ, s ∈ Set.Ioo d T ∧
            N < ‖(h3AuditActualSpectralVelocityTotal hH3 s) i‖ := by
    refine ⟨j, ?_⟩
    intro d hd N
    exact hj d ⟨lt_trans hb.1 hd.1, hd.2⟩ N
  exact
    h3Path_fixedSpectralCoordinateEscape_forces_highRadialRemainder244
      (a := b) (T := T)
      (h3AuditActualSpectralVelocityTotal hH3)
      ρ
      (h3TerminalRadialSobolevWeightSquareCeiling ρ *
        velocityH3Energy0At u b)
      hLow hFixed c ⟨hbc, hc.2⟩ M

/-- Unconditional (within the H³ path and kinetic energy class) terminal
alternative: an exact-mass physical L² trace, or positive terminal kinetic
mass together with cofinal algebraic high-radial escape for **every** fixed
cutoff.  This does not equate H³ nonextension with physical L² trace failure. -/
theorem h3Path_physicalL2Trace_or_allHighRadialRemainderEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U) ∧
        ‖U‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T) ∨
      (0 < h3PathCanonicalTerminalKineticEnergyAt u a T ∧
        ∀ ρ : ℝ, 0 ≤ ρ →
          ∀ c : ℝ, c ∈ Set.Ioo a T → ∀ M : ℝ,
            ∃ r : ℝ, r ∈ Set.Ioo c T ∧
              M < h3PathActualSpectralHighRadialRemainder244 ρ
                (h3AuditActualSpectralVelocityTotal hH3 r)) := by
  by_cases hTrace :
      ∃ U : H3PhysicalRealFinVectorL2Hilbert,
        Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
          (𝓝[<] T) (𝓝 U)
  · obtain ⟨U, hU⟩ := hTrace
    exact Or.inl ⟨U, hU,
      h3Path_physicalVelocity_terminalTrace_norm_sq_eq_kineticLimit244
        hH3 hClass U hU⟩
  · have hL :
        0 < h3PathCanonicalTerminalKineticEnergyAt u a T := by
      rcases h3Path_physicalL2Trace_or_fixedSpectralCoordinateEscape_allKinetic244
          hH3 hClass with hStrong | hEscape
      · obtain ⟨U, hU, _⟩ := hStrong
        exact False.elim (hTrace ⟨U, hU⟩)
      · exact hEscape.1
    exact Or.inr ⟨hL, fun ρ hρ =>
      h3Path_physicalNoL2Trace_forces_highRadialRemainder_kinetic244
        hH3 hClass hL hTrace ρ hρ⟩

end
end PrimeTensor.FirstMonomialTriad
