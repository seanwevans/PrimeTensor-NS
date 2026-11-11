import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalHighpassFifthPhaseBalance
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalDyadicSharpFourierHighpass
import Mathlib.Tactic

/-!
# Physical highpass Hilbert cubic: exact Fourier mass and critical fifth/phase charge

The previous highband density inequality concerned the true scalar Leray
source, with density q(ξ)^3 |N_j(ξ)|². The physical third-radial forcing
Hilbert state uses |ξ|^3 N_j(ξ), not q(ξ)^(3/2) N_j(ξ). Hence the exact
normalization is (2π)^6 times the Hilbert square norm.

This module proves that normalization on the SHARP complementary frequency
region and transfers the derivative-free signed phase/fifth moment inequality
to the actual physical highpass Hilbert budget. Finally the established
critical dyadic witness carries the same physical fifth/phase high-frequency
necessity for every subsequently selected radius.

This does not claim that either high fifth moment or phase mismatch is
uniformly controlled on terminal tails. The kinetic low-band budget grows
with the cutoff: sending the radius to infinity does not close the estimate.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeCriticalHighPhasePhysical244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceCriticalHighPhasePhysical244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- EXACT physical highpass cubic forcing norm-square identity. The factor
(2π)^6 is forced by the project's convention q=(2π)^2 |ξ|²; it is not
an adjustable inequality constant. The time is a genuine strict PDE time. -/
theorem thirdFullPhysical_highpassThirdHilbert_eq_actualCubicBand244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (ρ : ℝ) (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralVelocityState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    (2 * Real.pi) ^ 6 *
        ‖thirdFullPhysicalCriticalThirdForcingHighpass244
          hH3 hClass ρ j t‖ ^ 2 =
      ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
        h3FourierGradientSquare ξ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergence U U j ξ‖ ^ 2 ∂volume := by
  dsimp only
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let F : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
      hH3 hClass j t
  have hRep :
      (F : H3FourierPoint3 → ℂ) =ᵐ[(volume : Measure H3FourierPoint3)]
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 3 : ℝ) : ℂ) *
            h3RawFinLerayOuterProductDivergence U U j ξ) := by
    dsimp only [F]
    rw [h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path_eq
      hH3 hClass ht j]
    simpa only [U, htAbs] using
      (h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At_ae
        hH3 hClass ht j)
  have hHigh :
      ‖thirdFullPhysicalCriticalThirdForcingHighpass244
          hH3 hClass ρ j t‖ ^ 2 =
        ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
          ‖(F : H3FourierPoint3 → ℂ) ξ‖ ^ 2 ∂volume := by
    dsimp only [F]
    exact thirdFullPhysical_criticalThirdForcingHighpass_norm_sq_eq_integral244
      hH3 hClass ρ j t
  calc
    (2 * Real.pi) ^ 6 *
        ‖thirdFullPhysicalCriticalThirdForcingHighpass244
          hH3 hClass ρ j t‖ ^ 2 =
        (2 * Real.pi) ^ 6 *
          (∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
            ‖(F : H3FourierPoint3 → ℂ) ξ‖ ^ 2 ∂volume) := by
          rw [hHigh]
    _ = ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
          (2 * Real.pi) ^ 6 *
            ‖(F : H3FourierPoint3 → ℂ) ξ‖ ^ 2 ∂volume := by
          rw [integral_const_mul]
    _ = ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
          h3FourierGradientSquare ξ ^ 3 *
            ‖h3RawFinLerayOuterProductDivergence U U j ξ‖ ^ 2 ∂volume := by
          apply integral_congr_ae
          filter_upwards [
            ae_restrict_of_ae
              (s := (h3TerminalRadialFrequencyBelow ρ)ᶜ) hRep
          ] with ξ hξ
          rw [hξ]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 3), mul_pow]
          dsimp only [h3FourierGradientSquare]
          ring

/-- Summing the exact norm-to-band identity over the actual three physical
Leray coordinates preserves the Fourier normalization without factors lost. -/
theorem thirdFullPhysical_highpassThirdHilbertSum_eq_actualCubicBand244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (ρ : ℝ) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralVelocityState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    (2 * Real.pi) ^ 6 *
        (∑ j : Fin 3,
          ‖thirdFullPhysicalCriticalThirdForcingHighpass244
            hH3 hClass ρ j t‖ ^ 2) =
      ∑ j : Fin 3,
        ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
          h3FourierGradientSquare ξ ^ 3 *
            ‖h3RawFinLerayOuterProductDivergence U U j ξ‖ ^ 2 ∂volume := by
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact thirdFullPhysical_highpassThirdHilbert_eq_actualCubicBand244
    hH3 hClass ht ρ j

/-- Actual physical H³ highpass Hilbert source, measured with the correct
(2π)^6 factor, is paid by the genuine high-fifth dissipation plus the exact
nonnegative high signed-phase remainder. No fourth-Q or sixth moment needed. -/
theorem thirdFullPhysical_highpassThirdHilbert_le_twoHighFifthPhase244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (ρ : ℝ) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralVelocityState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    (2 * Real.pi) ^ 6 *
      (∑ j : Fin 3,
        ‖thirdFullPhysicalCriticalThirdForcingHighpass244
          hH3 hClass ρ j t‖ ^ 2) ≤
      2 * (∑ j : Fin 3,
        ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
          h3FourierGradientSquare ξ ^ 5 *
            ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume) +
      2 * (∑ j : Fin 3,
        ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
          h3GlobalSignedPhaseDensity244
            (h3FourierGradientSquare ξ)
            (h3SpectralScalarRawFourierL2 (U j) ξ)
            (h3RawFinLerayOuterProductDivergence U U j ξ) ∂volume) := by
  dsimp only
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  have hExact :=
    thirdFullPhysical_highpassThirdHilbertSum_eq_actualCubicBand244
      hH3 hClass ht ρ
  rw [hExact]
  simpa only [U, htAbs] using
    (thirdFullPhysical_highCubic_le_twoHighFifthPhase244
      hH3 hClass ht ρ)


/-- Exact highband fifth-radial viscosity cost at one strict physical time.
The membership argument only selects the canonical native Fourier velocity. -/
noncomputable def thirdFullPhysicalCriticalHighFifthBand244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (_hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (ρ : ℝ) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans _hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  ∑ j : Fin 3,
    ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3FourierGradientSquare ξ ^ 5 *
        ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2 ∂volume

/-- Exact highband nonnegative signed phase expenditure on the same
strict physical Fourier velocity and its projected nonlinear Leray source. -/
noncomputable def thirdFullPhysicalCriticalHighSignedPhaseBand244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (ρ : ℝ) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralVelocityState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  ∑ j : Fin 3,
    ∫ ξ in (h3TerminalRadialFrequencyBelow ρ)ᶜ,
      h3GlobalSignedPhaseDensity244
        (h3FourierGradientSquare ξ)
        (h3SpectralScalarRawFourierL2 (U j) ξ)
        (h3RawFinLerayOuterProductDivergence U U j ξ) ∂volume

/-- The SAME actual dyadic log-growth witness forces a genuine high-fifth
viscous or high signed-phase Fourier expenditure, for EVERY subsequently
chosen radius. Both costs use the selected actual velocity, and no
terminal-uniform moment hypothesis is introduced. The extra witness
`hrClass` is derived, not postulated. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_highFifthPhaseBand244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hs : s ∈ Set.Ioo b T) (ht : t ∈ Set.Ioo b T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDouble : T - s = 2 * (T - t))
    (B : ℝ) (hB : 0 < B)
    (hRate : 1 ≤ B * (T - t) ^ 8 *
      (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3)
    (K : ℝ)
    (hNear : Real.log B + 8 * Real.log (T - s) +
        3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) <
        8 * Real.log 2 - 3 * K * (t - s)) :
    ∃ (r : ℝ) (_hr : r ∈ Set.Ioo s t) (hrClass : r ∈ Set.Ioo a T),
      K < h3PathPhysicalTopSignedLogRate244 hClass r ∧
      ∀ ρ : ℝ, 0 < ρ →
        (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
            h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
          h3TerminalPhysicalTopDissipation3Path hClass r <
          (2 * Real.pi) ^ 6 *
            (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
              ρ (velocityH3Energy0At u b)) +
          2 * thirdFullPhysicalCriticalHighFifthBand244
            hH3 hClass hrClass ρ +
          2 * thirdFullPhysicalCriticalHighSignedPhaseBand244
            hH3 hClass hrClass ρ := by
  obtain ⟨r, hr, hNet⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_netSignedLogPeak244
      hH3 hClass
      (show s ∈ Set.Ioo a T from
        ⟨lt_trans hb.1 hs.1, hs.2⟩)
      (show t ∈ Set.Ioo a T from
        ⟨lt_trans hb.1 ht.1, ht.2⟩)
      hst hD hDouble B hB hRate K hNear
  have hrTail : r ∈ Set.Ioo b T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hrTail.1, hrTail.2⟩
  refine ⟨r, hr, hrClass, hNet, ?_⟩
  have hDr : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hrClass]
    exact hD r ⟨hr.1.le, hr.2.le⟩
  intro ρ hρ
  have hLogPlus :
      K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
          h3PathPhysicalTopPhaseActionRate244 hH3 hClass r <
      h3PathPhysicalTopSignedLogRate244 hClass r +
          h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
          h3PathPhysicalTopPhaseActionRate244 hH3 hClass r := by
    linarith only [hNet]
  have hCubicBudget :=
    thirdFullPhysical_signedLogPlusFifthPhase_le_sharpKineticLowHigh244
      hH3 hClass b hb r hrTail
      (hD r ⟨hr.1.le, hr.2.le⟩) ρ hρ.le
  have hBand :
      (2 * Real.pi) ^ 6 *
        (∑ j : Fin 3,
          ‖thirdFullPhysicalCriticalThirdForcingHighpass244
            hH3 hClass ρ j r‖ ^ 2) ≤
        2 * thirdFullPhysicalCriticalHighFifthBand244
          hH3 hClass hrClass ρ +
        2 * thirdFullPhysicalCriticalHighSignedPhaseBand244
          hH3 hClass hrClass ρ := by
    simpa only [thirdFullPhysicalCriticalHighFifthBand244,
      thirdFullPhysicalCriticalHighSignedPhaseBand244] using
      (thirdFullPhysical_highpassThirdHilbert_le_twoHighFifthPhase244
        hH3 hClass hrClass ρ)
  calc
    (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
        h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
      h3TerminalPhysicalTopDissipation3Path hClass r <
        (h3PathPhysicalTopSignedLogRate244 hClass r +
          h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
          h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
          h3TerminalPhysicalTopDissipation3Path hClass r :=
      mul_lt_mul_of_pos_right hLogPlus hDr
    _ ≤ (2 * Real.pi) ^ 6 *
      (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
        ρ (velocityH3Energy0At u b) +
        ∑ j : Fin 3,
          ‖thirdFullPhysicalCriticalThirdForcingHighpass244
            hH3 hClass ρ j r‖ ^ 2) := hCubicBudget
    _ = (2 * Real.pi) ^ 6 *
      (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
        ρ (velocityH3Energy0At u b)) +
      (2 * Real.pi) ^ 6 *
        (∑ j : Fin 3,
          ‖thirdFullPhysicalCriticalThirdForcingHighpass244
            hH3 hClass ρ j r‖ ^ 2) := by ring
    _ ≤ (2 * Real.pi) ^ 6 *
      (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
        ρ (velocityH3Energy0At u b)) +
      (2 * thirdFullPhysicalCriticalHighFifthBand244
        hH3 hClass hrClass ρ +
        2 * thirdFullPhysicalCriticalHighSignedPhaseBand244
          hH3 hClass hrClass ρ) :=
      add_le_add_right hBand _
    _ = _ := by ring

end
end PrimeTensor.FirstMonomialTriad
