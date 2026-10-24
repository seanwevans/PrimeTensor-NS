import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralCoordinateEscape244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Bounded.Radial.Weighted.Cauchy
import Mathlib.Tactic

/-!
# Fixed radial carrier ceiling and cofinal complementary spectral mass

The source-to-actual-state transfer and the fixed-coordinate extraction are
norm statements in the genuine weighted Fourier H³ velocity state.  The
previously established radial reweighting theorem gives a complementary,
quantitative fact: below each fixed radial cutoff ρ, weighted spectral square
mass is bounded by

  (1 + ρ² + ρ⁴ + ρ⁶) * (global raw Fourier velocity square mass).

Here the raw mass is expressed as the zero-comparison square defect, so no
pointwise spectral evaluation, compactness assumption or Fourier inversion
is needed.  The final theorem proves that if this *raw Fourier/kinetic*
square mass has a uniform terminal ceiling, absence of a strong physical L²
trace forces unbounded spectral square mass *outside the fixed radial
carrier*, for every fixed ρ.  A separate physical-kinetic-to-raw-Fourier
identification is available in the repository, but is intentionally not
silently inserted as an implicit hypothesis here.

The quantity called the high-radial remainder is defined algebraically as
global squared spectral mass minus integrated low-radial spectral mass.
Its equality with the integral over the complementary radial set is the next
measure-theoretic normalization step, not a theorem asserted here.

No H³ nonextension-to-L²-nonconvergence inference is made.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The genuine three-component weighted H³ square mass below a fixed
radial frequency cutoff, measured against the zero spectral state. -/
noncomputable def h3PathActualSpectralLowRadialSquareMass244
    (ρ : ℝ) (G : H3SpectralVelocityState) : ℝ :=
  h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ G 0

/-- The algebraic complementary mass relative to the same frequency ball.
The exact complement-integral identity is intentionally a later lemma. -/
noncomputable def h3PathActualSpectralHighRadialRemainder244
    (ρ : ℝ) (G : H3SpectralVelocityState) : ℝ :=
  h3SpectralVelocitySquareEnergy G -
    h3PathActualSpectralLowRadialSquareMass244 ρ G

/-- Previously proved exact H³ radial Sobolev ceiling, specialized to a
single state compared to zero.  This is integrated, not pointwise control. -/
theorem h3Path_actualSpectralLowRadialSquareMass_le_rawSquare244
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (G : H3SpectralVelocityState) :
    h3PathActualSpectralLowRadialSquareMass244 ρ G ≤
      h3TerminalRadialSobolevWeightSquareCeiling ρ *
        h3TerminalRawVelocityFourierTotalSquareDefect G 0 := by
  exact
    weightedSpectralVelocityRadialSquareDefect_le_ceiling_mul_rawVelocityFourierTotalSquareDefect
      hρ G 0

/-- A uniform raw Fourier square ceiling gives a *fixed*, explicitly
polynomial low-frequency spectral square ceiling. -/
theorem h3Path_actualSpectralLowRadialSquareMass_ceiling244
    {a T : ℝ}
    (S : ℝ → H3SpectralVelocityState)
    (ρ E : ℝ) (hρ : 0 ≤ ρ)
    (hRaw : ∀ r : ℝ, r ∈ Set.Ioo a T →
      h3TerminalRawVelocityFourierTotalSquareDefect (S r) 0 ≤ E) :
    ∀ r : ℝ, r ∈ Set.Ioo a T →
      h3PathActualSpectralLowRadialSquareMass244 ρ (S r) ≤
        h3TerminalRadialSobolevWeightSquareCeiling ρ * E := by
  intro r hr
  exact
    (h3Path_actualSpectralLowRadialSquareMass_le_rawSquare244
      ρ hρ (S r)).trans
      (mul_le_mul_of_nonneg_left (hRaw r hr)
        (h3TerminalRadialSobolevWeightSquareCeiling_pos ρ).le)

/-- The norm square of each coordinate is contained in the total squared
spectral energy.  This uses the sum of three squares, NOT the sup norm as
an equality. -/
theorem h3Path_spectralCoordinateSquare_le_totalSquareEnergy244
    (G : H3SpectralVelocityState) (j : Fin 3) :
    ‖G j‖ ^ 2 ≤ h3SpectralVelocitySquareEnergy G := by
  unfold h3SpectralVelocitySquareEnergy
  exact Finset.single_le_sum
    (fun k _ => sq_nonneg ‖G k‖) (Finset.mem_univ j)

/-- Finite-product selection plus a *uniform integrated low radial ceiling*
forces cofinal growth of the complementary spectral square remainder.
The coordinate chosen by the prior theorem is independent of the subtail. -/
theorem h3Path_fixedSpectralCoordinateEscape_forces_highRadialRemainder244
    {a T : ℝ}
    (S : ℝ → H3SpectralVelocityState)
    (ρ C : ℝ)
    (hLow : ∀ r : ℝ, r ∈ Set.Ioo a T →
      h3PathActualSpectralLowRadialSquareMass244 ρ (S r) ≤ C)
    (hFixed : ∃ j : Fin 3, ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ M : ℝ, ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < ‖(S r) j‖) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < h3PathActualSpectralHighRadialRemainder244 ρ (S r) := by
  obtain ⟨j, hj⟩ := hFixed
  intro b hb M
  let D : ℝ := max M 0
  let Q : ℝ := max (C + D + 1) 1
  obtain ⟨r, hr, hLarge⟩ := hj b hb Q
  refine ⟨r, hr, ?_⟩
  have hrTail : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hr.1, hr.2⟩
  have hQOne : (1 : ℝ) ≤ Q := le_max_right _ _
  have hQBase : C + D + 1 ≤ Q := le_max_left _ _
  have hD : M ≤ D := le_max_left M 0
  have hValOne : 1 ≤ ‖(S r) j‖ :=
    le_trans hQOne (le_of_lt hLarge)
  have hValAbove : C + D + 1 < ‖(S r) j‖ :=
    lt_of_le_of_lt hQBase hLarge
  have hSqAbove : ‖(S r) j‖ ≤ ‖(S r) j‖ ^ 2 := by
    nlinarith
  have hCoord : ‖(S r) j‖ ^ 2 ≤
      h3SpectralVelocitySquareEnergy (S r) :=
    h3Path_spectralCoordinateSquare_le_totalSquareEnergy244 (S r) j
  have hLowAt := hLow r hrTail
  dsimp only [h3PathActualSpectralHighRadialRemainder244]
  linarith

/-- Main carrier-level statement. The raw Fourier square bound is explicitly
retained, rather than incorrectly inferred from a bounded *H³* norm. -/
theorem h3Path_physicalNoL2Trace_forces_highRadialRemainder_of_rawCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (E : ℝ)
    (hRaw : ∀ r : ℝ, r ∈ Set.Ioo a T →
      h3TerminalRawVelocityFourierTotalSquareDefect
        (h3AuditActualSpectralVelocityTotal hH3 r) 0 ≤ E)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < h3PathActualSpectralHighRadialRemainder244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 r) := by
  apply h3Path_fixedSpectralCoordinateEscape_forces_highRadialRemainder244
    (h3AuditActualSpectralVelocityTotal hH3)
    ρ (h3TerminalRadialSobolevWeightSquareCeiling ρ * E)
  · exact h3Path_actualSpectralLowRadialSquareMass_ceiling244
      (h3AuditActualSpectralVelocityTotal hH3) ρ E hρ hRaw
  · exact h3Path_physicalNoL2Trace_forces_fixedSpectralCoordinateEscape244
      hH3 hClass hL hNoTrace

end
end PrimeTensor.FirstMonomialTriad
