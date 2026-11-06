import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileSuperEighthCarrierEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileFirstShellKinetic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Critical-eighth kinetic concentration or genuine outer-frequency escape

The previous super-eighth argument used the constant global order-zero energy
ceiling. The exact annular physical Fourier comparison is sharper: the
crossing height is paid by the raw kinetic mass *inside the actual annulus*.
At critical eighth height, bounded relative outer frequency forces that
band mass to remain bounded away from zero. If the selected moving raw band
mass tends to zero, the minimal outer radius must therefore escape at the
critical eighth scale, not just above it.

The moving-band mass convergence premise is NOT inferred here merely from
physical L2 terminal convergence; the latter needs its own Fourier tail
transfer theorem. The nonvanishing-mass alternative is unconditional once
the physical minimal crossing has been selected.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeProfileCriticalEighth244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceProfileCriticalEighth244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Nonnegative actual Fourier kinetic mass, integrated over exactly the
measurable annulus used by the physical H3 dissipation. -/
theorem thirdFull_bandRawKineticMass_nonneg244
    (R Q : ℝ) (G : H3SpectralVelocityState) :
    0 ≤ h3PathActualBandRawKineticMass244 R Q G := by
  unfold h3PathActualBandRawKineticMass244
  apply integral_nonneg
  intro ξ
  unfold h3TerminalRawVelocityFourierTotalSquareDensity
  positivity

/-- The physical first crossing is paid by mass IN its finite Fourier
annulus, not by all order-zero kinetic energy. There is no need for an
independent H3 energy or moment ceiling. -/
theorem thirdFullPhysical_profileAnnulus_rawEighthKineticCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    (n N : ℕ) (hnN : n ≤ N) (M : ℝ)
    (hCross : M / 2 <
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) :
    M < 8 * (((N : ℝ) + 2) ^ 8) *
      h3PathActualBandRawKineticMass244
        ((n : ℝ) + 1) ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  have hCast : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have hRQ : (n : ℝ) + 1 ≤ (N : ℝ) + 1 := by
    linarith only [hCast]
  have hDiss := h3Path_actualAnnularDissipation_le_shiftedEighthBandMass244
    hH3 hClass t ht ((n : ℝ) + 1) ((N : ℝ) + 1)
    hRQ (by positivity)
  have hDiss' :
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ≤
      4 * (((N : ℝ) + 2) ^ 8) *
        h3PathActualBandRawKineticMass244
          ((n : ℝ) + 1) ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) := by
    convert hDiss using 1; ring
  linarith only [hCross, hDiss']

/-- At the exact critical exponent eight, every bounded relative outer
radius demands a fixed positive moving-band raw kinetic mass. -/
theorem thirdFull_criticalEighthHeight_forces_farCarrier_or_kineticMass244
    (R Q M μ D η : ℝ)
    (hR : 1 ≤ R) (hQ : 0 ≤ Q) (hμ : 0 ≤ μ)
    (hD : 0 ≤ D) (hη : 0 < η)
    (hHeight : η * R ^ 8 ≤ M)
    (hCost : M < 8 * (Q + 1) ^ 8 * μ) :
    D * R < Q + 1 ∨ η < 8 * D ^ 8 * μ := by
  by_cases hFar : D * R < Q + 1
  · exact Or.inl hFar
  · right
    have hQR : Q + 1 ≤ D * R := le_of_not_gt hFar
    have hQpos : 0 ≤ Q + 1 := by linarith only [hQ]
    have hPower : (Q + 1) ^ 8 ≤ (D * R) ^ 8 :=
      pow_le_pow_left₀ hQpos hQR 8
    have hScaled : (Q + 1) ^ 8 * (8 * μ) ≤
        (D * R) ^ 8 * (8 * μ) :=
      mul_le_mul_of_nonneg_right hPower (by positivity)
    have hUpper : η * R ^ 8 < (8 * D ^ 8 * μ) * R ^ 8 := by
      calc
        η * R ^ 8 ≤ M := hHeight
        _ < 8 * (Q + 1) ^ 8 * μ := hCost
        _ = (Q + 1) ^ 8 * (8 * μ) := by ring
        _ ≤ (D * R) ^ 8 * (8 * μ) := hScaled
        _ = (8 * D ^ 8 * μ) * R ^ 8 := by ring
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hR8 : 0 ≤ R ^ 8 := (pow_pos hRpos 8).le
    by_contra hNot
    have hReverse : 8 * D ^ 8 * μ ≤ η := le_of_not_gt hNot
    have hReverseScaled := mul_le_mul_of_nonneg_right hReverse hR8
    exact (not_lt_of_ge hReverseScaled) hUpper

/-- A critical-eighth profile forces the relative carrier radius to
escape whenever its *actual moving-band kinetic mass* vanishes. This
is the exact compactness mechanism still to be supplied by physical
terminal L2 Fourier tightness. -/
theorem thirdFull_criticalEighthHeight_vanishingBand_forces_escape244
    (R Q M μ : ℕ → ℝ) (η : ℝ)
    (hR : ∀ k, 1 ≤ R k) (hQ : ∀ k, 0 ≤ Q k)
    (hμ : ∀ k, 0 ≤ μ k) (hη : 0 < η)
    (hHeight : ∀ᶠ k : ℕ in atTop, η * R k ^ 8 ≤ M k)
    (hCost : ∀ᶠ k : ℕ in atTop,
      M k < 8 * (Q k + 1) ^ 8 * μ k)
    (hVanishing : Tendsto μ atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k : ℕ => (Q k + 1) / R k) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro A
  let D : ℝ := max A 0
  have hAD : A ≤ D := le_max_left _ _
  have hD : 0 ≤ D := le_max_right _ _
  have hScaled : Tendsto (fun k => 8 * D ^ 8 * μ k)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hVanishing.const_mul (8 * D ^ 8)
  have hSmall : ∀ᶠ k : ℕ in atTop, 8 * D ^ 8 * μ k < η :=
    hScaled.eventually (eventually_lt_nhds hη)
  filter_upwards [hHeight, hCost, hSmall] with k hkHeight hkCost hkSmall
  have hRpos : 0 < R k := lt_of_lt_of_le zero_lt_one (hR k)
  rcases thirdFull_criticalEighthHeight_forces_farCarrier_or_kineticMass244
      (R k) (Q k) (M k) (μ k) D η
      (hR k) (hQ k) (hμ k) hD hη hkHeight hkCost with hFar | hLargeMass
  · have hCompare : A * R k ≤ D * R k :=
      mul_le_mul_of_nonneg_right hAD hRpos.le
    exact (le_div_iff₀ hRpos).2 (hCompare.trans hFar.le)
  · exact False.elim (lt_asymm hLargeMass hkSmall)

end
end PrimeTensor.FirstMonomialTriad
