import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileMinimalCarrierRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEMinimalBandKineticNinthEighth244
import Mathlib.Tactic

/-!
# Arbitrary-height minimal H³ carrier: the physical order-zero kinetic anchor

The minimal crossing annulus cannot borrow an arbitrarily large amount of
unweighted Fourier kinetic mass: its true band mass is bounded by the actual
strict-time kinetic energy, which is antitone after the selected anchor b.
For a positive prescribed height M the crossing forces

  M < 8 * (N + 2)^8 * velocityH3Energy0At u b.

The exponent eight comes from the existing physical H³ viscous Fourier
weight estimate, not from a new hypothetical spectral bound. The last-shell
overshoot may still be arbitrarily small and is not used as a mass floor.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeProfileKineticEighth244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceProfileKineticEighth244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Every arbitrary-height finite annulus that captures more than M/2 of
physical viscous dissipation must be supported by the genuine order-zero
kinetic energy at the earlier time b. The bound does not require last-shell
overshoot or a uniform bound on H³ itself. -/
theorem thirdFullPhysical_profileAnnulus_kineticEighthAnchor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (t : ℝ) (ht : t ∈ Set.Ioo b T)
    (n N : ℕ) (hnN : n ≤ N)
    (M : ℝ)
    (hCross : M / 2 <
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) :
    M < 8 * (((N : ℝ) + 2) ^ 8) * velocityH3Energy0At u b := by
  have htAbs : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hnNReal : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have hRQ : ((n : ℝ) + 1) ≤ ((N : ℝ) + 1) := by
    linarith only [hnNReal]
  have hDiss := h3Path_actualAnnularDissipation_le_shiftedEighthBandMass244
    hH3 hClass t htAbs ((n : ℝ) + 1) ((N : ℝ) + 1)
    hRQ (by positivity)
  have hBand := h3Path_bandRawKineticMass_le_rawTotal244
    ((n : ℝ) + 1) ((N : ℝ) + 1)
    (h3AuditActualSpectralVelocityTotal hH3 t)
  have hAnchor := h3Path_actualRawFourierSquareMass_le_kineticAnchor244
    hH3 hClass b hb t ht
  have hMass :
      h3PathActualBandRawKineticMass244 ((n : ℝ) + 1) ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ≤
        velocityH3Energy0At u b := hBand.trans hAnchor
  have hFactor : 0 ≤ 4 * (((N : ℝ) + 2) ^ 8) := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hMass hFactor
  have hDiss' :
      h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ≤
      4 * (((N : ℝ) + 2) ^ 8) *
        h3PathActualBandRawKineticMass244 ((n : ℝ) + 1) ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) := by
    convert hDiss using 1 <;> ring
  linarith only [hCross, hDiss', hScaled]

/-- A selected cofinal family of arbitrary-height first crossings inherits
the physical kinetic ceiling from any fixed earlier strict-time anchor.
This is on the original snapshots; no replacement Fourier bands are chosen. -/
theorem thirdFullPhysical_profileCofinalAnnuli_kineticEighthAnchor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (M : ℕ → ℝ)
    (hLimit : Tendsto τ atTop (𝓝 T))
    (hEnd : ∀ n : ℕ, τ n < T)
    (hnN : ∀ n : ℕ, n ≤ N n)
    (hCross : ∀ n : ℕ, M n / 2 <
      h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ n))) :
    ∀ᶠ n : ℕ in atTop,
      M n < 8 * (((N n : ℝ) + 2) ^ 8) * velocityH3Energy0At u b := by
  have hAfter : ∀ᶠ n : ℕ in atTop, b < τ n :=
    hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)
  filter_upwards [hAfter] with n hbn
  exact thirdFullPhysical_profileAnnulus_kineticEighthAnchor244
    hH3 hClass b hb (τ n) ⟨hbn, hEnd n⟩
    n (N n) (hnN n) (M n) (hCross n)

end
end PrimeTensor.FirstMonomialTriad
