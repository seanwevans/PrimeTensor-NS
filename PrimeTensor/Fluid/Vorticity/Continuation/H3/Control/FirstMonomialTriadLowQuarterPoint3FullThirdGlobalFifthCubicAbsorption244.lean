import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGlobalForcingTwoMoment244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Majorant
import Mathlib.Tactic

/-!
# Signed global fourth-radial absorption: fifth velocity vs cubic Leray forcing

Earlier modules proved the physical zero-cutoff identity

  D3' = Heat5 + Leray5,     Heat5 = -2 M5,

and the absolute transfer Young bound

  G = 2 sum ∫ q^4 |Re <z,F>| <= M5 + M3.

Here a previously proved *radial-tail* majorant is specialized to cutoff R=0:

  Leray5 <= G.

The resulting **signed** actual PDE inequality is

  D3' + M5 <= M3.

This retains one full copy of the genuinely dissipative fifth moment;
no terminal boundedness assumption is introduced. If cubic forcing stays below
one fraction θ of fifth velocity mass, top dissipation decreases at a rate
at least (1-θ) M5. Conversely, nonnegative D3 growth forces M3 >= M5.

This is a top-dissipation estimate, NOT an upper bound on the normalized
variance production: that production involves -E2² E0 D3', reversing the
relevant sign. It therefore does not independently prove continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1400000

noncomputable local instance axisFintypeGlobalFifthCubicAbsorption244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At cutoff zero, the old sharp radial-tail Leray transfer is exactly the
new globally defined fourth-radial Leray rate, with its original PDE sign. -/
theorem h3Path_globalLerayRate_eq_zeroTailTransfer244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierGlobalLerayRate244 hH3 t
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ =
      h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
        hH3 hClass ht (0 : ℝ) := by
  unfold h3PathTopFourierGlobalLerayRate244
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferCoordinateRateAt
  dsimp only
  simp only [h3Path_zeroRadialBelow_eq_empty244, Set.compl_empty,
    Measure.restrict_univ]

/-- The global SIGNED Leray transfer is bounded above by the earlier
cutoff-independent full absolute transfer profile. In particular this is
opposite in sign from the comparison needed for normalized Leray production. -/
theorem h3Path_globalLerayRate_le_fullAbsoluteTransfer244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierGlobalLerayRate244 hH3 t
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ ≤
      h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt
        hH3 hClass ht := by
  rw [h3Path_globalLerayRate_eq_zeroTailTransfer244 hH3 hClass ht]
  exact
    h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt_le_fullAbsolute
      hH3 hClass ht

/-- The genuine global Fourier heat rate is exactly minus twice the
unrestricted fifth-radial velocity square mass. -/
theorem h3Path_globalHeatRate_eq_negTwoFifthMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierGlobalHeatRate244 hH3 t
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ =
      (-2 : ℝ) * h3PathTopFourierGlobalFifthMass244
        hH3 hClass t ht := by
  unfold h3PathTopFourierGlobalHeatRate244
    h3PathTopFourierGlobalFifthMass244
  dsimp only
  rw [Finset.mul_sum]

/-- The actual differentiated physical top H³ dissipation is coercive
against the *full* fifth velocity mass up to the cubic Leray-forcing mass:

  D3' + M5 <= M3.

The proof preserves the signs of the global heat and Leray terms, applies
the existing zero-radius sharp-tail upper bound to the SIGNED Leray term,
and uses the already-proved two-moment Young inequality. -/
theorem h3Path_globalFourthRadialPairing_add_fifth_le_cubic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t +
      h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht ≤
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
      hH3 hClass ht := by
  have hTop := h3Path_fourthRadialPairing_eq_globalHeat_add_Leray244
    hH3 hClass ht
  have hHeat := h3Path_globalHeatRate_eq_negTwoFifthMass244
    hH3 hClass ht
  have hSigned := h3Path_globalLerayRate_le_fullAbsoluteTransfer244
    hH3 hClass ht
  have hYoung := h3Path_globalAbsoluteLerayTransfer_le_fifth_add_cubic244
    hH3 hClass ht
  rw [hTop, hHeat]
  linarith only [hSigned, hYoung]

/-- If the cubic forcing does not exceed the fifth velocity moment,
the physical fourth-radial dissipation cannot increase. -/
theorem h3Path_globalFourthRadialPairing_nonpos_of_cubic_le_fifth244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hDominated :
      h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
        hH3 hClass ht ≤
      h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht) :
    h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t ≤ 0 := by
  have hRate := h3Path_globalFourthRadialPairing_add_fifth_le_cubic244
    hH3 hClass ht
  linarith only [hRate, hDominated]

/-- Positive growth of actual top dissipation forces the cubic Leray
forcing mass to be strictly larger than the fifth velocity moment. -/
theorem h3Path_globalFourthRadialPairing_pos_forces_cubic_gt_fifth244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hGrowth : 0 < h3PathTopFourierFourthRadialPairingRate244
      hH3 hClass t) :
    h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht <
      h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
        hH3 hClass ht := by
  have hRate := h3Path_globalFourthRadialPairing_add_fifth_le_cubic244
    hH3 hClass ht
  linarith only [hRate, hGrowth]

/-- Quantitative dissipation when cubic forcing consumes only a fraction
θ of the fifth-radial velocity mass. No uniform θ is assumed here. -/
theorem h3Path_globalFourthRadialPairing_le_negRemainingFifth244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t θ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hFraction :
      h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
        hH3 hClass ht ≤
      θ * h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht) :
    h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t ≤
      -(1 - θ) * h3PathTopFourierGlobalFifthMass244
        hH3 hClass t ht := by
  have hRate := h3Path_globalFourthRadialPairing_add_fifth_le_cubic244
    hH3 hClass ht
  have hAlgebra :
      -(1 - θ) * h3PathTopFourierGlobalFifthMass244
          hH3 hClass t ht =
        θ * h3PathTopFourierGlobalFifthMass244
          hH3 hClass t ht -
        h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht := by
    ring
  rw [hAlgebra]
  linarith only [hRate, hFraction]

/-- A strict forcing fraction, together with positive fifth velocity mass,
forces a strictly negative actual fourth-radial dissipation derivative. -/
theorem h3Path_globalFourthRadialPairing_strictNeg_of_cubic_fraction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t θ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hθ : θ < 1)
    (hFifth : 0 < h3PathTopFourierGlobalFifthMass244
      hH3 hClass t ht)
    (hFraction :
      h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
        hH3 hClass ht ≤
      θ * h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht) :
    h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t < 0 := by
  have hBound := h3Path_globalFourthRadialPairing_le_negRemainingFifth244
    hH3 hClass ht hFraction
  have hResidual :
      0 < (1 - θ) * h3PathTopFourierGlobalFifthMass244
        hH3 hClass t ht :=
    mul_pos (by linarith only [hθ]) hFifth
  linarith only [hBound, hResidual]

end
end PrimeTensor.FirstMonomialTriad
