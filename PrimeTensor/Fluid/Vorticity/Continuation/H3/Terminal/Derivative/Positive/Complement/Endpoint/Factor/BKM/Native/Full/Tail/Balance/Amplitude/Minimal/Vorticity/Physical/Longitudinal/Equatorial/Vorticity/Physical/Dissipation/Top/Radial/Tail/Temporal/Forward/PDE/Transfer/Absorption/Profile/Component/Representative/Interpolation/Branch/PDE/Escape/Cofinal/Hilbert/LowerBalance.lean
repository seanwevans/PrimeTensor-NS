import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert

/-!
# Lower weighted physical PDE balance

The remaining lower forcing obstruction is the canonical Hilbert factor

    C_j(t) = q F_j(t).

The already-existing terminal fourth-radial velocity state is

    V_j(t) = q² û_j(t).

Package their normalized unit-viscosity PDE combination

    R¹_j(t) := -V_j(t) - C_j(t).

This is the lower weighted spectral Navier--Stokes right-hand side.  Algebraically

    C_j = -R¹_j - V_j,

and therefore

    ‖C_j‖ ≤ ‖R¹_j‖ + ‖V_j‖.

This checkpoint is intentionally algebraic.  It does not yet identify `R¹_j`
with the strong derivative of the `q û_j` path; that temporal identification
is the next seam.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalLowerWeightedPDEBalance
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 900000

/-! ## Strict-time lower weighted RHS -/

/--
Canonical lower weighted physical PDE RHS

    -q² û_j - q F_j

at one strict preterminal time.
-/
noncomputable def h3TerminalPhysicalLowerWeightedPDERHSFourierL2At
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    H3FourierComplexL2 :=
  -
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
      hH3 hClass ht j
  -
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
      hH3 hClass ht j

/--
Exact Hilbert-space rearrangement of the lower weighted PDE balance.
-/
theorem h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At_eq_neg_lowerWeightedPDERHS_sub_fourthRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
        hH3 hClass ht j
      =
    -
      h3TerminalPhysicalLowerWeightedPDERHSFourierL2At
        hH3 hClass ht j
      -
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
      hH3 hClass ht j := by

  unfold
    h3TerminalPhysicalLowerWeightedPDERHSFourierL2At

  abel

/--
Triangle inequality for the lower weighted forcing factor.
-/
theorem norm_h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At_le_lowerWeightedPDERHS_add_fourthRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ‖h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At
        hH3 hClass ht j‖
      ≤
    ‖h3TerminalPhysicalLowerWeightedPDERHSFourierL2At
        hH3 hClass ht j‖
      +
    ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
        hH3 hClass ht j‖ := by

  rw [
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At_eq_neg_lowerWeightedPDERHS_sub_fourthRadial
      hH3 hClass ht j
  ]

  calc
    ‖-
        h3TerminalPhysicalLowerWeightedPDERHSFourierL2At
          hH3 hClass ht j
        -
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
        hH3 hClass ht j‖
        ≤
      ‖-
        h3TerminalPhysicalLowerWeightedPDERHSFourierL2At
          hH3 hClass ht j‖
        +
      ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
          hH3 hClass ht j‖ :=
      norm_sub_le _ _
    _ =
      ‖h3TerminalPhysicalLowerWeightedPDERHSFourierL2At
          hH3 hClass ht j‖
        +
      ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
          hH3 hClass ht j‖ := by
      rw [norm_neg]

/-! ## Zero-extended path form -/

noncomputable def h3TerminalPhysicalLowerWeightedPDERHSFourierL2Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    H3FourierComplexL2 :=
  if ht : t ∈ Set.Ioo a T then
    h3TerminalPhysicalLowerWeightedPDERHSFourierL2At
      hH3 hClass ht j
  else
    0

theorem h3TerminalPhysicalLowerWeightedPDERHSFourierL2Path_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalLowerWeightedPDERHSFourierL2Path
        hH3 hClass j t
      =
    h3TerminalPhysicalLowerWeightedPDERHSFourierL2At
      hH3 hClass ht j := by

  simp [
    h3TerminalPhysicalLowerWeightedPDERHSFourierL2Path,
    ht
  ]

/--
Path-level exact lower weighted PDE balance on every strict physical slice.
-/
theorem h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path_eq_neg_lowerWeightedPDERHSPath_sub_fourthRadialPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
        hH3 hClass j t
      =
    -
      h3TerminalPhysicalLowerWeightedPDERHSFourierL2Path
        hH3 hClass j t
      -
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
      hH3 hClass j t := by

  rw [
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path_eq
      hH3 hClass ht j,
    h3TerminalPhysicalLowerWeightedPDERHSFourierL2Path_eq
      hH3 hClass ht j,
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_eq
      hH3 hClass ht j
  ]

  exact
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At_eq_neg_lowerWeightedPDERHS_sub_fourthRadial
      hH3 hClass ht j

/--
Path-level triangle inequality for the lower weighted forcing branch.
-/
theorem norm_h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path_le_lowerWeightedPDERHSPath_add_fourthRadialPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ‖h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path
        hH3 hClass j t‖
      ≤
    ‖h3TerminalPhysicalLowerWeightedPDERHSFourierL2Path
        hH3 hClass j t‖
      +
    ‖h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
        hH3 hClass j t‖ := by

  rw [
    h3TerminalPhysicalTopDissipationForcingSecondQFourierL2Path_eq
      hH3 hClass ht j,
    h3TerminalPhysicalLowerWeightedPDERHSFourierL2Path_eq
      hH3 hClass ht j,
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_eq
      hH3 hClass ht j
  ]

  exact
    norm_h3TerminalPhysicalTopDissipationForcingSecondQFourierL2At_le_lowerWeightedPDERHS_add_fourthRadial
      hH3 hClass ht j

end

end Euclidean
end Bridge
end PrimeTensor
