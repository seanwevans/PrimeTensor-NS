import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Derivative.Representative

/-!
# Split the fourth-order forcing factor through the physical PDE balance

The previous checkpoint identifies the fourth adjacent-order branch with the
canonical Hilbert forcing factor

    B_j(t) = q² F_j(t).

The physical fourth-radial derivative representative already gives

    W_j(t)
      =
    -q³ û_j(t) - q² F_j(t).

Rather than re-run the positive-time smoothing construction to choose a
sixth-radial velocity state, define the canonical diffusion factor directly by

    A_j(t) := -W_j(t) - B_j(t).

The PDE representative then proves that `A_j` has the literal Fourier
representative `q³ û_j` almost everywhere.  Hence in Hilbert space

    B_j = -W_j - A_j,

and therefore

    ‖B_j‖ ≤ ‖W_j‖ + ‖A_j‖.

This is the exact triangle inequality needed for the next finite-channel
extraction: divergence of the fourth-order forcing branch must be paid by
either the temporal fourth-radial derivative or the sixth-radial diffusion
factor.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailForcingPDEBalance
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1200000

/-! ## Canonical q³ velocity diffusion factor -/

/--
The canonical strict-time sixth-radial velocity / diffusion factor.

It is defined algebraically from the already-canonical fourth-radial temporal
derivative and canonical `q² F_j` forcing factor.
-/
noncomputable def h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    H3FourierComplexL2 :=
  -
    deriv
      (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
        hH3 hClass j)
      t
  -
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
      hH3 hClass ht j

/--
The algebraically canonical diffusion state is literally `q³ û_j` almost
everywhere.
-/
theorem h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ((
      h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At
        hH3 hClass ht j :
      H3FourierComplexL2
    ) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
        *
      h3SpectralScalarRawFourierL2
        (U j) ξ) := by

  dsimp only

  let W : H3FourierComplexL2 :=
    deriv
      (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
        hH3 hClass j)
      t

  let B : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
      hH3 hClass ht j

  have hW :
      ((W : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        (-(h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
            *
          h3SpectralScalarRawFourierL2
            ((h3TerminalVelocitySpectralStateAt
                hH3 t
                ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩) j) ξ
          -
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
            *
          h3RawFinLerayOuterProductDivergence
            (h3TerminalVelocitySpectralStateAt
              hH3 t
              ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
            (h3TerminalVelocitySpectralStateAt
              hH3 t
              ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
            j ξ) := by

    dsimp only [W]

    exact
      h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_deriv_ae_unitPDE
        hH3 hClass ht j

  have hB :
      ((B : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        h3RawFinLerayOuterProductDivergence
          (h3TerminalVelocitySpectralStateAt
            hH3 t
            ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
          (h3TerminalVelocitySpectralStateAt
            hH3 t
            ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩)
          j ξ) := by

    dsimp only [B]

    exact
      h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At_ae
        hH3 hClass ht j

  have hNeg :=
    MeasureTheory.Lp.coeFn_neg W

  have hSub :=
    MeasureTheory.Lp.coeFn_sub (-W) B

  unfold
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At

  change
    (((-W - B : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ))
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
        *
      h3SpectralScalarRawFourierL2
        ((h3TerminalVelocitySpectralStateAt
            hH3 t
            ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩) j) ξ)

  filter_upwards [
    hSub,
    hNeg,
    hW,
    hB
  ] with ξ hSubξ hNegξ hWξ hBξ

  rw [hSubξ]

  simp only [Pi.sub_apply]

  rw [hNegξ]

  simp only [Pi.neg_apply]

  rw [hWξ, hBξ]

  ring

/-! ## Exact Hilbert PDE identity -/

/--
The canonical fourth-order forcing factor is exactly the negative temporal
derivative minus the canonical sixth-radial diffusion factor.
-/
theorem h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At_eq_neg_deriv_sub_velocityThirdQ
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
        hH3 hClass ht j
      =
    -
      deriv
        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j)
        t
      -
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At
      hH3 hClass ht j := by

  unfold
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At

  abel

/--
Triangle form of the exact fourth-radial PDE balance.
-/
theorem norm_h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At_le_deriv_add_velocityThirdQ
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At
        hH3 hClass ht j‖
      ≤
    ‖deriv
        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j)
        t‖
      +
    ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At
        hH3 hClass ht j‖ := by

  rw [
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At_eq_neg_deriv_sub_velocityThirdQ
      hH3 hClass ht j
  ]

  calc
    ‖-
        deriv
          (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass j)
          t
        -
      h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At
        hH3 hClass ht j‖
        ≤
      ‖-
        deriv
          (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass j)
          t‖
        +
      ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At
          hH3 hClass ht j‖ :=
      norm_sub_le _ _
    _ =
      ‖deriv
          (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass j)
          t‖
        +
      ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At
          hH3 hClass ht j‖ := by
      rw [norm_neg]

/-! ## Strict-time path form -/

noncomputable def h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    H3FourierComplexL2 :=
  if ht : t ∈ Set.Ioo a T then
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At
      hH3 hClass ht j
  else
    0

theorem h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
        hH3 hClass j t
      =
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At
      hH3 hClass ht j := by

  simp [
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path,
    ht
  ]

/--
Path-level triangle bound on the strict physical interval.
-/
theorem norm_h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_le_deriv_add_velocityThirdQPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
        hH3 hClass j t‖
      ≤
    ‖deriv
        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j)
        t‖
      +
    ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
        hH3 hClass j t‖ := by

  rw [
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_eq
      hH3 hClass ht j,
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path_eq
      hH3 hClass ht j
  ]

  exact
    norm_h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At_le_deriv_add_velocityThirdQ
      hH3 hClass ht j

end

end Euclidean
end Bridge
end PrimeTensor
