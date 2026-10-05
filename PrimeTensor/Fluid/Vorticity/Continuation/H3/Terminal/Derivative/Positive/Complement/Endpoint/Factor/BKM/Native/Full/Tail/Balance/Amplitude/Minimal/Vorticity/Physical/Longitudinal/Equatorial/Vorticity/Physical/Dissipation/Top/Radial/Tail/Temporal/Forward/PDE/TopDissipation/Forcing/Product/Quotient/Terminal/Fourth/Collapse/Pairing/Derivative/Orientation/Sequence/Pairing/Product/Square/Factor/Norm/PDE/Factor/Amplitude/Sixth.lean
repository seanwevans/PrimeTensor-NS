import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude

/-!
# Canonical terminal sixth-diffusion PDE RHS

The remaining genuinely new state branch is the derivative of the canonical
terminal `q³ û_j` path.

The selected restart analysis already proves, on every positive compact slab,

    d/dt (q³ û_j) = -q⁴ û_j - q³ F_j.

The only issue is that the restart slab depends on the strict physical time.
Rather than make a global arbitrary choice of restart window, define the
terminal sixth-diffusion PDE RHS canonically as the actual derivative of the
terminal `q³ û_j` path.  Then prove that on *any* valid local restart slab whose
interior contains the physical time, this canonical value equals the selected
sixth-diffusion RHS.

Thus the sixth derivative-norm frontier is a canonical terminal quantity with
a concrete local representative

    -q⁴ û_j - q³ F_j

on every admissible restart chart.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/--
Canonical terminal sixth-diffusion PDE RHS: the strong derivative of the
physical `q³ û_j` path.
-/
noncomputable def h3TerminalResolvedSixthDiffusionPDERHS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (t : ℝ) :
    H3FourierComplexL2 :=
  deriv
    (h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
      hH3 hClass j)
    t

/--
The canonical sixth-diffusion RHS is also the derivative of the abstract
resolved sixth-diffusion Hilbert state.
-/
theorem h3TerminalResolvedSixthDiffusionPDERHS_eq_deriv_hilbertState
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3) :
    h3TerminalResolvedSixthDiffusionPDERHS
        hH3 hClass j t
      =
    deriv
      (h3TerminalResolvedSixthDiffusionHilbertState
        hH3 hClass j)
      t := by

  have hPath :
      h3TerminalResolvedSixthDiffusionHilbertState
          hH3 hClass j
        =
      h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
        hH3 hClass j := by
    funext r
    rfl

  unfold
    h3TerminalResolvedSixthDiffusionPDERHS

  rw [hPath]

/--
Accordingly, the sixth-diffusion Hilbert derivative norm envelope is exactly
the norm of the canonical terminal sixth-diffusion PDE RHS.
-/
theorem h3TerminalResolvedSixthDiffusionHilbertDerivativeNormEnvelope_eq_norm_pdeRHS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3) :
    h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
        hH3 hClass j
        H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
        t
      =
    ‖h3TerminalResolvedSixthDiffusionPDERHS
      hH3 hClass j t‖ := by

  rw [
    h3TerminalResolvedSixthDiffusionHilbertDerivativeNormEnvelope_eq
  ]

  rw [
    ←
      h3TerminalResolvedSixthDiffusionPDERHS_eq_deriv_hilbertState
        hH3 hClass j
  ]

/--
On any valid local restart slab whose interior contains the strict physical
time `r`, the canonical terminal sixth-diffusion PDE RHS equals the selected
restart RHS

    -q⁴ û_j - q³ F_j

at elapsed time `r - t₀`.

This statement is independent of which admissible restart chart is used.
-/
theorem h3TerminalResolvedSixthDiffusionPDERHS_eq_selectedSixthDiffusionRHS
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T S a t₀ Q r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNS : LoggedPreterminalNavierStokesAdmissible u S)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) S)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ S E)
    (hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u S t₀ hNS ht₀ hE hTail)
    (hQ : 0 < Q)
    (hQR : Q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hrClass : r ∈ Set.Ioo a T)
    (hrS : r < S)
    (hrSlab :
      r - t₀ ∈ Set.Ioo (Q / 2) Q)
    (j : Fin 3) :
    h3TerminalResolvedSixthDiffusionPDERHS
        hH3 hClass j r
      =
    h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR j
      ⟨r - t₀, hrSlab.1.le, hrSlab.2.le⟩ := by

  let x : ℝ :=
    r - t₀

  let xSlab :
      Set.Icc (Q / 2) Q :=
    ⟨x, hrSlab.1.le, hrSlab.2.le⟩

  let Vclosed :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR j

  let Vselected :
      ℝ → H3FourierComplexL2 :=
    fun s =>
      Set.IccExtend
        (by linarith : Q / 2 ≤ Q)
        Vclosed
        (s - t₀)

  let Vphysical :
      ℝ → H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
      hH3 hClass j

  let W : H3FourierComplexL2 :=
    h3PreterminalSelectedSixthDiffusionRHSFourierL2OnSlab
      hNS ht₀ hE hTail hQ hQR j xSlab

  have hx :
      x ∈ Set.Ioo (Q / 2) Q := by
    dsimp only [x]
    exact hrSlab

  have hRelative :=
    h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab_hasDerivAt
      hNS ht₀ hE hTail hQ hQR j hx

  have hShift :
      HasDerivAt
        (fun s : ℝ => s - t₀)
        1
        r := by
    simpa using
      (hasDerivAt_id r).sub_const t₀

  have hSelectedAbsolute :
      HasDerivAt
        Vselected
        W
        r := by

    have hComp :=
      hRelative.scomp
        r
        hShift

    dsimp only [
      Vselected,
      Vclosed,
      W,
      xSlab,
      x
    ] at hComp ⊢

    simpa only [
      Function.comp_def,
      one_smul
    ] using hComp

  have hClassNeighborhood :
      Set.Ioo a T ∈ 𝓝 r :=
    Ioo_mem_nhds
      hrClass.1
      hrClass.2

  have hSlabLeft :
      t₀ + Q / 2 < r := by
    linarith [hrSlab.1]

  have hSlabRight :
      r < t₀ + Q := by
    linarith [hrSlab.2]

  have hSlabNeighborhood :
      Set.Ioo
          (t₀ + Q / 2)
          (t₀ + Q)
        ∈
      𝓝 r :=
    Ioo_mem_nhds
      hSlabLeft
      hSlabRight

  have hSNeighborhood :
      Set.Iio S ∈ 𝓝 r :=
    Iio_mem_nhds hrS

  have hEventuallyEq :
      Vphysical =ᶠ[𝓝 r] Vselected := by

    filter_upwards [
      hClassNeighborhood,
      hSlabNeighborhood,
      hSNeighborhood
    ] with s hsClass hsSlabAbs hsS

    have hsSlab :
        s - t₀ ∈ Set.Icc (Q / 2) Q := by
      constructor
      · linarith [hsSlabAbs.1]
      · linarith [hsSlabAbs.2]

    let sSlab :
        Set.Icc (Q / 2) Q :=
      ⟨s - t₀, hsSlab⟩

    have hBridge :=
      h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab_eq_terminalPhysicalVelocityThirdQFourierL2At
        hH3
        hClass
        hNS
        ht₀
        hE
        hTail
        hPhysical
        hQ
        hQR
        hsClass
        hsS
        hsSlab
        j

    have hPhysicalAt :
        Vphysical s
          =
        h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At
          hH3 hClass hsClass j := by
      dsimp only [Vphysical]
      exact
        h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path_eq
          hH3 hClass hsClass j

    have hSelectedAt :
        Vselected s
          =
        Vclosed sSlab := by

      dsimp only [Vselected]

      rw [
        Set.IccExtend_of_mem
          (by linarith : Q / 2 ≤ Q)
          Vclosed
          hsSlab
      ]

    calc
      Vphysical s
          =
        h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2At
          hH3 hClass hsClass j :=
        hPhysicalAt
      _ =
        h3PreterminalSelectedSixthDiffusionVelocityFourierL2OnSlab
          hNS ht₀ hE hTail hQ hQR j sSlab := by
        exact hBridge.symm
      _ =
        Vselected s := by
        exact hSelectedAt.symm

  have hPhysicalDerivative :
      HasDerivAt
        Vphysical
        W
        r :=
    hSelectedAbsolute.congr_of_eventuallyEq
      hEventuallyEq

  have hDeriv :
      deriv Vphysical r = W :=
    hPhysicalDerivative.deriv

  unfold
    h3TerminalResolvedSixthDiffusionPDERHS

  dsimp only [Vphysical, W, xSlab, x] at hDeriv ⊢

  exact hDeriv

end

end Euclidean
end Bridge
end PrimeTensor
