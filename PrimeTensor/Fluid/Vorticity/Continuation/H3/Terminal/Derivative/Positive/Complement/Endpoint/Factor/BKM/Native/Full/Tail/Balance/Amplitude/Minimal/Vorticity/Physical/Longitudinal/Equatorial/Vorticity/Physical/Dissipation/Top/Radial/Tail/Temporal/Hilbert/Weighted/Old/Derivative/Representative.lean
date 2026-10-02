import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Derivative.Closure

/-!
# Physical PDE representative of the fourth-radial Hilbert derivative

The global physical `q² û_j` derivative is already closed.  This file records
its literal Fourier representative.

At every strict physical time,

    d/dt (q² û_j)
      =
    -q³ û_j - q² F_j(U,U)

almost everywhere in Fourier space, where `U` is the canonical terminal
strict-time spectral state.

The proof reuses the same local selected restart germ used in the derivative
closure, then identifies its selected spectral state with the canonical old
state and finally with `h3TerminalVelocitySpectralStateAt`.

A corollary uses uniqueness of `HasDerivAt` to give the same representative for
*any* proposed derivative value of the physical fourth-radial path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailWeightedDerivativeRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 3000000

/--
The ordinary derivative of the terminal physical fourth-radial `L²` path has
the exact unit-viscosity Fourier Navier--Stokes representative.
-/
theorem h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_deriv_ae_unitPDE
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
    (
      (
        deriv
          (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass j)
          t :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      (-(h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
          *
        (
          h3SpectralScalarRawFourierL2
            (U j)
        ) ξ
        -
      ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        h3RawFinLerayOuterProductDivergence
          U U j ξ) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let Uterm : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  rcases
    hH3.exists_localCanonicalRestartWindowAt htAbs
  with
    ⟨
      t₀,
      S,
      E,
      ht₀,
      hST,
      hE,
      hTail,
      hGap0,
      hGapR,
      hTarget,
      htS
    ⟩

  have hS :
      0 < S :=
    lt_trans ht₀.1 ht₀.2

  have hNSShort :
      LoggedPreterminalNavierStokesAdmissible u S :=
    loggedPreterminalNavierStokesAdmissible_mono_terminal
      hH3.navier_stokes
      hS
      (le_of_lt hST)

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  have hR :
      0 < R := by
    dsimp only [R]
    exact
      h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
        (one_pos : (0 : ℝ) < 1)
        hE

  let δ : ℝ :=
    min
      (R / 2)
      ((t - t₀) / 2)

  have hGapHalf :
      0 < (t - t₀) / 2 := by
    linarith [hGap0]

  have hRHalf :
      0 < R / 2 := by
    linarith

  have hδ0 :
      0 < δ := by
    dsimp only [δ]
    exact
      lt_min
        hRHalf
        hGapHalf

  have hδRHalf :
      δ ≤ R / 2 := by
    dsimp only [δ]
    exact min_le_left _ _

  have hδGapHalf :
      δ ≤ (t - t₀) / 2 := by
    dsimp only [δ]
    exact min_le_right _ _

  let t₁ : ℝ :=
    t - δ

  have ht₀t₁ :
      t₀ ≤ t₁ := by
    dsimp only [t₁]
    linarith [hδGapHalf]

  have ht₁t :
      t₁ < t := by
    dsimp only [t₁]
    linarith [hδ0]

  have ht₁S :
      t₁ < S :=
    lt_trans ht₁t htS

  have ht₁0 :
      0 < t₁ :=
    lt_of_lt_of_le
      ht₀.1
      ht₀t₁

  have ht₁ :
      t₁ ∈ Set.Ioo (0 : ℝ) S :=
    ⟨ht₁0, ht₁S⟩

  have hTail₁ :
      CanonicalH3TailDataFrom u t₁ S E :=
    canonicalH3TailDataFrom_mono_start
      ht₀t₁
      ht₁S
      hTail

  let q : ℝ :=
    t - t₁

  have hqδ :
      q = δ := by
    dsimp only [q, t₁]
    ring

  have hq0 :
      0 < q := by
    rw [hqδ]
    exact hδ0

  have hqRHalf :
      q ≤ R / 2 := by
    rw [hqδ]
    exact hδRHalf

  have hqR :
      q ≤ R := by
    exact
      hqRHalf.trans
        (by linarith [hR])

  have htq :
      t₁ + q = t := by
    dsimp only [q]
    ring

  have hEnd :
      t₁ + q < S := by
    rw [htq]
    exact htS

  let Q : ℝ :=
    3 * q / 2

  have hQ :
      0 < Q := by
    dsimp only [Q]
    linarith [hq0]

  have hqLower :
      Q / 2 < q := by
    dsimp only [Q]
    linarith [hq0]

  have hqUpper :
      q < Q := by
    dsimp only [Q]
    linarith [hq0]

  have hQR :
      Q < R := by
    have hThreeQuarter :
        3 * R / 4 < R := by
      linarith [hR]

    have hQLe :
        Q ≤ 3 * R / 4 := by
      dsimp only [Q]
      linarith [hqRHalf]

    exact
      lt_of_le_of_lt
        hQLe
        hThreeQuarter

  have hWeakFTC :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
        E u S t₁ hNSShort ht₁ hE hTail₁ :=
    H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_tailH3_curl
      E hE u S t₁ hNSShort ht₁ hTail₁

  have hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u S t₁ hNSShort ht₁ hE hTail₁ :=
    h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_projectedRHSWeakFTC
      hNSShort
      ht₁
      hE
      hTail₁
      hWeakFTC

  let qSlab :
      Set.Icc (Q / 2) Q :=
    ⟨q, hqLower.le, hqUpper.le⟩

  let W :
      H3FourierComplexL2 :=
    h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab
      hNSShort ht₁ hE hTail₁ hQ hQR j qSlab

  let Vclosed :
      Set.Icc (Q / 2) Q →
        H3FourierComplexL2 :=
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
      hNSShort ht₁ hE hTail₁ hQ hQR j

  let Vselected :
      ℝ → H3FourierComplexL2 :=
    fun r =>
      Set.IccExtend
        (by linarith : Q / 2 ≤ Q)
        Vclosed
        (r - t₁)

  let Vphysical :
      ℝ → H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
      hH3 hClass j

  have hRelative :=
    h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_hasDerivAt
      hNSShort
      ht₁
      hE
      hTail₁
      hQ
      hQR
      j
      ⟨hqLower, hqUpper⟩

  have hShift :
      HasDerivAt
        (fun r : ℝ => r - t₁)
        1
        t := by
    simpa using
      (hasDerivAt_id t).sub_const t₁

  have hSelectedAbsolute :
      HasDerivAt
        Vselected
        W
        t := by

    have hComp :=
      hRelative.scomp
        t
        hShift

    dsimp only [Vselected, Vclosed, W, qSlab, q] at hComp ⊢

    simpa only [
      Function.comp_def,
      one_smul
    ] using hComp

  have hClassNeighborhood :
      Set.Ioo a T ∈ 𝓝 t :=
    Ioo_mem_nhds
      ht.1
      ht.2

  have hSlabLeft :
      t₁ + Q / 2 < t := by
    linarith [htq, hqLower]

  have hSlabRight :
      t < t₁ + Q := by
    linarith [htq, hqUpper]

  have hSlabNeighborhood :
      Set.Ioo
          (t₁ + Q / 2)
          (t₁ + Q)
        ∈
      𝓝 t :=
    Ioo_mem_nhds
      hSlabLeft
      hSlabRight

  have hSNeighborhood :
      Set.Iio S ∈ 𝓝 t :=
    Iio_mem_nhds htS

  have hEventuallyEq :
      Vphysical =ᶠ[𝓝 t] Vselected := by

    filter_upwards [
      hClassNeighborhood,
      hSlabNeighborhood,
      hSNeighborhood
    ] with r hrClass hrSlabAbs hrS

    have hrSlab :
        r - t₁ ∈ Set.Icc (Q / 2) Q := by
      constructor
      · linarith [hrSlabAbs.1]
      · linarith [hrSlabAbs.2]

    let rSlab :
        Set.Icc (Q / 2) Q :=
      ⟨r - t₁, hrSlab⟩

    have hBridge :=
      h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab_eq_terminalPhysicalFourthRadialL2At
        hH3
        hClass
        hNSShort
        ht₁
        hE
        hTail₁
        hPhysical
        hQ
        hQR
        hrClass
        hrS
        hrSlab
        j

    have hPhysicalAt :
        Vphysical r
          =
        h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
          hH3 hClass hrClass j := by
      dsimp only [Vphysical]
      exact
        h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_eq
          hH3 hClass hrClass j

    have hSelectedAt :
        Vselected r
          =
        Vclosed rSlab := by

      dsimp only [Vselected]

      rw [
        Set.IccExtend_of_mem
          (by linarith : Q / 2 ≤ Q)
          Vclosed
          hrSlab
      ]

    calc
      Vphysical r
          =
        h3TerminalPhysicalTopDissipationFourthRadialComponentL2At
          hH3 hClass hrClass j :=
        hPhysicalAt
      _ =
        h3PreterminalSelectedTopTailWeightedVelocityFourierL2OnSlab
          hNSShort ht₁ hE hTail₁ hQ hQR j rSlab := by
        exact hBridge.symm
      _ =
        Vselected r := by
        exact hSelectedAt.symm

  have hPhysicalDerivative :
      HasDerivAt
        Vphysical
        W
        t :=
    hSelectedAbsolute.congr_of_eventuallyEq
      hEventuallyEq

  have hDeriv :
      deriv Vphysical t = W :=
    hPhysicalDerivative.deriv

  let qClosed :
      Set.Icc (0 : ℝ) q :=
    ⟨q, hq0.le, le_rfl⟩

  have hStateOld :=
    h3PreterminalSelectedUnitSpectralStateOnRadius_eq_tailCanonical_of_restartRadiusAgreement
      hNSShort
      ht₁
      hEnd
      hE
      hTail₁
      hqR
      hPhysical
      qClosed
      hq0

  let Usel : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalSelectedDecoderAnchorState
        hNSShort ht₁ hTail₁)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalSelectedDecoderAnchorState_le
        hNSShort ht₁ hE hTail₁)
      q

  let Uold : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNSShort ht₁ hEnd hTail₁ qClosed

  have hSelOld :
      Usel = Uold := by
    dsimp only [Usel, Uold]
    simpa only [
      h3PreterminalSelectedUnitSpectralStateOnRadius,
      h3PreterminalElapsedToSelectedUnitRadius_coe,
      qClosed
    ] using hStateOld

  have hOldTerm :
      Uold = Uterm := by

    dsimp only [Uold, Uterm]

    unfold
      h3PreterminalTailCanonicalSpectralStateOnElapsed
      h3TerminalVelocitySpectralStateAt

    apply
      velocityH3SpectralStateAt_eq_of_time_eq
        u
        htq

  have hSelTerm :
      Usel = Uterm :=
    hSelOld.trans hOldTerm

  have hWAE :=
    h3PreterminalSelectedTopTailWeightedRHSFourierL2OnSlab_ae_gradientSquare
      hNSShort
      ht₁
      hE
      hTail₁
      hQ
      hQR
      j
      qSlab

  rw [hDeriv]

  filter_upwards [hWAE] with ξ hWξ

  rw [hWξ]

  dsimp only [W, qSlab, q] at *

  have hRaw :
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState
            hNSShort ht₁ hTail₁)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNSShort ht₁ hE hTail₁)
          q
          j
        =
      h3SpectralScalarRawFourierL2
        (Uterm j) := by

    unfold
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2

    rw [← hSelTerm]

    rfl

  rw [hRaw]

  change
    (-(h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
          *
        (
          h3SpectralScalarRawFourierL2
            (Uterm j)
        ) ξ
        -
      ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        h3RawFinLerayOuterProductDivergence
          Usel Usel j ξ
      =
    (-(h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
          *
        (
          h3SpectralScalarRawFourierL2
            (Uterm j)
        ) ξ
        -
      ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        h3RawFinLerayOuterProductDivergence
          Uterm Uterm j ξ

  rw [hSelTerm]

/--
Any strong derivative value of the terminal physical fourth-radial path has
the same literal Fourier PDE representative.
-/
theorem h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_derivativeValue_ae_unitPDE
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (W : H3FourierComplexL2)
    (hW :
      HasDerivAt
        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j)
        W
        t) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    (
      (W : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      (-(h3FourierGradientSquare ξ ^ 3 : ℝ) : ℂ)
          *
        (
          h3SpectralScalarRawFourierL2
            (U j)
        ) ξ
        -
      ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ)
          *
        h3RawFinLerayOuterProductDivergence
          U U j ξ) := by

  dsimp only

  have hDeriv :
      deriv
          (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass j)
          t
        =
      W :=
    hW.deriv

  rw [← hDeriv]

  exact
    h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path_deriv_ae_unitPDE
      hH3 hClass ht j

end

end Euclidean
end Bridge
end PrimeTensor
