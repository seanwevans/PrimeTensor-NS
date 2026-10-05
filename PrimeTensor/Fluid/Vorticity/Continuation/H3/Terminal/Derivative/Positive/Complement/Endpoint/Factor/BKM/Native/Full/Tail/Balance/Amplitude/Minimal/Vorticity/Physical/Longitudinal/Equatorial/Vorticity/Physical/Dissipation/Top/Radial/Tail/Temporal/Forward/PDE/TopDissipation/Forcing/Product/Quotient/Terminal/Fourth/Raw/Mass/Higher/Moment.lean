import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Mass.Higher
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.Moment.Third.Seed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.Moment.Nat.Iteration

/-!
# Arbitrary terminal raw Fourier moments at strict times

The selected positive-time mild solution already carries a uniform cubic raw
moment slab.  The natural-moment induction upgrades that slab to every finite
natural order after moving the lower endpoint a finite number of times toward
zero.

At a strict physical time, the local canonical restart window identifies the
selected mild spectral state with the canonical terminal spectral state.
Therefore every natural raw Fourier moment of order at least three is
integrable for every terminal spectral coordinate at every strict preterminal
time.

The order-fourteen specialization is the exact input needed by the radial
order-six Leray estimate for the remaining `q³ F_j` factor.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2200000

noncomputable local instance axisFintypeH3TerminalNaturalMoment
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalNaturalMoment :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
Repeated moment-induction backsteps never move a nonnegative lower endpoint
to the right.
-/
private theorem h3SelectedMomentBackstep_le_self_terminal
    (k : ℕ)
    {a : ℝ}
    (ha : 0 ≤ a) :
    h3SelectedMomentBackstep k a ≤ a := by

  induction k generalizing a with
  | zero =>
      simp [h3SelectedMomentBackstep]

  | succ k ih =>
      rw [h3SelectedMomentBackstep]

      have haQuarter :
          0 ≤ a / 4 := by
        positivity

      have hRec :
          h3SelectedMomentBackstep k (a / 4)
            ≤
          a / 4 :=
        ih haQuarter

      have hQuarter :
          a / 4 ≤ a := by
        linarith

      exact hRec.trans hQuarter

/--
At every strict preterminal time, every natural raw Fourier moment of order at
least three is integrable for every coordinate of the canonical terminal
spectral state.
-/
theorem h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_nat
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (m : ℕ)
    (hm : 3 ≤ m) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ∀ k : Fin 3,
      H3RawFourierMomentIntegrable
        (m : ℝ)
        (U k) := by

  dsimp only

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  rcases
    hH3.exists_localCanonicalRestartWindowAt htAbs
  with
    ⟨t₀, S, E, ht₀, hST, hE, hTail, hGap0, hGapR, hTarget, htS⟩

  have hS : 0 < S :=
    lt_trans ht₀.1 ht₀.2

  have hNSShort :
      LoggedPreterminalNavierStokesAdmissible u S :=
    loggedPreterminalNavierStokesAdmissible_mono_terminal
      hH3.navier_stokes hS hST.le

  have hWeakFTC :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
        E u S t₀ hNSShort ht₀ hE hTail :=
    H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_tailH3_curl
      E hE u S t₀ hNSShort ht₀ hTail

  have hPhysical :
      H3PreterminalSelectedPhysicalAgreementOnRestartRadius
        (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
        u S t₀ hNSShort ht₀ hE hTail :=
    h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_projectedRHSWeakFTC
      hNSShort ht₀ hE hTail hWeakFTC

  let q : ℝ :=
    t - t₀

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  have hq0 :
      0 < q := by
    dsimp only [q]
    exact hGap0

  have hqR :
      q < R := by
    dsimp only [q, R]
    exact hGapR

  /-
  A compact selected overlap slab containing the target elapsed time `q`.
  This is used only to identify the selected and terminal spectral states.
  -/
  let B : ℝ :=
    min (2 * q) R

  let Q : ℝ :=
    (q + B) / 2

  have hqB :
      q < B := by
    dsimp only [B]
    exact
      lt_min
        (by linarith [hq0])
        hqR

  have hB_le_twoq :
      B ≤ 2 * q := by
    dsimp only [B]
    exact min_le_left _ _

  have hB_le_R :
      B ≤ R := by
    dsimp only [B]
    exact min_le_right _ _

  have hQ :
      0 < Q := by
    dsimp only [Q]
    linarith [hq0, hqB]

  have hqUpper :
      q < Q := by
    dsimp only [Q]
    linarith [hqB]

  have hqLower :
      Q / 2 < q := by
    dsimp only [Q]
    linarith [hB_le_twoq, hq0]

  have hQR :
      Q < R := by
    dsimp only [Q]
    linarith [hqR, hB_le_R]

  have hState :=
    h3PreterminalSelectedSpectralStateOnOverlap_eq_terminalVelocitySpectralStateAt
      hH3 hClass hNSShort ht₀ hE hTail hPhysical
      hQ hQR ht htS
      ⟨
        by
          simpa only [q] using hqLower.le,
        by
          simpa only [q] using hqUpper.le
      ⟩

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNSShort ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNSShort ht₀ hE hTail

  let Usel : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ q

  let Uterm : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  have hState' :
      Usel = Uterm := by

    dsimp only [
      Usel,
      Uterm,
      U₀,
      hA,
      hU₀
    ]

    simpa only [q] using hState

  /-
  The cubic selected moment slab is iterated `m-3` times.  We ask for the
  final slab only on `[q/2,q]`; all recursively earlier lower endpoints remain
  positive.
  -/
  let aM : ℝ :=
    q / 2

  let steps : ℕ :=
    m - 3

  have haM0 :
      0 < aM := by
    dsimp only [aM]
    positivity

  have haMq :
      aM ≤ q := by
    dsimp only [aM]
    linarith [hq0]

  have hSeed0 :
      0 <
        h3SelectedMomentBackstep
          steps aM :=
    h3SelectedMomentBackstep_pos
      steps haM0

  have hSeedLeA :
      h3SelectedMomentBackstep
          steps aM
        ≤
      aM :=
    h3SelectedMomentBackstep_le_self_terminal
      steps haM0.le

  have hSeedLeQ :
      h3SelectedMomentBackstep
          steps aM
        ≤
      q :=
    hSeedLeA.trans haMq

  have hSlabThree :=
    h3SelectedMomentSlab_three
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      hSeed0
      hSeedLeQ
      hqR.le

  obtain
    ⟨BStateM, BDuhamelM, hSlabM⟩ :=
    h3SelectedMomentSlab_nat_iterate
      3
      steps
      (by norm_num)
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀
      haM0
      haMq
      hqR.le
      hSlabThree

  have hmNat :
      3 + steps = m := by
    dsimp only [steps]
    omega

  unfold H3SelectedMomentSlab at hSlabM

  rcases hSlabM with
    ⟨_hStateNonneg, _hDuhamelNonneg, _hL1Nonneg, hData⟩

  intro k

  have hSelected :=
    (hData
      q
      ⟨haMq, le_rfl⟩
      k).1

  have hSelected' :
      H3RawFourierMomentIntegrable
        (m : ℝ)
        (Usel k) := by

    dsimp only [Usel]

    simpa only [hmNat] using hSelected

  change
    H3RawFourierMomentIntegrable
      (m : ℝ)
      (Uterm k)

  rw [← hState']

  exact hSelected'

/--
Order fourteen is the exact doubled input moment required by the radial
order-six finite Leray estimate.
-/
theorem h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_fourteen
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U : H3SpectralFinVectorState :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ∀ k : Fin 3,
      H3RawFourierMomentIntegrable
        (14 : ℝ)
        (U k) := by

  exact
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_nat
      hH3 hClass ht 14 (by norm_num)

end

end Euclidean
end Bridge
end PrimeTensor
