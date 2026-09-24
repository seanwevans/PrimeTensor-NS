import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.One.Selected.Relative.Strong.L2.Reduction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

/-!
# Close selected order-one strong L² differentiation from coefficient continuity

The preceding checkpoints have established:

* every selected first spatial jet is a canonical `H3ScalarL2` state;
* its literal mixed temporal derivative is also a canonical `H3ScalarL2`
  state at every strict restart time;
* every compact smooth scalar test sees the correct derivative of the first
  jet;
* compact smooth scalar tests are dense in physical scalar `L²`;
* elapsed-time strong differentiation is sufficient for the absolute-time
  order-one H³ energy identity.

Consequently only one topology remains: strong `H3ScalarL2` continuity of the
packaged mixed temporal coefficient on the open restart interval.

This file proves that this continuity is sufficient.

At a target elapsed time `q`, choose a compact interval

    [a,b] = [q/2, (q+R)/2] ⊂ (0,R).

The coefficient path on `(0,R)` is restricted to `[a,b]` and extended to all
real times with `Set.IccExtend`; this gives a globally continuous
`H3ScalarL2` path `Y` which agrees with the genuine coefficient throughout
`[a,b]`.

For each compact scalar weak test `φ`, the weak first-jet theorem and the
Hilbert representative bridges give

    d/ds ⟪φ, X(s)⟫ = ⟪φ, Y(s)⟫

on `[a,b]`. Scalar FTC and commutation of a fixed Hilbert pairing with the
Bochner interval integral imply

    ⟪φ, X(y)-X(a)⟫
      =
    ⟪φ, ∫_a^y Y(s) ds⟫.

Scalar weak-test density then upgrades this to the exact Hilbert evolution

    X(y)-X(a) = ∫_a^y Y(s) ds.

Finally the Banach-valued FTC differentiates the right-hand side at `q`.
Thus coefficient continuity closes the genuine strong selected first-jet
derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderOneSelectedStrongL2FromCoefficientContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderOneSelectedStrongL2FromCoefficientContinuity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The only remaining order-one analytic frontier: the canonical physical
`L²` mixed temporal coefficient is strongly continuous on the open selected
restart interval. -/
def H3CanonicalSelectedOrder1RelativeTemporalScalarL2ContinuousOnRestartRadius : Prop :=
  ∀
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t₀ : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (j i : PrimeTensor.Axis Depth.three),
      Continuous
        (fun q :
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) =>
          h3PreterminalSelectedFirstJetRelativeTemporalScalarL2At
            h3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius_closed
            hNS ht₀ hE hTail q.property j i)

/-- For a spectral coordinate, the canonical first-jet `L²` pairing is exactly
the literal selected weak first-jet coordinate pairing. -/
theorem inner_h3WeakTestFunctionPhysicalL2_selectedFirstJetScalarL2At_eq_weakFirstJetPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (φ : H3WeakTestFunction)
    (j : Fin 3)
    (a : PrimeTensor.Axis Depth.three) :
    inner ℝ
        (h3WeakTestFunctionPhysicalL2 φ)
        (h3PreterminalSelectedFirstJetScalarL2At
          hNS ht₀ hE hTail r (h3AxisOfFin3 j) a)
      =
    h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal
      hNS ht₀ hE hTail φ j a r := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht₀ hE hTail

  have hField :
      (fun x : Point3 =>
        ((h3PreterminalSelectedWeakStrongVelocity
          (one_pos : (0 : ℝ) < 1)
          hNS ht₀ hE hTail)
          r x).component (h3AxisOfFin3 j))
        =
      h3SpectralScalarRealC1RepresentativeOnPoint3
        (W r j) := by
    funext x

    dsimp only [
      W,
      h3PreterminalTailCanonicalSelectedRestart
    ]

    unfold h3PreterminalSelectedWeakStrongVelocity

    simp only [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
      h3SpectralVelocityRealC1RepresentativeOnPoint3,
      h3PreterminalTailCanonicalAnchorSpectralState,
      h3PreterminalSelectedDecoderAnchorState
    ]

  rw [h3WeakTestFunctionPhysicalL2_inner_eq_integral]

  unfold h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal
  dsimp only [W]

  apply integral_congr_ae

  filter_upwards [
    h3PreterminalSelectedFirstJetScalarL2At_ae
      hNS ht₀ hE hTail r (h3AxisOfFin3 j) a
  ] with x hx

  rw [hx, hField]

/-- The canonical mixed temporal `L²` coefficient pairing is exactly the
literal selected weak mixed first-jet pairing. -/
theorem inner_h3WeakTestFunctionPhysicalL2_selectedFirstJetRelativeTemporalScalarL2At_eq_weakTemporalPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (hq :
      q ∈ Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (φ : H3WeakTestFunction)
    (j : Fin 3)
    (a : PrimeTensor.Axis Depth.three) :
    inner ℝ
        (h3WeakTestFunctionPhysicalL2 φ)
        (h3PreterminalSelectedFirstJetRelativeTemporalScalarL2At
          h3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius_closed
          hNS ht₀ hE hTail hq (h3AxisOfFin3 j) a)
      =
    h3PreterminalSelectedUnitWeakFirstJetTemporalCoordinatePairingReal
      hNS ht₀ hE hTail φ j a q := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht₀ hE hTail

  have hSpaceTime :
      (fun r : ℝ =>
        fun x : Point3 =>
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalSelectedDecoderAnchorState
              hNS ht₀ hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalSelectedDecoderAnchorState_le
              hNS ht₀ hE hTail)
            r x).component (h3AxisOfFin3 j))
        =
      (fun r : ℝ =>
        h3SpectralScalarRealC1RepresentativeOnPoint3
          (W r j)) := by
    funext r x

    dsimp only [
      W,
      h3PreterminalTailCanonicalSelectedRestart
    ]

    simp only [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
      h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
      h3SpectralVelocityRealC1RepresentativeOnPoint3,
      h3PreterminalTailCanonicalAnchorSpectralState,
      h3PreterminalSelectedDecoderAnchorState
    ]

  have hMixed :
      spatial3.d
          a
          (fun y : Point3 =>
            temporal.d
              (fun r : ℝ =>
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                  (one_pos : (0 : ℝ) < 1)
                  (h3PreterminalSelectedDecoderAnchorState
                    hNS ht₀ hTail)
                  (lt_of_lt_of_le zero_lt_one hE)
                  (norm_h3PreterminalSelectedDecoderAnchorState_le
                    hNS ht₀ hE hTail)
                  r y).component (h3AxisOfFin3 j))
              q)
        =
      spatial3.d
          a
          (fun y : Point3 =>
            temporal.d
              (fun r : ℝ =>
                h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W r j)
                  y)
              q) := by
    congr 1
    funext y

    have hPath :
        (fun r : ℝ =>
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalSelectedDecoderAnchorState
              hNS ht₀ hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalSelectedDecoderAnchorState_le
              hNS ht₀ hE hTail)
            r y).component (h3AxisOfFin3 j))
          =
        (fun r : ℝ =>
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (W r j)
            y) := by
      funext r
      exact congrFun (congrFun hSpaceTime r) y

    rw [hPath]

  rw [h3WeakTestFunctionPhysicalL2_inner_eq_integral]

  unfold
    h3PreterminalSelectedUnitWeakFirstJetTemporalCoordinatePairingReal

  dsimp only [W]

  apply integral_congr_ae

  filter_upwards [
    h3PreterminalSelectedFirstJetRelativeTemporalScalarL2At_ae
      h3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius_closed
      hNS ht₀ hE hTail hq (h3AxisOfFin3 j) a
  ] with x hx

  rw [hx, hMixed]

/-- Strong continuity of the packaged mixed coefficient implies the genuine
restart-relative strong `L²` derivative of every selected first jet. -/
theorem h3CanonicalSelectedOrder1RelativePhysicalL2StrongDerivativeOnRestartRadius_of_temporalCoefficientContinuous
    (hContinuous :
      H3CanonicalSelectedOrder1RelativeTemporalScalarL2ContinuousOnRestartRadius) :
    H3CanonicalSelectedOrder1RelativePhysicalL2StrongDerivativeOnRestartRadius := by
  intro E u T t₀ hNS ht₀ hE hTail
  intro q hq
  intro j a

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  let jf : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have hAxis :
      h3AxisOfFin3 jf = j := by
    dsimp only [jf]
    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis j

  let left : ℝ :=
    q / 2

  let right : ℝ :=
    (q + R) / 2

  let tau : ℝ :=
    (right + R) / 2

  have hq0 : 0 < q := hq.1

  have hqR : q < R := by
    simpa only [R] using hq.2

  have hR0 : 0 < R :=
    lt_trans hq0 hqR

  have hleft0 : 0 < left := by
    dsimp only [left]
    linarith

  have hleftq : left < q := by
    dsimp only [left]
    linarith

  have hqright : q < right := by
    dsimp only [right]
    linarith

  have hrightR : right < R := by
    dsimp only [right]
    linarith

  have hleftright : left ≤ right := by
    exact (hleftq.trans hqright).le

  have hrighttau : right < tau := by
    dsimp only [tau]
    linarith

  have htauR : tau ≤ R := by
    dsimp only [tau]
    linarith

  have htau0 : 0 < tau :=
    lt_trans hleft0
      (lt_trans
        (hleftq.trans hqright)
        hrighttau)

  let openCoefficient :
      Set.Ioo (0 : ℝ) R → H3ScalarL2 :=
    fun s =>
      h3PreterminalSelectedFirstJetRelativeTemporalScalarL2At
        h3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius_closed
        hNS ht₀ hE hTail
        (by
          simpa only [R] using s.property)
        (h3AxisOfFin3 jf)
        a

  have hOpenContinuous :
      Continuous openCoefficient := by
    dsimp only [openCoefficient, R]
    exact
      hContinuous
        E u T t₀ hNS ht₀ hE hTail
        (h3AxisOfFin3 jf) a

  let closedToOpen :
      Set.Icc left right →
        Set.Ioo (0 : ℝ) R :=
    fun s =>
      ⟨(s : ℝ),
        lt_of_lt_of_le hleft0 s.property.1,
        lt_of_le_of_lt s.property.2 hrightR⟩

  have hClosedToOpenContinuous :
      Continuous closedToOpen := by
    exact
      Continuous.subtype_mk
        continuous_subtype_val
        _

  let closedCoefficient :
      Set.Icc left right → H3ScalarL2 :=
    fun s =>
      openCoefficient (closedToOpen s)

  have hClosedCoefficientContinuous :
      Continuous closedCoefficient := by
    exact
      hOpenContinuous.comp hClosedToOpenContinuous

  let Y : ℝ → H3ScalarL2 :=
    Set.IccExtend hleftright closedCoefficient

  have hYContinuous :
      Continuous Y := by
    dsimp only [Y]
    exact
      hClosedCoefficientContinuous.Icc_extend'

  have hY_eq
      (s : ℝ)
      (hs : s ∈ Set.Icc left right) :
      Y s
        =
      h3PreterminalSelectedFirstJetRelativeTemporalScalarL2At
        h3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius_closed
        hNS ht₀ hE hTail
        (show
          s ∈ Set.Ioo (0 : ℝ) R
        from
          ⟨lt_of_lt_of_le hleft0 hs.1,
            lt_of_le_of_lt hs.2 hrightR⟩)
        (h3AxisOfFin3 jf)
        a := by
    dsimp only [Y]

    rw [
      Set.IccExtend_of_mem
        hleftright
        closedCoefficient
        hs
    ]

  let X : ℝ → H3ScalarL2 :=
    fun s =>
      h3PreterminalSelectedFirstJetScalarL2At
        hNS ht₀ hE hTail s
        (h3AxisOfFin3 jf)
        a

  have hXPairing
      (φ : H3WeakTestFunction)
      (s : ℝ) :
      inner ℝ
          (h3WeakTestFunctionPhysicalL2 φ)
          (X s)
        =
      h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal
        hNS ht₀ hE hTail φ jf a s := by
    dsimp only [X]

    exact
      inner_h3WeakTestFunctionPhysicalL2_selectedFirstJetScalarL2At_eq_weakFirstJetPairing
        hNS ht₀ hE hTail φ jf a

  have hYPairing
      (φ : H3WeakTestFunction)
      (s : ℝ)
      (hs : s ∈ Set.Icc left right) :
      inner ℝ
          (h3WeakTestFunctionPhysicalL2 φ)
          (Y s)
        =
      h3PreterminalSelectedUnitWeakFirstJetTemporalCoordinatePairingReal
        hNS ht₀ hE hTail φ jf a s := by
    rw [hY_eq s hs]

    exact
      inner_h3WeakTestFunctionPhysicalL2_selectedFirstJetRelativeTemporalScalarL2At_eq_weakTemporalPairing
        hNS ht₀ hE hTail
        ⟨lt_of_lt_of_le hleft0 hs.1,
          by
            simpa only [R] using
              lt_of_le_of_lt hs.2 hrightR⟩
        φ jf a

  have hWeakDerivativeOnClosed
      (φ : H3WeakTestFunction)
      (s : ℝ)
      (hs : s ∈ Set.Icc left right) :
      HasDerivAt
        (h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal
          hNS ht₀ hE hTail φ jf a)
        (h3PreterminalSelectedUnitWeakFirstJetTemporalCoordinatePairingReal
          hNS ht₀ hE hTail φ jf a s)
        s := by
    have hs0 :
        0 < s :=
      lt_of_lt_of_le hleft0 hs.1

    have hstau :
        s < tau :=
      lt_of_le_of_lt hs.2 hrighttau

    exact
      h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal_hasDerivAt
        hNS ht₀ htau0 hE hTail htauR
        ⟨hs0, hstau⟩
        φ jf a

  have hWeakPathContinuousOn
      (φ : H3WeakTestFunction) :
      ContinuousOn
        (h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal
          hNS ht₀ hE hTail φ jf a)
        (Set.Icc left right) := by
    intro s hs

    exact
      (hWeakDerivativeOnClosed φ s hs).continuousAt.continuousWithinAt

  have hEvolution :
      ∀ y : ℝ,
        y ∈ Set.Icc left right →
        X y - X left
          =
        ∫ s in left..y, Y s := by
    intro y hy

    have hlefty : left ≤ y :=
      hy.1

    apply
      h3ScalarL2_eq_of_weakTest_inner_eq_orderOne

    intro φ

    let P : ℝ → ℝ :=
      h3PreterminalSelectedUnitWeakFirstJetCoordinatePairingReal
        hNS ht₀ hE hTail φ jf a

    let G : ℝ → ℝ :=
      fun s =>
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 φ)
          (Y s)

    have hPContinuous :
        ContinuousOn P (Set.Icc left y) := by
      dsimp only [P]

      exact
        (hWeakPathContinuousOn φ).mono
          (Set.Icc_subset_Icc_right hy.2)

    have hGContinuous :
        Continuous G := by
      dsimp only [G]

      exact
        continuous_const.inner hYContinuous

    have hGIntegrable :
        IntervalIntegrable G volume left y :=
      hGContinuous.intervalIntegrable left y

    have hPDeriv :
        ∀ s : ℝ,
          s ∈ Set.Ioo left y →
          HasDerivAt P (G s) s := by
      intro s hs

      have hsClosed :
          s ∈ Set.Icc left right :=
        ⟨hs.1.le, hs.2.le.trans hy.2⟩

      have hWeak :=
        hWeakDerivativeOnClosed φ s hsClosed

      have hCoeff :=
        hYPairing φ s hsClosed

      dsimp only [P, G]

      exact
        hWeak.congr_deriv hCoeff.symm

    have hFTC :
        (∫ s in left..y, G s)
          =
        P y - P left :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        hlefty
        hPContinuous
        hPDeriv
        hGIntegrable

    have hYIntegrable :
        IntervalIntegrable Y volume left y :=
      hYContinuous.intervalIntegrable left y

    let L : H3ScalarL2 →L[ℝ] ℝ :=
      innerSL ℝ (h3WeakTestFunctionPhysicalL2 φ)

    have hComm :
        (∫ s in left..y, L (Y s))
          =
        L (∫ s in left..y, Y s) :=
      L.intervalIntegral_comp_comm hYIntegrable

    calc
      inner ℝ
          (h3WeakTestFunctionPhysicalL2 φ)
          (X y - X left)
          =
        inner ℝ
            (h3WeakTestFunctionPhysicalL2 φ)
            (X y)
          -
        inner ℝ
            (h3WeakTestFunctionPhysicalL2 φ)
            (X left) := by
              rw [inner_sub_right]
      _ =
        P y - P left := by
          rw [
            hXPairing φ y,
            hXPairing φ left
          ]
      _ =
        ∫ s in left..y, G s :=
          hFTC.symm
      _ =
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 φ)
          (∫ s in left..y, Y s) := by
            simpa only [
              G,
              L,
              innerSL_apply_apply
            ] using hComm

  have hqClosed :
      q ∈ Set.Icc left right :=
    ⟨hleftq.le, hqright.le⟩

  have hYIntegrable :
      IntervalIntegrable Y volume left q :=
    hYContinuous.intervalIntegrable left q

  have hYAt :
      ∀ y ∈ Set.Ioo left right,
        ContinuousAt Y y := by
    intro y hy
    exact hYContinuous.continuousAt

  have hYMeasurable :
      StronglyMeasurableAtFilter
        Y
        (𝓝 q)
        (volume : Measure ℝ) := by
    exact
      ContinuousAt.stronglyMeasurableAtFilter
        (μ := (volume : Measure ℝ))
        isOpen_Ioo
        hYAt
        q
        ⟨hleftq, hqright⟩

  have hIntegralDerivative :
      HasDerivAt
        (fun y : ℝ =>
          ∫ s in left..y, Y s)
        (Y q)
        q :=
    intervalIntegral.integral_hasDerivAt_right
      hYIntegrable
      hYMeasurable
      hYContinuous.continuousAt

  let J : ℝ → H3ScalarL2 :=
    fun y =>
      X left + ∫ s in left..y, Y s

  have hJDerivative :
      HasDerivAt J (Y q) q := by
    dsimp only [J]
    exact
      hIntegralDerivative.const_add (X left)

  have hJEq :
      ∀ y ∈ Set.Icc left right,
        J y = X y := by
    intro y hy

    have hEvol :=
      hEvolution y hy

    dsimp only [J]

    rw [← hEvol]

    abel

  have hNeighborhood :
      Set.Icc left right ∈ 𝓝 q :=
    Icc_mem_nhds hleftq hqright

  have hEventuallyEq :
      X =ᶠ[𝓝 q] J := by
    filter_upwards [hNeighborhood] with y hy

    exact
      (hJEq y hy).symm

  have hXDerivative :
      HasDerivAt X (Y q) q :=
    hJDerivative.congr_of_eventuallyEq
      hEventuallyEq

  let D : H3ScalarL2 :=
    h3PreterminalSelectedFirstJetRelativeTemporalScalarL2At
      h3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius_closed
      hNS ht₀ hE hTail hq
      (h3AxisOfFin3 jf)
      a

  have hYq :
      Y q = D := by
    dsimp only [D]

    rw [hY_eq q hqClosed]

  have hDerivativeAxis :
      HasDerivAt
        (fun r : ℝ =>
          h3PreterminalSelectedFirstJetScalarL2At
            hNS ht₀ hE hTail r
            (h3AxisOfFin3 jf)
            a)
        D
        q := by
    dsimp only [X] at hXDerivative

    exact
      hXDerivative.congr_deriv hYq

  have hDae :
      (((D : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      spatial3.d
        a
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                (one_pos : (0 : ℝ) < 1)
                (h3PreterminalSelectedDecoderAnchorState
                  hNS ht₀ hTail)
                (lt_of_lt_of_le zero_lt_one hE)
                (norm_h3PreterminalSelectedDecoderAnchorState_le
                  hNS ht₀ hE hTail)
                r
                y).component (h3AxisOfFin3 jf))
            q)) := by
    dsimp only [D]

    exact
      h3PreterminalSelectedFirstJetRelativeTemporalScalarL2At_ae
        h3CanonicalSelectedOrder1RepeatedThirdVelocityJetMemLp2OnRestartRadius_closed
        hNS ht₀ hE hTail hq
        (h3AxisOfFin3 jf) a

  rw [hAxis] at hDerivativeAxis hDae

  exact
    ⟨D, hDerivativeAxis, hDae⟩

/-- Strong continuity of the mixed first-jet `L²` coefficient closes the
selected order-one scalar energy derivative frontier. -/
theorem h3CanonicalSelectedOrder1EnergyDerivativeOnRestartRadius_of_temporalCoefficientContinuous
    (hContinuous :
      H3CanonicalSelectedOrder1RelativeTemporalScalarL2ContinuousOnRestartRadius) :
    H3CanonicalSelectedOrder1EnergyDerivativeOnRestartRadius := by
  exact
    h3CanonicalSelectedOrder1EnergyDerivativeOnRestartRadius_of_relativePhysicalL2StrongDerivative
      (h3CanonicalSelectedOrder1RelativePhysicalL2StrongDerivativeOnRestartRadius_of_temporalCoefficientContinuous
        hContinuous)

/-- Strong continuity of the mixed first-jet `L²` coefficient closes the
actual old-path order-one H³ energy derivative identity. -/
theorem h3PathEnergyClassProducesOrder1EnergyDerivativeIdentity_of_selectedTemporalCoefficientContinuous
    (hContinuous :
      H3CanonicalSelectedOrder1RelativeTemporalScalarL2ContinuousOnRestartRadius)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) :
    HasDerivAt
      (velocityH3Energy1At u)
      (velocityH3FormalDerivative1At u s)
      s := by
  exact
    h3PathEnergyClassProducesOrder1EnergyDerivativeIdentity_of_selectedRelativePhysicalL2StrongDerivative
      (h3CanonicalSelectedOrder1RelativePhysicalL2StrongDerivativeOnRestartRadius_of_temporalCoefficientContinuous
        hContinuous)
      hH3 hClass hs

end

end Euclidean
end Bridge
end PrimeTensor
