import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderThreeSelectedTemporalL2Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderThreeSelectedWeakThirdJetDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderTwoSelectedStrongL2FromCoefficientContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

/-!
# Close selected order-three strong L² differentiation from coefficient continuity

The selected ordered third spatial jets and their mixed temporal coefficients
are now both packaged in physical `H3ScalarL2`.  The temporal coefficient path
is strongly continuous on the open restart interval, and every compact smooth
test sees the correct weak derivative of the third jet.

The order-two Hilbert-space FTC argument therefore lifts verbatim one order
higher: restrict the continuous coefficient to a compact interval about the
target time, extend it with `Set.IccExtend`, recover the exact Hilbert evolution
from compact-test pairings, and differentiate its Bochner integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathOrderThreeSelectedStrongL2FromCoefficientContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PathOrderThreeSelectedStrongL2FromCoefficientContinuity :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- For a spectral coordinate, the canonical selected third-jet `L²` pairing
is exactly the literal selected weak third-jet coordinate pairing at a strict
positive restart time. -/
theorem inner_h3WeakTestFunctionPhysicalL2_selectedThirdJetScalarL2At_eq_weakThirdJetPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ s tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (φ : H3WeakTestFunction)
    (j : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three) :
    inner ℝ
        (h3WeakTestFunctionPhysicalL2 φ)
        (h3PreterminalSelectedThirdJetScalarL2At
          hNS ht₀ hE hTail s (h3AxisOfFin3 j) a b c)
      =
    h3PreterminalSelectedUnitWeakThirdJetCoordinatePairingReal
      hNS ht₀ hE hTail φ j a b c s := by

  have hsR :
      s ∈ Set.Ioo
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨hs.1, lt_of_lt_of_le hs.2 htauR⟩

  have hWeakLiteral :=
    h3PreterminalSelectedUnitWeakThirdJetCoordinatePairingReal_eq_literal
      hNS ht₀ htau hE hTail htauR hs
      φ j a b c

  rw [h3WeakTestFunctionPhysicalL2_inner_eq_integral]

  have hJetAE :=
    h3PreterminalSelectedThirdJetScalarL2At_ae
      hNS ht₀ hE hTail hsR
      (h3AxisOfFin3 j) a b c

  calc
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (((h3PreterminalSelectedThirdJetScalarL2At
          hNS ht₀ hE hTail s (h3AxisOfFin3 j) a b c :
          H3ScalarL2) : Point3 → ℝ) x)
      ∂volume)
        =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          (spatial3.d a
            (spatial3.d b
              (spatial3.d c
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (h3PreterminalTailCanonicalSelectedRestart
                    (one_pos : (0 : ℝ) < 1)
                    hNS ht₀ hE hTail s j))))
            x)
        ∂volume := by
      apply integral_congr_ae
      filter_upwards [hJetAE] with x hx
      rw [hx]
      simp only [
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
        h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
        h3SpectralVelocityRealC1RepresentativeOnPoint3,
        h3PreterminalTailCanonicalSelectedRestart,
        h3PreterminalTailCanonicalAnchorSpectralState,
        h3PreterminalSelectedDecoderAnchorState
      ]
    _ =
      h3PreterminalSelectedUnitWeakThirdJetCoordinatePairingReal
        hNS ht₀ hE hTail φ j a b c s :=
      hWeakLiteral.symm

/-- The canonical selected order-three temporal `L²` coefficient pairing is
exactly the literal selected weak temporal third-jet pairing. -/
theorem inner_h3WeakTestFunctionPhysicalL2_selectedThirdJetRelativeTemporalScalarL2At_eq_weakTemporalPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ s tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (φ : H3WeakTestFunction)
    (j : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three) :
    inner ℝ
        (h3WeakTestFunctionPhysicalL2 φ)
        (h3PreterminalSelectedThirdJetRelativeTemporalScalarL2At
          hNS ht₀ hE hTail
          ⟨hs.1, lt_of_lt_of_le hs.2 htauR⟩
          (h3AxisOfFin3 j) a b c)
      =
    h3PreterminalSelectedUnitWeakThirdJetTemporalCoordinatePairingReal
      hNS ht₀ hE hTail φ j a b c s := by

  have hCoeffAE :=
    h3PreterminalSelectedThirdJetRelativeTemporalScalarL2At_ae
      hNS ht₀ hE hTail
      ⟨hs.1, lt_of_lt_of_le hs.2 htauR⟩
      (h3AxisOfFin3 j) a b c

  have hWeakLiteral :=
    h3PreterminalSelectedUnitWeakThirdJetTemporalCoordinatePairingReal_eq_literal
      hNS ht₀ htau hE hTail htauR hs
      φ j a b c

  rw [h3WeakTestFunctionPhysicalL2_inner_eq_integral]

  calc
    (∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ x)
        (((h3PreterminalSelectedThirdJetRelativeTemporalScalarL2At
          hNS ht₀ hE hTail
          ⟨hs.1, lt_of_lt_of_le hs.2 htauR⟩
          (h3AxisOfFin3 j) a b c :
          H3ScalarL2) : Point3 → ℝ) x)
      ∂volume)
        =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          (spatial3.d a
            (spatial3.d b
              (spatial3.d c
                (fun y : Point3 =>
                  temporal.d
                    (fun r : ℝ =>
                      h3SpectralScalarRealC1RepresentativeOnPoint3
                        (h3PreterminalTailCanonicalSelectedRestart
                          (one_pos : (0 : ℝ) < 1)
                          hNS ht₀ hE hTail r j)
                        y)
                    s)))
            x)
        ∂volume := by
      apply integral_congr_ae
      filter_upwards [hCoeffAE] with x hx
      rw [hx]
      simp only [
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity,
        h3SpectralRealVelocityOfPath_component_h3AxisOfFin3,
        h3SpectralVelocityRealC1RepresentativeOnPoint3,
        h3PreterminalTailCanonicalSelectedRestart,
        h3PreterminalTailCanonicalAnchorSpectralState,
        h3PreterminalSelectedDecoderAnchorState
      ]
    _ =
      h3PreterminalSelectedUnitWeakThirdJetTemporalCoordinatePairingReal
        hNS ht₀ hE hTail φ j a b c s :=
      hWeakLiteral.symm

/-- Strong continuity of the packaged order-three mixed coefficient implies the
genuine restart-relative strong `L²` derivative of every selected third jet. -/
theorem h3CanonicalSelectedOrder3RelativePhysicalL2StrongDerivativeOnRestartRadius_of_temporalCoefficientContinuous
    (hContinuous :
      H3CanonicalSelectedOrder3RelativeTemporalScalarL2ContinuousOnRestartRadius) :
    H3CanonicalSelectedOrder3RelativePhysicalL2StrongDerivativeOnRestartRadius := by

  intro E u T t₀ hNS ht₀ hE hTail
  intro q hq
  intro j a b c

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  let jf : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have hAxis :
      h3AxisOfFin3 jf = j := by
    dsimp only [jf]
    exact h3AxisOfFin3_h3ClassicalizationFinOfAxis j

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
      h3PreterminalSelectedThirdJetRelativeTemporalScalarL2At
        hNS ht₀ hE hTail
        (by simpa only [R] using s.property)
        (h3AxisOfFin3 jf) a b c

  have hOpenContinuous :
      Continuous openCoefficient := by
    dsimp only [openCoefficient, R]
    exact
      hContinuous
        E u T t₀ hNS ht₀ hE hTail
        (h3AxisOfFin3 jf) a b c

  let closedToOpen :
      Set.Icc left right →
        Set.Ioo (0 : ℝ) R :=
    fun s =>
      ⟨(s : ℝ),
        lt_of_lt_of_le hleft0 s.property.1,
        lt_of_le_of_lt s.property.2 hrightR⟩

  have hClosedToOpenContinuous :
      Continuous closedToOpen :=
    Continuous.subtype_mk
      continuous_subtype_val
      _

  let closedCoefficient :
      Set.Icc left right → H3ScalarL2 :=
    fun s =>
      openCoefficient (closedToOpen s)

  have hClosedCoefficientContinuous :
      Continuous closedCoefficient :=
    hOpenContinuous.comp hClosedToOpenContinuous

  let Y : ℝ → H3ScalarL2 :=
    Set.IccExtend hleftright closedCoefficient

  have hYContinuous :
      Continuous Y := by
    dsimp only [Y]
    exact hClosedCoefficientContinuous.Icc_extend'

  have hY_eq
      (s : ℝ)
      (hs : s ∈ Set.Icc left right) :
      Y s
        =
      h3PreterminalSelectedThirdJetRelativeTemporalScalarL2At
        hNS ht₀ hE hTail
        (show
          s ∈ Set.Ioo (0 : ℝ) R
        from
          ⟨lt_of_lt_of_le hleft0 hs.1,
            lt_of_le_of_lt hs.2 hrightR⟩)
        (h3AxisOfFin3 jf) a b c := by

    dsimp only [Y]

    rw [
      Set.IccExtend_of_mem
        hleftright
        closedCoefficient
        hs
    ]

  let X : ℝ → H3ScalarL2 :=
    fun s =>
      h3PreterminalSelectedThirdJetScalarL2At
        hNS ht₀ hE hTail s
        (h3AxisOfFin3 jf) a b c

  have hXPairing
      (φ : H3WeakTestFunction)
      (s : ℝ)
      (hs : s ∈ Set.Icc left right) :
      inner ℝ
          (h3WeakTestFunctionPhysicalL2 φ)
          (X s)
        =
      h3PreterminalSelectedUnitWeakThirdJetCoordinatePairingReal
        hNS ht₀ hE hTail φ jf a b c s := by

    dsimp only [X]

    exact
      inner_h3WeakTestFunctionPhysicalL2_selectedThirdJetScalarL2At_eq_weakThirdJetPairing
        hNS ht₀ htau0 hE hTail
        (by simpa only [R] using htauR)
        ⟨lt_of_lt_of_le hleft0 hs.1,
          lt_of_le_of_lt hs.2 hrighttau⟩
        φ jf a b c

  have hYPairing
      (φ : H3WeakTestFunction)
      (s : ℝ)
      (hs : s ∈ Set.Icc left right) :
      inner ℝ
          (h3WeakTestFunctionPhysicalL2 φ)
          (Y s)
        =
      h3PreterminalSelectedUnitWeakThirdJetTemporalCoordinatePairingReal
        hNS ht₀ hE hTail φ jf a b c s := by

    rw [hY_eq s hs]

    exact
      inner_h3WeakTestFunctionPhysicalL2_selectedThirdJetRelativeTemporalScalarL2At_eq_weakTemporalPairing
        hNS ht₀ htau0 hE hTail
        (by simpa only [R] using htauR)
        ⟨lt_of_lt_of_le hleft0 hs.1,
          lt_of_le_of_lt hs.2 hrighttau⟩
        φ jf a b c

  have hWeakDerivativeOnClosed
      (φ : H3WeakTestFunction)
      (s : ℝ)
      (hs : s ∈ Set.Icc left right) :
      HasDerivAt
        (h3PreterminalSelectedUnitWeakThirdJetCoordinatePairingReal
          hNS ht₀ hE hTail φ jf a b c)
        (h3PreterminalSelectedUnitWeakThirdJetTemporalCoordinatePairingReal
          hNS ht₀ hE hTail φ jf a b c s)
        s := by

    exact
      h3PreterminalSelectedUnitWeakThirdJetCoordinatePairingReal_hasDerivAt
        hNS ht₀ htau0 hE hTail
        (by simpa only [R] using htauR)
        ⟨lt_of_lt_of_le hleft0 hs.1,
          lt_of_le_of_lt hs.2 hrighttau⟩
        φ jf a b c

  have hWeakPathContinuousOn
      (φ : H3WeakTestFunction) :
      ContinuousOn
        (h3PreterminalSelectedUnitWeakThirdJetCoordinatePairingReal
          hNS ht₀ hE hTail φ jf a b c)
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

    apply h3ScalarL2_eq_of_weakTest_inner_eq_orderOne

    intro φ

    let P : ℝ → ℝ :=
      h3PreterminalSelectedUnitWeakThirdJetCoordinatePairingReal
        hNS ht₀ hE hTail φ jf a b c

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

      exact hWeak.congr_deriv hCoeff.symm

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
            hXPairing φ y hy,
            hXPairing φ left ⟨le_rfl, hleftright⟩
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
    h3PreterminalSelectedThirdJetRelativeTemporalScalarL2At
      hNS ht₀ hE hTail hq
      (h3AxisOfFin3 jf) a b c

  have hYq :
      Y q = D := by
    dsimp only [D]

    rw [hY_eq q hqClosed]

  have hDerivativeAxis :
      HasDerivAt
        (fun r : ℝ =>
          h3PreterminalSelectedThirdJetScalarL2At
            hNS ht₀ hE hTail r
            (h3AxisOfFin3 jf) a b c)
        D
        q := by

    dsimp only [X] at hXDerivative

    exact
      hXDerivative.congr_deriv hYq

  have hDae :
      (((D : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      spatial3.d a
        (spatial3.d b
          (spatial3.d c
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
                    r y).component (h3AxisOfFin3 jf))
                q)))) := by

    dsimp only [D]

    exact
      h3PreterminalSelectedThirdJetRelativeTemporalScalarL2At_ae
        hNS ht₀ hE hTail hq
        (h3AxisOfFin3 jf) a b c

  rw [hAxis] at hDerivativeAxis hDae

  exact
    ⟨D, hDerivativeAxis, hDae⟩

/-- Strong continuity of the selected order-three temporal coefficient closes
the relative order-three scalar energy derivative frontier. -/
theorem h3CanonicalSelectedOrder3RelativeEnergyDerivativeOnRestartRadius_of_temporalCoefficientContinuous
    (hContinuous :
      H3CanonicalSelectedOrder3RelativeTemporalScalarL2ContinuousOnRestartRadius) :
    H3CanonicalSelectedOrder3RelativeEnergyDerivativeOnRestartRadius := by

  exact
    h3CanonicalSelectedOrder3RelativeEnergyDerivativeOnRestartRadius_of_physicalL2StrongDerivative
      (h3CanonicalSelectedOrder3RelativePhysicalL2StrongDerivativeOnRestartRadius_of_temporalCoefficientContinuous
        hContinuous)

/-- The closed order-three coefficient continuity theorem supplies the genuine
strong selected third-jet `L²` derivative frontier. -/
theorem h3CanonicalSelectedOrder3RelativePhysicalL2StrongDerivativeOnRestartRadius_closed :
    H3CanonicalSelectedOrder3RelativePhysicalL2StrongDerivativeOnRestartRadius := by

  exact
    h3CanonicalSelectedOrder3RelativePhysicalL2StrongDerivativeOnRestartRadius_of_temporalCoefficientContinuous
      h3CanonicalSelectedOrder3RelativeTemporalScalarL2ContinuousOnRestartRadius_closed

/-- The closed order-three coefficient continuity theorem also closes the
selected relative order-three scalar energy derivative. -/
theorem h3CanonicalSelectedOrder3RelativeEnergyDerivativeOnRestartRadius_closed :
    H3CanonicalSelectedOrder3RelativeEnergyDerivativeOnRestartRadius := by

  exact
    h3CanonicalSelectedOrder3RelativeEnergyDerivativeOnRestartRadius_of_temporalCoefficientContinuous
      h3CanonicalSelectedOrder3RelativeTemporalScalarL2ContinuousOnRestartRadius_closed

end

end Euclidean
end Bridge
end PrimeTensor
