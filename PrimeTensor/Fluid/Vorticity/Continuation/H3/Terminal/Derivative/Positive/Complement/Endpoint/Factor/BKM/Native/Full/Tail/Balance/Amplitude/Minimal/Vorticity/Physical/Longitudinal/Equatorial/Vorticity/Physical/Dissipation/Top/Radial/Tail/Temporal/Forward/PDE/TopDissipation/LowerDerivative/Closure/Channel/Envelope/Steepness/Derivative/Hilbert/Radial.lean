import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Seventh.Bound

/-!
# Order-generic selected velocity radial Fourier L² state

The remaining sixth-diffusion derivative frontier requires the PDE derivative

    d/dt (q³ û_j)
      =
    -q⁴ û_j - q³ F_j,

so the next velocity factor is the eighth Euclidean radial raw-Fourier state.
A continuity proof for that eighth-radial state will in turn use one locally
uniform ninth-radial bound.

The repository already contains all the existence ingredients at arbitrary
finite radial order:

* positive free heat absorbs every natural radial multiplier;
* the positive-lag midpoint Duhamel head absorbs every natural radial
  multiplier;
* the terminal-half Duhamel tail belongs to weighted Fourier `L²` at every
  natural order `m ≥ 2`.

The previous files assembled these ingredients separately at orders five,
six, and seven.  This file removes that packaging ceiling.  For every
`m ≥ 2` it defines one quotient-safe selected mild coordinate

    |ξ|^m û_j(t,ξ) ∈ L²

on a positive compact restart slab and proves its literal almost-everywhere
representative.

In particular, the eighth- and ninth-radial selected velocity states now exist
canonically.  No uniform-in-time estimate or temporal differentiability is
asserted here; those are the next analytic steps.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalGenericVelocityRadialState
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 1800000

/-! ## Arbitrary-order terminal tail -/

/--
The quotient-safe selected terminal-half Duhamel tail with natural radial
weight `m ≥ 2`.
-/
noncomputable def h3SelectedDuhamelTailNatRadialFourierL2
    (m : ℕ)
    (hm : 2 ≤ m)
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  (h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_radialWeight_memLp2
      m hm
      hν U₀ hA hU₀ hq hqR i).toLp
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        (((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := q) hν U₀ hA hU₀ i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ))

/--
The generic weighted terminal-tail package has the literal radial
representative.
-/
theorem h3SelectedDuhamelTailNatRadialFourierL2_ae
    (m : ℕ)
    (hm : 2 ≤ m)
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ((h3SelectedDuhamelTailNatRadialFourierL2
        m hm hν U₀ hA hU₀ hq hqR i :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        (((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := q) hν U₀ hA hU₀ i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)) := by

  unfold h3SelectedDuhamelTailNatRadialFourierL2

  exact
    MemLp.coeFn_toLp
      (h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_radialWeight_memLp2
        m hm
        hν U₀ hA hU₀ hq hqR i)

/-! ## Arbitrary-order free heat -/

/--
Selected initial heat with arbitrary natural radial Fourier weight `m` on a
positive compact slab.
-/
noncomputable def h3SelectedInitialHeatNatRadialFourierL2OnCompact
    (m : ℕ)
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  h3HeatRadialFourierL2OfLowerLag
    hν ha q.property.1 m
    (h3SpectralScalarRawFourierL2 (U₀ i))

/--
The generic free-heat package is almost everywhere the literal radial
multiplier applied to the named selected initial heat.
-/
theorem h3SelectedInitialHeatNatRadialFourierL2OnCompact_ae
    (m : ℕ)
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ((h3SelectedInitialHeatNatRadialFourierL2OnCompact
        m hν U₀ hA hU₀ ha q i :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        (((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
            hν U₀
            (lt_of_lt_of_le ha q.property.1)
            i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)) := by

  have hWeighted :=
    h3HeatRadialFourierL2OfLowerLag_ae
      hν ha q.property.1 m
      (h3SpectralScalarRawFourierL2 (U₀ i))

  have hRaw :=
    h3SpectralScalarRawFourierL2_ae
      (U₀ i)

  have hq0 :
      0 < (q : ℝ) :=
    lt_of_lt_of_le ha q.property.1

  have hHeat :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_ae_eq_heatRepresentative
      hν U₀ hq0 i

  unfold h3SelectedInitialHeatNatRadialFourierL2OnCompact

  filter_upwards [hWeighted, hRaw, hHeat]
    with ξ hWeightedξ hRawξ hHeatξ

  rw [hWeightedξ, hHeatξ]

  unfold h3SpectralScalarHeatRawRepresentative

  rw [hRawξ]

/--
The arbitrary-order free-heat package has the expected compact-slab norm
bound.
-/
theorem norm_h3SelectedInitialHeatNatRadialFourierL2OnCompact_le
    (m : ℕ)
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ‖h3SelectedInitialHeatNatRadialFourierL2OnCompact
        m hν U₀ hA hU₀ ha q i‖
      ≤
    h3HeatNatMomentCoefficient m ν a * A := by

  have hHeat :=
    norm_h3HeatRadialFourierL2OfLowerLag_le
      hν ha q.property.1 m
      (h3SpectralScalarRawFourierL2 (U₀ i))

  have hRaw :
      ‖h3SpectralScalarRawFourierL2 (U₀ i)‖ ≤ A := by
    calc
      ‖h3SpectralScalarRawFourierL2 (U₀ i)‖
          ≤
        ‖U₀ i‖ :=
        norm_h3SpectralScalarRawFourierL2_le
          (U₀ i)
      _ ≤
        ‖U₀‖ :=
        h3SpectralVelocity_coordinate_norm_le
          U₀ i
      _ ≤
        A :=
        hU₀

  have hCoeff0 :
      0 ≤ h3HeatNatMomentCoefficient m ν a :=
    h3HeatNatMomentCoefficient_nonneg m ν a

  unfold h3SelectedInitialHeatNatRadialFourierL2OnCompact

  exact
    hHeat.trans
      (mul_le_mul_of_nonneg_left hRaw hCoeff0)

/-! ## Arbitrary-order midpoint Duhamel head -/

/--
Selected midpoint Duhamel head with arbitrary natural radial Fourier weight.
The positive half-lag supplies all finite orders.
-/
noncomputable def h3SelectedDuhamelHeadNatRadialFourierL2OnCompact
    (m : ℕ)
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  let hlag0 : 0 < a / 2 := by
    positivity
  let hlag : a / 2 ≤ (q : ℝ) / 2 := by
    linarith [q.property.1]
  let Dhalf : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := (q : ℝ) / 2) hν U₀ hA hU₀ i
  h3HeatRadialFourierL2OfLowerLag
    hν hlag0 hlag m Dhalf

/--
The arbitrary-order midpoint-head package has its literal weighted
representative.
-/
theorem h3SelectedDuhamelHeadNatRadialFourierL2OnCompact_ae
    (m : ℕ)
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ((h3SelectedDuhamelHeadNatRadialFourierL2OnCompact
        m hν U₀ hA hU₀ ha q i :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        ((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
            hν U₀ hA hU₀
            (lt_of_lt_of_le ha q.property.1)
            i :
          H3FourierComplexL2) ξ)) := by

  let Dhalf : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := (q : ℝ) / 2) hν U₀ hA hU₀ i

  have hq0 :
      0 < (q : ℝ) :=
    lt_of_lt_of_le ha q.property.1

  have hlag0 :
      0 < a / 2 := by
    positivity

  have hlag :
      a / 2 ≤ (q : ℝ) / 2 := by
    linarith [q.property.1]

  have hWeighted :=
    h3HeatRadialFourierL2OfLowerLag_ae
      hν hlag0 hlag m Dhalf

  have hHead :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heat_mul_halfDuhamelRawFourierL2
      hν U₀ hA hU₀ hq0 i

  unfold h3SelectedDuhamelHeadNatRadialFourierL2OnCompact

  filter_upwards [hWeighted, hHead]
    with ξ hWeightedξ hHeadξ

  rw [hWeightedξ, hHeadξ]

/--
The arbitrary-order midpoint-head package has a uniform compact-slab norm
bound.
-/
theorem norm_h3SelectedDuhamelHeadNatRadialFourierL2OnCompact_le
    (m : ℕ)
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ‖h3SelectedDuhamelHeadNatRadialFourierL2OnCompact
        m hν U₀ hA hU₀ ha q i‖
      ≤
    h3HeatNatMomentCoefficient m ν (a / 2) * (3 * A) := by

  let Dhalf : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := (q : ℝ) / 2) hν U₀ hA hU₀ i

  have hq0 :
      0 < (q : ℝ) :=
    lt_of_lt_of_le ha q.property.1

  have hqR :
      (q : ℝ) ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans q.property.2 hbR.le

  have hhalf0 :
      0 < (q : ℝ) / 2 := by
    positivity

  have hhalfR :
      (q : ℝ) / 2 ≤ h3FinHeatLerayRestartRadius ν A := by
    calc
      (q : ℝ) / 2
          ≤
        (q : ℝ) := by
        linarith
      _ ≤
        h3FinHeatLerayRestartRadius ν A :=
        hqR

  have hlag0 :
      0 < a / 2 := by
    positivity

  have hlag :
      a / 2 ≤ (q : ℝ) / 2 := by
    linarith [q.property.1]

  have hHeat :
      ‖h3HeatRadialFourierL2OfLowerLag
          hν hlag0 hlag m Dhalf‖
        ≤
      h3HeatNatMomentCoefficient m ν (a / 2) *
        ‖Dhalf‖ :=
    norm_h3HeatRadialFourierL2OfLowerLag_le
      hν hlag0 hlag m Dhalf

  have hD :
      ‖Dhalf‖ ≤ 3 * A := by
    dsimp only [Dhalf]
    exact
      norm_h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_le_threeA
        hν U₀ hA hU₀ hhalf0 hhalfR i

  have hCoeff0 :
      0 ≤ h3HeatNatMomentCoefficient m ν (a / 2) :=
    h3HeatNatMomentCoefficient_nonneg
      m ν (a / 2)

  unfold h3SelectedDuhamelHeadNatRadialFourierL2OnCompact

  exact
    hHeat.trans
      (mul_le_mul_of_nonneg_left hD hCoeff0)

/-! ## Arbitrary-order selected mild state -/

/--
Local quotient-safe selected mild velocity coordinate at arbitrary natural
radial order `m ≥ 2`.
-/
noncomputable def h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
    (m : ℕ)
    (hm : 2 ≤ m)
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (q : Set.Icc a b)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  h3SelectedInitialHeatNatRadialFourierL2OnCompact
      m hν U₀ hA hU₀ ha q i
    -
  h3SelectedDuhamelHeadNatRadialFourierL2OnCompact
      m hν U₀ hA hU₀ ha q i
    -
  h3SelectedDuhamelTailNatRadialFourierL2
      m hm
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      i

/--
The generic selected mild package is almost everywhere exactly
`|ξ|^m` times the selected mild raw Fourier coordinate.
-/
theorem h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact_ae
    (m : ℕ)
    (hm : 2 ≤ m)
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ((h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
        m hm hν U₀ hA hU₀ ha hbR q i :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        (((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
            hν U₀ hA hU₀ (q : ℝ) i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)) := by

  let Hm : H3FourierComplexL2 :=
    h3SelectedInitialHeatNatRadialFourierL2OnCompact
      m hν U₀ hA hU₀ ha q i

  let DmHead : H3FourierComplexL2 :=
    h3SelectedDuhamelHeadNatRadialFourierL2OnCompact
      m hν U₀ hA hU₀ ha q i

  let DmTail : H3FourierComplexL2 :=
    h3SelectedDuhamelTailNatRadialFourierL2
      m hm
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      i

  let W0 : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
      hν U₀ hA hU₀ (q : ℝ) i

  let H0 : H3FourierComplexL2 :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
      hν U₀
      (lt_of_lt_of_le ha q.property.1)
      i

  let D0 : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := (q : ℝ))
      hν U₀ hA hU₀ i

  let Dh0 : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      i

  let Dt0 : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
      (t := (q : ℝ))
      hν U₀ hA hU₀ i

  have hMild :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_heat_add_duhamel
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      i

  have hDsplit :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_head_add_tail
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      i

  have hHm :=
    h3SelectedInitialHeatNatRadialFourierL2OnCompact_ae
      m hν U₀ hA hU₀ ha q i

  have hDh :=
    h3SelectedDuhamelHeadNatRadialFourierL2OnCompact_ae
      m hν U₀ hA hU₀ ha q i

  have hDt :=
    h3SelectedDuhamelTailNatRadialFourierL2_ae
      m hm
      hν U₀ hA hU₀
      (lt_of_lt_of_le ha q.property.1)
      (le_trans q.property.2 hbR.le)
      i

  have hSub1 :=
    MeasureTheory.Lp.coeFn_sub
      Hm DmHead

  have hSub2 :=
    MeasureTheory.Lp.coeFn_sub
      (Hm - DmHead) DmTail

  unfold h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact

  filter_upwards [
    hMild,
    hDsplit,
    hHm,
    hDh,
    hDt,
    hSub1,
    hSub2
  ] with ξ hMildξ hDsplitξ hHmξ hDhξ hDtξ hSub1ξ hSub2ξ

  rw [hSub2ξ]

  simp only [Pi.sub_apply] at hSub1ξ ⊢

  rw [hSub1ξ]

  rw [hHmξ, hDhξ, hDtξ]

  change
    ((‖ξ‖ ^ m : ℝ) : ℂ) * H0 ξ -
        ((‖ξ‖ ^ m : ℝ) : ℂ) * Dh0 ξ -
        ((‖ξ‖ ^ m : ℝ) : ℂ) * Dt0 ξ
      =
    ((‖ξ‖ ^ m : ℝ) : ℂ) * W0 ξ

  rw [hMildξ, hDsplitξ]

  ring

/-! ## The two new radial orders needed by the sixth-diffusion derivative -/

/--
Canonical selected eighth-radial velocity state on a positive compact restart
slab.
-/
noncomputable def h3PreterminalSelectedVelocityEighthRadialFourierL2OnCompact
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (q : Set.Icc a b)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
    8 (by norm_num)
    hν U₀ hA hU₀ ha hbR q i

/--
The eighth-radial state is literally `|ξ|⁸` times the selected raw Fourier
velocity almost everywhere.
-/
theorem h3PreterminalSelectedVelocityEighthRadialFourierL2OnCompact_ae
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ((h3PreterminalSelectedVelocityEighthRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha hbR q i :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 8 : ℝ) : ℂ) *
        (((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
            hν U₀ hA hU₀ (q : ℝ) i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)) := by

  unfold h3PreterminalSelectedVelocityEighthRadialFourierL2OnCompact

  exact
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact_ae
      8 (by norm_num)
      hν U₀ hA hU₀ ha hbR q i

/--
Canonical selected ninth-radial velocity state on a positive compact restart
slab.
-/
noncomputable def h3PreterminalSelectedVelocityNinthRadialFourierL2OnCompact
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (q : Set.Icc a b)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact
    9 (by norm_num)
    hν U₀ hA hU₀ ha hbR q i

/--
The ninth-radial state is literally `|ξ|⁹` times the selected raw Fourier
velocity almost everywhere.
-/
theorem h3PreterminalSelectedVelocityNinthRadialFourierL2OnCompact_ae
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hbR : b < h3FinHeatLerayRestartRadius ν A)
    (q : Set.Icc a b)
    (i : Fin 3) :
    ((h3PreterminalSelectedVelocityNinthRadialFourierL2OnCompact
        hν U₀ hA hU₀ ha hbR q i :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ 9 : ℝ) : ℂ) *
        (((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
            hν U₀ hA hU₀ (q : ℝ) i :
          H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)) := by

  unfold h3PreterminalSelectedVelocityNinthRadialFourierL2OnCompact

  exact
    h3PreterminalSelectedVelocityNatRadialFourierL2OnCompact_ae
      9 (by norm_num)
      hν U₀ hA hU₀ ha hbR q i

end

end Euclidean
end Bridge
end PrimeTensor
