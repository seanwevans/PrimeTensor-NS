import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedDuhamelTailCubicL2Baseline
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.C3.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.Moment.Free.Heat
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Representative

/-!
# Arbitrary radial L² source slices for the selected terminal Duhamel tail

The active high-frequency frontier is now the selected terminal half-tail.
The important distinction is between:

* **fixed strict source time** `s < t`, where the heat lag `t-s` is positive;
* the **source-time integral** as `s ↑ t`, where the heat lag degenerates.

At every fixed strict source time, there is no spatial obstruction at all.
The unheated finite Leray forcing already belongs to Fourier `L²`, and the
positive heat multiplier absorbs every finite radial power:

    ‖ξ‖^n H_{t-s}(ξ) N_s(ξ) ∈ L²_ξ

for every natural `n`.

This file packages those weighted source slices as genuine quotient-safe
Fourier `L²` states and proves that their representatives are exactly the
weighted explicit selected tail kernels.

Consequently the unresolved fourth/fifth tail problem is now purely temporal:
whether the order-four and order-five weighted `L²` source states are Bochner
integrable on `(t/2,t)` as the lag tends to zero.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedDuhamelTailWeightedKernelL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Fixed positive-lag radial L² smoothing -/

/--
At every positive heat lag, an arbitrary natural radial weight of the raw
finite Leray forcing remains in Fourier `L²`.

This uses only the unweighted forcing `L²` theorem and the generic
positive-time heat moment multiplier bound.
-/
theorem h3RawFinLerayOuterProductDivergenceHeatRepresentative_radialWeight_memLp2
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (n : ℕ) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ n : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  let C : ℝ :=
    h3HeatNatMomentCoefficient n ν τ

  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ n : ℝ) : ℂ) *
            h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν τ U V i ξ)
        (volume : Measure H3FourierPoint3) := by
    exact
      (Complex.continuous_ofReal.comp
        (continuous_norm.pow n)).aestronglyMeasurable.mul
        (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
          ν τ U V i)

  refine
    (h3RawFinLerayOuterProductDivergence_memLp2 U V i).of_le_mul
      (c := C)
      hMeas
      ?_

  filter_upwards with ξ

  have hMoment :=
    h3HeatFourierMomentMultiplier_le_nat
      hν hτ n ξ

  have hWeight0 :
      0 ≤ ‖ξ‖ ^ n :=
    pow_nonneg (norm_nonneg ξ) n

  dsimp only [C]

  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hWeight0,
    norm_mul
  ]

  calc
    ‖ξ‖ ^ n *
        (‖h3HeatFourierSymbol ν τ ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        =
      (‖ξ‖ ^ n *
        ‖h3HeatFourierSymbol ν τ ξ‖) *
      ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by
        ring
    _ ≤
      h3HeatNatMomentCoefficient n ν τ *
        ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ :=
      mul_le_mul_of_nonneg_right
        (by
          simpa only [
            h3FourierMomentWeight_natCast
          ] using hMoment)
        (norm_nonneg _)

/-! ## Quotient-safe weighted selected tail source states -/

/--
The order-`n` radially weighted selected terminal-tail source slice, packaged
as a genuine Fourier `L²` state.

At and beyond the terminal endpoint it is set to zero, matching the existing
endpoint-safe Duhamel convention.
-/
noncomputable def h3SelectedDuhamelTailRadialRawFourierL2Integrand
    (n : ℕ)
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (s : ℝ) :
    H3FourierComplexL2 :=
  if hs : s < t then
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let hτ : 0 < t - s :=
      sub_pos.mpr hs
    (h3RawFinLerayOuterProductDivergenceHeatRepresentative_radialWeight_memLp2
        hν hτ (W s) (W s) i n).toLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ n : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν (t - s) (W s) (W s) i ξ)
  else
    0

/--
At every strict source time, the quotient-safe weighted `L²` slice has exactly
the weighted explicit selected terminal-tail kernel as its representative.
-/
theorem h3SelectedDuhamelTailRadialRawFourierL2Integrand_ae_of_lt
    {ν A t s : ℝ}
    (n : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (hs : s < t) :
    ((h3SelectedDuhamelTailRadialRawFourierL2Integrand
        n ν A t hν U₀ hA hU₀ i s :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ n : ℝ) : ℂ) *
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ)) := by

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let hτ : 0 < t - s :=
    sub_pos.mpr hs

  unfold h3SelectedDuhamelTailRadialRawFourierL2Integrand
  rw [dif_pos hs]

  have hRep :=
    MemLp.coeFn_toLp
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_radialWeight_memLp2
        hν hτ (W s) (W s) i n)

  filter_upwards [hRep] with ξ hξ

  calc
    (((h3RawFinLerayOuterProductDivergenceHeatRepresentative_radialWeight_memLp2
          hν hτ (W s) (W s) i n).toLp
        (fun ζ : H3FourierPoint3 =>
          ((‖ζ‖ ^ n : ℝ) : ℂ) *
            h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν (t - s) (W s) (W s) i ζ) :
        H3FourierComplexL2) :
      H3FourierPoint3 → ℂ) ξ
        =
      ((‖ξ‖ ^ n : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν (t - s) (W s) (W s) i ξ :=
      hξ
    _ =
      ((‖ξ‖ ^ n : ℝ) : ℂ) *
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ) := by
      unfold
        h3RawFinLerayOuterProductDivergenceHeatRepresentative
        h3SelectedDuhamelTailComplexKernel
      dsimp only [W]

/--
The same representative identity on the terminal open half.
-/
theorem h3SelectedDuhamelTailRadialRawFourierL2Integrand_ae_of_mem_Ioo
    {ν A t s : ℝ}
    (n : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo (t / 2) t) :
    ((h3SelectedDuhamelTailRadialRawFourierL2Integrand
        n ν A t hν U₀ hA hU₀ i s :
      H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ n : ℝ) : ℂ) *
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ)) :=
  h3SelectedDuhamelTailRadialRawFourierL2Integrand_ae_of_lt
    n hν U₀ hA hU₀ i hs.2

/-! ## The remaining endpoint condition is purely temporal -/

/--
The remaining fourth/fifth terminal-tail condition phrased at the natural
quotient-safe level: the weighted Fourier `L²` source slices must be Bochner
integrable in source time over the terminal half.

Fixed-time spatial `L²` membership is automatic by the preceding theorem.
Only the endpoint behavior of the `L²` norms as `s ↑ q` is left here.
-/
def H3CanonicalSelectedDuhamelTailFourthFifthWeightedKernelIntervalIntegrableOnRestartRadius :
    Prop :=
  ∀
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t₀ : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E),
      ∀ q : ℝ,
        q ∈
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        let U₀ : H3SpectralVelocityState :=
          h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail
        let hA : 0 < E :=
          lt_of_lt_of_le zero_lt_one hE
        let hU₀ : ‖U₀‖ ≤ E :=
          norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail
        (
          ∀ j : Fin 3,
            IntervalIntegrable
              (h3SelectedDuhamelTailRadialRawFourierL2Integrand
                4 (1 : ℝ) E q
                (one_pos : (0 : ℝ) < 1)
                U₀ hA hU₀ j)
              volume
              (q / 2)
              q
        )
          ∧
        (
          ∀ j : Fin 3,
            IntervalIntegrable
              (h3SelectedDuhamelTailRadialRawFourierL2Integrand
                5 (1 : ℝ) E q
                (one_pos : (0 : ℝ) < 1)
                U₀ hA hU₀ j)
              volume
              (q / 2)
              q
        )

end

end Euclidean
end Bridge
end PrimeTensor
