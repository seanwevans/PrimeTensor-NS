import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Fin.Heat.Leray.Duhamel.Raw.Fourier.Representative
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Classicalization: quotient-safe pairings for the raw Fourier Duhamel state

The preceding two checkpoints identify

* exact H³ deweighting of the actual Banach-valued Duhamel state with a
  Fourier `L²`-valued source-time interval integral; and
* every source-time `L²` kernel with its explicit endpoint-safe raw Fourier
  representative almost everywhere.

This file combines those facts by Hilbert-space duality.

First, the packaged raw Fourier `L²` source kernel is shown to be genuinely
interval-integrable.  Pairing the exact deweighted Duhamel state against an
arbitrary Fourier `L²` test state may therefore be commuted through the
source-time integral.

Specializing the test state to the indicator of a measurable finite-measure
frequency set turns that pairing into an ordinary set integral.  The
fixed-source-time representative theorem then replaces the quotient-safe
kernel by the explicit raw retarded kernel inside every such set integral.

The result is the finite-set integral identity needed for the subsequent
Fubini and sigma-finite uniqueness step.  No point evaluation of an `L²`
equivalence class is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SpectralFinHeatLerayDuhamelRawFourierPairing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The quotient-safe raw Fourier `L²` source kernel of the general
heat--Leray Duhamel state is genuinely interval-integrable. -/
theorem h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand_intervalIntegrable
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (i : Fin 3) :
    IntervalIntegrable
      (h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
        ν t hν U V i)
      volume
      0
      t := by
  let P : H3SpectralFinVectorState →L[ℂ] H3SpectralScalarState :=
    ContinuousLinearMap.proj (R := ℂ) i

  let E : H3SpectralFinVectorState →L[ℂ] H3FourierComplexL2 :=
    h3SpectralScalarRawFourierL2CLM.comp P

  have hUint :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖U s‖ ≤ MU := by
    intro s hs
    exact hU s

  have hVint :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖V s‖ ≤ MV := by
    intro s hs
    exact hV s

  have hD :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν U V)
        volume
        0
        t :=
    h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
      hν ht hMU hMV U V
      hUcont hVcont hUint hVint

  have hMapped :
      IntervalIntegrable
        (fun s : ℝ =>
          E
            (h3SpectralFinHeatLerayDuhamelIntegrand
              ν t hν U V s))
        volume
        0
        t := by
    constructor
    · exact E.integrable_comp hD.1
    · exact E.integrable_comp hD.2

  refine hMapped.congr ?_
  intro s hs

  by_cases hlag : 0 < t - s

  · simp only [
      h3SpectralFinHeatLerayDuhamelIntegrand,
      dif_pos hlag,
      h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand,
      dif_pos hlag
    ]

    change
      h3SpectralScalarRawFourierL2
          (h3SpectralFinHeatLerayVelocityApply
            ν (t - s) hν hlag (U s) (V s) i)
        =
      h3RawFinLerayOuterProductDivergenceHeatFourierL2
        ν (t - s) hν hlag (U s) (V s) i

    exact
      h3SpectralFinHeatLerayVelocityApply_rawFourierL2_eq_rawHeatForcingL2
        hν hlag (U s) (V s) i

  · simp only [
      h3SpectralFinHeatLerayDuhamelIntegrand,
      dif_neg hlag,
      h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand,
      dif_neg hlag
    ]

    exact E.map_zero

/-- Hilbert-space dual form of exact H³ deweighting of the general
heat--Leray Duhamel state. -/
theorem inner_h3SpectralFinHeatLerayDuhamel_rawFourierL2_eq_intervalIntegral
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (i : Fin 3)
    (φ : H3FourierComplexL2) :
    inner ℂ φ
        (h3SpectralScalarRawFourierL2
          (h3SpectralFinHeatLerayDuhamel
            ν t hν U V i))
      =
    ∫ s in (0 : ℝ)..t,
      inner ℂ φ
        (h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
          ν t hν U V i s) := by
  rw [
    h3SpectralFinHeatLerayDuhamel_rawFourierL2_eq_intervalIntegral
      hν ht hMU hMV U V
      hUcont hVcont hU hV i
  ]

  have hG :=
    h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand_intervalIntegrable
      hν ht hMU hMV U V
      hUcont hVcont hU hV i

  let L : H3FourierComplexL2 →L[ℂ] ℂ :=
    innerSL ℂ φ

  have hComm :
      (∫ s in (0 : ℝ)..t,
        L
          (h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
            ν t hν U V i s))
        =
      L
        (∫ s in (0 : ℝ)..t,
          h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
            ν t hν U V i s) :=
    L.intervalIntegral_comp_comm hG

  simpa only [L, innerSL_apply_apply] using hComm.symm

/-- Pairing one quotient-safe source-time raw Fourier `L²` kernel against the
indicator of a finite-measure frequency set gives the set integral of its
explicit endpoint-safe raw Fourier representative. -/
theorem inner_indicatorConstLp_h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand_eq_setIntegral
    {ν t s : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hμS : (volume : Measure H3FourierPoint3) S ≠ ∞) :
    inner ℂ
        (indicatorConstLp
          (μ := (volume : Measure H3FourierPoint3))
          2 hS hμS (1 : ℂ))
        (h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
          ν t hν U V i s)
      =
    ∫ ξ in S,
      h3SpectralFinHeatLerayDuhamelRawFourierIntegrand
        ν t U V i s ξ := by
  let φ : H3FourierComplexL2 :=
    indicatorConstLp
      (μ := (volume : Measure H3FourierPoint3))
      2 hS hμS (1 : ℂ)

  have hIndicator :
      inner ℂ φ
          (h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
            ν t hν U V i s)
        =
      ∫ ξ in S,
        ((h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
            ν t hν U V i s : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ := by
    dsimp only [φ]
    exact
      MeasureTheory.L2.inner_indicatorConstLp_one
        hS hμS
        (h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
          ν t hν U V i s)

  have hRep :=
    h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand_ae
      (ν := ν) (t := t) hν U V i s

  have hSet :
      (∫ ξ in S,
        ((h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
            ν t hν U V i s : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)
        =
      ∫ ξ in S,
        h3SpectralFinHeatLerayDuhamelRawFourierIntegrand
          ν t U V i s ξ := by
    apply setIntegral_congr_ae hS
    exact hRep.mono (fun ξ hξ _ => hξ)

  change
    inner ℂ φ
        (h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
          ν t hν U V i s)
      =
    ∫ ξ in S,
      h3SpectralFinHeatLerayDuhamelRawFourierIntegrand
        ν t U V i s ξ

  exact hIndicator.trans hSet

/-- On every measurable finite-measure frequency set, exact H³ deweighting of
the actual general Duhamel state has the same set integral as the source-time
integral of the explicit endpoint-safe raw Fourier kernel. -/
theorem setIntegral_h3SpectralFinHeatLerayDuhamel_rawFourierL2_eq_intervalIntegral
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (i : Fin 3)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hμS : (volume : Measure H3FourierPoint3) S ≠ ∞) :
    (∫ ξ in S,
      ((h3SpectralScalarRawFourierL2
          (h3SpectralFinHeatLerayDuhamel
            ν t hν U V i) : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ)
      =
    ∫ s in (0 : ℝ)..t,
      ∫ ξ in S,
        h3SpectralFinHeatLerayDuhamelRawFourierIntegrand
          ν t U V i s ξ := by
  let φ : H3FourierComplexL2 :=
    indicatorConstLp
      (μ := (volume : Measure H3FourierPoint3))
      2 hS hμS (1 : ℂ)

  have hActual :
      inner ℂ φ
          (h3SpectralScalarRawFourierL2
            (h3SpectralFinHeatLerayDuhamel
              ν t hν U V i))
        =
      ∫ ξ in S,
        ((h3SpectralScalarRawFourierL2
            (h3SpectralFinHeatLerayDuhamel
              ν t hν U V i) : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ := by
    dsimp only [φ]
    exact
      MeasureTheory.L2.inner_indicatorConstLp_one
        hS hμS
        (h3SpectralScalarRawFourierL2
          (h3SpectralFinHeatLerayDuhamel
            ν t hν U V i))

  have hPair :=
    inner_h3SpectralFinHeatLerayDuhamel_rawFourierL2_eq_intervalIntegral
      hν ht hMU hMV U V
      hUcont hVcont hU hV i φ

  have hOuter :
      (∫ s in (0 : ℝ)..t,
        inner ℂ φ
          (h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
            ν t hν U V i s))
        =
      ∫ s in (0 : ℝ)..t,
        ∫ ξ in S,
          h3SpectralFinHeatLerayDuhamelRawFourierIntegrand
            ν t U V i s ξ := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact
      inner_indicatorConstLp_h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand_eq_setIntegral
        hν U V i S hS hμS

  calc
    (∫ ξ in S,
      ((h3SpectralScalarRawFourierL2
          (h3SpectralFinHeatLerayDuhamel
            ν t hν U V i) : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ)
        =
      inner ℂ φ
        (h3SpectralScalarRawFourierL2
          (h3SpectralFinHeatLerayDuhamel
            ν t hν U V i)) := by
      exact hActual.symm
    _ =
      ∫ s in (0 : ℝ)..t,
        inner ℂ φ
          (h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
            ν t hν U V i s) :=
      hPair
    _ =
      ∫ s in (0 : ℝ)..t,
        ∫ ξ in S,
          h3SpectralFinHeatLerayDuhamelRawFourierIntegrand
            ν t U V i s ξ :=
      hOuter

end

end Euclidean
end Bridge
end PrimeTensor
