import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzSpectralFirstJet244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzDifferenceEnergyBridge244
import Mathlib.Tactic

/-!
# Zeroth-order reconstruction forces the full Schwartz / spectral first-jet match

The previous spectral-first-jet theorem required pointwise identities of BOTH
Schwartz first derivatives and differences of first derivatives with the
canonical weighted-H³ real C¹ representatives. Those identities are not new
analytic assumptions once the underlying reconstructed velocity components
are exactly equal as physical functions.

This module obtains both derivative identities from just zero-order physical
realization. It reuses the previously proved:

* exact Point3-to-Euclidean Schwartz pullback / spatial derivative commutation;
* Schwartz line derivative subtraction;
* exact subtraction of the weighted H³ real C¹ representative.

The resulting comparison is then fed directly into the genuine spectral-H³
first-jet L∞ bound and the full 3–3–1 gradient continuity theorem.

Crucial scope: zero-order REALIZATION of the Schwartz sequence by spectral
states is retained as an explicit hypothesis. Weighted spectral density alone
has not been proved to supply this equality, nor physical PDE identification.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeZerothSpectral244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The actual Point3–Euclidean carrier maps are inverse at every coordinate.
In particular evaluating a pulled-back Schwartz first jet at `ofLp x`
recovers its original value at `x`, with no norm or measure normalization. -/
theorem thirdFullSchwartz_point3_fourier_roundtrip244 (x : V3) :
    h3Point3ToFourierCLM ((WithLp.ofLp : V3 → Point3) x) = x := by
  rw [h3Point3ToFourierCLM_apply]

/-- A ZERO-ORDER equality of physical functions forces the genuine first
Schwartz directional derivative to agree with the canonical reconstructed
first spatial derivative at every point. No derivative matching is assumed. -/
theorem thirdFullSchwartz_firstJet_eq_of_zerothRealization244
    (f : SchwartzMap V3 ℝ) (S : H3SpectralScalarState)
    (hZero : h3SchwartzPoint3Scalar f =
      h3SpectralScalarRealC1RepresentativeOnPoint3 S)
    (i : A3) (x : V3) :
    (∂_{h3FourierAxisDirection i} f) x =
      spatial3.d i (h3SpectralScalarRealC1RepresentativeOnPoint3 S)
        ((WithLp.ofLp : V3 → Point3) x) := by
  have hDerivative :=
    congrArg (fun v : ScalarField3 => spatial3.d i v) hZero
  rw [h3SchwartzPoint3Scalar_spatial_d] at hDerivative
  have hAt := congrFun hDerivative ((WithLp.ofLp : V3 → Point3) x)
  change (∂_{h3FourierAxisDirection i} f)
      (h3Point3ToFourierCLM ((WithLp.ofLp : V3 → Point3) x)) =
    spatial3.d i (h3SpectralScalarRealC1RepresentativeOnPoint3 S)
      ((WithLp.ofLp : V3 → Point3) x) at hAt
  rw [thirdFullSchwartz_point3_fourier_roundtrip244] at hAt
  exact hAt

/-- Exact reconstruction respects subtraction at the physical function
level. Thus zero-order realization of the two individual fields already
realizes their DIFFERENCE by the spectral difference state. -/
theorem thirdFullSchwartz_zerothDifferenceRealization244
    (f g : SchwartzMap V3 ℝ)
    (S G : H3SpectralScalarState)
    (hf : h3SchwartzPoint3Scalar f =
      h3SpectralScalarRealC1RepresentativeOnPoint3 S)
    (hg : h3SchwartzPoint3Scalar g =
      h3SpectralScalarRealC1RepresentativeOnPoint3 G) :
    h3SchwartzPoint3Scalar (f - g) =
      h3SpectralScalarRealC1RepresentativeOnPoint3 (S - G) := by
  rw [h3SpectralScalarRealC1RepresentativeOnPoint3_sub]
  funext x
  have hfx := congrFun hf x
  have hgx := congrFun hg x
  change f (h3Point3ToFourierCLM x) =
      h3SpectralScalarRealC1RepresentativeOnPoint3 S x at hfx
  change g (h3Point3ToFourierCLM x) =
      h3SpectralScalarRealC1RepresentativeOnPoint3 G x at hgx
  change (f - g) (h3Point3ToFourierCLM x) =
      h3SpectralScalarRealC1RepresentativeOnPoint3 S x -
        h3SpectralScalarRealC1RepresentativeOnPoint3 G x
  simpa only [sub_apply] using
    (congrArg₂ (fun a b : ℝ => a - b) hfx hgx)

/-- At every spatial point, the difference of the ACTUAL Schwartz first
jets is exactly the first derivative of the spectral difference state. -/
theorem thirdFullSchwartz_firstJetDifference_eq_of_zerothRealization244
    (f g : SchwartzMap V3 ℝ)
    (S G : H3SpectralScalarState)
    (hf : h3SchwartzPoint3Scalar f =
      h3SpectralScalarRealC1RepresentativeOnPoint3 S)
    (hg : h3SchwartzPoint3Scalar g =
      h3SpectralScalarRealC1RepresentativeOnPoint3 G)
    (i : A3) (x : V3) :
    ((∂_{h3FourierAxisDirection i} f : SchwartzMap V3 ℝ) -
      ∂_{h3FourierAxisDirection i} g) x =
    spatial3.d i
      (h3SpectralScalarRealC1RepresentativeOnPoint3 (S - G))
      ((WithLp.ofLp : V3 → Point3) x) := by
  have hDifference := thirdFullSchwartz_firstJet_eq_of_zerothRealization244
    (f - g) (S - G)
    (thirdFullSchwartz_zerothDifferenceRealization244 f g S G hf hg)
    i x
  rw [schwartzLineDeriv_sub244] at hDifference
  exact hDifference

/-- No independent first-derivative matching assumption is needed: both
matching fields in the old comparison structure follow from zeroth-order
Schwartz/spectral realization plus its existing norm constraints. -/
theorem thirdFullSchwartz_firstJetComparison_of_zerothRealization244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ)
    (S : ℕ → A3 → H3SpectralScalarState)
    (G : A3 → H3SpectralScalarState)
    (hSpectral : ∀ j : A3,
      Tendsto (fun n => ‖S n j - G j‖) atTop (𝓝 0))
    (hUnit : ∀ n : ℕ, ∀ j : A3, ‖S n j - G j‖ ≤ 1)
    (hApprox : ∀ n : ℕ, ∀ j : A3,
      h3SchwartzPoint3Scalar (f n j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3 (S n j))
    (hTarget : ∀ j : A3,
      h3SchwartzPoint3Scalar (g j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3 (G j)) :
    H3SchwartzSpectralFirstJetComparison244 f g S G := by
  refine {
    spectral := hSpectral
    unitError := hUnit
    targetFirst := ?_
    differenceFirst := ?_ }
  · intro j i x
    exact thirdFullSchwartz_firstJet_eq_of_zerothRealization244
      (g j) (G j) (hTarget j) i x
  · intro n j i x
    exact thirdFullSchwartz_firstJetDifference_eq_of_zerothRealization244
      (f n j) (g j) (S n j) (G j)
      (hApprox n j) (hTarget j) i x

/-- The entire signed 3+3+1 gradient channel now converges from zeroth-order
Schwartz realization, weighted spectral H³ convergence and third-jet L²
convergence. The previous first-jet matching hypotheses have disappeared. -/
theorem fullSchwartzGradientTransport_tendsto_of_zerothSpectralMatch244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ)
    (S : ℕ → A3 → H3SpectralScalarState)
    (G : A3 → H3SpectralScalarState)
    (hSpectral : ∀ j : A3,
      Tendsto (fun n => ‖S n j - G j‖) atTop (𝓝 0))
    (hUnit : ∀ n : ℕ, ∀ j : A3, ‖S n j - G j‖ ≤ 1)
    (hApprox : ∀ n : ℕ, ∀ j : A3,
      h3SchwartzPoint3Scalar (f n j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3 (S n j))
    (hTarget : ∀ j : A3,
      h3SchwartzPoint3Scalar (g j) =
        h3SpectralScalarRealC1RepresentativeOnPoint3 (G j))
    (hThird : ∀ j i k l : A3,
      Tendsto (fun n => schwartzIntegralL2Root244
        ((∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection k}
            (∂_{h3FourierAxisDirection l} (f n j))) : SchwartzMap V3 ℝ) -
          ∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection k}
              (∂_{h3FourierAxisDirection l} (g j)))))
        atTop (𝓝 0)) :
    Tendsto (fun n => fullSchwartzGradientTransport244 (f n)) atTop
      (𝓝 (fullSchwartzGradientTransport244 g)) := by
  have hComparison :=
    thirdFullSchwartz_firstJetComparison_of_zerothRealization244
      f g S G hSpectral hUnit hApprox hTarget
  exact fullSchwartzGradientTransport_tendsto_of_spectralH3FirstJet244
    hComparison hThird

end
end PrimeTensor.FirstMonomialTriad
