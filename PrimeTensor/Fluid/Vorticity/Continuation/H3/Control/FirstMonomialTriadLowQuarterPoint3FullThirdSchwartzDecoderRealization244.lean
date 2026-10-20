import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzZerothSpectralMatch244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzCompactWeightedPhysicalBridge244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Selected.Spatial.First
import Mathlib.Tactic

/-!
# Decode real Schwartz L² identities into exact pointwise H³ spectral realization

The previous first-jet comparison required the zeroth-order Schwartz/spectral
matching itself as a hypothesis. Smooth compact weighted spectral density has
already constructed approximating states with EXACT real L² decoder equality
to a real physical Schwartz map. This module upgrades that equality to an
exact equality of continuous physical functions, via the canonical C¹
representative and uniqueness of continuous versions.

Consequences:
* exact pointwise zeroth-order Schwartz realization for each synchronized
  compact-weighted spectral approximant;
* exact first-derivative match and quantitative L∞ difference estimate;
* convergence of those actual Schwartz first jets to the canonical first
  derivative of ANY weighted H³ target, even if that target is not Schwartz.

No claim is made that the target is Schwartz or that every signed 243-slot
third-order monomial converges from H³ alone. The separate physical nonlinear
transport identification is still a substantive obligation.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeDecoderRealization244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Equality of the ACTUAL real L² decoder with a Schwartz class forces
pointwise equality of their continuous spatial representatives. -/
theorem thirdFullSchwartz_zerothRealization_of_decoderEquality244
    (G : H3SpectralScalarState)
    (ψ : SchwartzMap V3 ℝ)
    (hDecoder : h3SpectralScalarDecodeRealL2 G =
      ψ.toLp 2 (volume : Measure V3)) :
    h3SchwartzPoint3Scalar ψ =
      h3SpectralScalarRealC1RepresentativeOnPoint3 G := by
  have hAE : h3SpectralScalarRealC1Representative G
      =ᵐ[(volume : Measure V3)] (ψ : V3 → ℝ) := by
    have hCanonical :=
      h3SpectralScalarRealC1Representative_ae_eq_decodeRealL2 G
    rw [hDecoder] at hCanonical
    exact hCanonical.trans (ψ.coeFn_toLp 2 (volume : Measure V3))
  have hPointwise : h3SpectralScalarRealC1Representative G =
      (ψ : V3 → ℝ) :=
    MeasureTheory.Measure.eq_of_ae_eq hAE
      (h3SpectralScalarRealC1Representative_contDiff_one G).continuous
      ψ.continuous
  funext x
  change ψ (h3Point3ToFourierCLM x) =
    h3SpectralScalarRealC1Representative G
      ((WithLp.toLp 2 : Point3 → V3) x)
  rw [h3Point3ToFourierCLM_apply]
  exact (congrFun hPointwise ((WithLp.toLp 2 : Point3 → V3) x)).symm

/-- The already constructed genuine compact-weighted real Schwartz
approximants satisfy pointwise realization, not merely an L² equivalence. -/
theorem exists_thirdFullSchwartz_exactDecoderApproximation244
    (G : H3SpectralScalarState)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : H3SpectralScalarState,
    ∃ ψ : SchwartzMap V3 ℝ,
      ‖G - F‖ < ε ∧
      h3SchwartzPoint3Scalar ψ =
        h3SpectralScalarRealC1RepresentativeOnPoint3 F := by
  obtain ⟨F, ψ, hClose, hDecoder⟩ :=
    exists_h3SmoothCompactWeighted_realSchwartzExact244 G hε
  exact ⟨F, ψ, hClose,
    thirdFullSchwartz_zerothRealization_of_decoderEquality244 F ψ hDecoder⟩

/-- All three real physical Schwartz components in the existing synchronized
weighted H³ sequence realize their OWN canonical C¹ spectral states exactly.
The same sequence also retains its already-proved third-jet L² convergence. -/
theorem exists_thirdFullSchwartz_exactDecoderVelocitySequence244
    (U : H3SpectralVelocityState) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ,
      Tendsto V atTop (𝓝 U) ∧
      (∀ n : ℕ, ∀ j : Fin 3,
        h3SchwartzPoint3Scalar (Ψ n j) =
          h3SpectralScalarRealC1RepresentativeOnPoint3 (V n j)) ∧
      Tendsto (fun n : ℕ =>
        h3SpectralVelocityThirdPhysicalJetFamily244 (V n))
        atTop (𝓝 (h3SpectralVelocityThirdPhysicalJetFamily244 U)) := by
  obtain ⟨V, Ψ, hWeighted, hDecoder, _hPhysical, hThird⟩ :=
    exists_h3SmoothCompactWeighted_realSchwartzAndThirdSequence244 U
  refine ⟨V, Ψ, hWeighted, ?_, hThird⟩
  intro n j
  have hEq := hDecoder n j
  change h3SpectralScalarDecodeRealL2 (V n j) =
    (Ψ n j).toLp 2 (volume : Measure V3) at hEq
  exact thirdFullSchwartz_zerothRealization_of_decoderEquality244
    (V n j) (Ψ n j) hEq

/-- Exact pointwise first-derivative difference inequality for TWO
Schwartz maps realized by two weighted spectral states. This avoids a
Schwartz-target assumption and retains the same optimal H³ coefficient. -/
theorem thirdFullSchwartz_matchedFirstJetDifference_le_spectralDistance244
    (f g : SchwartzMap V3 ℝ)
    (F G : H3SpectralScalarState)
    (hf : h3SchwartzPoint3Scalar f =
      h3SpectralScalarRealC1RepresentativeOnPoint3 F)
    (hg : h3SchwartzPoint3Scalar g =
      h3SpectralScalarRealC1RepresentativeOnPoint3 G)
    (i : A3) (x : V3) :
    |((∂_{h3FourierAxisDirection i} f : SchwartzMap V3 ℝ) -
        ∂_{h3FourierAxisDirection i} g) x| ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        ‖F - G‖ := by
  rw [thirdFullSchwartz_firstJetDifference_eq_of_zerothRealization244
    f g F G hf hg i x]
  have hEval :=
    norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_apply_le
      (F - G) (h3ClassicalizationFinOfAxis i)
      ((WithLp.ofLp : V3 → Point3) x)
  simpa only [h3AxisOfFin3_h3ClassicalizationFinOfAxis,
    Real.norm_eq_abs] using hEval

/-- Weighted H³ convergence gives convergence of actual FIRST Schwartz
jets to the canonical first jet of an arbitrary H³ target. The target is NOT
required to have a Schwartz realization. -/
theorem thirdFullSchwartz_matchedFirstJet_tendsto_canonical244
    (F : ℕ → H3SpectralScalarState)
    (G : H3SpectralScalarState)
    (ψ : ℕ → SchwartzMap V3 ℝ)
    (hMatch : ∀ n : ℕ,
      h3SchwartzPoint3Scalar (ψ n) =
        h3SpectralScalarRealC1RepresentativeOnPoint3 (F n))
    (hSpectral : Tendsto (fun n => ‖F n - G‖) atTop (𝓝 0))
    (i : A3) (x : V3) :
    Tendsto (fun n => (∂_{h3FourierAxisDirection i} (ψ n)) x)
      atTop (𝓝 (spatial3.d i
        (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
        ((WithLp.ofLp : V3 → Point3) x))) := by
  let C : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  let L : ℝ := spatial3.d i
    (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
    ((WithLp.ofLp : V3 → Point3) x)
  have hUpper : Tendsto (fun n => C * ‖F n - G‖)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => C)
        atTop (𝓝 C)).mul hSpectral
  have hNonneg (n : ℕ) :
      0 ≤ |(∂_{h3FourierAxisDirection i} (ψ n)) x - L| :=
    abs_nonneg _
  have hPointBound (n : ℕ) :
      |(∂_{h3FourierAxisDirection i} (ψ n)) x - L| ≤
        C * ‖F n - G‖ := by
    have hEq := thirdFullSchwartz_firstJet_eq_of_zerothRealization244
      (ψ n) (F n) (hMatch n) i x
    have hEst :=
      norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_sub_apply_le
        (F n) G (h3ClassicalizationFinOfAxis i)
        ((WithLp.ofLp : V3 → Point3) x)
    simpa only [hEq, L, C,
      h3AxisOfFin3_h3ClassicalizationFinOfAxis, Real.norm_eq_abs]
      using hEst
  have hAbs : Tendsto (fun n =>
      |(∂_{h3FourierAxisDirection i} (ψ n)) x - L|)
      atTop (𝓝 0) :=
    squeeze_zero hNonneg hPointBound hUpper
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using hAbs

/-- Every weighted H³ velocity has one coherent sequence of real physical
Schwartz components whose FIRST spatial derivatives converge pointwise to
the corresponding canonical H³ C¹ representative, with no Schwartz target. -/
theorem exists_thirdFullSchwartz_velocityFirstJets_tendsto244
    (U : H3SpectralVelocityState) :
    ∃ V : ℕ → H3SpectralVelocityState,
    ∃ Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ,
      Tendsto V atTop (𝓝 U) ∧
      (∀ n : ℕ, ∀ j : Fin 3,
        h3SchwartzPoint3Scalar (Ψ n j) =
          h3SpectralScalarRealC1RepresentativeOnPoint3 (V n j)) ∧
      (∀ j : Fin 3, ∀ i : A3, ∀ x : V3,
        Tendsto (fun n => (∂_{h3FourierAxisDirection i} (Ψ n j)) x)
          atTop (𝓝 (spatial3.d i
            (h3SpectralScalarRealC1RepresentativeOnPoint3 (U j))
            ((WithLp.ofLp : V3 → Point3) x)))) := by
  obtain ⟨V, Ψ, hWeighted, hMatch, _hThird⟩ :=
    exists_thirdFullSchwartz_exactDecoderVelocitySequence244 U
  refine ⟨V, Ψ, hWeighted, hMatch, ?_⟩
  intro j i x
  have hCoordinate : Tendsto (fun n => V n j) atTop (𝓝 (U j)) :=
    (tendsto_pi_nhds.mp hWeighted) j
  have hNorm : Tendsto (fun n => ‖V n j - U j‖)
      atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hCoordinate
  exact thirdFullSchwartz_matchedFirstJet_tendsto_canonical244
    (fun n => V n j) (U j) (fun n => Ψ n j)
    (fun n => hMatch n j) hNorm i x

end
end PrimeTensor.FirstMonomialTriad
