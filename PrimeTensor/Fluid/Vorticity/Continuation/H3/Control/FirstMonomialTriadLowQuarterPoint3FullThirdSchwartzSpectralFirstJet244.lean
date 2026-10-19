import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzGradientL2L2Linf244
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Cubic.Third.Jet.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Envelope
import Mathlib.Tactic

/-!
# H³ spectral control of the first jet in the signed 3–3–1 gradient

The quantitative canonical Fourier theorem

  |∂ᵢ RealRep(F)(x)| ≤ C₁ ‖F‖_{weighted H³}

is uniform in x. Applying it to spectral DIFFERENCES supplies the L∞
error gauges required by the preceding L²–L²–L∞ gradient continuity proof.

The precise physical-to-Schwartz matching of first-jet differences and the
limit of the third derivative L² roots remain EXPLICIT. In particular this
module does not infer any nonlinear physical identification merely from
spectral density, nor assert global Navier–Stokes regularity.

A unit-ball condition on every spectral error gives a bound for ALL n (not
merely eventually); this form is compatible with selecting 1/(n+1)-accurate
Schwartz spectral approximants and is exactly what the preceding triple
continuity interface requires.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeSpectralFirstJet244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

private abbrev spectralFirstJet244 (f : A3 → SchwartzMap V3 ℝ)
    (j i : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection i} (f j)

private abbrev spectralThirdJet244 (f : A3 → SchwartzMap V3 ℝ)
    (j i k l : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection i}
    (∂_{h3FourierAxisDirection k}
      (∂_{h3FourierAxisDirection l} (f j)))

/-- Spectral convergence together with exact first-jet comparison on the
common Point3/WithLp Euclidean carriers. The comparison identities are an
actual physical Fourier/Schwartz matching obligation, not mere density. -/
structure H3SchwartzSpectralFirstJetComparison244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ)
    (S : ℕ → A3 → H3SpectralScalarState)
    (G : A3 → H3SpectralScalarState) : Prop where
  spectral : ∀ j : A3,
    Tendsto (fun n => ‖S n j - G j‖) atTop (𝓝 0)
  unitError : ∀ n : ℕ, ∀ j : A3, ‖S n j - G j‖ ≤ 1
  targetFirst : ∀ j i : A3, ∀ x : V3,
    spectralFirstJet244 g j i x =
      spatial3.d i
        (h3SpectralScalarRealC1RepresentativeOnPoint3 (G j))
        ((WithLp.ofLp : V3 → Point3) x)
  differenceFirst : ∀ n : ℕ, ∀ j i : A3, ∀ x : V3,
    (spectralFirstJet244 (f n) j i - spectralFirstJet244 g j i) x =
      spatial3.d i
        (h3SpectralScalarRealC1RepresentativeOnPoint3 (S n j - G j))
        ((WithLp.ofLp : V3 → Point3) x)

/-- The already-established H³ C¹ evaluation estimate gives a pointwise
first-jet bound on the exact REAL Schwartz derivative difference. -/
theorem spectralFirstJet_difference_abs_le_weightedH3_244
    {f : ℕ → A3 → SchwartzMap V3 ℝ}
    {g : A3 → SchwartzMap V3 ℝ}
    {S : ℕ → A3 → H3SpectralScalarState}
    {G : A3 → H3SpectralScalarState}
    (h : H3SchwartzSpectralFirstJetComparison244 f g S G)
    (n : ℕ) (j i : A3) (x : V3) :
    |(spectralFirstJet244 (f n) j i - spectralFirstJet244 g j i) x| ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        ‖S n j - G j‖ := by
  rw [h.differenceFirst n j i x]
  have hEval :=
    norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_apply_le
      (S n j - G j) (h3ClassicalizationFinOfAxis i)
      ((WithLp.ofLp : V3 → Point3) x)
  simpa only [h3AxisOfFin3_h3ClassicalizationFinOfAxis,
    Real.norm_eq_abs] using hEval

/-- One target Schwartz first jet is bounded uniformly by the genuine H³
norm of its canonical spectral representative. -/
theorem spectralFirstJet_target_abs_le_weightedH3_244
    {f : ℕ → A3 → SchwartzMap V3 ℝ}
    {g : A3 → SchwartzMap V3 ℝ}
    {S : ℕ → A3 → H3SpectralScalarState}
    {G : A3 → H3SpectralScalarState}
    (h : H3SchwartzSpectralFirstJetComparison244 f g S G)
    (j i : A3) (x : V3) :
    |spectralFirstJet244 g j i x| ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        ‖G j‖ := by
  rw [h.targetFirst j i x]
  have hEval :=
    norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_apply_le
      (G j) (h3ClassicalizationFinOfAxis i)
      ((WithLp.ofLp : V3 → Point3) x)
  simpa only [h3AxisOfFin3_h3ClassicalizationFinOfAxis,
    Real.norm_eq_abs] using hEval

/-- The missing natural-gradient L∞ interface follows from a SINGLE weighted
spectral H³ difference norm per velocity coordinate. The gauge δₙ tends to
zero without a separate pointwise-convergence postulate. -/
theorem spectralFirstJet_uniformAndVanishingGauges244
    {f : ℕ → A3 → SchwartzMap V3 ℝ}
    {g : A3 → SchwartzMap V3 ℝ}
    {S : ℕ → A3 → H3SpectralScalarState}
    {G : A3 → H3SpectralScalarState}
    (h : H3SchwartzSpectralFirstJetComparison244 f g S G)
    (j i : A3) :
    ∃ (K : ℝ) (δ : ℕ → ℝ),
      0 ≤ K ∧
      (∀ n : ℕ, ∀ x : V3, |spectralFirstJet244 (f n) j i x| ≤ K) ∧
      (∀ n : ℕ, ∀ x : V3,
        |(spectralFirstJet244 (f n) j i - spectralFirstJet244 g j i) x| ≤ δ n) ∧
      Tendsto δ atTop (𝓝 0) := by
  let C : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  let K : ℝ := C * (‖G j‖ + 1)
  let δ : ℕ → ℝ := fun n => C * ‖S n j - G j‖
  have hC : 0 ≤ C :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have hConst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) :=
      tendsto_const_nhds
    simpa only [δ, mul_zero] using hConst.mul (h.spectral j)
  refine ⟨K, δ, hK, ?_, ?_, hδ⟩
  · intro n x
    have hDiff := spectralFirstJet_difference_abs_le_weightedH3_244
      h n j i x
    have hTarget := spectralFirstJet_target_abs_le_weightedH3_244
      h j i x
    have hTriangle :
        |spectralFirstJet244 (f n) j i x| ≤
          |(spectralFirstJet244 (f n) j i - spectralFirstJet244 g j i) x| +
            |spectralFirstJet244 g j i x| := by
      have hAdd := abs_add_le
        ((spectralFirstJet244 (f n) j i - spectralFirstJet244 g j i) x)
        (spectralFirstJet244 g j i x)
      have hEq :
          (spectralFirstJet244 (f n) j i - spectralFirstJet244 g j i) x +
            spectralFirstJet244 g j i x =
            spectralFirstJet244 (f n) j i x := by
        simp only [sub_apply]
        ring
      rwa [hEq] at hAdd
    have hScaled : C * ‖S n j - G j‖ ≤ C := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (h.unitError n j) hC
    dsimp only [K, C]
    dsimp only [C] at hDiff hTarget hScaled
    linarith only [hTriangle, hDiff, hTarget, hScaled]
  · intro n x
    exact spectralFirstJet_difference_abs_le_weightedH3_244 h n j i x

/-- All 3+3+1 triples now inherit their formerly independent first-jet L∞
conditions from ONE spectral H³ approximation, if third jets converge in L². -/
theorem spectralFirstJet_produces_naturalGradientJets244
    {f : ℕ → A3 → SchwartzMap V3 ℝ}
    {g : A3 → SchwartzMap V3 ℝ}
    {S : ℕ → A3 → H3SpectralScalarState}
    {G : A3 → H3SpectralScalarState}
    (h : H3SchwartzSpectralFirstJetComparison244 f g S G)
    (hThird : ∀ j i k l : A3,
      Tendsto (fun n => schwartzIntegralL2Root244
        (spectralThirdJet244 (f n) j i k l -
          spectralThirdJet244 g j i k l)) atTop (𝓝 0)) :
    SchwartzFullGradientL2L2LinfJets244 f g := by
  have hTriple (j₁ i₁ k₁ l₁ j₂ i₂ k₂ l₂ j₃ i₃ : A3) :
      SchwartzGradientTripleL2L2LinfJets244
        (fun n => spectralThirdJet244 (f n) j₁ i₁ k₁ l₁)
        (fun n => spectralThirdJet244 (f n) j₂ i₂ k₂ l₂)
        (fun n => spectralFirstJet244 (f n) j₃ i₃)
        (spectralThirdJet244 g j₁ i₁ k₁ l₁)
        (spectralThirdJet244 g j₂ i₂ k₂ l₂)
        (spectralFirstJet244 g j₃ i₃) := by
    obtain ⟨K, δ, hK, hBound, hError, hδ⟩ :=
      spectralFirstJet_uniformAndVanishingGauges244 h j₃ i₃
    exact ⟨hThird j₁ i₁ k₁ l₁, hThird j₂ i₂ k₂ l₂,
      K, δ, hK, hBound, hError, hδ⟩
  intro j i k l r
  exact ⟨
    hTriple j i k l r i k l j r,
    hTriple j i k l j i k r r l,
    hTriple j i k l j i r l r k,
    hTriple j i k l j r k l r i⟩

/-- The complete REAL 3+3+1 gradient channel is sequentially continuous
under natural third-jet L² convergence and the spectral H³ bridge. -/
theorem fullSchwartzGradientTransport_tendsto_of_spectralH3FirstJet244
    {f : ℕ → A3 → SchwartzMap V3 ℝ}
    {g : A3 → SchwartzMap V3 ℝ}
    {S : ℕ → A3 → H3SpectralScalarState}
    {G : A3 → H3SpectralScalarState}
    (h : H3SchwartzSpectralFirstJetComparison244 f g S G)
    (hThird : ∀ j i k l : A3,
      Tendsto (fun n => schwartzIntegralL2Root244
        (spectralThirdJet244 (f n) j i k l -
          spectralThirdJet244 g j i k l)) atTop (𝓝 0)) :
    Tendsto (fun n => fullSchwartzGradientTransport244 (f n)) atTop
      (𝓝 (fullSchwartzGradientTransport244 g)) :=
  fullSchwartzGradientTransport_tendsto_of_L2L2LinfJets244 f g
    (spectralFirstJet_produces_naturalGradientJets244 h hThird)

/-- A PDE-facing version: the spectral bridge plus ordinary third-jet L²
limits supplies the gradient channel of the existing natural-gradient
approximation structure. No first-jet L∞ hypothesis is left. -/
theorem h3Path_spectralH3FirstJet_implies_fullThirdObservable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {f : ℕ → A3 → SchwartzMap V3 ℝ}
    {g : A3 → SchwartzMap V3 ℝ}
    {S : ℕ → A3 → H3SpectralScalarState}
    {G : A3 → H3SpectralScalarState}
    (hSpectral : H3SchwartzSpectralFirstJetComparison244 f g S G)
    (hThird : ∀ j i k l : A3,
      Tendsto (fun n => schwartzIntegralL2Root244
        (spectralThirdJet244 (f n) j i k l -
          spectralThirdJet244 g j i k l)) atTop (𝓝 0))
    (hMonomial : SchwartzStrongJetConvergence244 f g)
    (hPhysical : fullSchwartzGradientTransport244 g +
        3 * lowNormalRealSchwartzPoint3Monomial g =
          velocityH3TransportDerivative3At u t)
    (h0 : Tendsto (fun n => lowNormalRealSchwartzH3Energy0 (f n)) atTop
      (𝓝 (velocityH3Energy0At u t)))
    (h1 : Tendsto (fun n => lowNormalRealSchwartzH3Energy1 (f n)) atTop
      (𝓝 (velocityH3Energy1At u t)))
    (h2 : Tendsto (fun n => lowNormalRealSchwartzH3Energy2 (f n)) atTop
      (𝓝 (velocityH3Energy2At u t)))
    (h3 : Tendsto (fun n => lowNormalRealSchwartzH3Energy3 (f n)) atTop
      (𝓝 (velocityH3Energy3At u t)))
    (h4 : Tendsto (fun n => lowNormalRealSchwartzH3TopDissipation (f n)) atTop
      (𝓝 (velocityH3Dissipation3At u t))) :
    H3FullThirdSchwartzObservableApproximation244 u t f := by
  let h : H3FullThirdSchwartzNaturalGradientApproximation244 u t f g :=
    { monomialJets := hMonomial
      gradientJets := spectralFirstJet_produces_naturalGradientJets244
        hSpectral hThird
      physical := hPhysical
      energy0 := h0
      energy1 := h1
      energy2 := h2
      energy3 := h3
      top := h4 }
  exact h.toObservable

end
end PrimeTensor.FirstMonomialTriad
