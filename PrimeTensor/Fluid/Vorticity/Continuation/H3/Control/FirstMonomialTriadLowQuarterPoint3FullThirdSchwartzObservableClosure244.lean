import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzKineticAbsorption244
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
# Sequential closure of the actual full-third signed Schwartz budget

Exact real-Schwartz realization of an arbitrary positive-time Navier--Stokes
slice is a stronger premise than the physical H3 path hypotheses supply.
This module weakens that premise to convergence of FIVE actual observables:

* normalized H3 energy E;
* third-jet energy E3;
* fourth-jet dissipation D4;
* full dissipation D;
* the COMPLETE signed full-third transport T3 = G3 + 3 M.

Unlike the earlier first-monomial approximation package, this requires
convergence of the entire signed third-order cubic, including its gradient
part. It does not infer that convergence from ordinary L2 Schwartz density.

The existing kinetic-absorbed nonextension theorem then produces an actual
Schwartz *approximant* with an arbitrarily adverse signed top cubic on each
strict subtail, not merely a hypothetical exact Schwartz solution slice.
Conversely, uniform (or eventually uniform) bounds on the approximants pass
to physical slices and yield conditional continuation.

The approximation premise remains a separate, substantive analytic obligation.
No unrestricted regularity or finite-time singularity conclusion follows.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdObservableClosure244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Five-observable convergence of real Schwartz representatives to the
ACTUAL physical H3 slice. The last limit is for the entire signed T3 cubic,
not just the earlier first interpolation monomial. -/
def H3FullThirdSchwartzObservableApproximation244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : ℕ → A3 → SchwartzMap V3 ℝ) : Prop :=
  Tendsto (fun n => lowNormalRealSchwartzH3Energy (f n)) atTop
    (𝓝 (velocityH3EnergyAt u t)) ∧
  Tendsto (fun n => lowNormalRealSchwartzH3Energy3 (f n)) atTop
    (𝓝 (velocityH3Energy3At u t)) ∧
  Tendsto (fun n => lowNormalRealSchwartzH3TopDissipation (f n)) atTop
    (𝓝 (velocityH3Dissipation3At u t)) ∧
  Tendsto (fun n => lowNormalRealSchwartzH3FullDissipation244 (f n)) atTop
    (𝓝 (velocityH3DissipationAt u t)) ∧
  Tendsto (fun n => fullSchwartzThirdCommutator244 (f n)) atTop
    (𝓝 (velocityH3TransportDerivative3At u t))

/-- Sequential Schwartz-observable approximability at one physical time. -/
def H3FullThirdSchwartzObservableApproximable244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : Prop :=
  ∃ f : ℕ → A3 → SchwartzMap V3 ℝ,
    H3FullThirdSchwartzObservableApproximation244 u t f

/-- Every actual real-Schwartz realization supplies all five observable
limits, through its CONSTANT approximating sequence. -/
theorem h3Path_exactRealSchwartz_implies_fullThirdObservableApproximable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (f : A3 → SchwartzMap V3 ℝ)
    (hRealization : ∀ j : A3,
      loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)) :
    H3FullThirdSchwartzObservableApproximable244 u t := by
  have hE := lowNormalRealSchwartz_pathEnergy_eq u t f hRealization
  have hE3 := lowNormalRealSchwartz_pathEnergy3_eq u t f hRealization
  have hD4 := lowNormalRealSchwartz_pathTopDissipation_eq u t f hRealization
  have hD : velocityH3DissipationAt u t =
      lowNormalRealSchwartzH3FullDissipation244 f := by
    simpa only [lowNormalRealSchwartzH3FullDissipation244] using
      thirdFullSchwartz_pathFullDissipation_eq244 u t f hRealization
  have hT := h3Path_fullThirdTransport_eq_realSchwartz_of_realization244
    hH3 hClass ht f hRealization
  refine ⟨fun _ => f, ?_⟩
  change
    Tendsto (fun _ : ℕ => lowNormalRealSchwartzH3Energy f) atTop
      (𝓝 (velocityH3EnergyAt u t)) ∧
    Tendsto (fun _ : ℕ => lowNormalRealSchwartzH3Energy3 f) atTop
      (𝓝 (velocityH3Energy3At u t)) ∧
    Tendsto (fun _ : ℕ => lowNormalRealSchwartzH3TopDissipation f) atTop
      (𝓝 (velocityH3Dissipation3At u t)) ∧
    Tendsto (fun _ : ℕ => lowNormalRealSchwartzH3FullDissipation244 f) atTop
      (𝓝 (velocityH3DissipationAt u t)) ∧
    Tendsto (fun _ : ℕ => fullSchwartzThirdCommutator244 f) atTop
      (𝓝 (velocityH3TransportDerivative3At u t))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hE]
    exact tendsto_const_nhds
  · rw [hE3]
    exact tendsto_const_nhds
  · rw [hD4]
    exact tendsto_const_nhds
  · rw [hD]
    exact tendsto_const_nhds
  · rw [hT]
    exact tendsto_const_nhds

/-- A signed top-cubic envelope that holds EVENTUALLY along one approximating
Schwartz sequence passes to the actual physical H3 slice. -/
theorem h3Path_fullThirdObservable_limit_signedEnvelope244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t B : ℝ) (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (hApprox : H3FullThirdSchwartzObservableApproximation244 u t f)
    (hBound : ∀ᶠ n : ℕ in atTop,
      -fullSchwartzThirdCommutator244 (f n) ≤
        B * lowNormalRealSchwartzH3Energy (f n) +
          lowNormalRealSchwartzH3FullDissipation244 (f n)) :
    -velocityH3TransportDerivative3At u t ≤
      B * velocityH3EnergyAt u t + velocityH3DissipationAt u t := by
  obtain ⟨hE, _, _, hD, hT⟩ := hApprox
  have hB : Tendsto (fun _ : ℕ => B) atTop (𝓝 B) := tendsto_const_nhds
  exact le_of_tendsto_of_tendsto hT.neg ((hB.mul hE).add hD) hBound

/-- Likewise, a top-fourth-order dissipative dominance statement survives
Schwartz-observable convergence, provided it holds eventually in the sequence. -/
theorem h3Path_fullThirdObservable_limit_spectralDominance244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (hApprox : H3FullThirdSchwartzObservableApproximation244 u t f)
    (hBound : ∀ᶠ n : ℕ in atTop,
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (lowNormalRealSchwartzH3Energy (f n)))) *
        lowNormalRealSchwartzH3Energy3 (f n) ≤
      lowNormalRealSchwartzH3TopDissipation (f n)) :
    (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t))) *
        velocityH3Energy3At u t ≤ velocityH3Dissipation3At u t := by
  obtain ⟨hE, hE3, hD4, _, _⟩ := hApprox
  have hSqrt : Tendsto (fun n => Real.sqrt
      (lowNormalRealSchwartzH3Energy (f n))) atTop
      (𝓝 (Real.sqrt (velocityH3EnergyAt u t))) :=
    (Real.continuous_sqrt.tendsto _).comp hE
  have h4398 : Tendsto (fun _ : ℕ => (4398 : ℝ)) atTop
      (𝓝 (4398 : ℝ)) := tendsto_const_nhds
  have hC : Tendsto
      (fun _ : ℕ => h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient)
      atTop (𝓝 h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) :=
    tendsto_const_nhds
  exact le_of_tendsto_of_tendsto
    ((h4398.mul (hC.mul hSqrt)).mul hE3) hD4 hBound

/-- An eventual Schwartz-approximation envelope on every strict time of one
tail excludes the existing kinetic-absorbed signed nonextension witness.
The approximation premise is NOT inferred from ordinary H3 regularity. -/
theorem h3Path_extension_of_fullThirdApproxSignedEnvelope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hB : 0 ≤ B)
    (hTail : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∃ f : ℕ → A3 → SchwartzMap V3 ℝ,
        H3FullThirdSchwartzObservableApproximation244 u t f ∧
        ∀ᶠ n : ℕ in atTop,
          -fullSchwartzThirdCommutator244 (f n) ≤
            B * lowNormalRealSchwartzH3Energy (f n) +
              lowNormalRealSchwartzH3FullDissipation244 (f n)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨t, ht, hPhysical⟩ :=
    h3PathCanonical_signedTopDominatesDissipation_on_every_subtail
      hH3 hNoExtension hClass hb hd hB
  obtain ⟨f, hApprox, hBound⟩ := hTail t ht
  have hClosed := h3Path_fullThirdObservable_limit_signedEnvelope244
    u t B f hApprox hBound
  exact (not_lt_of_ge hClosed) hPhysical

/-- A sequential real-Schwartz TOP spectral dominance contract likewise
implies physical continuation without any exact slice representation. -/
theorem h3Path_extension_of_fullThirdApproxSpectralDominance244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hTail : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∃ f : ℕ → A3 → SchwartzMap V3 ℝ,
        H3FullThirdSchwartzObservableApproximation244 u t f ∧
        ∀ᶠ n : ℕ in atTop,
          (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (lowNormalRealSchwartzH3Energy (f n)))) *
              lowNormalRealSchwartzH3Energy3 (f n) ≤
            lowNormalRealSchwartzH3TopDissipation (f n)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  apply h3PathCanonical_extension_of_eventual_topSpectralDissipationDominance
    hH3 hClass hb hd
  intro t ht
  obtain ⟨f, hApprox, hBound⟩ := hTail t ht
  exact h3Path_fullThirdObservable_limit_spectralDominance244
    u t f hApprox hBound

/-- If actual H3 continuation fails, on each strict subtail and for every
nonnegative M, SOME MEMBER of any convergent five-observable Schwartz family
violates the kinetic-absorbed signed cubic envelope. This does not require
the sequence to consist of exact time-slices of a Navier--Stokes trajectory. -/
theorem h3Path_noExtension_fullThirdApproxSignedWitness244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hM : 0 ≤ M)
    (hApproxTail : ∀ t : ℝ, t ∈ Set.Ioo d T →
      H3FullThirdSchwartzObservableApproximable244 u t) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      ∃ f : ℕ → A3 → SchwartzMap V3 ℝ,
        H3FullThirdSchwartzObservableApproximation244 u t f ∧
          ∃ n : ℕ,
            M * lowNormalRealSchwartzH3Energy (f n) +
              lowNormalRealSchwartzH3FullDissipation244 (f n) <
            -fullSchwartzThirdCommutator244 (f n) := by
  obtain ⟨t, ht, hPhysical⟩ :=
    h3PathCanonical_signedTopDominatesDissipation_on_every_subtail
      hH3 hNoExtension hClass hb hd hM
  obtain ⟨f, hApprox⟩ := hApproxTail t ht
  refine ⟨t, ht, f, hApprox, ?_⟩
  by_contra hNone
  have hAll : ∀ n : ℕ,
      -fullSchwartzThirdCommutator244 (f n) ≤
        M * lowNormalRealSchwartzH3Energy (f n) +
          lowNormalRealSchwartzH3FullDissipation244 (f n) := by
    intro n
    by_contra hNot
    have hStrict :
        M * lowNormalRealSchwartzH3Energy (f n) +
          lowNormalRealSchwartzH3FullDissipation244 (f n) <
        -fullSchwartzThirdCommutator244 (f n) := lt_of_not_ge hNot
    exact hNone ⟨n, hStrict⟩
  have hClosed := h3Path_fullThirdObservable_limit_signedEnvelope244
    u t M f hApprox (Filter.Eventually.of_forall hAll)
  exact (not_lt_of_ge hClosed) hPhysical

end
end PrimeTensor.FirstMonomialTriad
