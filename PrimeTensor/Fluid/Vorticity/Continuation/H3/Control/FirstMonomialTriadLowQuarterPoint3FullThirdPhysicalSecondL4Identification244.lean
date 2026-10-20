import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdCanonicalSecondL4Trace244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzMatchedSecondFamily244
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Tactic

/-!
# The canonical second-order L⁴ trace is the actual physical H³ second derivative

The previously constructed choice-independent second-jet L⁴ completion and the
previously identified physical second-jet L² completion are limits of exactly
the same literal real Schwartz second derivatives.  A single sequence converges
in two different Banach spaces; mathlib's convergence-in-measure uniqueness
proves that the two limits agree almost everywhere, without requiring the
infinite Euclidean carrier to have finite measure.

This establishes a genuine L⁴ representative of the old physical H³ second
jet and its independence from Schwartz witnesses.  Identification of the
full third-order nonlinear spatial pairing remains a subsequent step.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypePhysicalSecondL4Ident244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

local instance l2ExponentAtLeastOnePhysical244 : Fact (1 ≤ (2 : ENNReal)) :=
  ⟨by norm_num⟩
local instance l4ExponentAtLeastOnePhysical244 : Fact (1 ≤ (4 : ENNReal)) :=
  ⟨by norm_num⟩

private abbrev L4PhysicalCarrier244 := Lp ℝ 4 (volume : Measure V3)

/-- **Dual-Lp uniqueness.** A sequence of actual functions converging in
both L² and L⁴ determines a single almost-everywhere limit.  Neither
finite-volume measure nor a new comparison hypothesis on the limits is used. -/
theorem h3SecondJet_dualLp_limits_ae_eq244
    (f₂ : ℕ → H3FourierRealL2)
    (f₄ : ℕ → L4PhysicalCarrier244)
    (L₂ : H3FourierRealL2) (L₄ : L4PhysicalCarrier244)
    (hEq : ∀ n : ℕ,
      (f₂ n : V3 → ℝ) =ᵐ[(volume : Measure V3)] (f₄ n : V3 → ℝ))
    (h₂ : Tendsto f₂ atTop (𝓝 L₂))
    (h₄ : Tendsto f₄ atTop (𝓝 L₄)) :
    (L₂ : V3 → ℝ) =ᵐ[(volume : Measure V3)] (L₄ : V3 → ℝ) := by
  have hMeasure₂ : TendstoInMeasure (volume : Measure V3)
      (fun n => (f₂ n : V3 → ℝ)) atTop (L₂ : V3 → ℝ) :=
    tendstoInMeasure_of_tendsto_Lp h₂
  have hMeasure₄ : TendstoInMeasure (volume : Measure V3)
      (fun n => (f₄ n : V3 → ℝ)) atTop (L₄ : V3 → ℝ) :=
    tendstoInMeasure_of_tendsto_Lp h₄
  exact tendstoInMeasure_ae_unique
    (hMeasure₂.congr_left hEq) hMeasure₄

/-- For ANY fully matched Schwartz family, its canonical strong L⁴
second-jet trace represents exactly the matched weighted-spectral L²
second jet, almost everywhere on the original Euclidean carrier. -/
theorem h3MatchedSchwartz_secondL4_ae_eq_spectralSecondL2244
    (U : H3SpectralVelocityState)
    (F : H3MatchedSchwartzGradientCompletion244 U)
    (j : Fin 3) (a b : A3) :
    (weightedH3CanonicalSecondJetL4Trace244 U j a b : V3 → ℝ)
      =ᵐ[(volume : Measure V3)]
    (matchedSpectralSecondFourierJets244 U
      (h3AxisOfFin3 j, (a, b)) : V3 → ℝ) := by
  let μ : Measure V3 := volume
  let D : ℕ → SchwartzMap V3 ℝ := fun n =>
    ∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b}
        (F.family.approximants n (h3AxisOfFin3 j)))
  let f₂ : ℕ → H3FourierRealL2 := fun n => (D n).toLp 2 μ
  let f₄ : ℕ → L4PhysicalCarrier244 := fun n => (D n).toLp 4 μ
  have hEq (n : ℕ) :
      (f₂ n : V3 → ℝ) =ᵐ[μ] (f₄ n : V3 → ℝ) := by
    change ((D n).toLp 2 μ : V3 → ℝ) =ᵐ[μ]
      ((D n).toLp 4 μ : V3 → ℝ)
    exact ((D n).coeFn_toLp 2 μ).trans
      ((D n).coeFn_toLp 4 μ).symm
  have hSpectral : Tendsto
      (fun n => matchedSpectralSecondFourierJets244 (F.spectral n))
      atTop (𝓝 (matchedSpectralSecondFourierJets244 U)) :=
    continuous_matchedSpectralSecondFourierJets244.continuousAt.tendsto.comp
      F.spectral_tendsto
  have hCoordinate := (tendsto_pi_nhds.mp hSpectral)
    (h3AxisOfFin3 j, (a, b))
  have hExact (n : ℕ) :
      f₂ n = matchedSpectralSecondFourierJets244 (F.spectral n)
        (h3AxisOfFin3 j, (a, b)) := by
    change (D n).toLp 2 μ = _
    exact F.second_exact n (h3AxisOfFin3 j) a b
  have hSeq : f₂ = fun n =>
      matchedSpectralSecondFourierJets244 (F.spectral n)
        (h3AxisOfFin3 j, (a, b)) := by
    funext n
    exact hExact n
  have h₂ : Tendsto f₂ atTop
      (𝓝 (matchedSpectralSecondFourierJets244 U
        (h3AxisOfFin3 j, (a, b)))) := by
    rw [hSeq]
    exact hCoordinate
  have h₄ : Tendsto f₄ atTop
      (𝓝 (weightedH3CanonicalSecondJetL4Trace244 U j a b)) := by
    exact weightedH3CanonicalSecondJetL4Trace_tendsto244 U F j a b
  exact (h3SecondJet_dualLp_limits_ae_eq244 f₂ f₄
    (matchedSpectralSecondFourierJets244 U (h3AxisOfFin3 j, (a, b)))
    (weightedH3CanonicalSecondJetL4Trace244 U j a b)
    hEq h₂ h₄).symm

/-- The resulting a.e. identity is **intrinsic** to U.  It has no
remaining approximation-family parameter in its statement. -/
theorem weightedH3CanonicalSecondJetL4Trace_ae_eq_spectralL2244
    (U : H3SpectralVelocityState) (j : Fin 3) (a b : A3) :
    (weightedH3CanonicalSecondJetL4Trace244 U j a b : V3 → ℝ)
      =ᵐ[(volume : Measure V3)]
    (matchedSpectralSecondFourierJets244 U
      (h3AxisOfFin3 j, (a, b)) : V3 → ℝ) := by
  let F := Classical.choice (exists_h3MatchedSchwartzGradientCompletion244 U)
  exact h3MatchedSchwartz_secondL4_ae_eq_spectralSecondL2244 U F j a b

/-- **Physical trace identification.** At an actual Fourier-compatible
H³ velocity snapshot, the canonical L⁴ trace and the old physical L²
second derivative have literally the same measurable representative,
a.e.  The coordinate carrier is the existing volume-preserving Point3
isometry; no Schwartz realization of u(t) is assumed. -/
theorem weightedH3CanonicalSecondJetL4Trace_ae_eq_actualPhysical244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) (a b : A3) :
    (weightedH3CanonicalSecondJetL4Trace244
        (velocityH3SpectralStateAt u t hInt hMeas hFourier) j a b :
        V3 → ℝ)
      =ᵐ[(volume : Measure V3)]
    (h3ToFourierRealL2
        (velocityH3L2JetAt u t hInt hMeas
          (h3JetSlot2 j (h3ClassicalizationFinOfAxis a)
            (h3ClassicalizationFinOfAxis b))) : V3 → ℝ) := by
  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt u t hInt hMeas hFourier
  have hAE := weightedH3CanonicalSecondJetL4Trace_ae_eq_spectralL2244
    U j a b
  have hExact :
      matchedSpectralSecondFourierJets244 U
          (h3AxisOfFin3 j, (a, b)) =
        h3ToFourierRealL2
          (velocityH3L2JetAt u t hInt hMeas
            (h3JetSlot2 j (h3ClassicalizationFinOfAxis a)
              (h3ClassicalizationFinOfAxis b))) := by
    -- The matched Fourier-jet coordinate is indexed by an Axis, not a Fin.
    -- First expose the inverse index map, then convert to the actual jet.
    change h3ToFourierRealL2
      (h3SpectralVelocitySecondPhysicalJetFamily244 U
        (h3ClassicalizationFinOfAxis (h3AxisOfFin3 j)) a b) = _
    rw [h3ClassicalizationFinOfAxis_h3AxisOfFin3]
    -- U is definitionally the physical snapshot's weighted spectral state.
    change h3ToFourierRealL2
      (h3SpectralVelocitySecondPhysicalJetFamily244
        (velocityH3SpectralStateAt u t hInt hMeas hFourier) j a b) = _
    rw [h3SpectralVelocitySecondPhysicalJetFamily_actualJet244 hFourier]
  rw [hExact] at hAE
  exact hAE

/-- All 27 physical ordered second derivatives possess a canonical,
choice-independent L⁴ representative.  This is an **existence** statement
for the old physical L² jet and no new regularity assumption on u(t). -/
theorem exists_actualPhysicalSecondJet_canonicalL4Representative244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    ∀ j : Fin 3, ∀ a b : A3,
      ∃ H : L4PhysicalCarrier244,
        (H : V3 → ℝ) =ᵐ[(volume : Measure V3)]
          (h3ToFourierRealL2
            (velocityH3L2JetAt u t hInt hMeas
              (h3JetSlot2 j (h3ClassicalizationFinOfAxis a)
                (h3ClassicalizationFinOfAxis b))) : V3 → ℝ) := by
  intro j a b
  exact ⟨weightedH3CanonicalSecondJetL4Trace244
    (velocityH3SpectralStateAt u t hInt hMeas hFourier) j a b,
    weightedH3CanonicalSecondJetL4Trace_ae_eq_actualPhysical244
      hFourier j a b⟩

end
end PrimeTensor.FirstMonomialTriad
