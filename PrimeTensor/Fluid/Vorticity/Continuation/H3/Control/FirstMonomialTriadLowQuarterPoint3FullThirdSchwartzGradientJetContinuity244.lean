import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzSplitJetClosure244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzRootContinuity244
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
# Three-difference-root continuity of the complete 3–3–1 gradient channel

The previous split-jet closure still assumed convergence of the entire
third-order Schwartz gradient transport. This module proves that convergence
from actual Lebesgue derivative difference norms, without postulating any
nonlinear gradient-integral limit.

Each 3+3+1 integrand has a third-derivative L² factor, a distinct third-
derivative L⁴ factor, and a first-derivative L⁴ factor. The established
real 2–4–4 Hölder/telescoping inequality bounds its perturbation by three
products. Convergence of the two undifferenced L⁴ norms follows from the
previously proved reverse triangle inequality. We then sum all four triple
products at every physical five-index slot, and all five finite axes.

This is stronger than an optimal H³-continuity theorem: third derivatives
converging in L⁴ is additional data, not implied by an H³ graph limit.
The physical target identity and quadratic jet-energy approximation still
remain independent hypotheses. No solution-slice realization or global
Navier–Stokes regularity is inferred from ordinary Schwartz density.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdGradientJet244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exactly THREE actual norm-difference limits for a signed 3–3–1 triple.
The independent L⁴ norm limits are NOT assumed. -/
def SchwartzGradientTripleDifferenceJets244
    (A B C : ℕ → SchwartzMap V3 ℝ)
    (a b c : SchwartzMap V3 ℝ) : Prop :=
  Tendsto (fun n => schwartzIntegralL2Root244 (A n - a)) atTop (𝓝 0) ∧
  Tendsto (fun n => schwartzIntegralL4Root244 (B n - b)) atTop (𝓝 0) ∧
  Tendsto (fun n => schwartzIntegralL4Root244 (C n - c)) atTop (𝓝 0)

/-- Real three-factor 2–4–4 continuity, retaining the factor 2 of the
physical transport pairing. All norm convergence follows from just the
three *difference* limits, with no assumed integral convergence. -/
theorem fullGradientTriple_tendsto_of_threeDifferenceJets244
    (A B C : ℕ → SchwartzMap V3 ℝ)
    (a b c : SchwartzMap V3 ℝ)
    (hJets : SchwartzGradientTripleDifferenceJets244 A B C a b c) :
    Tendsto (fun n => fullGradientTriple244 (A n) (B n) (C n)) atTop
      (𝓝 (fullGradientTriple244 a b c)) := by
  obtain ⟨hA, hB, hC⟩ := hJets
  have hBNorm := schwartzIntegralL4Root_tendsto_of_difference244 B b hB
  have hCNorm := schwartzIntegralL4Root_tendsto_of_difference244 C c hC
  have hFirst : Tendsto (fun n =>
      schwartzIntegralL2Root244 (A n - a) *
        (schwartzIntegralL4Root244 (B n) *
          schwartzIntegralL4Root244 (C n))) atTop (𝓝 0) := by
    simpa only [zero_mul] using hA.mul (hBNorm.mul hCNorm)
  have hSecond : Tendsto (fun n =>
      schwartzIntegralL2Root244 a *
        (schwartzIntegralL4Root244 (B n - b) *
          schwartzIntegralL4Root244 (C n))) atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => schwartzIntegralL2Root244 a)
        atTop (𝓝 (schwartzIntegralL2Root244 a))).mul
        (hB.mul hCNorm)
  have hThird : Tendsto (fun n =>
      schwartzIntegralL2Root244 a *
        (schwartzIntegralL4Root244 b *
          schwartzIntegralL4Root244 (C n - c))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => schwartzIntegralL2Root244 a)
        atTop (𝓝 (schwartzIntegralL2Root244 a))).mul
        ((tendsto_const_nhds : Tendsto
          (fun _ : ℕ => schwartzIntegralL4Root244 b)
          atTop (𝓝 (schwartzIntegralL4Root244 b))).mul hC)
  have hBound : Tendsto (fun n =>
      schwartzIntegralL2Root244 (A n - a) *
        (schwartzIntegralL4Root244 (B n) *
          schwartzIntegralL4Root244 (C n)) +
      schwartzIntegralL2Root244 a *
        (schwartzIntegralL4Root244 (B n - b) *
          schwartzIntegralL4Root244 (C n)) +
      schwartzIntegralL2Root244 a *
        (schwartzIntegralL4Root244 b *
          schwartzIntegralL4Root244 (C n - c))) atTop (𝓝 0) := by
    simpa only [zero_add] using (hFirst.add hSecond).add hThird
  have hAbs : Tendsto (fun n =>
      |schwartzTripleIntegral244 (A n) (B n) (C n) -
        schwartzTripleIntegral244 a b c|) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact abs_nonneg _
    · intro n
      exact schwartzTripleIntegral_difference_le244
        (A n) (B n) (C n) a b c
    · exact hBound
  have hIntegral : Tendsto (fun n =>
      schwartzTripleIntegral244 (A n) (B n) (C n)) atTop
      (𝓝 (schwartzTripleIntegral244 a b c)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using hAbs
  change Tendsto (fun n => 2 * schwartzTripleIntegral244 (A n) (B n) (C n))
    atTop (𝓝 (2 * schwartzTripleIntegral244 a b c))
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ))
    atTop (𝓝 2)).mul hIntegral

/-- The actual first-order Schwartz derivative in the gradient commutator. -/
private abbrev gradientFirstJet244 (f : A3 → SchwartzMap V3 ℝ)
    (j r : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection r} (f j)

/-- The actual third-order Schwartz derivative, with derivative order
unchanged from the physical 3+3+1 gradient transport. -/
private abbrev gradientThirdJet244 (f : A3 → SchwartzMap V3 ℝ)
    (j i k l : A3) : SchwartzMap V3 ℝ :=
  ∂_{h3FourierAxisDirection i}
    (∂_{h3FourierAxisDirection k}
      (∂_{h3FourierAxisDirection l} (f j)))

/-- Four actual 3–3–1 gradient triples per ordered five-axis slot.
Each triple needs only its three difference-root limits. -/
def SchwartzFullGradientDifferenceJets244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ) : Prop :=
  ∀ j i k l r : A3,
    SchwartzGradientTripleDifferenceJets244
      (fun n => gradientThirdJet244 (f n) j i k l)
      (fun n => gradientThirdJet244 (f n) r i k l)
      (fun n => gradientFirstJet244 (f n) j r)
      (gradientThirdJet244 g j i k l)
      (gradientThirdJet244 g r i k l)
      (gradientFirstJet244 g j r) ∧
    SchwartzGradientTripleDifferenceJets244
      (fun n => gradientThirdJet244 (f n) j i k l)
      (fun n => gradientThirdJet244 (f n) j i k r)
      (fun n => gradientFirstJet244 (f n) r l)
      (gradientThirdJet244 g j i k l)
      (gradientThirdJet244 g j i k r)
      (gradientFirstJet244 g r l) ∧
    SchwartzGradientTripleDifferenceJets244
      (fun n => gradientThirdJet244 (f n) j i k l)
      (fun n => gradientThirdJet244 (f n) j i r l)
      (fun n => gradientFirstJet244 (f n) r k)
      (gradientThirdJet244 g j i k l)
      (gradientThirdJet244 g j i r l)
      (gradientFirstJet244 g r k) ∧
    SchwartzGradientTripleDifferenceJets244
      (fun n => gradientThirdJet244 (f n) j i k l)
      (fun n => gradientThirdJet244 (f n) j r k l)
      (fun n => gradientFirstJet244 (f n) r i)
      (gradientThirdJet244 g j i k l)
      (gradientThirdJet244 g j r k l)
      (gradientFirstJet244 g r i)

/-- Finite indexed real sums preserve scalar sequential limits; all
five-axis sums below are genuinely finite. -/
private theorem fullGradient_finiteSum_tendsto244
    {J : Type*} [Fintype J]
    (F : ℕ → J → ℝ) (G : J → ℝ)
    (h : ∀ p : J, Tendsto (fun n => F n p) atTop (𝓝 (G p))) :
    Tendsto (fun n => ∑ p : J, F n p) atTop
      (𝓝 (∑ p : J, G p)) := by
  classical
  have hs (S : Finset J) :
      Tendsto (fun n => Finset.sum S (F n)) atTop
        (𝓝 (Finset.sum S G)) := by
    induction S using Finset.induction_on with
    | empty =>
        simpa using (tendsto_const_nhds : Tendsto
          (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    | @insert p S hp ih =>
        simpa only [Finset.sum_insert hp] using (h p).add ih
  exact hs (Finset.univ : Finset J)

/-- Five nested axis sums preserve the limits, with every one of the 243
ordered physical slots counted exactly once. -/
private theorem fullGradient_fivefold_tendsto244
    (F : ℕ → A3 → A3 → A3 → A3 → A3 → ℝ)
    (G : A3 → A3 → A3 → A3 → A3 → ℝ)
    (h : ∀ j i k l r : A3,
      Tendsto (fun n => F n j i k l r) atTop (𝓝 (G j i k l r))) :
    Tendsto (fun n => ∑ j : A3, ∑ i : A3, ∑ k : A3,
      ∑ l : A3, ∑ r : A3, F n j i k l r) atTop
      (𝓝 (∑ j : A3, ∑ i : A3, ∑ k : A3,
        ∑ l : A3, ∑ r : A3, G j i k l r)) := by
  have hR (j i k l : A3) :=
    fullGradient_finiteSum_tendsto244
      (fun n r => F n j i k l r) (fun r => G j i k l r)
      (fun r => h j i k l r)
  have hL (j i k : A3) :=
    fullGradient_finiteSum_tendsto244
      (fun n l => ∑ r : A3, F n j i k l r)
      (fun l => ∑ r : A3, G j i k l r) (hR j i k)
  have hK (j i : A3) :=
    fullGradient_finiteSum_tendsto244
      (fun n k => ∑ l : A3, ∑ r : A3, F n j i k l r)
      (fun k => ∑ l : A3, ∑ r : A3, G j i k l r) (hL j i)
  have hI (j : A3) :=
    fullGradient_finiteSum_tendsto244
      (fun n i => ∑ k : A3, ∑ l : A3, ∑ r : A3, F n j i k l r)
      (fun i => ∑ k : A3, ∑ l : A3, ∑ r : A3, G j i k l r) (hK j)
  exact fullGradient_finiteSum_tendsto244
    (fun n j => ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
      F n j i k l r)
    (fun j => ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3,
      G j i k l r) hI

/-- The ENTIRE real-Schwartz 3–3–1 gradient channel converges from the
four sets of difference roots at each physical five-index slot. No
convergence of the nonlinear gradient observable is an input. -/
theorem fullSchwartzGradientTransport_tendsto_of_differenceJets244
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ)
    (hJets : SchwartzFullGradientDifferenceJets244 f g) :
    Tendsto (fun n => fullSchwartzGradientTransport244 (f n)) atTop
      (𝓝 (fullSchwartzGradientTransport244 g)) := by
  have hAxis (j i k l r : A3) :
      Tendsto (fun n => fullSchwartzGradientAxis244 (f n) j i k l r)
        atTop (𝓝 (fullSchwartzGradientAxis244 g j i k l r)) := by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hJets j i k l r
    have hTerm1 := fullGradientTriple_tendsto_of_threeDifferenceJets244
      (fun n => gradientThirdJet244 (f n) j i k l)
      (fun n => gradientThirdJet244 (f n) r i k l)
      (fun n => gradientFirstJet244 (f n) j r)
      (gradientThirdJet244 g j i k l)
      (gradientThirdJet244 g r i k l)
      (gradientFirstJet244 g j r) h₁
    have hTerm2 := fullGradientTriple_tendsto_of_threeDifferenceJets244
      (fun n => gradientThirdJet244 (f n) j i k l)
      (fun n => gradientThirdJet244 (f n) j i k r)
      (fun n => gradientFirstJet244 (f n) r l)
      (gradientThirdJet244 g j i k l)
      (gradientThirdJet244 g j i k r)
      (gradientFirstJet244 g r l) h₂
    have hTerm3 := fullGradientTriple_tendsto_of_threeDifferenceJets244
      (fun n => gradientThirdJet244 (f n) j i k l)
      (fun n => gradientThirdJet244 (f n) j i r l)
      (fun n => gradientFirstJet244 (f n) r k)
      (gradientThirdJet244 g j i k l)
      (gradientThirdJet244 g j i r l)
      (gradientFirstJet244 g r k) h₃
    have hTerm4 := fullGradientTriple_tendsto_of_threeDifferenceJets244
      (fun n => gradientThirdJet244 (f n) j i k l)
      (fun n => gradientThirdJet244 (f n) j r k l)
      (fun n => gradientFirstJet244 (f n) r i)
      (gradientThirdJet244 g j i k l)
      (gradientThirdJet244 g j r k l)
      (gradientFirstJet244 g r i) h₄
    change Tendsto (fun n =>
      fullGradientTriple244 (gradientThirdJet244 (f n) j i k l) (gradientThirdJet244 (f n) r i k l) (gradientFirstJet244 (f n) j r) +
      fullGradientTriple244 (gradientThirdJet244 (f n) j i k l) (gradientThirdJet244 (f n) j i k r) (gradientFirstJet244 (f n) r l) +
      fullGradientTriple244 (gradientThirdJet244 (f n) j i k l) (gradientThirdJet244 (f n) j i r l) (gradientFirstJet244 (f n) r k) +
      fullGradientTriple244 (gradientThirdJet244 (f n) j i k l) (gradientThirdJet244 (f n) j r k l) (gradientFirstJet244 (f n) r i)) atTop
      (𝓝 (
        fullGradientTriple244 (gradientThirdJet244 g j i k l) (gradientThirdJet244 g r i k l) (gradientFirstJet244 g j r) +
        fullGradientTriple244 (gradientThirdJet244 g j i k l) (gradientThirdJet244 g j i k r) (gradientFirstJet244 g r l) +
        fullGradientTriple244 (gradientThirdJet244 g j i k l) (gradientThirdJet244 g j i r l) (gradientFirstJet244 g r k) +
        fullGradientTriple244 (gradientThirdJet244 g j i k l) (gradientThirdJet244 g j r k l) (gradientFirstJet244 g r i)))
    exact ((hTerm1.add hTerm2).add hTerm3).add hTerm4
  change Tendsto (fun n => ∑ j : A3, ∑ i : A3, ∑ k : A3,
      ∑ l : A3, ∑ r : A3, fullSchwartzGradientAxis244 (f n) j i k l r)
    atTop (𝓝 (∑ j : A3, ∑ i : A3, ∑ k : A3,
      ∑ l : A3, ∑ r : A3, fullSchwartzGradientAxis244 g j i k l r))
  exact fullGradient_fivefold_tendsto244
    (fun n j i k l r => fullSchwartzGradientAxis244 (f n) j i k l r)
    (fun j i k l r => fullSchwartzGradientAxis244 g j i k l r)
    hAxis

/-- Replace the previous postulated nonlinear gradient limit with actual
Schwartz 2–4–4 norm-difference hypotheses. The signed 243-slot monomial
requires only its established three-difference-jet convergence. -/
structure H3FullThirdSchwartzGradientJetApproximation244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ) : Prop where
  monomialJets : SchwartzThreeDifferenceJetConvergence244 f g
  gradientJets : SchwartzFullGradientDifferenceJets244 f g
  physical : fullSchwartzGradientTransport244 g +
      3 * lowNormalRealSchwartzPoint3Monomial g =
    velocityH3TransportDerivative3At u t
  energy0 : Tendsto (fun n => lowNormalRealSchwartzH3Energy0 (f n)) atTop
    (𝓝 (velocityH3Energy0At u t))
  energy1 : Tendsto (fun n => lowNormalRealSchwartzH3Energy1 (f n)) atTop
    (𝓝 (velocityH3Energy1At u t))
  energy2 : Tendsto (fun n => lowNormalRealSchwartzH3Energy2 (f n)) atTop
    (𝓝 (velocityH3Energy2At u t))
  energy3 : Tendsto (fun n => lowNormalRealSchwartzH3Energy3 (f n)) atTop
    (𝓝 (velocityH3Energy3At u t))
  top : Tendsto (fun n => lowNormalRealSchwartzH3TopDissipation (f n)) atTop
    (𝓝 (velocityH3Dissipation3At u t))

/-- The genuinely derived gradient convergence discharges the split-jet
structure's former separate gradient limit hypothesis. -/
theorem H3FullThirdSchwartzGradientJetApproximation244.toSplitJet
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    {f : ℕ → A3 → SchwartzMap V3 ℝ}
    {g : A3 → SchwartzMap V3 ℝ}
    (h : H3FullThirdSchwartzGradientJetApproximation244 u t f g) :
    H3FullThirdSchwartzSplitJetApproximation244 u t f g := by
  exact {
    jets := h.monomialJets.toStrongJets
    gradient := fullSchwartzGradientTransport_tendsto_of_differenceJets244
      f g h.gradientJets
    physical := h.physical
    energy0 := h.energy0
    energy1 := h.energy1
    energy2 := h.energy2
    energy3 := h.energy3
    top := h.top
  }

/-- The five physical observables follow without assuming convergence of
either nonlinear cubic channel. -/
theorem H3FullThirdSchwartzGradientJetApproximation244.toObservable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    {f : ℕ → A3 → SchwartzMap V3 ℝ}
    {g : A3 → SchwartzMap V3 ℝ}
    (h : H3FullThirdSchwartzGradientJetApproximation244 u t f g) :
    H3FullThirdSchwartzObservableApproximation244 u t f :=
  h.toSplitJet.toObservable

/-- An existence condition with ONLY derivative norms, quadratic block
limits and a physical target identity; no nonlinear limit is assumed. -/
def H3FullThirdSchwartzGradientJetApproximable244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : Prop :=
  ∃ f : ℕ → A3 → SchwartzMap V3 ℝ,
    ∃ g : A3 → SchwartzMap V3 ℝ,
      H3FullThirdSchwartzGradientJetApproximation244 u t f g

/-- The root-level approximation condition implies all five previous
Schwartz-observable limits, including the COMPLETE signed third cubic. -/
theorem h3Path_gradientJets_implies_fullThirdObservableApproximable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    (hJets : H3FullThirdSchwartzGradientJetApproximable244 u t) :
    H3FullThirdSchwartzObservableApproximable244 u t := by
  obtain ⟨f, g, h⟩ := hJets
  exact ⟨f, h.toObservable⟩

/-- Actual nonextension plus gradient-jet approximability forces some
Schwartz approximant to violate every fixed signed cubic envelope on each
strict subtail. Neither nonlinear cubic convergence is an assumption. -/
theorem h3Path_noExtension_gradientJetSignedWitness244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hM : 0 ≤ M)
    (hTail : ∀ t : ℝ, t ∈ Set.Ioo d T →
      H3FullThirdSchwartzGradientJetApproximable244 u t) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      ∃ f : ℕ → A3 → SchwartzMap V3 ℝ,
        H3FullThirdSchwartzObservableApproximation244 u t f ∧
        ∃ n : ℕ,
          M * lowNormalRealSchwartzH3Energy (f n) +
            lowNormalRealSchwartzH3FullDissipation244 (f n) <
            -fullSchwartzThirdCommutator244 (f n) := by
  exact h3Path_noExtension_fullThirdApproxSignedWitness244
    hH3 hNoExtension hClass hb hd hM
    (fun t ht => h3Path_gradientJets_implies_fullThirdObservableApproximable244
      (hTail t ht))

/-- A signed cubic envelope verified on these root-convergent families
supplies a conditional genuine H³ smooth continuation. -/
theorem h3Path_extension_of_gradientJetSignedEnvelope244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hB : 0 ≤ B)
    (hTail : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∃ f : ℕ → A3 → SchwartzMap V3 ℝ,
        ∃ g : A3 → SchwartzMap V3 ℝ,
          H3FullThirdSchwartzGradientJetApproximation244 u t f g ∧
          (∀ᶠ n : ℕ in atTop,
            -fullSchwartzThirdCommutator244 (f n) ≤
              B * lowNormalRealSchwartzH3Energy (f n) +
                lowNormalRealSchwartzH3FullDissipation244 (f n))) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  apply h3Path_extension_of_fullThirdApproxSignedEnvelope244
    hH3 hClass hb hd hB
  intro t ht
  obtain ⟨f, g, h, hBound⟩ := hTail t ht
  exact ⟨f, h.toObservable, hBound⟩

/-- The previously proved spectral continuation criterion also survives
when the approximation contracts are supplied by derivative-root limits. -/
theorem h3Path_extension_of_gradientJetTopSpectralDominance244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hd : d ∈ Set.Ioo b T)
    (hTail : ∀ t : ℝ, t ∈ Set.Ioo d T →
      ∃ f : ℕ → A3 → SchwartzMap V3 ℝ,
        ∃ g : A3 → SchwartzMap V3 ℝ,
          H3FullThirdSchwartzGradientJetApproximation244 u t f g ∧
          (∀ᶠ n : ℕ in atTop,
            (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
              Real.sqrt (lowNormalRealSchwartzH3Energy (f n)))) *
                lowNormalRealSchwartzH3Energy3 (f n) ≤
              lowNormalRealSchwartzH3TopDissipation (f n))) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  apply h3Path_extension_of_fullThirdApproxSpectralDominance244
    hH3 hClass hb hd
  intro t ht
  obtain ⟨f, g, h, hBound⟩ := hTail t ht
  exact ⟨f, h.toObservable, hBound⟩

end
end PrimeTensor.FirstMonomialTriad
