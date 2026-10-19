import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSchwartzObservableClosure244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzStrongJetContinuity244
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
# Split-jet route to the complete signed Schwartz H³ observable closure

The five-observable closure in the preceding module is a useful final
interface, but demanding convergence of the entire signed third commutator
as an input conceals its two distinct analytic channels.

Here the 243-slot monomial channel is discharged by the already-proved
strong L²/L⁴ jet continuity theorem. Only convergence of the separate
four-term-per-axis gradient block and its identification with the physical
signed transport remain explicit.

The canonical full H³ energy and full dissipation limits are assembled from
limits of the four physical derivative-square energy blocks and the fourth-
order top dissipation. No total-energy or total-dissipation limit is assumed.

This does NOT establish strong Schwartz graph density for every actual H³
slice. In particular, the gradient-channel convergence and the physical
identity are substantive unproved-by-this-file hypotheses.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeFullThirdSplitJetClosure244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- All four separately convergent quadratic blocks jointly determine the
normalized physical energy limit; its constant 1 is retained. -/
theorem thirdFullSchwartz_energy_tendsto_of_fourBlocks244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (h0 : Tendsto (fun n => lowNormalRealSchwartzH3Energy0 (f n)) atTop
      (𝓝 (velocityH3Energy0At u t)))
    (h1 : Tendsto (fun n => lowNormalRealSchwartzH3Energy1 (f n)) atTop
      (𝓝 (velocityH3Energy1At u t)))
    (h2 : Tendsto (fun n => lowNormalRealSchwartzH3Energy2 (f n)) atTop
      (𝓝 (velocityH3Energy2At u t)))
    (h3 : Tendsto (fun n => lowNormalRealSchwartzH3Energy3 (f n)) atTop
      (𝓝 (velocityH3Energy3At u t))) :
    Tendsto (fun n => lowNormalRealSchwartzH3Energy (f n)) atTop
      (𝓝 (velocityH3EnergyAt u t)) := by
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hSum := (((hOne.add h0).add h1).add h2).add h3
  have hRewrite :
      (fun n => lowNormalRealSchwartzH3Energy (f n)) =
        (fun n => 1 + lowNormalRealSchwartzH3Energy0 (f n) +
          lowNormalRealSchwartzH3Energy1 (f n) +
          lowNormalRealSchwartzH3Energy2 (f n) +
          lowNormalRealSchwartzH3Energy3 (f n)) := by
    funext n
    rw [lowNormalRealSchwartzH3Energy_eq_one_add_quadratic,
      lowNormalRealSchwartzH3EnergyQuadratic_eq_sum]
    ring
  rw [hRewrite]
  change Tendsto
    (fun n => 1 + lowNormalRealSchwartzH3Energy0 (f n) +
      lowNormalRealSchwartzH3Energy1 (f n) +
      lowNormalRealSchwartzH3Energy2 (f n) +
      lowNormalRealSchwartzH3Energy3 (f n)) atTop
    (𝓝 (1 + velocityH3Energy0At u t + velocityH3Energy1At u t +
      velocityH3Energy2At u t + velocityH3Energy3At u t))
  exact hSum

/-- Four actual Schwartz viscous blocks converge to the complete physical
H³ dissipation. The equality D=D₀+D₁+D₂+D₃ is already established. -/
theorem thirdFullSchwartz_dissipation_tendsto_of_fourBlocks244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (h1 : Tendsto (fun n => lowNormalRealSchwartzH3Energy1 (f n)) atTop
      (𝓝 (velocityH3Energy1At u t)))
    (h2 : Tendsto (fun n => lowNormalRealSchwartzH3Energy2 (f n)) atTop
      (𝓝 (velocityH3Energy2At u t)))
    (h3 : Tendsto (fun n => lowNormalRealSchwartzH3Energy3 (f n)) atTop
      (𝓝 (velocityH3Energy3At u t)))
    (h4 : Tendsto (fun n => lowNormalRealSchwartzH3TopDissipation (f n)) atTop
      (𝓝 (velocityH3Dissipation3At u t))) :
    Tendsto (fun n => lowNormalRealSchwartzH3FullDissipation244 (f n)) atTop
      (𝓝 (velocityH3DissipationAt u t)) := by
  have hSum := ((h1.add h2).add h3).add h4
  have hRewrite :
      (fun n => lowNormalRealSchwartzH3FullDissipation244 (f n)) =
        (fun n => lowNormalRealSchwartzH3Energy1 (f n) +
          lowNormalRealSchwartzH3Energy2 (f n) +
          lowNormalRealSchwartzH3Energy3 (f n) +
          lowNormalRealSchwartzH3TopDissipation (f n)) := by
    rfl
  rw [hRewrite]
  rw [thirdFullPhysicalDissipation_eq_lowerEnergies_add_top244]
  exact hSum

/-- Strong convergence in the genuine 243-slot mixed jets already forces
convergence of the signed monomial. Thus full third-order transport follows
from convergence of ONLY the separate gradient block and a physical target
identity. The full cubic is NOT postulated convergent. -/
theorem thirdFullSchwartz_cubic_tendsto_of_splitJets244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ)
    (hJets : SchwartzStrongJetConvergence244 f g)
    (hGradient : Tendsto
      (fun n => fullSchwartzGradientTransport244 (f n)) atTop
      (𝓝 (fullSchwartzGradientTransport244 g)))
    (hPhysical : fullSchwartzGradientTransport244 g +
        3 * lowNormalRealSchwartzPoint3Monomial g =
      velocityH3TransportDerivative3At u t) :
    Tendsto (fun n => fullSchwartzThirdCommutator244 (f n)) atTop
      (𝓝 (velocityH3TransportDerivative3At u t)) := by
  have hM := lowNormalRealSchwartz_firstMonomial_tendsto_of_strongJets244
    f g hJets
  have hThree : Tendsto
      (fun n => 3 * lowNormalRealSchwartzPoint3Monomial (f n)) atTop
      (𝓝 (3 * lowNormalRealSchwartzPoint3Monomial g)) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (3 : ℝ))
      atTop (𝓝 3)).mul hM
  have hFull := hGradient.add hThree
  rw [← hPhysical]
  simpa only [fullSchwartzThirdCommutator244] using hFull

/-- Replace the five-observable closure premise with separate quadratic
block limits and a signed-gradient / strong-jet split. -/
structure H3FullThirdSchwartzSplitJetApproximation244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (f : ℕ → A3 → SchwartzMap V3 ℝ)
    (g : A3 → SchwartzMap V3 ℝ) : Prop where
  jets : SchwartzStrongJetConvergence244 f g
  gradient : Tendsto
    (fun n => fullSchwartzGradientTransport244 (f n)) atTop
    (𝓝 (fullSchwartzGradientTransport244 g))
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

/-- The split-jet graph data discharge all five abstract observable limits.
Crucially, full signed transport convergence is derived, not assumed. -/
theorem H3FullThirdSchwartzSplitJetApproximation244.toObservable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    {f : ℕ → A3 → SchwartzMap V3 ℝ}
    {g : A3 → SchwartzMap V3 ℝ}
    (h : H3FullThirdSchwartzSplitJetApproximation244 u t f g) :
    H3FullThirdSchwartzObservableApproximation244 u t f := by
  exact ⟨
    thirdFullSchwartz_energy_tendsto_of_fourBlocks244 u t f
      h.energy0 h.energy1 h.energy2 h.energy3,
    h.energy3,
    h.top,
    thirdFullSchwartz_dissipation_tendsto_of_fourBlocks244 u t f
      h.energy1 h.energy2 h.energy3 h.top,
    thirdFullSchwartz_cubic_tendsto_of_splitJets244 u t f g
      h.jets h.gradient h.physical⟩

/-- Existence of a sequence with the stronger, analytically decomposed
convergence property. Nothing here asserts this for all physical H³ slices. -/
def H3FullThirdSchwartzSplitJetApproximable244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : Prop :=
  ∃ f : ℕ → A3 → SchwartzMap V3 ℝ,
    ∃ g : A3 → SchwartzMap V3 ℝ,
      H3FullThirdSchwartzSplitJetApproximation244 u t f g

/-- The split-jet property is sufficient for the previous full-observable
approximation contract, including the signed top cubic. -/
theorem h3Path_splitJet_implies_fullThirdObservableApproximable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {t : ℝ}
    (hSplit : H3FullThirdSchwartzSplitJetApproximable244 u t) :
    H3FullThirdSchwartzObservableApproximable244 u t := by
  obtain ⟨f, g, h⟩ := hSplit
  exact ⟨f, h.toObservable⟩

/-- Under hypothetical nonextension, approximants satisfying the split
jets/gradient data violate every fixed kinetic-absorbed signed cubic envelope
arbitrarily late. The 243-slot monomial limit need NOT be assumed. -/
theorem h3Path_noExtension_splitJetSignedWitness244
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
      H3FullThirdSchwartzSplitJetApproximable244 u t) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      ∃ f : ℕ → A3 → SchwartzMap V3 ℝ,
        H3FullThirdSchwartzObservableApproximation244 u t f ∧
        ∃ n : ℕ,
          M * lowNormalRealSchwartzH3Energy (f n) +
            lowNormalRealSchwartzH3FullDissipation244 (f n) <
            -fullSchwartzThirdCommutator244 (f n) := by
  exact h3Path_noExtension_fullThirdApproxSignedWitness244
    hH3 hNoExtension hClass hb hd hM
    (fun t ht => h3Path_splitJet_implies_fullThirdObservableApproximable244
      (hTail t ht))

/-- The complementary conditional continuation route: one eventual signed
cubic envelope, verified on split-jet approximants at each late time, rules
out the signed obstruction. The split-jet contract is still explicit. -/
theorem h3Path_extension_of_splitJetSignedEnvelope244
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
          H3FullThirdSchwartzSplitJetApproximation244 u t f g ∧
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

end
end PrimeTensor.FirstMonomialTriad
