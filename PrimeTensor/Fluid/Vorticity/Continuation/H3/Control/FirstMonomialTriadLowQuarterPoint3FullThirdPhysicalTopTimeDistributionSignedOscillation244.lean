import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionInteriorSignedPDE244
import Mathlib.Tactic

/-!
# Compact-support temporal oscillation criterion for physical momentum distributions

The previous interior signed-PDE criterion assumes uniform bounds in both
physical time and space for the complete signed momentum expression on the
support of each compact solenoidal test. The existing fixed-time theorem
already supplies spatial boundedness on every such support. Thus it remains
to control only the temporal *oscillation* relative to each fixed snapshot.

We formulate a testwise, locally uniform temporal modulus of continuity for
the signed physical Navier--Stokes momentum expression and combine it with
the existing fixed-time compact bound. The resulting local signed bound
implies genuine Hilbert differentiation and the real-time distributional
momentum equation on a straddling canonical restart interval.

This temporal modulus is an explicit additional hypothesis: pointwise
spatial continuity at each time, and H3-path L2 continuity of the projected
source, do not by themselves imply it. No conclusion of unconditional
Navier--Stokes regularity is made.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter TopologicalSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

/-- The FULL signed classical physical momentum expression. The pressure
is the existing pressure witness of the old preterminal Navier--Stokes PDE.
No estimate on its three terms separately is imposed. -/
noncomputable def h3PreterminalSignedPhysicalMomentumAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t : ℝ) (x : Point3) (i : Fin 3) : ℝ :=
  PrimeTensor.Bridge.RealFluid.laplacian spatial3
    (fun y : Point3 =>
      (PrimeTensor.Bridge.logSpaceTimeVectorField u t y).component
        (h3AxisOfFin3 i)) x
  - realAdvectionComponent
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x
      (h3AxisOfFin3 i)
  - spatial3.d (h3AxisOfFin3 i)
      ((Classical.choose hNS :
        SpaceTimeScalarField ℝ ℝ ℝ Depth.three) t) x

/-- A uniform temporal modulus, only on the compact spatial supports of
solenoidal test coordinates. Neighborhood and modulus depend on the test,
time and coordinate, but are uniform in the spatial point. -/
def h3PreterminalSignedMomentumUniformTimeOscillationOnElapsed244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t₀ τ : ℝ) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) τ →
    ∀ i : Fin 3, ∀ ε : ℝ, 0 < ε →
      ∃ S : Set ℝ,
        S ∈ 𝓝 s ∧
        (∀ r : ℝ, r ∈ S → t₀ + r ∈ Set.Ioo (0 : ℝ) T) ∧
        (∀ r : ℝ, r ∈ S →
          ∀ x : Point3, x ∈ tsupport (φ i : Point3 → ℝ) →
            ‖h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) x i -
              h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + s) x i‖ ≤ ε)

/-- Fixed-time spatial compactness plus a locally uniform temporal
oscillation of the complete signed PDE expression give the OLD signed
momentum compact bound. In particular, no separate uniform-in-time bounds
on the Laplacian, advection or pressure are needed. -/
theorem h3Preterminal_signedMomentumBound_of_uniformTimeOscillation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t₀ τ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : 0 < t₀) (hEnd : t₀ + τ < T)
    (hOsc : h3PreterminalSignedMomentumUniformTimeOscillationOnElapsed244
      hNS t₀ τ) :
    h3PreterminalSignedMomentumCompactBoundOnElapsed244 hNS t₀ τ := by
  intro φ hφ s hs i
  have hTime : t₀ + s ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith only [ht₀, hs.1]
    · linarith only [hEnd, hs.2]
  obtain ⟨C₀, hC₀, hSnapshot⟩ :=
    h3Preterminal_signedMomentum_bounded_on_compactTestAt244
      hNS hTime φ i
  obtain ⟨S, hS, hSAbs, hVariation⟩ :=
    hOsc φ hφ s hs i 1 (by norm_num)
  refine ⟨S, hS, hSAbs, C₀ + 1, by linarith only [hC₀], ?_⟩
  intro r hr x hx
  have hAt :
      ‖h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + s) x i‖ ≤ C₀ :=
    hSnapshot x hx
  have hV := hVariation r hr x hx
  change ‖h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) x i‖ ≤ C₀ + 1
  calc
    ‖h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) x i‖ =
        ‖(h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) x i -
          h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + s) x i) +
          h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + s) x i‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + r) x i -
          h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + s) x i‖ +
          ‖h3PreterminalSignedPhysicalMomentumAt244 hNS (t₀ + s) x i‖ :=
      norm_add_le _ _
    _ ≤ 1 + C₀ := add_le_add hV hAt
    _ = C₀ + 1 := by ring

/-- A straddling canonical restart interval satisfying just the compact-test
uniform temporal oscillation condition, rather than a signed absolute PDE
bound or global joint spacetime continuity. -/
def h3PathInteriorTimeSignedOscillationAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (_hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s : ℝ) : Prop :=
  ∃ (t₀ S E τ : ℝ)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) S)
    (_hST : S < T)
    (_hE : 1 ≤ E)
    (_hTail : CanonicalH3TailDataFrom u t₀ S E)
    (_hτ : 0 < τ)
    (_hEnd : t₀ + τ < S)
    (hNSShort : LoggedPreterminalNavierStokesAdmissible u S),
      s ∈ Set.Ioo t₀ (t₀ + τ) ∧
      h3PreterminalSignedMomentumUniformTimeOscillationOnElapsed244
        hNSShort t₀ τ

/-- Temporal oscillation gives the full signed compact-support bound on
the same straddling interval. -/
theorem h3Path_interiorSignedBound_of_signedOscillation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOsc : h3PathInteriorTimeSignedOscillationAt244 hH3 s) :
    h3PathInteriorTimeSignedMomentumBoundAt244 hH3 s := by
  rcases hOsc with
    ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
      hNSShort, hs, hOsc⟩
  refine ⟨t₀, S, E, τ, ht₀, hST, hE, hTail, hτ, hEnd,
    hNSShort, hs, ?_⟩
  exact h3Preterminal_signedMomentumBound_of_uniformTimeOscillation244
    hNSShort ht₀.1 hEnd hOsc

/-- The actual physical old velocity has its strong L2 time derivative
when the signed PDE has a uniform compact-test temporal modulus on a
straddling restart window. -/
theorem h3Path_physicalHilbertHasDerivAt_of_signedOscillation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hOsc : h3PathInteriorTimeSignedOscillationAt244 hH3 s) :
    HasDerivAt (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (h3PathActualProjectedMomentumSource244 hH3 s) s := by
  exact h3Path_physicalHilbertHasDerivAt_of_interiorSignedMomentumBound244
    hH3 (h3Path_interiorSignedBound_of_signedOscillation244 hH3 hOsc)

/-- Uniform temporal oscillation on compact spatial test supports at every
interior physical time implies the genuine regular time-distribution
momentum equation on the whole interval. -/
theorem h3Path_distributionalMomentum_of_signedOscillation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hOsc : ∀ s : ℝ, s ∈ Set.Ioo a b →
      h3PathInteriorTimeSignedOscillationAt244 hH3 s) :
    h3PathSolenoidalDistributionalMomentumOn244 hH3 a b := by
  apply h3Path_distributionalMomentum_of_interiorSignedMomentumBound244
    hH3 ha hab hb
  intro s hs
  exact h3Path_interiorSignedBound_of_signedOscillation244
    hH3 (hOsc s hs)

/-- Consequently a nonzero physical FTC defect certifies that no such
uniform-on-compact-test time-oscillation criterion can hold at some
strict interior observation time. -/
theorem h3Path_nonzeroPhysicalFTCDefect_forces_signedOscillationFailure244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hNonzero : h3PathActualProjectedMomentumFTCDefect244 hH3 a b ≠ 0) :
    ∃ s : ℝ, s ∈ Set.Ioo a b ∧
      ¬ h3PathInteriorTimeSignedOscillationAt244 hH3 s := by
  obtain ⟨s, hs, hFail⟩ :=
    h3Path_nonzeroPhysicalFTCDefect_forces_interiorSignedFailure244
      hH3 ha hab hb hNonzero
  refine ⟨s, hs, ?_⟩
  intro hOsc
  exact hFail (h3Path_interiorSignedBound_of_signedOscillation244 hH3 hOsc)

end
end PrimeTensor.FirstMonomialTriad
