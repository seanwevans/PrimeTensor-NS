import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedWeakTemporalJointContinuity
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Local domination for selected weak temporal pairings

The selected temporal derivative is now jointly continuous on every strict
elapsed slab.  Compact weak tests therefore supply the exact local domination
needed by Mathlib's parametric-integral differentiation theorem.

At one strict elapsed time `s` and one coordinate `i`:

* choose a compact time slab `[a,b]` with
  `s ∈ (a,b) ⊂ (0,tau)`;
* multiply that slab by the compact topological support of `φ i`;
* joint continuity gives a uniform scalar bound for the selected temporal
  derivative on this compact product;
* use that scalar times `‖φ i x‖` as the spatial majorant.

The majorant is integrable because `φ i` is compactly supported.

This closes the selected branch's domination frontier without any old-path
regularity or strong `L²` temporal derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakTemporalLocalDomination
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Match the norm topology used by `H3WeakTestFunction`. -/
local instance point3NormTopologicalSpaceH3SelectedOldWeakStrongSelectedWeakTemporalLocalDomination :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Exact selected-side local domination condition for differentiating the
compact-test velocity pairing under the spatial integral. -/
def H3PreterminalSelectedUnitWeakTemporalLocalDominationAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (s : ℝ)
    (φ : H3WeakTestVector) : Prop :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
  ∀ i : Fin 3,
    ∃ S : Set ℝ,
      S ∈ 𝓝 s
      ∧
      S ⊆ Set.Ioo (0 : ℝ) tau
      ∧
      ∃ bound : Point3 → ℝ,
        Integrable bound (volume : Measure Point3)
        ∧
        ∀ᵐ x : Point3 ∂volume,
          ∀ r : ℝ,
            r ∈ S →
            ‖(ContinuousLinearMap.lsmul ℝ ℝ)
                (φ i x)
                (temporal.d
                  (fun q : ℝ =>
                    h3SpectralScalarRealC1RepresentativeOnPoint3
                      (W q i) x)
                  r)‖
              ≤
            bound x

/-- Joint continuity of the selected temporal derivative closes the local
domination condition at every strict elapsed time. -/
theorem H3PreterminalSelectedUnitWeakTemporalLocalDominationAt_of_jointContinuity
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (φ : H3WeakTestVector) :
    H3PreterminalSelectedUnitWeakTemporalLocalDominationAt
      hNS ht htau hE hTail htauR s φ := by
  dsimp only [H3PreterminalSelectedUnitWeakTemporalLocalDominationAt]

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  intro i

  let a : ℝ := s / 2
  let b : ℝ := (s + tau) / 2

  have haPos : 0 < a := by
    dsimp only [a]
    linarith [hs.1]

  have has : a < s := by
    dsimp only [a]
    linarith [hs.1]

  have hsb : s < b := by
    dsimp only [b]
    linarith [hs.2]

  have hbTau : b < tau := by
    dsimp only [b]
    linarith [hs.2]

  have hSlab :
      Set.Icc a b ⊆ Set.Ioo (0 : ℝ) tau := by
    intro r hr
    exact
      ⟨
        lt_of_lt_of_le haPos hr.1,
        lt_of_le_of_lt hr.2 hbTau
      ⟩

  let S : Set ℝ := Set.Ioo a b

  have hS : S ∈ 𝓝 s := by
    dsimp only [S]
    exact Ioo_mem_nhds has hsb

  have hSsub :
      S ⊆ Set.Ioo (0 : ℝ) tau := by
    intro r hr
    exact hSlab ⟨hr.1.le, hr.2.le⟩

  refine ⟨S, hS, hSsub, ?_⟩

  have hSupportCompact :
      IsCompact
        (tsupport (φ i : Point3 → ℝ)) := by
    exact (φ i).hasCompactSupport

  have hProductCompact :
      IsCompact
        (Set.Icc a b ×ˢ
          tsupport (φ i : Point3 → ℝ)) :=
    isCompact_Icc.prod hSupportCompact

  have hJoint :=
    h3PreterminalSelectedUnitRealVelocity_temporalDerivative_jointContinuousOnElapsed
      hNS ht hE hTail htauR i

  dsimp only at hJoint

  have hSubset :
      Set.Icc a b ×ˢ tsupport (φ i : Point3 → ℝ)
        ⊆
      Set.Ioo (0 : ℝ) tau ×ˢ Set.univ := by
    intro z hz
    exact ⟨hSlab hz.1, Set.mem_univ z.2⟩

  have hContinuous :
      ContinuousOn
        (fun z : ℝ × Point3 =>
          temporal.d
            (fun r : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W r i) z.2)
            z.1)
        (Set.Icc a b ×ˢ
          tsupport (φ i : Point3 → ℝ)) := by
    dsimp only [W]
    exact hJoint.mono hSubset

  obtain ⟨C, hC⟩ :=
    hProductCompact.exists_bound_of_continuousOn
      hContinuous

  let C0 : ℝ := max C 0

  have hC0 : 0 ≤ C0 := by
    dsimp only [C0]
    exact le_max_right C 0

  let bound : Point3 → ℝ :=
    fun x => C0 * ‖φ i x‖

  have hNormIntegrable :
      Integrable
        (fun x : Point3 => ‖φ i x‖)
        (volume : Measure Point3) := by
    exact
      (φ i).continuous.norm.integrable_of_hasCompactSupport
        (φ i).hasCompactSupport.norm

  have hBoundIntegrable :
      Integrable bound
        (volume : Measure Point3) := by
    dsimp only [bound]
    exact Integrable.const_mul hNormIntegrable C0

  refine ⟨bound, hBoundIntegrable, ?_⟩

  filter_upwards with x

  intro r hr

  by_cases hx : φ i x = 0

  · change
      ‖(φ i x) *
          temporal.d
            (fun q : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W q i) x)
            r‖
        ≤
      bound x

    dsimp only [bound]
    rw [hx]
    norm_num

  · have hxSupport :
        x ∈ tsupport (φ i : Point3 → ℝ) :=
      subset_tsupport _ hx

    have hrClosed :
        r ∈ Set.Icc a b := by
      dsimp only [S] at hr
      exact ⟨hr.1.le, hr.2.le⟩

    have hPoint :
        (r, x) ∈
          Set.Icc a b ×ˢ
            tsupport (φ i : Point3 → ℝ) :=
      ⟨hrClosed, hxSupport⟩

    have hDerivative :
        ‖temporal.d
            (fun q : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W q i) x)
            r‖
          ≤
        C0 := by
      have hRaw :=
        hC (r, x) hPoint

      exact
        hRaw.trans
          (le_max_left C 0)

    change
      ‖(φ i x) *
          temporal.d
            (fun q : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W q i) x)
            r‖
        ≤
      bound x

    dsimp only [bound]

    calc
      ‖(φ i x) *
          temporal.d
            (fun q : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W q i) x)
            r‖
          =
        ‖φ i x‖ *
          ‖temporal.d
            (fun q : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (W q i) x)
            r‖ := by
              exact norm_mul _ _
      _ ≤ ‖φ i x‖ * C0 :=
        mul_le_mul_of_nonneg_left
          hDerivative
          (norm_nonneg _)
      _ = C0 * ‖φ i x‖ := by
        rw [mul_comm]

/-- The local domination condition therefore holds at every strict elapsed
time for every compact weak test vector. -/
theorem h3PreterminalSelectedUnitWeakTemporalLocallyDominated
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (φ : H3WeakTestVector) :
    ∀ s : ℝ,
      s ∈ Set.Ioo (0 : ℝ) tau →
      H3PreterminalSelectedUnitWeakTemporalLocalDominationAt
        hNS ht htau hE hTail htauR s φ := by
  intro s hs

  exact
    H3PreterminalSelectedUnitWeakTemporalLocalDominationAt_of_jointContinuity
      hNS ht htau hE hTail htauR hs φ

end

end Euclidean
end Bridge
end PrimeTensor
