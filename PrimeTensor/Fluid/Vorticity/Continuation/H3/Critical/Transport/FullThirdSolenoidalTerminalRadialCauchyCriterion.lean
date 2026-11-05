import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalCompactTimeFluxTail
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

/-!
# Endpoint H³ Cauchy criterion from low-band evolution and high-tail tightness

The preceding strict-compact-slab theorem cannot supply a cutoff uniform as
`t ↑ T`. This file isolates the exact functional-analytic alternative:

* Every fixed low-radial piece of the actual weighted H³ spectral trajectory
  must be Cauchy toward `T` (a low-frequency evolution obligation).
* Its high-radial L² tails must be uniformly small sufficiently near `T`.

Together, these yield a full spectral H³ terminal trace by completeness.
Conversely, in the presence of low-band Cauchy control, absence of a trace
forces a single positive tail threshold to recur arbitrarily close to `T`
for every fixed radial cutoff. No terminal-time tightness is asserted from
compact-time continuity alone.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators ENNReal Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeTerminalRadialCauchy244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)
set_option maxRecDepth 4096

/-- Exact complementary low-radial projection on the genuine weighted H³
velocity state. This is defined from the already-verified high projection. -/
noncomputable def thirdFullSpectralVelocityLowRadialApply244
    (R : ℕ) (U : H3SpectralVelocityState) : H3SpectralVelocityState :=
  U - thirdFullSpectralVelocityHighRadialApply244 R U

/-- Exact decomposition of the H³ state, including the cutoff boundary. -/
theorem thirdFullSpectralVelocity_lowHigh_decompose244
    (R : ℕ) (U : H3SpectralVelocityState) :
    thirdFullSpectralVelocityLowRadialApply244 R U +
      thirdFullSpectralVelocityHighRadialApply244 R U = U := by
  unfold thirdFullSpectralVelocityLowRadialApply244
  exact sub_add_cancel _ _

/-- The complementary low-radial projection is additive. -/
theorem thirdFullSpectralVelocityLowRadialApply_add244
    (R : ℕ) (U V : H3SpectralVelocityState) :
    thirdFullSpectralVelocityLowRadialApply244 R (U + V) =
      thirdFullSpectralVelocityLowRadialApply244 R U +
        thirdFullSpectralVelocityLowRadialApply244 R V := by
  unfold thirdFullSpectralVelocityLowRadialApply244
  rw [thirdFullSpectralVelocityHighRadialApply_add244]
  abel

/-- The full H³ difference splits into a low-band difference and two
individual high-radial tails. There is no regularity or PDE hypothesis. -/
theorem thirdFullSpectralVelocity_distance_le_lowDifference_highTails244
    (R : ℕ) (U V : H3SpectralVelocityState) :
    ‖U - V‖ ≤
      ‖thirdFullSpectralVelocityLowRadialApply244 R U -
        thirdFullSpectralVelocityLowRadialApply244 R V‖ +
      (‖thirdFullSpectralVelocityHighRadialApply244 R U‖ +
        ‖thirdFullSpectralVelocityHighRadialApply244 R V‖) := by
  have hDecomp : U - V =
      (thirdFullSpectralVelocityLowRadialApply244 R U -
        thirdFullSpectralVelocityLowRadialApply244 R V) +
      (thirdFullSpectralVelocityHighRadialApply244 R U -
        thirdFullSpectralVelocityHighRadialApply244 R V) := by
    unfold thirdFullSpectralVelocityLowRadialApply244
    abel
  calc
    ‖U - V‖ =
        ‖(thirdFullSpectralVelocityLowRadialApply244 R U -
            thirdFullSpectralVelocityLowRadialApply244 R V) +
          (thirdFullSpectralVelocityHighRadialApply244 R U -
            thirdFullSpectralVelocityHighRadialApply244 R V)‖ :=
      congrArg norm hDecomp
    _ ≤ ‖thirdFullSpectralVelocityLowRadialApply244 R U -
            thirdFullSpectralVelocityLowRadialApply244 R V‖ +
          ‖thirdFullSpectralVelocityHighRadialApply244 R U -
            thirdFullSpectralVelocityHighRadialApply244 R V‖ :=
      norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl
      (norm_sub_le
        (thirdFullSpectralVelocityHighRadialApply244 R U)
        (thirdFullSpectralVelocityHighRadialApply244 R V))

/-- Every fixed spectral low band is Cauchy as time approaches `T` from
below, measured only on the physical preterminal interval `(a,T)`. -/
def ThirdFullTerminalLowRadialCauchyOn244
    (U : ℝ → H3SpectralVelocityState) (a T : ℝ) : Prop :=
  ∀ (R : ℕ) (ε : ℝ), 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s t : ℝ, s ∈ Set.Ioo a T → t ∈ Set.Ioo a T →
        T - s < δ → T - t < δ →
        ‖thirdFullSpectralVelocityLowRadialApply244 R (U s) -
          thirdFullSpectralVelocityLowRadialApply244 R (U t)‖ < ε

/-- One common high-radial cutoff is small at all sufficiently late times.
The cutoff and start of the terminal subinterval may depend on ε. -/
def ThirdFullTerminalUniformHighRadialTightOn244
    (U : ℝ → H3SpectralVelocityState) (a T : ℝ) : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∃ (R : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ t : ℝ, t ∈ Set.Ioo a T → T - t < δ →
        ‖thirdFullSpectralVelocityHighRadialApply244 R (U t)‖ < ε

/-- Full weighted H³ Cauchy modulus on a terminal tail. -/
def ThirdFullTerminalSpectralCauchyOn244
    (U : ℝ → H3SpectralVelocityState) (a T : ℝ) : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s t : ℝ, s ∈ Set.Ioo a T → t ∈ Set.Ioo a T →
        T - s < δ → T - t < δ → ‖U s - U t‖ < ε

/-- HARD MATH: radial-tightness plus terminal low-band Cauchy control
imply terminal Cauchy control of the full weighted H³ state. -/
theorem thirdFullTerminalSpectralCauchy_of_lowAndTight244
    (U : ℝ → H3SpectralVelocityState) (a T : ℝ)
    (hLow : ThirdFullTerminalLowRadialCauchyOn244 U a T)
    (hTight : ThirdFullTerminalUniformHighRadialTightOn244 U a T) :
    ThirdFullTerminalSpectralCauchyOn244 U a T := by
  intro ε hε
  have hHalf : 0 < ε / 2 := by linarith
  have hQuarter : 0 < ε / 4 := by linarith
  obtain ⟨R, δHigh, hδHigh, hHigh⟩ := hTight (ε / 4) hQuarter
  obtain ⟨δLow, hδLow, hLowR⟩ := hLow R (ε / 2) hHalf
  refine ⟨min δHigh δLow,
    lt_min_iff.mpr ⟨hδHigh, hδLow⟩, ?_⟩
  intro s t hs ht hsNear htNear
  have hsHigh : T - s < δHigh :=
    lt_of_lt_of_le hsNear (min_le_left δHigh δLow)
  have htHigh : T - t < δHigh :=
    lt_of_lt_of_le htNear (min_le_left δHigh δLow)
  have hsLow : T - s < δLow :=
    lt_of_lt_of_le hsNear (min_le_right δHigh δLow)
  have htLow : T - t < δLow :=
    lt_of_lt_of_le htNear (min_le_right δHigh δLow)
  have hLowSmall := hLowR s t hs ht hsLow htLow
  have hS := hHigh s hs hsHigh
  have hT := hHigh t ht htHigh
  have hSplit := thirdFullSpectralVelocity_distance_le_lowDifference_highTails244
    R (U s) (U t)
  linarith only [hSplit, hLowSmall, hS, hT]

/-- Complete weighted H³ spectral state has a terminal limit when its
preterminal trajectory is Cauchy on every sufficiently short final interval.
The proof uses Hilbert completeness, not compact embedding. -/
theorem thirdFullTerminalSpectralTrace_of_Cauchy244
    (U : ℝ → H3SpectralVelocityState) (a T : ℝ)
    (haT : a < T)
    (hCauchy : ThirdFullTerminalSpectralCauchyOn244 U a T) :
    ∃ L : H3SpectralVelocityState,
      Tendsto U (𝓝[<] T) (𝓝 L) := by
  have hFilter : Cauchy (Filter.map U (𝓝[<] T)) := by
    apply Metric.cauchy_iff.mpr
    constructor
    · infer_instance
    · intro ε hε
      obtain ⟨δ, hδ, hChord⟩ := hCauchy ε hε
      let A : Set ℝ := {s | s ∈ Set.Ioo a T ∧ T - s < δ}
      have hAMem : A ∈ 𝓝[<] T := by
        have hAfter0 : ∀ᶠ t : ℝ in 𝓝 T, a < t :=
          Ioi_mem_nhds haT
        have hAfter : Set.Ioi a ∈ 𝓝[<] T :=
          hAfter0.filter_mono nhdsWithin_le_nhds
        have hGap0 : ∀ᶠ t : ℝ in 𝓝 T, T - δ < t :=
          Ioi_mem_nhds (by linarith : T - δ < T)
        have hGap : Set.Ioi (T - δ) ∈ 𝓝[<] T :=
          hGap0.filter_mono nhdsWithin_le_nhds
        filter_upwards [hAfter, hGap, self_mem_nhdsWithin] with s hsAfter hsGap hsBefore
        change s ∈ A
        refine ⟨⟨hsAfter, hsBefore⟩, ?_⟩
        change T - δ < s at hsGap
        linarith only [hsGap]
      refine ⟨U '' A, ?_, ?_⟩
      · change U ⁻¹' (U '' A) ∈ 𝓝[<] T
        exact Filter.mem_of_superset hAMem
          (fun s hs => ⟨s, hs, rfl⟩)
      · intro x hx y hy
        obtain ⟨s, hs, rfl⟩ := hx
        obtain ⟨t, ht, rfl⟩ := hy
        change dist (U s) (U t) < ε
        rw [dist_eq_norm]
        exact hChord s t hs.1 ht.1 hs.2 ht.2
  exact (cauchy_map_iff_exists_tendsto).mp hFilter

/-- Terminal radial tightness becomes a full H³ trace once the fixed
low-frequency pieces are known to be Cauchy. -/
theorem thirdFullTerminalSpectralTrace_of_lowAndTight244
    (U : ℝ → H3SpectralVelocityState) (a T : ℝ)
    (haT : a < T)
    (hLow : ThirdFullTerminalLowRadialCauchyOn244 U a T)
    (hTight : ThirdFullTerminalUniformHighRadialTightOn244 U a T) :
    ∃ L : H3SpectralVelocityState,
      Tendsto U (𝓝[<] T) (𝓝 L) :=
  thirdFullTerminalSpectralTrace_of_Cauchy244 U a T haT
    (thirdFullTerminalSpectralCauchy_of_lowAndTight244 U a T hLow hTight)

end
end PrimeTensor.FirstMonomialTriad
