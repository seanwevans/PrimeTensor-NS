import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalGlobalHighMaxTail
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialActualPhysicalSourceMeasurability
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Compact-time H³ spectral tightness from strong physical continuity

A fixed weighted H³ state has small Fourier high-radial mass for a large
cutoff. This file proves the much stronger compact-family statement:
  ∀ compact C ⊆ H³_spectral, ∀ ε>0, ∃ R, ∀ U∈C, ‖P_R U‖<ε.

The proof uses the *actual* high-radial indicator operator and the existing
strong cutoff convergence. Its norm decreases with cutoff; each operator is
1-Lipschitz. The open tail-smallness sets therefore form a directed cover
of a compact spectral family and have a common covering radius.

The original preterminal Navier–Stokes spectral path is strongly continuous
on (0,T), so every closed interval [a,b] strictly inside (0,T) has a
single high-radial cutoff, automatically, without extra regularity or a
uniform-in-time Schwartz representation. This does not extend to [a,T].
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

-- The Fourier carrier is indexed by the project's three-dimensional axis.
-- This local finite-axis instance supplies the product MeasureSpace required
-- by the restricted Fourier integrals below, as in the preceding flux modules.
noncomputable local instance axisFintypeCompactTimeRadialTightness244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The weighted H³ spectral high-frequency projection decreases in norm
as the natural high-radial cutoff increases. -/
theorem thirdFullSpectralVelocityHighRadialApply_norm_antitone244
    (n m : ℕ) (hnm : n ≤ m) (U : H3SpectralVelocityState) :
    ‖thirdFullSpectralVelocityHighRadialApply244 m U‖ ≤
      ‖thirdFullSpectralVelocityHighRadialApply244 n U‖ := by
  have hScalar (j : Fin 3) :
      ‖thirdFullSpectralHighRadialApply244 m (U j)‖ ≤
        ‖thirdFullSpectralHighRadialApply244 n (U j)‖ := by
    have hInt : Integrable
        (fun ξ : H3FourierPoint3 => ‖U j ξ‖ ^ 2) volume :=
      (MeasureTheory.Lp.memLp (U j)).norm.integrable_sq
    have hSubset : h3TopTailNaturalHighRadialSet m ⊆
        h3TopTailNaturalHighRadialSet n :=
      antitone_h3TopTailNaturalHighRadialSet hnm
    have hSquare :
        ‖thirdFullSpectralHighRadialApply244 m (U j)‖ ^ 2 ≤
          ‖thirdFullSpectralHighRadialApply244 n (U j)‖ ^ 2 := by
      calc
        ‖thirdFullSpectralHighRadialApply244 m (U j)‖ ^ 2 =
            ∫ ξ in h3TopTailNaturalHighRadialSet m,
              ‖U j ξ‖ ^ 2 ∂volume :=
          thirdFullSpectralHighRadialApply_norm_sq244 m (U j)
        _ ≤ ∫ ξ in h3TopTailNaturalHighRadialSet n,
              ‖U j ξ‖ ^ 2 ∂volume := by
          apply setIntegral_mono_set hInt.integrableOn
          · filter_upwards with ξ
            exact sq_nonneg _
          · filter_upwards with ξ
            intro hξ
            exact hSubset hξ
        _ = ‖thirdFullSpectralHighRadialApply244 n (U j)‖ ^ 2 :=
          (thirdFullSpectralHighRadialApply_norm_sq244 n (U j)).symm
    exact (sq_le_sq₀
      (norm_nonneg (thirdFullSpectralHighRadialApply244 m (U j)))
      (norm_nonneg (thirdFullSpectralHighRadialApply244 n (U j)))).mp hSquare
  apply (pi_norm_le_iff_of_nonneg
    (norm_nonneg (thirdFullSpectralVelocityHighRadialApply244 n U))).2
  intro j
  exact (hScalar j).trans
    (h3SpectralFinVector_coordinate_norm_le
      (thirdFullSpectralVelocityHighRadialApply244 n U) j)

/-- This is a genuine nonexpansive projection on the vector H³ Fourier state.
The argument uses its already proved additivity and contraction. -/
theorem thirdFullSpectralVelocityHighRadialApply_lipschitz244
    (n : ℕ) :
    LipschitzWith 1 (thirdFullSpectralVelocityHighRadialApply244 n) := by
  apply LipschitzWith.mk_one
  intro U V
  rw [dist_eq_norm, dist_eq_norm]
  have hAdd := thirdFullSpectralVelocityHighRadialApply_add244 n (U - V) V
  rw [sub_add_cancel] at hAdd
  have hSub :
      thirdFullSpectralVelocityHighRadialApply244 n U -
          thirdFullSpectralVelocityHighRadialApply244 n V =
        thirdFullSpectralVelocityHighRadialApply244 n (U - V) := by
    rw [hAdd]
    abel
  rw [hSub]
  exact thirdFullSpectralVelocityHighRadialApply_norm_le244 n (U - V)

/-- Tail norms vary continuously under perturbations in weighted H³. -/
theorem thirdFullSpectralVelocityHighRadialApply_norm_continuous244
    (n : ℕ) :
    Continuous (fun U : H3SpectralVelocityState =>
      ‖thirdFullSpectralVelocityHighRadialApply244 n U‖) :=
  continuous_norm.comp
    (thirdFullSpectralVelocityHighRadialApply_lipschitz244 n).continuous

/-- HARD COMPACTNESS STEP: the strong high-radial projections tend to zero
uniformly on every compact subset of the true weighted spectral state space.
No common bound on higher Fourier moments is assumed. -/
theorem thirdFullSpectralVelocityHighRadialApply_uniformOnCompact244
    (C : Set H3SpectralVelocityState) (hC : IsCompact C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ U ∈ C,
      ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ < ε := by
  let O : ℕ → Set H3SpectralVelocityState :=
    fun n => {U | ‖thirdFullSpectralVelocityHighRadialApply244 n U‖ < ε}
  have hOpen (n : ℕ) : IsOpen (O n) :=
    isOpen_lt (thirdFullSpectralVelocityHighRadialApply_norm_continuous244 n)
      continuous_const
  have hCover : C ⊆ ⋃ n : ℕ, O n := by
    intro U hU
    obtain ⟨R, hR⟩ :=
      (Metric.tendsto_atTop.mp
        (thirdFullSpectralVelocityHighRadialApply_norm_tendsto_zero244 U))
        ε hε
    have hSmall : ‖thirdFullSpectralVelocityHighRadialApply244 R U‖ < ε := by
      have h := hR R le_rfl
      simpa only [Real.dist_eq, sub_zero,
        abs_of_nonneg (norm_nonneg _)] using h
    exact Set.mem_iUnion.mpr ⟨R, hSmall⟩
  have hMonotone : Monotone O := by
    intro n m hnm U hU
    exact lt_of_le_of_lt
      (thirdFullSpectralVelocityHighRadialApply_norm_antitone244 n m hnm U) hU
  have hDirected : Directed
      (fun S T : Set H3SpectralVelocityState => S ⊆ T) O := by
    intro n m
    exact ⟨max n m, hMonotone (le_max_left n m),
      hMonotone (le_max_right n m)⟩
  obtain ⟨R, hR⟩ :=
    hC.elim_directed_cover O hOpen hCover hDirected
  exact ⟨R, fun U hU => hR hU⟩

/-- The ACTUAL preterminal H³ spectral path has a common high-radial
frequency cutoff on every compact strict-time slab. Both endpoints remain
strictly inside (0,T); no terminal spectral compactness is asserted. -/
theorem thirdFullPhysicalStrictSlab_uniformHighRadial244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < T)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ t ∈ Set.Icc a b,
      ‖thirdFullSpectralVelocityHighRadialApply244 R
        (h3AuditActualSpectralVelocityTotal hH3 t)‖ < ε := by
  have hSubset : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hCont : ContinuousOn (h3AuditActualSpectralVelocityTotal hH3)
      (Set.Icc a b) :=
    (h3Audit_initialActualSpectralVelocity_continuousOn hH3).mono hSubset
  have hCompact : IsCompact
      ((h3AuditActualSpectralVelocityTotal hH3) '' Set.Icc a b) :=
    isCompact_Icc.image_of_continuousOn hCont
  obtain ⟨R, hR⟩ :=
    thirdFullSpectralVelocityHighRadialApply_uniformOnCompact244
      _ hCompact ε hε
  refine ⟨R, ?_⟩
  intro t ht
  exact hR _ ⟨t, ht, rfl⟩

end
end PrimeTensor.FirstMonomialTriad
