import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3PrescribedFourierLocalExistence
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic

/-!
# Exact transverse Leray source and projected analytic initial data

The completed Z³ Fourier flow has the exact complex Leray quadratic symbol.
Here we establish the physically essential pressure-elimination identity:
the *entire* ordered nonlinear source lies in the orthogonal complement of
its output frequency, both for finite Galerkin input sets and for the
absolutely convergent infinite ordered series. This includes the zero mode
and all output collisions; no cutoff-dependent factors occur.

The source therefore supplies no longitudinal Fourier forcing. The exact
viscous-plus-Leray finite vector field has precisely the same longitudinal
component as the heat multiplier alone. Finally, Leray projection of a
specified analytic initial field preserves its strict Wiener bound and
produces a genuinely transverse initial field; the preceding Galerkin
compactness theorem constructs a local Fourier solution from those data.

The transverse source identity must not be confused with a proof that all
Fourier coefficients of the resulting solution remain transverse. That
requires propagation of the homogeneous longitudinal heat equation, the
next analytical step. Nor is an arbitrary complex Fourier field Hermitian.
-/

namespace PrimeTensor.FirstMonomialTriad

open Set Filter
noncomputable section

private abbrev TrIndex244 := thirdFullThreeBandZ3Index244
private abbrev TrBand244 := EuclideanSpace ℂ (Fin 3)

/-- The precise solenoidal Fourier constraint at one output frequency. -/
def thirdFullThreeBandZ3FourierIsTransverse244
    (n : TrIndex244) (v : TrBand244) : Prop :=
  inner ℂ (thirdFullThreeBandZ3ComplexFrequency244 n) v = 0

/-- The original complex Leray projection takes values perpendicular to
its *output* Fourier frequency, including the zero frequency. -/
theorem thirdFullThreeBand_z3ComplexLeray_transverse244
    (n : TrIndex244) (v : TrBand244) :
    thirdFullThreeBandZ3FourierIsTransverse244 n
      (thirdFullThreeBandZ3ComplexLeray244 n v) := by
  unfold thirdFullThreeBandZ3FourierIsTransverse244
  have hMem : thirdFullThreeBandZ3ComplexLeray244 n v ∈
      (ℂ ∙ thirdFullThreeBandZ3ComplexFrequency244 n)ᗮ := by
    exact Submodule.starProjection_apply_mem
      ((ℂ ∙ thirdFullThreeBandZ3ComplexFrequency244 n)ᗮ) v
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hMem

/-- Each exact complex ordered transport interaction is transverse to its
output frequency, regardless of the two input Fourier coefficients. -/
theorem thirdFullThreeBand_z3ComplexTransport_transverse244
    (n q : TrIndex244) (u v : TrBand244) :
    thirdFullThreeBandZ3FourierIsTransverse244 n
      (thirdFullThreeBandZ3ComplexTransport244 n q u v) := by
  exact thirdFullThreeBand_z3ComplexLeray_transverse244 n _

/-- Every collision-sensitive finite double Fourier sum is exactly
transverse at EVERY output mode, even outside the retained input set. -/
theorem thirdFullThreeBand_z3GalerkinQuadratic_transverse244
    (s t : Finset TrIndex244)
    (u v : TrIndex244 → TrBand244) (n : TrIndex244) :
    thirdFullThreeBandZ3FourierIsTransverse244 n
      (thirdFullThreeBandZ3GalerkinQuadratic244 s t u v n) := by
  classical
  have hMem : thirdFullThreeBandZ3GalerkinQuadratic244 s t u v n ∈
      (ℂ ∙ thirdFullThreeBandZ3ComplexFrequency244 n)ᗮ := by
    unfold thirdFullThreeBandZ3GalerkinQuadratic244
    apply Submodule.sum_mem
    intro p hp
    apply Submodule.sum_mem
    intro q hq
    by_cases h : p + q = n
    · simp only [if_pos h]
      exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mpr
        (thirdFullThreeBand_z3ComplexTransport_transverse244 n q (u p) (v q))
    · simp only [if_neg h]
      exact Submodule.zero_mem _
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hMem

/-- The completed genuine ordered Leray series is transverse in the
infinite Fourier lattice. The high analytic Wiener bound guarantees that
this is a genuine absolutely convergent ordered series, not a formal sum. -/
theorem thirdFullThreeBand_z3InfiniteOrderedLeray_transverse244
    (u : TrIndex244 → TrBand244)
    (hHigh : ∀ q : Finset TrIndex244,
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q u ≤ 100)
    (n : TrIndex244) :
    thirdFullThreeBandZ3FourierIsTransverse244 n
      (thirdFullThreeBandZ3InfiniteOrderedLeray244 u n) := by
  classical
  let K : Submodule ℂ TrBand244 :=
    (ℂ ∙ thirdFullThreeBandZ3ComplexFrequency244 n)ᗮ
  have hTerm (p : TrIndex244) :
      thirdFullThreeBandZ3ComplexTransport244 n (n - p)
        (u p) (u (n - p)) ∈ K := by
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mpr
      (thirdFullThreeBand_z3ComplexTransport_transverse244
        n (n - p) (u p) (u (n - p)))
  have hSeries := thirdFullThreeBand_z3InfiniteOrderedLeray_summable244 u hHigh n
  have hClosed : IsClosed (K : Set TrBand244) := by
    exact Submodule.isClosed_orthogonal (ℂ ∙ thirdFullThreeBandZ3ComplexFrequency244 n)
  have hTsum : (∑' p : TrIndex244,
      thirdFullThreeBandZ3ComplexTransport244 n (n - p)
        (u p) (u (n - p))) ∈ K := by
    exact tsum_mem (s := K.toAddSubmonoid) hClosed hTerm
  unfold thirdFullThreeBandZ3FourierIsTransverse244
    thirdFullThreeBandZ3InfiniteOrderedLeray244
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hTsum

/-- Replace the finite-output 100-ball hypothesis by the full infinite
Wiener norm, as supplied by the constructed local Fourier solution. -/
theorem thirdFullThreeBand_z3InfiniteOrderedLeray_transverse_of_mass244
    (u : TrIndex244 → TrBand244)
    (hSummable : Summable (fun n : TrIndex244 =>
      thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n * ‖u n‖))
    (hMass : thirdFullThreeBandZ3InfiniteWienerMass244
      (Real.log (9 / 5 : ℝ)) u ≤ 100)
    (n : TrIndex244) :
    thirdFullThreeBandZ3FourierIsTransverse244 n
      (thirdFullThreeBandZ3InfiniteOrderedLeray244 u n) := by
  have hFinite (q : Finset TrIndex244) :
      thirdFullThreeBandZ3GalerkinWienerMass244
        (Real.log (9 / 5 : ℝ)) q u ≤ 100 := by
    unfold thirdFullThreeBandZ3GalerkinWienerMass244
    have hFull : (∑' i : TrIndex244,
        thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) i * ‖u i‖) ≤ 100 := by
      simpa only [thirdFullThreeBandZ3InfiniteWienerMass244] using hMass
    exact (hSummable.sum_le_tsum q (fun i hi =>
      mul_nonneg (thirdFullThreeBand_z3Weight_pos244 _ i).le
        (norm_nonneg _))).trans hFull
  exact thirdFullThreeBand_z3InfiniteOrderedLeray_transverse244 u hFinite n

/-- The finite Galerkin NS vector field has NO nonlinear longitudinal
component: testing against the output frequency leaves only heat damping. -/
theorem thirdFullThreeBand_z3GalerkinNSField_longitudinalHeat244
    (mu : ℝ) (s : Finset TrIndex244)
    (u : TrIndex244 → TrBand244) (n : TrIndex244) :
    inner ℂ (thirdFullThreeBandZ3ComplexFrequency244 n)
      (thirdFullThreeBandZ3GalerkinNSField244 mu s u n) =
    inner ℂ (thirdFullThreeBandZ3ComplexFrequency244 n)
      ((-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) • u n) := by
  have hSource := thirdFullThreeBand_z3GalerkinQuadratic_transverse244 s s u u n
  change inner ℂ (thirdFullThreeBandZ3ComplexFrequency244 n)
      ((-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) • u n +
        thirdFullThreeBandZ3GalerkinQuadratic244 s s u u n) = _
  rw [inner_add_right, hSource, add_zero]

/-- Define the genuinely frequency-by-frequency Leray projection of an
arbitrary infinite initial Fourier velocity field. -/
def thirdFullThreeBandZ3ProjectedInitial244
    (u0 : TrIndex244 → TrBand244) (n : TrIndex244) : TrBand244 :=
  thirdFullThreeBandZ3ComplexLeray244 n (u0 n)

/-- Leray projection of initial data preserves summability and the STRICT
analytic-radius 2 Wiener ball: no loss of analyticity or multiplicative
constant is incurred. -/
theorem thirdFullThreeBand_z3ProjectedInitial_admissible244
    (u0 : TrIndex244 → TrBand244)
    (hSummable : Summable (fun n : TrIndex244 =>
      thirdFullThreeBandZ3Weight244 (Real.log (2 : ℝ)) n * ‖u0 n‖))
    (hMass : thirdFullThreeBandZ3InfiniteWienerMass244
      (Real.log (2 : ℝ)) u0 < 100) :
    Summable (fun n : TrIndex244 =>
      thirdFullThreeBandZ3Weight244 (Real.log (2 : ℝ)) n *
        ‖thirdFullThreeBandZ3ProjectedInitial244 u0 n‖) ∧
    thirdFullThreeBandZ3InfiniteWienerMass244 (Real.log (2 : ℝ))
      (thirdFullThreeBandZ3ProjectedInitial244 u0) < 100 := by
  have hTerm (n : TrIndex244) :
      thirdFullThreeBandZ3Weight244 (Real.log (2 : ℝ)) n *
        ‖thirdFullThreeBandZ3ProjectedInitial244 u0 n‖ ≤
      thirdFullThreeBandZ3Weight244 (Real.log (2 : ℝ)) n * ‖u0 n‖ :=
    mul_le_mul_of_nonneg_left
      (thirdFullThreeBand_z3ComplexLeray_norm_le244 n (u0 n))
      (thirdFullThreeBand_z3Weight_pos244 _ n).le
  have hNonneg (n : TrIndex244) :
      0 ≤ thirdFullThreeBandZ3Weight244 (Real.log (2 : ℝ)) n *
        ‖thirdFullThreeBandZ3ProjectedInitial244 u0 n‖ :=
    mul_nonneg (thirdFullThreeBand_z3Weight_pos244 _ n).le (norm_nonneg _)
  have hProjSum : Summable (fun n : TrIndex244 =>
      thirdFullThreeBandZ3Weight244 (Real.log (2 : ℝ)) n *
        ‖thirdFullThreeBandZ3ProjectedInitial244 u0 n‖) :=
    Summable.of_nonneg_of_le hNonneg hTerm hSummable
  refine ⟨hProjSum, ?_⟩
  unfold thirdFullThreeBandZ3InfiniteWienerMass244 at hMass ⊢
  exact (hProjSum.tsum_le_tsum hTerm hSummable).trans_lt hMass

/-- The projected initial field satisfies the exact Fourier divergence-free
constraint at each nonzero (and zero) lattice frequency. -/
theorem thirdFullThreeBand_z3ProjectedInitial_transverse244
    (u0 : TrIndex244 → TrBand244) (n : TrIndex244) :
    thirdFullThreeBandZ3FourierIsTransverse244 n
      (thirdFullThreeBandZ3ProjectedInitial244 u0 n) :=
  thirdFullThreeBand_z3ComplexLeray_transverse244 n (u0 n)

/-- Construct a local Fourier solution from ACTUALLY SOLENOIDAL analytic
initial coefficients, with an exact transverse nonlinear source and full
coefficientwise integral evolution. The remaining separate obligation is to
show that the linear longitudinal heat defect remains zero for all t. -/
theorem thirdFullThreeBand_z3ProjectedInitial_localFourierExistence244
    (mu a : ℝ) (hmu : 0 ≤ mu) (hmuMax : mu ≤ (1 / 10 : ℝ))
    (s : ℕ → Finset TrIndex244)
    (hExhaust : thirdFullThreeBandZ3GalerkinExhausts244 s)
    (u0 : TrIndex244 → TrBand244)
    (hSummable : Summable (fun n : TrIndex244 =>
      thirdFullThreeBandZ3Weight244 (Real.log (2 : ℝ)) n * ‖u0 n‖))
    (hMass : thirdFullThreeBandZ3InfiniteWienerMass244
      (Real.log (2 : ℝ)) u0 < 100) :
    ∃ g : ℝ → TrIndex244 → TrBand244,
      (∀ n, ContinuousOn (fun t => g t n)
        (Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a))) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        Summable (fun n : TrIndex244 =>
          thirdFullThreeBandZ3Weight244 (Real.log (9 / 5 : ℝ)) n * ‖g t n‖) ∧
        thirdFullThreeBandZ3InfiniteWienerMass244
          (Real.log (9 / 5 : ℝ)) (g t) ≤ 100) ∧
      (∀ n, g a n = thirdFullThreeBandZ3ProjectedInitial244 u0 n) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        Summable (fun n : TrIndex244 =>
          thirdFullThreeBandZ3Weight244 (Real.log (5 / 4 : ℝ)) n *
            ‖thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n‖) ∧
        thirdFullThreeBandZ3InfiniteWienerMass244 (Real.log (5 / 4 : ℝ))
          (thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t)) ≤ 50000) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        ∀ n, thirdFullThreeBandZ3FourierIsTransverse244 n
          (thirdFullThreeBandZ3InfiniteOrderedLeray244 (g t) n)) ∧
      (∀ t ∈ Icc a (thirdFullThreeBandZ3GalerkinCommonHorizon244 a),
        ∀ n : TrIndex244,
          g t n - thirdFullThreeBandZ3ProjectedInitial244 u0 n =
            ∫ r in a..t,
              (-(mu * ‖thirdFullThreeBandZ3ComplexFrequency244 n‖ ^ 2)) •
                g r n + thirdFullThreeBandZ3InfiniteOrderedLeray244 (g r) n) := by
  obtain ⟨hProjSum, hProjMass⟩ :=
    thirdFullThreeBand_z3ProjectedInitial_admissible244 u0 hSummable hMass
  obtain ⟨g, hCont, hHigh, hTrace, hSource, hEquation⟩ :=
    thirdFullThreeBand_z3PrescribedFourier_localExistence244
      mu a hmu hmuMax s hExhaust
      (thirdFullThreeBandZ3ProjectedInitial244 u0) hProjSum hProjMass
  refine ⟨g, hCont, hHigh, hTrace, hSource, ?_, hEquation⟩
  intro t ht n
  exact thirdFullThreeBand_z3InfiniteOrderedLeray_transverse_of_mass244
    (g t) (hHigh t ht).1 (hHigh t ht).2 n

end
end PrimeTensor.FirstMonomialTriad
