import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalStrongTrace244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzH3CrossEnergyInvariant244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzRootContinuity244
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Tactic

/-!
# Canonical 27-coordinate strong L⁴ second-jet trace of a weighted H³ velocity

A genuine H³ spectral Schwartz completion already controls all 27 second-jet
L⁴ difference roots by the E₂/E₃ mixed-jet graph.  We now identify those
roots with exact distances in mathlib's complete L⁴ space, deduce a strong
L⁴ limit for each literal second Schwartz derivative, and show that the limit
is independent of the chosen decoder- and derivative-matched Schwartz family.

No extra L⁴ approximation premise is assumed.  This establishes a canonical
L⁴ SECOND-JET trace, not yet its almost-everywhere identification with the
previously defined physical L² derivative of an actual Navier–Stokes slice.
That identification is needed before passing 3–2–2 products to the physical
transport integral; no such equality is asserted below.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology
open scoped SchwartzMap LineDeriv BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeSecondL4Trace244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

-- Mathlib's normed/metric/topological structure on Lp requires p ≥ 1.
-- The explicit exponent fact resolves all downstream L⁴ typeclasses.
local instance l4ExponentAtLeastOne244 : Fact (1 ≤ (4 : ENNReal)) :=
  ⟨by norm_num⟩

private abbrev L4Carrier244 := MeasureTheory.Lp ℝ 4 (volume : Measure V3)

/-- Actual real Schwartz L⁴ fourth-root integral equals the norm of its
mathlib L⁴ class, with no additional 2π or carrier normalization. -/
theorem h3RealSchwartz_norm_toLp_four_eq_root244
    (f : SchwartzMap V3 ℝ) :
    ‖f.toLp 4 (volume : Measure V3)‖ = schwartzIntegralL4Root244 f := by
  have hRaw :
      realLpEnorm volume 4 (f : V3 → ℝ) =
        eLpNorm (f : V3 → ℝ) (ENNReal.ofReal (4 : ℝ))
          (volume : Measure V3) := by
    unfold realLpEnorm
    have hELp :=
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (p := ENNReal.ofReal (4 : ℝ))
        (μ := (volume : Measure V3))
        (f := (f : V3 → ℝ)) (by norm_num) (by simp)
    symm
    simpa only [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (4 : ℝ))]
      using hELp
  have hEnorm :
      eLpNorm (f : V3 → ℝ) (4 : ENNReal) (volume : Measure V3) =
        ENNReal.ofReal (schwartzIntegralL4Root244 f) := by
    have h : eLpNorm (f : V3 → ℝ) (ENNReal.ofReal (4 : ℝ))
        (volume : Measure V3) =
        ENNReal.ofReal (schwartzIntegralL4Root244 f) := by
      rw [← hRaw]
      exact lowNormalSchwartz_realLpEnorm_four_eq_actualRoot244 f
    simpa only [show ENNReal.ofReal (4 : ℝ) = (4 : ENNReal) by norm_num]
      using h
  rw [SchwartzMap.norm_toLp, hEnorm]
  exact ENNReal.toReal_ofReal (schwartzIntegralL4Root244_nonneg f)

/-- The actual L⁴ class of a Schwartz difference equals the difference
of the two actual L⁴ classes. -/
theorem h3RealSchwartz_toLp_four_sub244
    (f g : SchwartzMap V3 ℝ) :
    (f - g).toLp 4 (volume : Measure V3) =
      f.toLp 4 (volume : Measure V3) -
      g.toLp 4 (volume : Measure V3) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    (f - g).coeFn_toLp 4 (volume : Measure V3),
    f.coeFn_toLp 4 (volume : Measure V3),
    g.coeFn_toLp 4 (volume : Measure V3),
    MeasureTheory.Lp.coeFn_sub
      (f.toLp 4 (volume : Measure V3))
      (g.toLp 4 (volume : Measure V3))
  ] with x hSub hf hg hDiff
  rw [hSub, hDiff]
  simp only [Pi.sub_apply, hf, hg, sub_apply]

/-- Exact metric identification for a second-derivative Schwartz pair.
This is a REAL L⁴ metric identity, not an assumed Sobolev difference norm. -/
theorem h3RealSchwartz_secondJet_L4dist_eq_root244
    (f g : A3 → SchwartzMap V3 ℝ) (j a b : A3) :
    dist
      ((∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b} (f j))).toLp
          4 (volume : Measure V3))
      ((∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b} (g j))).toLp
          4 (volume : Measure V3)) =
    schwartzSecondJetDifferenceRoot244 f g j a b := by
  calc
    dist
        ((∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b} (f j))).toLp
            4 (volume : Measure V3))
        ((∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b} (g j))).toLp
            4 (volume : Measure V3)) =
        ‖((∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b} (f j))) -
           (∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b} (g j)))).toLp
            4 (volume : Measure V3)‖ := by
              rw [dist_eq_norm]
              exact congrArg (fun x : L4Carrier244 => ‖x‖)
                (h3RealSchwartz_toLp_four_sub244 _ _).symm
    _ = schwartzIntegralL4Root244
          ((∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b} (f j))) -
           (∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b} (g j)))) :=
      h3RealSchwartz_norm_toLp_four_eq_root244 _
    _ = schwartzSecondJetDifferenceRoot244 f g j a b := rfl

/-- Literal second Schwartz derivatives of EVERY H³ energy-Cauchy family
are genuinely Cauchy in mathlib's complete L⁴ space, coordinatewise. -/
theorem h3MatchedSchwartz_secondJet_L4_cauchy244
    {U : H3SpectralVelocityState}
    (F : H3MatchedSchwartzGradientCompletion244 U)
    (j : Fin 3) (a b : A3) :
    CauchySeq (fun n =>
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (F.family.approximants n (h3AxisOfFin3 j)))).toLp
            4 (volume : Measure V3)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := F.family.energyCauchy.toMixedGraph ε hε
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hSlot := (schwartzMixedJetGraphDistance_bounds_slots244
    (F.family.approximants m) (F.family.approximants n)
    (b, (a, (b, (h3AxisOfFin3 j, h3AxisOfFin3 j))))).2.1
  have hDist := h3RealSchwartz_secondJet_L4dist_eq_root244
    (F.family.approximants m) (F.family.approximants n)
    (h3AxisOfFin3 j) a b
  calc
    dist
        ((∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b}
            (F.family.approximants m (h3AxisOfFin3 j)))).toLp
              4 (volume : Measure V3))
        ((∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b}
            (F.family.approximants n (h3AxisOfFin3 j)))).toLp
              4 (volume : Measure V3)) =
        schwartzSecondJetDifferenceRoot244
          (F.family.approximants m) (F.family.approximants n)
          (h3AxisOfFin3 j) a b := hDist
    _ ≤ schwartzMixedJetGraphDistance244
          (F.family.approximants m) (F.family.approximants n) := hSlot
    _ < ε := hN m hm n hn

/-- A canonical L⁴ second-derivative class of ONE matched Schwartz
completion. Completeness is used only after proving the actual metric Cauchy
theorem, so this definition has no nonlinear limit premise. -/
noncomputable def h3MatchedSchwartz_secondJet_L4_limit244
    {U : H3SpectralVelocityState}
    (F : H3MatchedSchwartzGradientCompletion244 U)
    (j : Fin 3) (a b : A3) : L4Carrier244 :=
  Classical.choose (cauchySeq_tendsto_of_complete
    (h3MatchedSchwartz_secondJet_L4_cauchy244 F j a b))

/-- Each literal second derivative converges STRONGLY in L⁴ to the trace,
not merely weakly or in its scalar fourth-power integral. -/
theorem h3MatchedSchwartz_secondJet_L4_tendsto244
    {U : H3SpectralVelocityState}
    (F : H3MatchedSchwartzGradientCompletion244 U)
    (j : Fin 3) (a b : A3) :
    Tendsto (fun n =>
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (F.family.approximants n (h3AxisOfFin3 j)))).toLp
            4 (volume : Measure V3)) atTop
      (𝓝 (h3MatchedSchwartz_secondJet_L4_limit244 F j a b)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete
    (h3MatchedSchwartz_secondJet_L4_cauchy244 F j a b))

/-- Two independently chosen, exactly matched H³ Schwartz completions
have the SAME L⁴ second-jet limit in every physical velocity/derivative slot.
This follows from cross E₂/E₃ energy, not a priori agreement in L⁴. -/
theorem h3MatchedSchwartz_secondJet_L4_limit_unique244
    (U : H3SpectralVelocityState)
    (F G : H3MatchedSchwartzGradientCompletion244 U)
    (j : Fin 3) (a b : A3) :
    h3MatchedSchwartz_secondJet_L4_limit244 F j a b =
      h3MatchedSchwartz_secondJet_L4_limit244 G j a b := by
  have hCross := matchedSpectral_crossEnergy_vanishes_of_sameLimit244
    U F.family G.family F.spectral G.spectral
    F.spectral_tendsto G.spectral_tendsto
    F.second_exact G.second_exact F.third_exact G.third_exact
  have hGraph := schwartzMixedJetGraph_tendsto_zero_of_crossEnergy244
    F.family.approximants G.family.approximants hCross
  have hRootBound (n : ℕ) :
      schwartzSecondJetDifferenceRoot244
        (F.family.approximants n) (G.family.approximants n)
        (h3AxisOfFin3 j) a b ≤
      schwartzMixedJetGraphDistance244
        (F.family.approximants n) (G.family.approximants n) :=
    (schwartzMixedJetGraphDistance_bounds_slots244
      (F.family.approximants n) (G.family.approximants n)
      (b, (a, (b, (h3AxisOfFin3 j, h3AxisOfFin3 j))))).2.1
  have hRootNonneg (n : ℕ) :
      0 ≤ schwartzSecondJetDifferenceRoot244
        (F.family.approximants n) (G.family.approximants n)
        (h3AxisOfFin3 j) a b := schwartzIntegralL4Root244_nonneg _
  have hRootZero :
      Tendsto (fun n => schwartzSecondJetDifferenceRoot244
        (F.family.approximants n) (G.family.approximants n)
        (h3AxisOfFin3 j) a b) atTop (𝓝 0) :=
    squeeze_zero hRootNonneg hRootBound hGraph
  have hDistZero : Tendsto (fun n =>
      dist
        ((∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b}
            (F.family.approximants n (h3AxisOfFin3 j)))).toLp
              4 (volume : Measure V3))
        ((∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b}
            (G.family.approximants n (h3AxisOfFin3 j)))).toLp
              4 (volume : Measure V3))) atTop (𝓝 0) := by
    have hDistance (n : ℕ) := h3RealSchwartz_secondJet_L4dist_eq_root244
      (F.family.approximants n) (G.family.approximants n)
      (h3AxisOfFin3 j) a b
    simpa only [hDistance] using hRootZero
  have hDistLimit :=
    (h3MatchedSchwartz_secondJet_L4_tendsto244 F j a b).dist
      (h3MatchedSchwartz_secondJet_L4_tendsto244 G j a b)
  have hEq :
      dist (h3MatchedSchwartz_secondJet_L4_limit244 F j a b)
        (h3MatchedSchwartz_secondJet_L4_limit244 G j a b) = 0 :=
    tendsto_nhds_unique hDistLimit hDistZero
  exact (dist_eq_zero.mp hEq)

/-- Choice-independent actual L⁴ trace for all weighted H³ states.
It is defined from one completed Schwartz family and proved equal to the
L⁴ limit obtained from EVERY fully matched alternative family. -/
noncomputable def weightedH3CanonicalSecondJetL4Trace244
    (U : H3SpectralVelocityState)
    (j : Fin 3) (a b : A3) : L4Carrier244 :=
  h3MatchedSchwartz_secondJet_L4_limit244
    (Classical.choice (exists_h3MatchedSchwartzGradientCompletion244 U))
    j a b

/-- Every decoder- and jet-matched Schwartz completion converges to the
same canonical second-derivative L⁴ field on the Euclidean carrier. -/
theorem weightedH3CanonicalSecondJetL4Trace_tendsto244
    (U : H3SpectralVelocityState)
    (F : H3MatchedSchwartzGradientCompletion244 U)
    (j : Fin 3) (a b : A3) :
    Tendsto (fun n =>
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (F.family.approximants n (h3AxisOfFin3 j)))).toLp
            4 (volume : Measure V3)) atTop
      (𝓝 (weightedH3CanonicalSecondJetL4Trace244 U j a b)) := by
  have hEq := h3MatchedSchwartz_secondJet_L4_limit_unique244
    U F (Classical.choice (exists_h3MatchedSchwartzGradientCompletion244 U))
    j a b
  rw [weightedH3CanonicalSecondJetL4Trace244]
  rw [← hEq]
  exact h3MatchedSchwartz_secondJet_L4_tendsto244 F j a b

/-- The complete 27-coordinate second-derivative L⁴ family converges
jointly in the finite product topology, not just in individually chosen
coordinate completions. -/
theorem weightedH3CanonicalSecondJetL4Trace_family_tendsto244
    (U : H3SpectralVelocityState)
    (F : H3MatchedSchwartzGradientCompletion244 U) :
    Tendsto
      (fun n : ℕ => fun j : Fin 3 => fun a b : A3 =>
        (∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b}
            (F.family.approximants n (h3AxisOfFin3 j)))).toLp
              4 (volume : Measure V3))
      atTop
      (𝓝 (fun j : Fin 3 => fun a b : A3 =>
        weightedH3CanonicalSecondJetL4Trace244 U j a b)) := by
  rw [tendsto_pi_nhds]
  intro j
  rw [tendsto_pi_nhds]
  intro a
  rw [tendsto_pi_nhds]
  intro b
  exact weightedH3CanonicalSecondJetL4Trace_tendsto244 U F j a b

end
end PrimeTensor.FirstMonomialTriad
