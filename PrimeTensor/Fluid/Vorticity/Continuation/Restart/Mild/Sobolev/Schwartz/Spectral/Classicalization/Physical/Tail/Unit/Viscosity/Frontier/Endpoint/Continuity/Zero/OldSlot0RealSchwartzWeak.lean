import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldJetCompactWeak
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Cutoff.Graph
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Real

/-!
# Pressure-free weak continuity against arbitrary real Schwartz tests

`OldJetCompactWeak` proves weak continuity of the actual old zeroth endpoint
`H3ScalarL2` coordinate against every compact smooth physical test.

The existing cutoff development provides, for every real Schwartz function
`φ` on the Euclidean Fourier carrier, compact Schwartz approximants

    χₙ φ

whose `L²` classes converge to `φ.toLp`.  Each cutoff is literally the
transport of an `H3WeakTestFunction`.

The old zeroth endpoint coordinate has a uniform `L²` norm bound `≤ E`,
directly from the retained canonical H³ tail energy.  Therefore compact-test
weak continuity extends by a standard uniform approximation argument to every
real Schwartz test:

    q ↦ ⟪ transport(J₀(q)), φ.toLp ⟫_ℝ

is continuous.

This remains completely pressure-free.  The next step can complexify real and
imaginary Schwartz tests and feed the result into the existing smooth-compact
weighted spectral bridge.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3ZeroOldSlot0RealSchwartzWeak
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ZeroOldSlot0RealSchwartzWeak :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Elementary real-Hilbert pairing stability in the test argument. -/
theorem dist_real_inner_right_le_norm_mul_norm_sub
    (F Φ G : H3FourierRealL2) :
    dist
        (inner ℝ F Φ)
        (inner ℝ F G)
      ≤
    ‖F‖ * ‖Φ - G‖ := by
  rw [dist_eq_norm, ← inner_sub_right]
  exact norm_inner_le_norm F (Φ - G)

/-- The transported old zeroth endpoint coordinate has uniform real `L²` norm
at most the retained H³ ceiling `E`. -/
theorem norm_h3ToFourierRealL2_preterminalOldSlot0_le_E
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : Fin 3) :
    ‖h3ToFourierRealL2
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 j) q)‖
      ≤
    E := by
  rw [norm_h3ToFourierRealL2]

  let hInt :
      VelocityH3IntegrableAt
        u
        (t + (q : ℝ)) :=
    h3PreterminalTailIntegrableOnElapsed
      hEnd hTail q

  let hMeas :
      VelocityH3MeasurableAt
        u
        (t + (q : ℝ)) :=
    h3PreterminalTailMeasurableOnElapsed
      hNS ht hEnd hTail q

  have hSq :
      ‖velocityH3L2JetAt
          u
          (t + (q : ℝ))
          hInt
          hMeas
          (h3JetSlot0 j)‖ ^ 2
        ≤
      velocityH3EnergyAt
        u
        (t + (q : ℝ)) :=
    velocityH3L2JetAt_coordinate_norm_sq_le_energy
      hInt hMeas (h3JetSlot0 j)

  have hAt :=
    hTail
      (t + (q : ℝ))
      ⟨
        by linarith [q.2.1],
        by linarith [q.2.2, hEnd]
      ⟩

  have hNorm0 :
      0 ≤
      ‖velocityH3L2JetAt
          u
          (t + (q : ℝ))
          hInt
          hMeas
          (h3JetSlot0 j)‖ :=
    norm_nonneg _

  unfold h3PreterminalCanonicalL2JetOnElapsed

  nlinarith [hSq, hAt.2]

/-- Every cutoff real-Schwartz pairing is continuous because the cutoff is
literally a transported compact weak test. -/
theorem continuous_h3PreterminalOldSlot0_realSchwartzCutoffPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (n : ℕ)
    (j : Fin 3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3ToFourierRealL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q))
          ((h3W12CutoffSchwartz n φ).toLp
            2 (volume : Measure H3FourierPoint3))) := by
  let ψ : H3WeakTestFunction :=
    h3W12CutoffWeakTest n φ

  have hCompact :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          inner ℝ
            (h3WeakTestFunctionPhysicalL2 ψ)
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q)) :=
    continuous_h3WeakTest_inner_preterminalOldSlot0
      hNS ht hEnd hE hTail ψ j

  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3ToFourierRealL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q))
          ((h3W12CutoffSchwartz n φ).toLp
            2 (volume : Measure H3FourierPoint3)))
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 ψ)
          (h3PreterminalCanonicalL2JetOnElapsed
            hNS ht hEnd hTail (h3JetSlot0 j) q)) := by
    funext q

    let J : H3ScalarL2 :=
      h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail (h3JetSlot0 j) q

    have hTransport :=
      inner_h3ToFourierRealL2_weakTestTransport
        J ψ

    have hSchwartz :
        h3WeakTestToFourierRealSchwartz ψ
          =
        h3W12CutoffSchwartz n φ := by
      dsimp only [ψ]
      exact
        h3WeakTestToFourierRealSchwartz_cutoffWeakTest
          n φ

    rw [hSchwartz] at hTransport

    calc
      inner ℝ
          (h3ToFourierRealL2 J)
          ((h3W12CutoffSchwartz n φ).toLp
            2 (volume : Measure H3FourierPoint3))
          =
        inner ℝ
          J
          (h3WeakTestFunctionPhysicalL2 ψ) :=
        hTransport
      _ =
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 ψ)
          J := by
        rw [real_inner_comm]

  rw [hEq]

  exact hCompact

/-- Pressure-free weak continuity of the transported old zeroth endpoint
coordinate against every real Schwartz test. -/
theorem continuous_h3PreterminalOldSlot0_realSchwartzPairing
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (j : Fin 3) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3ToFourierRealL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail (h3JetSlot0 j) q))
          (φ.toLp
            2 (volume : Measure H3FourierPoint3))) := by
  rw [continuous_iff_continuousAt]
  intro q₀

  rw [Metric.continuousAt_iff]
  intro ε hε

  have hE1 :
      0 < E + 1 := by
    linarith

  let η : ℝ :=
    ε / (4 * (E + 1))

  have hη :
      0 < η := by
    dsimp only [η]
    positivity

  have hApprox :=
    h3W12CutoffSchwartz_toLp_tendsto φ

  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        dist
            ((h3W12CutoffSchwartz n φ).toLp
              2 (volume : Measure H3FourierPoint3))
            (φ.toLp
              2 (volume : Measure H3FourierPoint3))
          <
        η :=
    hApprox.eventually
      (Metric.ball_mem_nhds
        (φ.toLp
          2 (volume : Measure H3FourierPoint3))
        hη)

  rw [Filter.eventually_atTop] at hEventually

  obtain ⟨n, hn⟩ :=
    hEventually

  have hCloseRaw :=
    hn n le_rfl

  have hClose :
      ‖(φ.toLp
            2 (volume : Measure H3FourierPoint3))
          -
        (h3W12CutoffSchwartz n φ).toLp
          2 (volume : Measure H3FourierPoint3)‖
        <
      η := by
    have hSymm :
        dist
            (φ.toLp
              2 (volume : Measure H3FourierPoint3))
            ((h3W12CutoffSchwartz n φ).toLp
              2 (volume : Measure H3FourierPoint3))
          <
        η := by
      simpa only [dist_comm] using hCloseRaw
    simpa only [dist_eq_norm] using hSymm

  let G : H3FourierRealL2 :=
    (h3W12CutoffSchwartz n φ).toLp
      2 (volume : Measure H3FourierPoint3)

  let Φ : H3FourierRealL2 :=
    φ.toLp
      2 (volume : Measure H3FourierPoint3)

  let F :
      Set.Icc (0 : ℝ) tau → H3FourierRealL2 :=
    fun q =>
      h3ToFourierRealL2
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail (h3JetSlot0 j) q)

  have hGCont :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          inner ℝ (F q) G) := by
    dsimp only [F, G]
    exact
      continuous_h3PreterminalOldSlot0_realSchwartzCutoffPairing
        hNS ht hEnd hE hTail φ n j

  have hMidAt :=
    Metric.continuousAt_iff.mp
      (hGCont.continuousAt (x := q₀))
      (ε / 2)
      (by linarith)

  obtain ⟨δ, hδ, hδprop⟩ :=
    hMidAt

  refine ⟨δ, hδ, ?_⟩
  intro q hq

  have hFq :
      ‖F q‖ ≤ E := by
    dsimp only [F]
    exact
      norm_h3ToFourierRealL2_preterminalOldSlot0_le_E
        hNS ht hEnd hE hTail q j

  have hFq₀ :
      ‖F q₀‖ ≤ E := by
    dsimp only [F]
    exact
      norm_h3ToFourierRealL2_preterminalOldSlot0_le_E
        hNS ht hEnd hE hTail q₀ j

  have hCloseFG :
      ‖Φ - G‖ < η := by
    simpa only [Φ, G] using hClose

  have hApproxQ :
      dist
          (inner ℝ (F q) Φ)
          (inner ℝ (F q) G)
        <
      ε / 4 := by
    have hPair :=
      dist_real_inner_right_le_norm_mul_norm_sub
        (F q) Φ G

    have hMul :
        ‖F q‖ * ‖Φ - G‖
          <
        E * η := by
      have hNormNonneg :
          0 ≤ ‖Φ - G‖ :=
        norm_nonneg _
      have hENonneg :
          0 ≤ E := by
        linarith
      exact
        lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right
            hFq hNormNonneg)
          (mul_lt_mul_of_pos_left
            hCloseFG
            (by linarith))

    have hEta :
        E * η < ε / 4 := by
      dsimp only [η]
      have hRatio :
          E / (E + 1) < 1 := by
        exact (div_lt_one hE1).2 (by linarith)
      have hε4 :
          0 < ε / 4 := by
        linarith
      calc
        E * (ε / (4 * (E + 1)))
            =
          (ε / 4) * (E / (E + 1)) := by
              field_simp
              <;> ring
        _ < (ε / 4) * 1 := by
              exact
                mul_lt_mul_of_pos_left
                  hRatio hε4
        _ = ε / 4 := by ring

    exact
      lt_of_le_of_lt
        hPair
        (lt_trans hMul hEta)

  have hApproxQ₀ :
      dist
          (inner ℝ (F q₀) G)
          (inner ℝ (F q₀) Φ)
        <
      ε / 4 := by
    rw [dist_comm]

    have hPair :=
      dist_real_inner_right_le_norm_mul_norm_sub
        (F q₀) Φ G

    have hMul :
        ‖F q₀‖ * ‖Φ - G‖
          <
        E * η := by
      have hNormNonneg :
          0 ≤ ‖Φ - G‖ :=
        norm_nonneg _
      exact
        lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right
            hFq₀ hNormNonneg)
          (mul_lt_mul_of_pos_left
            hCloseFG
            (by linarith))

    have hEta :
        E * η < ε / 4 := by
      dsimp only [η]
      have hRatio :
          E / (E + 1) < 1 := by
        exact (div_lt_one hE1).2 (by linarith)
      have hε4 :
          0 < ε / 4 := by
        linarith
      calc
        E * (ε / (4 * (E + 1)))
            =
          (ε / 4) * (E / (E + 1)) := by
              field_simp
              <;> ring
        _ < (ε / 4) * 1 := by
              exact
                mul_lt_mul_of_pos_left
                  hRatio hε4
        _ = ε / 4 := by ring

    exact
      lt_of_le_of_lt
        hPair
        (lt_trans hMul hEta)

  have hMid :
      dist
          (inner ℝ (F q) G)
          (inner ℝ (F q₀) G)
        <
      ε / 2 :=
    hδprop hq

  calc
    dist
        (inner ℝ (F q) Φ)
        (inner ℝ (F q₀) Φ)
        ≤
      dist
          (inner ℝ (F q) Φ)
          (inner ℝ (F q) G)
        +
      dist
          (inner ℝ (F q) G)
          (inner ℝ (F q₀) Φ) :=
      dist_triangle _ _ _
    _ ≤
      dist
          (inner ℝ (F q) Φ)
          (inner ℝ (F q) G)
        +
      (dist
          (inner ℝ (F q) G)
          (inner ℝ (F q₀) G)
        +
       dist
          (inner ℝ (F q₀) G)
          (inner ℝ (F q₀) Φ)) := by
      have hTri :=
        dist_triangle
          (inner ℝ (F q) G)
          (inner ℝ (F q₀) G)
          (inner ℝ (F q₀) Φ)
      linarith
    _ <
      ε / 4 + (ε / 2 + ε / 4) := by
      exact
        add_lt_add
          hApproxQ
          (add_lt_add hMid hApproxQ₀)
    _ = ε := by
      ring

end

end Euclidean
end Bridge
end PrimeTensor
