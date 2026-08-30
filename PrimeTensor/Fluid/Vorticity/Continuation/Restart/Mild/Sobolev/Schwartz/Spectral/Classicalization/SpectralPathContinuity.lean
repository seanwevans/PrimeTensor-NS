import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpectralDifferenceEnergy

/-!
# Classicalization: spectral path continuity from H³ Fourier-jet continuity

`SpectralDifferenceEnergy` proves the exact two-snapshot identity equating the
weighted spectral distance with the finite ordered H³ Fourier-jet distance.

This file turns that identity into the topological bridge needed by the
preterminal overlap path.

On an elapsed interval `[0,τ]` contained in the old H³ tail, define the
canonical Fourier jet

    q ↦ 𝓕(D^α u(t+q))

for every ordered jet slot `α` through order three.

If every one of those finitely many `L²`-valued coordinates is continuous,
then every weighted spectral velocity component is continuous.  The proof is
pointwise in elapsed time:

* the finite sum of squared Fourier-jet distances is continuous and vanishes
  at the base time;
* the exact spectral difference-energy identity identifies it with the square
  of the spectral norm-distance;
* continuity of `sqrt` therefore forces the spectral norm-distance to zero.

The final theorem transfers this to the exact
`h3PreterminalCanonicalSpectralStateOnElapsed` used by
`PreterminalCanonicalPath`.

No Navier--Stokes evolution identity is used here.  After this bridge, the
remaining overlap input is the restarted heat--Leray mild equation, together
with whichever classical PDE regularity theorem supplies the concrete H³
Fourier-jet continuity hypothesis below.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationSpectralPathContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical H³ integrability proof at one elapsed time, extracted from the
retained terminal-tail datum. -/
noncomputable def h3PreterminalTailIntegrableOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) τ) :
    VelocityH3IntegrableAt u (t + (q : ℝ)) :=
  canonicalH3TailDataFrom_integrableOnElapsed
    hEnd hTail q

/-- Canonical measurability proof at one elapsed preterminal time. -/
noncomputable def h3PreterminalTailMeasurableOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) τ) :
    VelocityH3MeasurableAt u (t + (q : ℝ)) :=
  velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
    hNS
    (h3PreterminalElapsedTime_mem_Ioo ht hEnd q)

/-- Canonical Fourier-compatibility proof at one elapsed preterminal time. -/
noncomputable def h3PreterminalTailFourierCompatibleOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) τ) :
    VelocityH3FourierCompatibleAt
      u
      (t + (q : ℝ))
      (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)
      (h3PreterminalTailMeasurableOnElapsed
        hNS ht hEnd hTail q) :=
  velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
    hNS
    (h3PreterminalElapsedTime_mem_Ioo ht hEnd q)
    (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)

/-- One concrete ordered H³ Fourier-jet coordinate of the old solution as a
function of elapsed time. -/
noncomputable def h3PreterminalCanonicalFourierJetOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (a : H3JetIndex)
    (q : Set.Icc (0 : ℝ) τ) :
    H3FourierComplexL2 :=
  velocityH3FourierJetAt
    u
    (t + (q : ℝ))
    (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)
    (h3PreterminalTailMeasurableOnElapsed
      hNS ht hEnd hTail q)
    a

/-- Strong continuity of every concrete ordered H³ Fourier-jet coordinate on
the elapsed overlap interval. -/
def H3PreterminalCanonicalFourierJetContinuousOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ a : H3JetIndex,
    Continuous
      (h3PreterminalCanonicalFourierJetOnElapsed
        hNS ht hEnd hTail a)

/-- The same canonical spectral state as
`h3PreterminalCanonicalSpectralStateOnElapsed`, written with the explicit tail
proofs above so the difference-energy theorem can be applied uniformly. -/
noncomputable def h3PreterminalTailCanonicalSpectralStateOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) τ) :
    H3SpectralVelocityState :=
  velocityH3SpectralStateAt
    u
    (t + (q : ℝ))
    (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)
    (h3PreterminalTailMeasurableOnElapsed
      hNS ht hEnd hTail q)
    (h3PreterminalTailFourierCompatibleOnElapsed
      hNS ht hEnd hTail q)

@[simp]
theorem h3PreterminalTailCanonicalSpectralStateOnElapsed_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) τ) :
    h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q
      =
    h3PreterminalCanonicalSpectralStateOnElapsed
      hNS ht hEnd
      (canonicalH3TailDataFrom_integrableOnElapsed hEnd hTail)
      q := by
  rfl

/-- Continuity of the four finite ordered jet families makes the finite
difference-energy sum continuous. -/
theorem continuous_h3PreterminalFourierJetDifferenceSquareSum
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hJet :
      H3PreterminalCanonicalFourierJetContinuousOnElapsed
        hNS ht hEnd hTail)
    (j : Fin 3)
    (q₀ : Set.Icc (0 : ℝ) τ) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) τ =>
        ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot0 j) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot0 j) q₀‖ ^ 2
          +
        (∑ i : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot1 j i) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot1 j i) q₀‖ ^ 2)
          +
        (∑ i : Fin 3, ∑ k : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot2 j i k) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot2 j i k) q₀‖ ^ 2)
          +
        (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot3 j i k l) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot3 j i k l) q₀‖ ^ 2)) := by
  have h0 :
      Continuous
        (fun q : Set.Icc (0 : ℝ) τ =>
          ‖h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot0 j) q
              -
            h3PreterminalCanonicalFourierJetOnElapsed
              hNS ht hEnd hTail
              (h3JetSlot0 j) q₀‖ ^ 2) :=
    (((hJet (h3JetSlot0 j)).sub continuous_const).norm.pow 2)

  have h1 :
      Continuous
        (fun q : Set.Icc (0 : ℝ) τ =>
          ∑ i : Fin 3,
            ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail
                (h3JetSlot1 j i) q
                -
              h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail
                (h3JetSlot1 j i) q₀‖ ^ 2) := by
    apply continuous_finset_sum
    intro i hi
    exact
      (((hJet (h3JetSlot1 j i)).sub continuous_const).norm.pow 2)

  have h2 :
      Continuous
        (fun q : Set.Icc (0 : ℝ) τ =>
          ∑ i : Fin 3, ∑ k : Fin 3,
            ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail
                (h3JetSlot2 j i k) q
                -
              h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail
                (h3JetSlot2 j i k) q₀‖ ^ 2) := by
    apply continuous_finset_sum
    intro i hi
    apply continuous_finset_sum
    intro k hk
    exact
      (((hJet (h3JetSlot2 j i k)).sub continuous_const).norm.pow 2)

  have h3 :
      Continuous
        (fun q : Set.Icc (0 : ℝ) τ =>
          ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
            ‖h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail
                (h3JetSlot3 j i k l) q
                -
              h3PreterminalCanonicalFourierJetOnElapsed
                hNS ht hEnd hTail
                (h3JetSlot3 j i k l) q₀‖ ^ 2) := by
    apply continuous_finset_sum
    intro i hi
    apply continuous_finset_sum
    intro k hk
    apply continuous_finset_sum
    intro l hl
    exact
      (((hJet (h3JetSlot3 j i k l)).sub continuous_const).norm.pow 2)

  exact
    ((h0.add h1).add h2).add h3

/-- Strong continuity of all concrete H³ Fourier-jet coordinates implies
continuity of the explicit tail-canonical weighted spectral state. -/
theorem continuous_h3PreterminalTailCanonicalSpectralStateOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hJet :
      H3PreterminalCanonicalFourierJetContinuousOnElapsed
        hNS ht hEnd hTail) :
    Continuous
      (h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail) := by
  apply continuous_pi

  intro j

  rw [continuous_iff_continuousAt]

  intro q₀

  unfold ContinuousAt

  rw [tendsto_iff_norm_sub_tendsto_zero]

  let D : Set.Icc (0 : ℝ) τ → ℝ :=
    fun q =>
      ‖h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 j) q
          -
        h3PreterminalCanonicalFourierJetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 j) q₀‖ ^ 2
        +
      (∑ i : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot1 j i) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot1 j i) q₀‖ ^ 2)
        +
      (∑ i : Fin 3, ∑ k : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot2 j i k) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot2 j i k) q₀‖ ^ 2)
        +
      (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        ‖h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot3 j i k l) q
            -
          h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail
            (h3JetSlot3 j i k l) q₀‖ ^ 2)

  have hDContinuous :
      Continuous D := by
    exact
      continuous_h3PreterminalFourierJetDifferenceSquareSum
        hNS ht hEnd hTail hJet j q₀

  have hDZero :
      D q₀ = 0 := by
    dsimp [D]
    simp

  have hDAt :
      ContinuousAt D q₀ :=
    hDContinuous.continuousAt

  have hDTendstoRaw :
      Tendsto D
        (𝓝 q₀)
        (𝓝 (D q₀)) :=
    hDAt

  have hDTendsto :
      Tendsto D
        (𝓝 q₀)
        (𝓝 0) := by
    rw [hDZero] at hDTendstoRaw
    exact hDTendstoRaw

  have hSq :
      ∀ q : Set.Icc (0 : ℝ) τ,
        ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
              hNS ht hEnd hTail q j
            -
          h3PreterminalTailCanonicalSpectralStateOnElapsed
              hNS ht hEnd hTail q₀ j‖ ^ 2
          =
        D q := by
    intro q

    exact
      norm_velocityH3SpectralScalarAt_sub_sq
        (h3PreterminalTailFourierCompatibleOnElapsed
          hNS ht hEnd hTail q)
        (h3PreterminalTailFourierCompatibleOnElapsed
          hNS ht hEnd hTail q₀)
        j

  have hSqTendsto :
      Tendsto
        (fun q : Set.Icc (0 : ℝ) τ =>
          ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
                hNS ht hEnd hTail q j
              -
            h3PreterminalTailCanonicalSpectralStateOnElapsed
                hNS ht hEnd hTail q₀ j‖ ^ 2)
        (𝓝 q₀)
        (𝓝 0) := by
    exact
      hDTendsto.congr'
        (Filter.Eventually.of_forall
          (fun q => (hSq q).symm))

  have hSqrtAt :
      Tendsto
        Real.sqrt
        (𝓝 (0 : ℝ))
        (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt

  have hSqrtComp :=
    hSqrtAt.comp hSqTendsto

  have hSqrtTendsto :
      Tendsto
        (fun q : Set.Icc (0 : ℝ) τ =>
          Real.sqrt
            (‖h3PreterminalTailCanonicalSpectralStateOnElapsed
                  hNS ht hEnd hTail q j
                -
              h3PreterminalTailCanonicalSpectralStateOnElapsed
                  hNS ht hEnd hTail q₀ j‖ ^ 2))
        (𝓝 q₀)
        (𝓝 0) := by
    rw [Real.sqrt_zero] at hSqrtComp
    change
      Tendsto
        (Real.sqrt ∘
          fun q : Set.Icc (0 : ℝ) τ =>
            ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
                  hNS ht hEnd hTail q j
                -
              h3PreterminalTailCanonicalSpectralStateOnElapsed
                  hNS ht hEnd hTail q₀ j‖ ^ 2)
        (𝓝 q₀)
        (𝓝 0)
    exact hSqrtComp

  simpa only [
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg,
    norm_nonneg
  ] using hSqrtTendsto

/-- Final continuity bridge in the exact representation used by
`PreterminalCanonicalPath`. -/
theorem continuous_h3PreterminalCanonicalSpectralStateOnElapsed_of_fourierJet
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hJet :
      H3PreterminalCanonicalFourierJetContinuousOnElapsed
        hNS ht hEnd hTail) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) τ =>
        h3PreterminalCanonicalSpectralStateOnElapsed
          hNS ht hEnd
          (canonicalH3TailDataFrom_integrableOnElapsed hEnd hTail)
          q) := by
  have hEq :
      (fun q : Set.Icc (0 : ℝ) τ =>
        h3PreterminalCanonicalSpectralStateOnElapsed
          hNS ht hEnd
          (canonicalH3TailDataFrom_integrableOnElapsed hEnd hTail)
          q)
        =
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail := by
    funext q
    symm
    exact
      h3PreterminalTailCanonicalSpectralStateOnElapsed_eq
        hNS ht hEnd hTail q

  rw [hEq]

  exact
    continuous_h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail hJet

end
end Euclidean
end Bridge
end PrimeTensor
