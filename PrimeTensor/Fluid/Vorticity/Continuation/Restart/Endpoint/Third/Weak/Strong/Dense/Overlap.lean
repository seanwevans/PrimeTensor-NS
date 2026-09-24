import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Endpoint.Pressure.Free.Energy

/-!
# Extend dense old/selected agreement through a weakly continuous endpoint

The energy route is not the only possible way to obtain strong endpoint
continuity.

Suppose an old Hilbert-valued path `F` is weakly continuous in every real
pairing, a comparison path `G` is strongly continuous, and `F = G` on a dense
set of times.  Then the two paths agree everywhere.  Indeed, every real weak
pairing agrees everywhere by continuity and density; testing the difference
against itself forces its norm to vanish.

This file packages that elementary weak/strong uniqueness principle and applies
it to the pressure-free weighted H³ spectral path.

Consequently, to bypass the scalar-energy / dominated-differentiation route it
is enough to prove that the old preterminal spectral state agrees with one
strongly continuous selected restart on any dense collection of strict overlap
times.  Endpoint equality and strong endpoint continuity then follow
automatically.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3WeakStrongDenseOverlap
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A weakly continuous Hilbert-valued path agrees everywhere with a strongly
continuous comparison path once they agree on a dense family of parameters.

Only real parts of complex inner products are required. -/
theorem eq_of_weakRealPairings_of_dense_strongAgreement
    {α D H : Type*}
    [TopologicalSpace α]
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (F G : α → H)
    (ι : D → α)
    (hDense : DenseRange ι)
    (hWeak :
      ∀ Φ : H,
        Continuous
          (fun q : α =>
            (inner ℂ (F q) Φ).re))
    (hStrong : Continuous G)
    (hEq :
      ∀ d : D,
        F (ι d) = G (ι d)) :
    F = G := by
  have hGWeak :
      ∀ Φ : H,
        Continuous
          (fun q : α =>
            (inner ℂ (G q) Φ).re) := by
    intro Φ

    have hInner :
        Continuous
          (fun q : α =>
            inner ℂ (G q) Φ) := by
      exact
        hStrong.inner continuous_const

    exact
      RCLike.continuous_re.comp hInner

  have hPairEq :
      ∀ Φ : H,
        (fun q : α =>
          (inner ℂ (F q) Φ).re)
          =
        (fun q : α =>
          (inner ℂ (G q) Φ).re) := by
    intro Φ

    apply
      hDense.equalizer
        (hWeak Φ)
        (hGWeak Φ)

    funext d
    simp only [Function.comp_apply]
    rw [hEq d]

  funext q

  let z : H :=
    F q - G q

  have hPairAt :
      (inner ℂ (F q) z).re
        =
      (inner ℂ (G q) z).re := by
    exact
      congrFun (hPairEq z) q

  have hZero :
      (inner ℂ (F q) z).re
          -
        (inner ℂ (G q) z).re
        =
      0 :=
    sub_eq_zero.mpr hPairAt

  have hzSq :
      ‖z‖ ^ 2 = 0 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]

    change
      (inner ℂ (F q - G q) z).re = 0

    rw [inner_sub_left, Complex.sub_re]

    exact hZero

  have hzNorm :
      ‖z‖ = 0 := by
    nlinarith [norm_nonneg z]

  have hz :
      z = 0 :=
    norm_eq_zero.mp hzNorm

  exact
    sub_eq_zero.mp
      (by
        simpa only [z] using hz)

/-- Pressure-free old weighted-H³ spectral state equals any strongly continuous
comparison path that agrees with it on a dense family of elapsed times. -/
theorem h3PreterminalCanonicalSpectralState_eq_of_denseStrongAgreement_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (G :
      Set.Icc (0 : ℝ) tau →
        H3SpectralVelocityState)
    {D : Type*}
    (ι :
      D →
        Set.Icc (0 : ℝ) tau)
    (hDense : DenseRange ι)
    (hG : Continuous G)
    (hEq :
      ∀ d : D,
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail (ι d)
          =
        G (ι d)) :
    (fun q : Set.Icc (0 : ℝ) tau =>
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q)
      =
    G := by
  have hWeak :
      H3PreterminalCanonicalSpectralWeakContinuousOnElapsed
        hNS ht hEnd hTail :=
    h3PreterminalCanonicalSpectralWeakContinuousOnElapsed_pressureFree
      hNS ht hEnd hE hTail

  funext q
  funext j

  let Fj :
      Set.Icc (0 : ℝ) tau →
        H3SpectralScalarState :=
    fun r =>
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail r j

  let Gj :
      Set.Icc (0 : ℝ) tau →
        H3SpectralScalarState :=
    fun r =>
      G r j

  have hWeakj :
      ∀ Φ : H3SpectralScalarState,
        Continuous
          (fun r : Set.Icc (0 : ℝ) tau =>
            (inner ℂ (Fj r) Φ).re) := by
    intro Φ
    simpa only [Fj] using
      hWeak j Φ

  have hGj :
      Continuous Gj := by
    exact
      (continuous_apply j).comp hG

  have hEqj :
      ∀ d : D,
        Fj (ι d) = Gj (ι d) := by
    intro d
    exact
      congrFun (hEq d) j

  have hAll :
      Fj = Gj :=
    eq_of_weakRealPairings_of_dense_strongAgreement
      Fj
      Gj
      ι
      hDense
      hWeakj
      hGj
      hEqj

  exact
    congrFun hAll q

/-- Dense agreement with a strongly continuous comparison path closes the full
strong weighted-H³ spectral continuity frontier without scalar-energy
continuity. -/
theorem h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_denseStrongAgreement_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (G :
      Set.Icc (0 : ℝ) tau →
        H3SpectralVelocityState)
    {D : Type*}
    (ι :
      D →
        Set.Icc (0 : ℝ) tau)
    (hDense : DenseRange ι)
    (hG : Continuous G)
    (hEq :
      ∀ d : D,
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail (ι d)
          =
        G (ι d)) :
    H3PreterminalCanonicalSpectralStateContinuousOnElapsed
      hNS ht hEnd hTail := by
  have hStateEq :=
    h3PreterminalCanonicalSpectralState_eq_of_denseStrongAgreement_pressureFree
      hNS ht hEnd hE hTail
      G ι hDense hG hEq

  unfold
    H3PreterminalCanonicalSpectralStateContinuousOnElapsed

  change
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q)

  rw [hStateEq]

  exact hG

/-- The same dense weak/strong agreement immediately supplies the physical
zeroth/ordered-third endpoint continuity consumed by the classical overlap
machinery. -/
theorem h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_denseStrongAgreement_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (G :
      Set.Icc (0 : ℝ) tau →
        H3SpectralVelocityState)
    {D : Type*}
    (ι :
      D →
        Set.Icc (0 : ℝ) tau)
    (hDense : DenseRange ι)
    (hG : Continuous G)
    (hEq :
      ∀ d : D,
        h3PreterminalTailCanonicalSpectralStateOnElapsed
            hNS ht hEnd hTail (ι d)
          =
        G (ι d)) :
    H3PreterminalCanonicalL2EndpointContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_spectralState_pressureFree
      hNS
      ht
      hEnd
      hTail
      (h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_denseStrongAgreement_pressureFree
        hNS ht hEnd hE hTail
        G ι hDense hG hEq)

end

end Euclidean
end Bridge
end PrimeTensor
