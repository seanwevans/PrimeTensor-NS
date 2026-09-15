import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.OldJetRealSchwartzWeak
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Complex
import Mathlib.Analysis.Fourier.LpSpace

/-!
# Pressure-free complex-Schwartz weak continuity of the old Fourier H³ jet

`OldJetRealSchwartzWeak` packages pressure-free weak continuity of every
physical H³ jet coordinate after canonical carrier transport, tested against
every real Schwartz function.

The canonical Fourier jet adds only two representation changes:

* real-to-complex `L²` embedding;
* the unitary `L²` Fourier transform.

For a complex Schwartz frequency test `Ψ`, unitarity gives

    ⟪𝓕(complexify f), Ψ⟫
      =
    ⟪complexify f, 𝓕⁻¹ Ψ⟫.

Because `f` is real-valued, the real part of the latter pairing depends only on
the real part of `𝓕⁻¹ Ψ`.  That real part is again a real Schwartz function.
Thus the already-proved real-Schwartz weak continuity transports directly
through Plancherel.

No pressure, temporal derivative, endpoint continuity, or density argument is
introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3ZeroOldJetFourierSchwartzWeak
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3ZeroOldJetFourierSchwartzWeak :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- For a real Fourier-carrier `L²` field, the real part of the complexified
pairing against a complex Schwartz test is exactly the real `L²` pairing
against the pointwise real part of that test. -/
theorem re_inner_h3ComplexifyFourierL2_schwartz_eq_realPart
    (f : H3FourierRealL2)
    (Φ : 𝓢(H3FourierPoint3, ℂ)) :
    (inner ℂ
        (h3ComplexifyFourierL2 f)
        (Φ.toLp 2 (volume : Measure H3FourierPoint3))).re
      =
    inner ℝ
      f
      ((h3ComplexSchwartzRealPart Φ).toLp
        2 (volume : Measure H3FourierPoint3)) := by
  rw [MeasureTheory.L2.inner_def]
  rw [MeasureTheory.L2.inner_def]

  have hIntegrable :=
    MeasureTheory.L2.integrable_inner
      (𝕜 := ℂ)
      (h3ComplexifyFourierL2 f)
      (Φ.toLp 2 (volume : Measure H3FourierPoint3))

  calc
    (∫ x : H3FourierPoint3,
        inner ℂ
          ((h3ComplexifyFourierL2 f : H3FourierPoint3 → ℂ) x)
          ((Φ.toLp 2 (volume : Measure H3FourierPoint3) :
              H3FourierPoint3 → ℂ) x)
      ∂volume).re
        =
      ∫ x : H3FourierPoint3,
        (inner ℂ
          ((h3ComplexifyFourierL2 f : H3FourierPoint3 → ℂ) x)
          ((Φ.toLp 2 (volume : Measure H3FourierPoint3) :
              H3FourierPoint3 → ℂ) x)).re
      ∂volume := by
        exact
          (Complex.reCLM.integral_comp_comm hIntegrable).symm

    _ =
      ∫ x : H3FourierPoint3,
        inner ℝ
          ((f : H3FourierPoint3 → ℝ) x)
          (((h3ComplexSchwartzRealPart Φ).toLp
              2 (volume : Measure H3FourierPoint3) :
              H3FourierPoint3 → ℝ) x)
      ∂volume := by
        apply integral_congr_ae

        filter_upwards [
          Complex.ofRealCLM.coeFn_compLp f,
          Φ.coeFn_toLp 2 (volume : Measure H3FourierPoint3),
          (h3ComplexSchwartzRealPart Φ).coeFn_toLp
            2 (volume : Measure H3FourierPoint3)
        ] with x hf hΦ hRe

        unfold h3ComplexifyFourierL2
        rw [hf, hΦ, hRe]

        simp [h3ComplexSchwartzRealPart_apply]

/-- Pull a complex Schwartz test backward through Plancherel.  The real part of
the resulting Fourier pairing is a physical-carrier real-Schwartz pairing. -/
theorem re_inner_h3ScalarFourierL2_schwartz_eq_inverseRealPart
    (f : H3ScalarL2)
    (Ψ : 𝓢(H3FourierPoint3, ℂ)) :
    (inner ℂ
        (h3ScalarFourierL2 f)
        (Ψ.toLp 2 (volume : Measure H3FourierPoint3))).re
      =
    inner ℝ
      (h3ToFourierRealL2 f)
      ((h3ComplexSchwartzRealPart (𝓕⁻ Ψ)).toLp
        2 (volume : Measure H3FourierPoint3)) := by
  let T :=
    MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ

  let F : H3FourierComplexL2 :=
    h3ComplexifyFourierL2
      (h3ToFourierRealL2 f)

  let Ψ₂ : H3FourierComplexL2 :=
    Ψ.toLp 2 (volume : Measure H3FourierPoint3)

  have hInv :
      T.symm Ψ₂
        =
      (𝓕⁻ Ψ).toLp
        2 (volume : Measure H3FourierPoint3) := by
    change
      𝓕⁻ (Ψ.toLp 2 (volume : Measure H3FourierPoint3))
        =
      (𝓕⁻ Ψ).toLp
        2 (volume : Measure H3FourierPoint3)

    exact
      SchwartzMap.toLp_fourierInv_eq Ψ

  have hPairUnitary :
      inner ℂ
          (T F)
          Ψ₂
        =
      inner ℂ
          F
          (T.symm Ψ₂) := by
    simpa only [T.apply_symm_apply] using
      (T.inner_map_map F (T.symm Ψ₂))

  have hPair :
      inner ℂ
          (T F)
          Ψ₂
        =
      inner ℂ
          F
          ((𝓕⁻ Ψ).toLp
            2 (volume : Measure H3FourierPoint3)) := by
    simpa only [hInv] using hPairUnitary

  change
    (inner ℂ (T F) Ψ₂).re
      =
    inner ℝ
      (h3ToFourierRealL2 f)
      ((h3ComplexSchwartzRealPart (𝓕⁻ Ψ)).toLp
        2 (volume : Measure H3FourierPoint3))

  rw [hPair]

  exact
    re_inner_h3ComplexifyFourierL2_schwartz_eq_realPart
      (h3ToFourierRealL2 f)
      (𝓕⁻ Ψ)

/-- Every old ordered H³ Fourier-jet coordinate has pressure-free weak
continuity against every complex Schwartz frequency test, in the real-part
pairing required by the weighted spectral weak topology. -/
theorem continuous_re_inner_h3PreterminalCanonicalFourierJetOnElapsed_schwartz
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (Ψ : 𝓢(H3FourierPoint3, ℂ))
    (a : H3JetIndex) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        (inner ℂ
          (h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail a q)
          (Ψ.toLp 2
            (volume : Measure H3FourierPoint3))).re) := by
  let φ : 𝓢(H3FourierPoint3, ℝ) :=
    h3ComplexSchwartzRealPart (𝓕⁻ Ψ)

  have hReal :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          inner ℝ
            (h3ToFourierRealL2
              (h3PreterminalCanonicalL2JetOnElapsed
                hNS ht hEnd hTail a q))
            (φ.toLp 2
              (volume : Measure H3FourierPoint3))) :=
    continuous_h3PreterminalOldJet_realSchwartzPairing
      hNS ht hEnd hE hTail φ a

  have hEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        (inner ℂ
          (h3PreterminalCanonicalFourierJetOnElapsed
            hNS ht hEnd hTail a q)
          (Ψ.toLp 2
            (volume : Measure H3FourierPoint3))).re)
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        inner ℝ
          (h3ToFourierRealL2
            (h3PreterminalCanonicalL2JetOnElapsed
              hNS ht hEnd hTail a q))
          (φ.toLp 2
            (volume : Measure H3FourierPoint3))) := by
    funext q

    rw [
      h3PreterminalCanonicalFourierJetOnElapsed_eq_scalarFourierL2
        hNS ht hEnd hTail a q
    ]

    exact
      re_inner_h3ScalarFourierL2_schwartz_eq_inverseRealPart
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail a q)
        Ψ

  rw [hEq]

  exact hReal

end

end Euclidean
end Bridge
end PrimeTensor
