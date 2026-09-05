import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Fourier.Algebra
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fourier.Derivative.AE

/-!
# Classicalization: tempered curl gives Fourier curl

The preceding increment closed the purely spectral theorem

    Fourier divergence-free + Fourier curl-free  ==>  zero.

Thus the only remaining analytic issue in physical Leray density is the passage

    weak compact-test curl  ==>  Fourier curl.

This file moves the frontier to the natural intermediate object already used
by PrimeTensor's Sobolev Fourier theory: tempered distributions.

For a physical scalar `L²` class `f`, transport it to the Euclidean carrier and
complexify it before Fourier transformation.  The canonical project transform

    h3ScalarFourierL2 f

is exactly the `L²` Fourier transform of this Euclidean complex `L²` class.

We define "tempered curl-free" by equality of the three corresponding
distributional coordinate derivatives.  Mathlib's Fourier theorem for
tempered-distribution derivatives then converts those identities to equality
of coordinate-multiplier distributions.  The existing local-integrability
argument from `Fourier.Derivative.AE` upgrades equality of those multiplier
distributions to equality of their raw representatives almost everywhere.

Consequently

    tempered curl-free  ==>  Fourier curl-free a.e.

is closed here.

After this checkpoint, the sole analytic frontier is therefore the compact-test
statement

    weak curl-free  ==>  tempered curl-free.

That is precisely the issue of extending the weak identities from compact
smooth test functions to Schwartz tests; no Fourier algebra remains.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlFourierTempered
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2AdmissibleClosureLerayDensityDualCurlFourierTempered :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Physical L² on the Euclidean carrier before Fourier transformation -/

/-- A physical real scalar `L²` class, transported to the Euclidean Fourier
carrier and complexified, but not yet Fourier transformed. -/
noncomputable def h3PhysicalScalarL2EuclideanComplex
    (f : H3ScalarL2) :
    H3FourierComplexL2 :=
  h3ComplexifyFourierL2
    (h3ToFourierRealL2 f)

/-- The project's scalar Fourier transform is exactly the `L²` Fourier
transform of the preceding Euclidean complex class. -/
theorem h3ScalarFourierL2_eq_fourier_physicalScalarL2EuclideanComplex
    (f : H3ScalarL2) :
    h3ScalarFourierL2 f
      =
    (𝓕 (h3PhysicalScalarL2EuclideanComplex f) :
      H3FourierComplexL2) := by
  rfl

/-! ## Tempered curl-free predicate -/

/-- The three curl-zero identities at the tempered-distribution level, before
Fourier transformation. -/
def H3PhysicalRealFinVectorL2HilbertTemperedCurlFree
    (V : H3PhysicalRealFinVectorL2Hilbert) : Prop :=
  ∂_{h3FourierAxisDirection (h3AxisOfFin3 1)}
      ((h3PhysicalScalarL2EuclideanComplex (V 0) :
          H3FourierComplexL2) :
        𝓢'(H3FourierPoint3, ℂ))
    =
  ∂_{h3FourierAxisDirection (h3AxisOfFin3 0)}
      ((h3PhysicalScalarL2EuclideanComplex (V 1) :
          H3FourierComplexL2) :
        𝓢'(H3FourierPoint3, ℂ))
  ∧
  ∂_{h3FourierAxisDirection (h3AxisOfFin3 2)}
      ((h3PhysicalScalarL2EuclideanComplex (V 0) :
          H3FourierComplexL2) :
        𝓢'(H3FourierPoint3, ℂ))
    =
  ∂_{h3FourierAxisDirection (h3AxisOfFin3 0)}
      ((h3PhysicalScalarL2EuclideanComplex (V 2) :
          H3FourierComplexL2) :
        𝓢'(H3FourierPoint3, ℂ))
  ∧
  ∂_{h3FourierAxisDirection (h3AxisOfFin3 2)}
      ((h3PhysicalScalarL2EuclideanComplex (V 1) :
          H3FourierComplexL2) :
        𝓢'(H3FourierPoint3, ℂ))
    =
  ∂_{h3FourierAxisDirection (h3AxisOfFin3 1)}
      ((h3PhysicalScalarL2EuclideanComplex (V 2) :
          H3FourierComplexL2) :
        𝓢'(H3FourierPoint3, ℂ))

/-- Exact remaining compact-test-to-Schwartz frontier. -/
def H3PhysicalL2WeakCurlFreeImpliesTemperedCurlFree : Prop :=
  ∀ V : H3PhysicalRealFinVectorL2Hilbert,
    H3PhysicalRealFinVectorL2HilbertWeakCurlFree V →
    H3PhysicalRealFinVectorL2HilbertTemperedCurlFree V

/-! ## Fourier transform of one physical L² distributional derivative -/

/-- Fourier transforming one coordinate derivative of a physical scalar `L²`
class gives multiplication of its canonical Fourier transform by the exact
PrimeTensor derivative symbol, as tempered distributions. -/
theorem h3PhysicalScalarL2_fourier_lineDeriv_eq_symbol_multiplier
    (f : H3ScalarL2)
    (i : Fin 3) :
    𝓕
      (∂_{h3FourierAxisDirection (h3AxisOfFin3 i)}
        ((h3PhysicalScalarL2EuclideanComplex f :
            H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ)))
      =
    TemperedDistribution.smulLeftCLM ℂ
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol i ξ)
      ((h3ScalarFourierL2 f :
          H3FourierComplexL2) :
        𝓢'(H3FourierPoint3, ℂ)) := by
  let F : H3FourierComplexL2 :=
    h3PhysicalScalarL2EuclideanComplex f

  calc
    𝓕
        (∂_{h3FourierAxisDirection (h3AxisOfFin3 i)}
          ((F : H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)))
        =
      (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM ℂ
          (fun ξ : H3FourierPoint3 =>
            (inner ℝ ξ
              (h3FourierAxisDirection
                (h3AxisOfFin3 i)) : ℂ))
          (𝓕
            ((F : H3FourierComplexL2) :
              𝓢'(H3FourierPoint3, ℂ))) := by
          simpa using
            (TemperedDistribution.fourier_lineDerivOp_eq
              ((F : H3FourierComplexL2) :
                𝓢'(H3FourierPoint3, ℂ))
              (h3FourierAxisDirection
                (h3AxisOfFin3 i)))
    _ =
      (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM ℂ
          (fun ξ : H3FourierPoint3 =>
            (inner ℝ ξ
              (h3FourierAxisDirection
                (h3AxisOfFin3 i)) : ℂ))
          ((h3ScalarFourierL2 f :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)) := by
          dsimp only [F]
          rw [
            MeasureTheory.Lp.fourier_toTemperedDistribution_eq
              (h3PhysicalScalarL2EuclideanComplex f)
          ]
          rw [
            h3ScalarFourierL2_eq_fourier_physicalScalarL2EuclideanComplex
              f
          ]
    _ =
      TemperedDistribution.smulLeftCLM ℂ
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol i ξ)
        ((h3ScalarFourierL2 f :
            H3FourierComplexL2) :
          𝓢'(H3FourierPoint3, ℂ)) := by
          have hg :
              (fun ξ : H3FourierPoint3 =>
                (inner ℝ ξ
                  (h3FourierAxisDirection
                    (h3AxisOfFin3 i)) : ℂ)).HasTemperateGrowth := by
            fun_prop

          rw [← smul_apply]
          rw [
            ← TemperedDistribution.smulLeftCLM_smul
              hg
              (2 * Real.pi * Complex.I)
          ]

          have hSymbol :
              ((2 * Real.pi * Complex.I) •
                  (fun ξ : H3FourierPoint3 =>
                    (inner ℝ ξ
                      (h3FourierAxisDirection
                        (h3AxisOfFin3 i)) : ℂ)))
                =
              (fun ξ : H3FourierPoint3 =>
                h3FourierDerivativeSymbol i ξ) := by
            funext ξ
            simpa only [Pi.smul_apply, smul_eq_mul] using
              (h3FourierDerivativeSymbol_eq_inner i ξ).symm

          rw [hSymbol]

/-! ## Equality of two multiplier distributions gives a.e. equality -/

/-- If two continuous temperate-growth multipliers applied to two `L²`
tempered distributions agree, then their locally integrable raw multiplier
representatives agree almost everywhere.

This is the two-sided version of `h3L2_distribution_multiplier_ae`. -/
theorem h3L2_distribution_multipliers_eq_ae
    {m n : H3FourierPoint3 → ℂ}
    (hmContinuous : Continuous m)
    (hmGrowth : m.HasTemperateGrowth)
    (hnContinuous : Continuous n)
    (hnGrowth : n.HasTemperateGrowth)
    (F G : H3FourierComplexL2)
    (hDist :
      TemperedDistribution.smulLeftCLM ℂ m
          ((F : H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ))
        =
      TemperedDistribution.smulLeftCLM ℂ n
          ((G : H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ))) :
    (fun ξ : H3FourierPoint3 =>
      m ξ * F ξ)
      =ᵐ[volume]
    (fun ξ : H3FourierPoint3 =>
      n ξ * G ξ) := by
  have hLeftLocal :
      LocallyIntegrable
        (fun ξ : H3FourierPoint3 =>
          m ξ * F ξ)
        volume :=
    h3Continuous_mul_l2_locallyIntegrable
      hmContinuous F

  have hRightLocal :
      LocallyIntegrable
        (fun ξ : H3FourierPoint3 =>
          n ξ * G ξ)
        volume :=
    h3Continuous_mul_l2_locallyIntegrable
      hnContinuous G

  apply
    ae_eq_of_integral_contDiff_smul_eq
      hLeftLocal hRightLocal

  intro g hgSmooth hgCompact

  have hgComplexCompact :
      HasCompactSupport
        (Complex.ofRealCLM ∘ g) :=
    hgCompact.comp_left rfl

  have hgComplexSmooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (Complex.ofRealCLM ∘ g) := by
    simpa [Function.comp_def] using
      (hgSmooth.continuousLinearMap_comp
        Complex.ofRealCLM)

  let φ : 𝓢(H3FourierPoint3, ℂ) :=
    hgComplexCompact.toSchwartzMap
      hgComplexSmooth

  have hEval :
      (TemperedDistribution.smulLeftCLM ℂ m
          ((F : H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ))) φ
        =
      (TemperedDistribution.smulLeftCLM ℂ n
          ((G : H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ))) φ := by
    exact congrArg
      (fun T : 𝓢'(H3FourierPoint3, ℂ) => T φ)
      hDist

  simpa [
    φ,
    MeasureTheory.Lp.toTemperedDistribution_apply,
    TemperedDistribution.smulLeftCLM_apply_apply,
    SchwartzMap.smulLeftCLM_apply_apply hmGrowth,
    SchwartzMap.smulLeftCLM_apply_apply hnGrowth,
    Function.comp_apply,
    smul_eq_mul,
    mul_assoc,
    mul_left_comm,
    mul_comm
  ] using hEval

/-! ## Tempered curl implies Fourier curl a.e. -/

/-- A physical `L²` vector that is curl-free as a tempered distribution is
Fourier curl-free almost everywhere. -/
theorem h3PhysicalRealFinVectorL2Hilbert_fourierCurlFree_of_temperedCurlFree
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hCurl :
      H3PhysicalRealFinVectorL2HilbertTemperedCurlFree V) :
    H3PhysicalRealFinVectorL2HilbertFourierCurlFree V := by
  have h01Dist :
      TemperedDistribution.smulLeftCLM ℂ
          (fun ξ : H3FourierPoint3 =>
            h3FourierDerivativeSymbol 1 ξ)
          ((h3ScalarFourierL2 (V 0) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ))
        =
      TemperedDistribution.smulLeftCLM ℂ
          (fun ξ : H3FourierPoint3 =>
            h3FourierDerivativeSymbol 0 ξ)
          ((h3ScalarFourierL2 (V 1) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)) := by
    have h :=
      congrArg
        (fun T : 𝓢'(H3FourierPoint3, ℂ) => 𝓕 T)
        hCurl.1

    simpa only [
      h3PhysicalScalarL2_fourier_lineDeriv_eq_symbol_multiplier
    ] using h

  have h02Dist :
      TemperedDistribution.smulLeftCLM ℂ
          (fun ξ : H3FourierPoint3 =>
            h3FourierDerivativeSymbol 2 ξ)
          ((h3ScalarFourierL2 (V 0) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ))
        =
      TemperedDistribution.smulLeftCLM ℂ
          (fun ξ : H3FourierPoint3 =>
            h3FourierDerivativeSymbol 0 ξ)
          ((h3ScalarFourierL2 (V 2) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)) := by
    have h :=
      congrArg
        (fun T : 𝓢'(H3FourierPoint3, ℂ) => 𝓕 T)
        hCurl.2.1

    simpa only [
      h3PhysicalScalarL2_fourier_lineDeriv_eq_symbol_multiplier
    ] using h

  have h12Dist :
      TemperedDistribution.smulLeftCLM ℂ
          (fun ξ : H3FourierPoint3 =>
            h3FourierDerivativeSymbol 2 ξ)
          ((h3ScalarFourierL2 (V 1) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ))
        =
      TemperedDistribution.smulLeftCLM ℂ
          (fun ξ : H3FourierPoint3 =>
            h3FourierDerivativeSymbol 1 ξ)
          ((h3ScalarFourierL2 (V 2) :
              H3FourierComplexL2) :
            𝓢'(H3FourierPoint3, ℂ)) := by
    have h :=
      congrArg
        (fun T : 𝓢'(H3FourierPoint3, ℂ) => 𝓕 T)
        hCurl.2.2

    simpa only [
      h3PhysicalScalarL2_fourier_lineDeriv_eq_symbol_multiplier
    ] using h

  have h01 :=
    h3L2_distribution_multipliers_eq_ae
      (h3FourierDerivativeSymbol_continuous 1)
      (h3FourierDerivativeSymbol_hasTemperateGrowth 1)
      (h3FourierDerivativeSymbol_continuous 0)
      (h3FourierDerivativeSymbol_hasTemperateGrowth 0)
      (h3ScalarFourierL2 (V 0))
      (h3ScalarFourierL2 (V 1))
      h01Dist

  have h02 :=
    h3L2_distribution_multipliers_eq_ae
      (h3FourierDerivativeSymbol_continuous 2)
      (h3FourierDerivativeSymbol_hasTemperateGrowth 2)
      (h3FourierDerivativeSymbol_continuous 0)
      (h3FourierDerivativeSymbol_hasTemperateGrowth 0)
      (h3ScalarFourierL2 (V 0))
      (h3ScalarFourierL2 (V 2))
      h02Dist

  have h12 :=
    h3L2_distribution_multipliers_eq_ae
      (h3FourierDerivativeSymbol_continuous 2)
      (h3FourierDerivativeSymbol_hasTemperateGrowth 2)
      (h3FourierDerivativeSymbol_continuous 1)
      (h3FourierDerivativeSymbol_hasTemperateGrowth 1)
      (h3ScalarFourierL2 (V 1))
      (h3ScalarFourierL2 (V 2))
      h12Dist

  unfold
    H3PhysicalRealFinVectorL2HilbertFourierCurlFree
    H3SpectralFinCurlFree

  filter_upwards [h01, h02, h12] with ξ h01ξ h02ξ h12ξ

  exact
    ⟨
      sub_eq_zero.mpr h01ξ,
      sub_eq_zero.mpr h02ξ,
      sub_eq_zero.mpr h12ξ
    ⟩

/-! ## The remaining weak-to-tempered bridge closes the full Fourier bridge -/

/-- Once compact weak curl identities are promoted to tempered-distribution
curl identities, the weak-to-Fourier bridge from `Fourier.Reduction` follows. -/
theorem H3PhysicalL2WeakCurlFreeImpliesFourierCurlFree_of_temperedBridge
    (hTempered :
      H3PhysicalL2WeakCurlFreeImpliesTemperedCurlFree) :
    H3PhysicalL2WeakCurlFreeImpliesFourierCurlFree := by
  intro V hWeak

  exact
    h3PhysicalRealFinVectorL2Hilbert_fourierCurlFree_of_temperedCurlFree
      (hTempered V hWeak)

/-- Since the spectral uniqueness theorem is already proved, the sole
weak-to-tempered bridge is now sufficient for the parameter-free physical
Leray-density theorem. -/
theorem H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_of_temperedBridge
    (hTempered :
      H3PhysicalL2WeakCurlFreeImpliesTemperedCurlFree) :
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan := by
  exact
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_of_fourierBridge_of_spectralTrivial
      (H3PhysicalL2WeakCurlFreeImpliesFourierCurlFree_of_temperedBridge
        hTempered)
      H3SpectralFinDivergenceFreeCurlFreeTrivial_proved

end

end Euclidean
end Bridge
end PrimeTensor
