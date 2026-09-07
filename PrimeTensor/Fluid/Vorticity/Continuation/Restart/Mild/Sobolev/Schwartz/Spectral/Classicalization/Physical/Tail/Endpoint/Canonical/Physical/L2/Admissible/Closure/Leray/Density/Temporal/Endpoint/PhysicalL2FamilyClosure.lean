import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.PhysicalL2FamilyOrthogonality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Reduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.RHS.Bochner.Leray.Fixed

/-!
# Physical L² temporal admissibility: close the intermediate evolution family

The intermediate weak evolution defect

    D_q = (U(q) - U(0)) - ∫₀^q R(s) ds

is already known to be orthogonal to every currently admissible compact smooth
solenoidal test.

This file proves that both terms of `D_q` lie in the exact physical
Leray-fixed subspace, for every `q ∈ [0,tau]`.

For the velocity increment this is immediate: every physical old-solution slice
is Leray-fixed, and the fixed states form a submodule.

For the shortened RHS Bochner state we repeat the quotient-safe Fourier
commutation already used at terminal time `tau`, but over `[0,q]`:

* the ambient Fourier RHS is interval-integrable on every shortened interval;
* finite Leray commutes with that Bochner integral;
* scalar Plancherel commutes with each shortened physical coordinate integral;
* the resulting physical raw Fourier vector is exactly the shortened Fourier
  Bochner integral.

Hence the intermediate defect is Leray-fixed.

Under the repository's sole remaining temporal frontier

    H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyLocallyDominated,

the admissible weak-test closed span equals the full divergence-free weak-test
closed span, which is already identified with the physical Leray-fixed
submodule.  Therefore `D_q` lies both in that closed span and in the orthogonal
complement of its algebraic generators, so `D_q = 0`.

This gives the genuine physical `L²` evolution identity for every
`q ∈ [0,tau]`, conditional only on the same explicit temporal-domination
frontier as the terminal-time theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointPhysicalL2FamilyClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2TemporalEndpointPhysicalL2FamilyClosure :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Intermediate velocity increment is Leray-fixed -/

/-- The physical velocity increment from zero to any intermediate target lies
in the exact closed physical Leray-fixed submodule. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_mem_lerayFixedSubmodule
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail q
      ∈
    h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
  unfold h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo

  apply
    h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule.sub_mem

  · rw [mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff]
    exact
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed_lerayFixed
        hNS ht hEnd hTail q

  · rw [mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff]
    exact
      h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed_lerayFixed
        hNS ht hEnd hTail
        ⟨0, ⟨le_rfl, htau.le⟩⟩

/-! ## Shortened Fourier RHS Bochner integral -/

/-- The ambient exact Fourier RHS remains interval-integrable on every
shortened interval `[0,q]`. -/
theorem h3PreterminalTailCanonicalProjectedRHSFourierL2Real_intervalIntegrable_to
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau) :
    IntervalIntegrable
      (h3PreterminalTailCanonicalProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint)
      volume
      (0 : ℝ)
      (q : ℝ) := by
  have hContinuousTau :=
    continuousOn_h3PreterminalTailCanonicalProjectedRHSFourierL2Real
      hNS ht htau hEnd hE hTail hEndpoint

  have hSub :
      Set.Icc (0 : ℝ) (q : ℝ)
        ⊆
      Set.Icc (0 : ℝ) tau := by
    intro s hs
    exact ⟨hs.1, hs.2.trans q.property.2⟩

  exact
    (hContinuousTau.mono hSub).intervalIntegrable_of_Icc
      q.property.1

/-- Shortened Fourier-vector Bochner integral of the projected RHS. -/
noncomputable def h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegralTo
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau) :
    H3SpectralFinVectorState :=
  ∫ s in (0 : ℝ)..(q : ℝ),
    h3PreterminalTailCanonicalProjectedRHSFourierL2Real
      hNS ht htau hEnd hE hTail hEndpoint s

/-- The shortened Fourier-vector Bochner integral is Leray-fixed. -/
theorem h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegralTo_lerayFixed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau) :
    h3SpectralFinLerayApply
        (h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegralTo
          hNS ht htau hEnd hE hTail hEndpoint q)
      =
    h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegralTo
      hNS ht htau hEnd hE hTail hEndpoint q := by
  have hInt :=
    h3PreterminalTailCanonicalProjectedRHSFourierL2Real_intervalIntegrable_to
      hNS ht htau hEnd hE hTail hEndpoint q

  unfold h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegralTo

  have hComm :
      h3SpectralFinLerayContinuousLinearMap
          (∫ s in (0 : ℝ)..(q : ℝ),
            h3PreterminalTailCanonicalProjectedRHSFourierL2Real
              hNS ht htau hEnd hE hTail hEndpoint s)
        =
      ∫ s in (0 : ℝ)..(q : ℝ),
        h3SpectralFinLerayContinuousLinearMap
          (h3PreterminalTailCanonicalProjectedRHSFourierL2Real
            hNS ht htau hEnd hE hTail hEndpoint s) := by
    symm
    exact
      h3SpectralFinLerayContinuousLinearMap.intervalIntegral_comp_comm
        hInt

  change
    h3SpectralFinLerayContinuousLinearMap
        (∫ s in (0 : ℝ)..(q : ℝ),
          h3PreterminalTailCanonicalProjectedRHSFourierL2Real
            hNS ht htau hEnd hE hTail hEndpoint s)
      =
    ∫ s in (0 : ℝ)..(q : ℝ),
      h3PreterminalTailCanonicalProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint s

  rw [hComm]

  apply intervalIntegral.integral_congr
  intro s hs

  simpa only [h3SpectralFinLerayContinuousLinearMap_apply] using
    h3PreterminalTailCanonicalProjectedRHSFourierL2Real_lerayFixed
      hNS ht htau hEnd hE hTail hEndpoint s

/-- Scalar Plancherel commutes with one shortened physical RHS coordinate
Bochner integral. -/
theorem h3ScalarFourierL2_projectedRHSPhysicalL2BochnerIntegralTo_eq_intervalIntegral
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3ScalarFourierL2
        (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralTo
          hNS ht htau hEnd hE hTail hEndpoint q i)
      =
    ∫ s in (0 : ℝ)..(q : ℝ),
      h3ScalarFourierL2
        (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
          hNS ht htau hEnd hE hTail hEndpoint i s) := by
  have hInt :=
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real_intervalIntegrable_to
      hNS ht htau hEnd hE hTail hEndpoint q i

  have hComm :
      h3ScalarFourierL2RealContinuousLinearMap
          (∫ s in (0 : ℝ)..(q : ℝ),
            h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
              hNS ht htau hEnd hE hTail hEndpoint i s)
        =
      ∫ s in (0 : ℝ)..(q : ℝ),
        h3ScalarFourierL2RealContinuousLinearMap
          (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
            hNS ht htau hEnd hE hTail hEndpoint i s) := by
    symm
    exact
      h3ScalarFourierL2RealContinuousLinearMap.intervalIntegral_comp_comm
        hInt

  simpa only [
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralTo,
    h3ScalarFourierL2RealContinuousLinearMap_apply
  ] using hComm

/-- The shortened Fourier-vector integral is coordinatewise the integral of the
ambient Fourier RHS coordinates. -/
theorem h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegralTo_apply
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegralTo
        hNS ht htau hEnd hE hTail hEndpoint q i
      =
    ∫ s in (0 : ℝ)..(q : ℝ),
      h3PreterminalTailCanonicalProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint s i := by
  have hInt :=
    h3PreterminalTailCanonicalProjectedRHSFourierL2Real_intervalIntegrable_to
      hNS ht htau hEnd hE hTail hEndpoint q

  have hComm :
      h3EndpointSpectralFinCoordinateCLM i
          (∫ s in (0 : ℝ)..(q : ℝ),
            h3PreterminalTailCanonicalProjectedRHSFourierL2Real
              hNS ht htau hEnd hE hTail hEndpoint s)
        =
      ∫ s in (0 : ℝ)..(q : ℝ),
        h3EndpointSpectralFinCoordinateCLM i
          (h3PreterminalTailCanonicalProjectedRHSFourierL2Real
            hNS ht htau hEnd hE hTail hEndpoint s) := by
    symm
    exact
      (h3EndpointSpectralFinCoordinateCLM i).intervalIntegral_comp_comm
        hInt

  simpa only [
    h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegralTo,
    h3EndpointSpectralFinCoordinateCLM_apply
  ] using hComm

/-- The raw Fourier vector of the shortened physical Hilbert RHS state is
exactly the shortened Fourier-vector Bochner integral. -/
theorem h3PhysicalRealFinVectorL2HilbertRawFourier_bochnerProjectedRHSTo_eq
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PhysicalRealFinVectorL2HilbertRawFourier
        (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo
          hNS ht htau hEnd hE hTail hEndpoint q)
      =
    h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegralTo
      hNS ht htau hEnd hE hTail hEndpoint q := by
  funext i

  unfold
    h3PhysicalRealFinVectorL2HilbertRawFourier
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo

  simp only [PiLp.toLp_apply]

  rw [
    h3ScalarFourierL2_projectedRHSPhysicalL2BochnerIntegralTo_eq_intervalIntegral
      hNS ht htau hEnd hE hTail hEndpoint q i,
    h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegralTo_apply
      hNS ht htau hEnd hE hTail hEndpoint q i
  ]

  apply intervalIntegral.integral_congr
  intro s hs

  exact
    h3ScalarFourierL2_projectedRHSPhysicalL2Real_eq_fourierL2Real
      hNS ht htau hEnd hE hTail hEndpoint i s

/-- The shortened physical RHS Hilbert state lies in the exact closed physical
Leray-fixed submodule. -/
theorem h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo_mem_lerayFixedSubmodule
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo
        hNS ht htau hEnd hE hTail hEndpoint q
      ∈
    h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
  rw [mem_h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule_iff]

  unfold H3PhysicalRealFinVectorL2HilbertLerayFixed

  rw [
    h3PhysicalRealFinVectorL2HilbertRawFourier_bochnerProjectedRHSTo_eq
      hNS ht htau hEnd hE hTail hEndpoint q
  ]

  exact
    h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegralTo_lerayFixed
      hNS ht htau hEnd hE hTail hEndpoint q

/-- The entire intermediate evolution defect belongs to the physical
Leray-fixed submodule. -/
theorem h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_mem_lerayFixedSubmodule
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
        hNS ht htau hEnd hE hTail hEndpoint q
      ∈
    h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
  unfold h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo

  exact
    h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule.sub_mem
      (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_mem_lerayFixedSubmodule
        hNS ht htau hEnd hTail q)
      (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo_mem_lerayFixedSubmodule
        hNS ht htau hEnd hE hTail hEndpoint q)

/-! ## Intermediate defect closure -/

/-- Generator orthogonality extends to the algebraic admissible weak-test span
for the intermediate defect. -/
theorem h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_mem_admissibleWeakTestSpan_orthogonal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
        hNS ht htau hEnd hE hTail hEndpoint q
      ∈
    (h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Span
      hNS ht htau hEnd hE hTail hEndpoint)ᗮ := by
  let D : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
      hNS ht htau hEnd hE hTail hEndpoint q

  let S : Set H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Set
      hNS ht htau hEnd hE hTail hEndpoint

  let K : Submodule ℝ H3PhysicalRealFinVectorL2Hilbert :=
    Submodule.span ℝ S

  let L : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] ℝ :=
    innerSL ℝ D

  have hGeneratorKer : S ⊆ L.ker := by
    intro Φ hΦ

    have hPair : inner ℝ Φ D = 0 := by
      dsimp only [D, S]
      exact
        h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Set_subset_evolutionDefectTo_zeroPairing
          hNS ht htau hEnd hE hTail hEndpoint q hΦ

    change L Φ = 0
    dsimp only [L]

    simpa only [innerSL_apply_apply, real_inner_comm] using hPair

  have hSpanKer : K ≤ L.ker := by
    dsimp only [K]
    exact Submodule.span_le.mpr hGeneratorKer

  change D ∈ Kᗮ
  rw [Submodule.mem_orthogonal']

  intro Φ hΦ

  have hKer : Φ ∈ L.ker := hSpanKer hΦ

  change L Φ = 0 at hKer
  dsimp only [L] at hKer

  simpa only [innerSL_apply_apply] using hKer

/-- Under generatorwise temporal domination, the intermediate defect belongs
to the admissible weak-test closed span. -/
theorem h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_mem_admissibleWeakTestClosedSpan_of_all_temporallyLocallyDominated
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hAll :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
        hNS ht htau hEnd hE hTail hEndpoint q
      ∈
    h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2ClosedSpan
      hNS ht htau hEnd hE hTail hEndpoint := by
  have hFixed :
      h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
          hNS ht htau hEnd hE hTail hEndpoint q
        ∈
      h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule :=
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_mem_lerayFixedSubmodule
      hNS ht htau hEnd hE hTail hEndpoint q

  rw [
    h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2ClosedSpan_eq_divergenceFreeWeakTestPhysicalL2ClosedSpan_of_all_temporallyLocallyDominated
      hNS ht htau hEnd hE hTail hEndpoint hAll,
    h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule
  ]

  exact hFixed

/-- Under the sole generatorwise temporal-domination frontier, the
intermediate physical evolution defect vanishes. -/
theorem h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_eq_zero_of_all_temporallyLocallyDominated
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hAll :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
        hNS ht htau hEnd hE hTail hEndpoint q
      =
    0 := by
  let D : H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
      hNS ht htau hEnd hE hTail hEndpoint q

  let K : Submodule ℝ H3PhysicalRealFinVectorL2Hilbert :=
    h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Span
      hNS ht htau hEnd hE hTail hEndpoint

  have hOrth : D ∈ Kᗮ := by
    dsimp only [D, K]
    exact
      h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_mem_admissibleWeakTestSpan_orthogonal
        hNS ht htau hEnd hE hTail hEndpoint q

  have hMem :
      D ∈
        h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2ClosedSpan
          hNS ht htau hEnd hE hTail hEndpoint := by
    dsimp only [D]
    exact
      h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_mem_admissibleWeakTestClosedSpan_of_all_temporallyLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint hAll q

  have hDouble : D ∈ Kᗮᗮ := by
    have hClosedEq :
        h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2ClosedSpan
            hNS ht htau hEnd hE hTail hEndpoint
          =
        Kᗮᗮ := by
      dsimp only [K]
      exact
        h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2ClosedSpan_eq_orthogonal_orthogonal
          hNS ht htau hEnd hE hTail hEndpoint

    rw [← hClosedEq]
    exact hMem

  have hBoth : D ∈ Kᗮ ⊓ Kᗮᗮ :=
    ⟨hOrth, hDouble⟩

  have hBot :
      D ∈ (⊥ : Submodule ℝ H3PhysicalRealFinVectorL2Hilbert) := by
    rw [← Submodule.inf_orthogonal_eq_bot Kᗮ]
    exact hBoth

  simpa using hBot

/-- Genuine physical `L²` vector evolution on every intermediate elapsed
target, conditional only on generatorwise temporal local domination. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_eq_BochnerProjectedRHSTo_of_all_temporallyLocallyDominated
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hAll :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail q
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo
      hNS ht htau hEnd hE hTail hEndpoint q := by
  have hZero :=
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_eq_zero_of_all_temporallyLocallyDominated
      hNS ht htau hEnd hE hTail hEndpoint hAll q

  unfold h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo at hZero

  exact sub_eq_zero.mp hZero

end

end Euclidean
end Bridge
end PrimeTensor
