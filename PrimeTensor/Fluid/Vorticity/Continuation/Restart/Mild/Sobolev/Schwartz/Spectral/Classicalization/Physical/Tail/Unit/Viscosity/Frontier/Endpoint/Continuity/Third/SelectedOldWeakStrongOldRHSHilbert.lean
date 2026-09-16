import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldL2FourierDiffusionSign
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalProjectedRHSFTC

/-!
# Endpoint-independent old projected RHS as a physical L² Hilbert vector

The strong-old-derivative uniqueness frontier is too strong for the endpoint
argument: the obvious Banach-valued old derivative route passes through the
very endpoint continuity we are trying to prove.

The zeroth-order endpoint-independent branch already contains the correct
replacement.  For each closed elapsed slice `q`, every old projected-RHS
coordinate

    Δu_i - (P div (u ⊗ u))_i

is a genuine real physical `H3ScalarL2`, with no endpoint-continuity
hypothesis.  This file bundles the three coordinates into the native physical
Hilbert product and rewrites the existing divergence-free weak temporal
identity and weak FTC in that Hilbert language.

Thus the old branch enters the future weak--strong uniqueness argument only
through

    ⟪Φ, R_old(q)⟫

for compact smooth divergence-free tests `Φ`, rather than through a postulated
strong `L²` time derivative.

No endpoint continuity, selected/old agreement, or old Banach-valued time
derivative is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldRHSHilbert
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The endpoint-independent old projected RHS, bundled in the native
three-component real physical `L²` Hilbert space. -/
noncomputable def h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    H3PhysicalRealFinVectorL2Hilbert :=
  WithLp.toLp 2
    (fun i : Fin 3 =>
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
        hNS ht hEnd hTail q i)

@[simp]
theorem h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed_apply
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q i
      =
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2OnElapsed
      hNS ht hEnd hTail q i := by
  rfl

/-- The existing scalar-summed projected-RHS weak pairing is exactly the native
physical Hilbert pairing with the bundled old RHS vector. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_zeroProjectedRHSPhysicalL2HilbertOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)
      =
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed
      hNS ht hEnd hTail φ q := by
  unfold
    h3WeakTestVectorPhysicalL2Hilbert
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed

  rw [PiLp.inner_apply]

/-- The actual old temporal derivative, tested weakly against a divergence-free
compact smooth vector, is the Hilbert pairing with the endpoint-independent
physical projected RHS vector. -/
theorem h3PreterminalLoggedVelocity_weakTemporalPairing_eq_zeroProjectedRHSPhysicalL2HilbertOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent
                u a (h3AxisOfFin3 i) x)
            (t + (q : ℝ)))
        ∂volume)
      =
    inner ℝ
      (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q) := by
  calc
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent
                u a (h3AxisOfFin3 i) x)
            (t + (q : ℝ)))
        ∂volume)
        =
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed
        hNS ht hEnd hTail φ q :=
      h3PreterminalLoggedVelocity_weakTemporalPairing_eq_zeroProjectedRHSPhysicalL2WeakPairingOnElapsed
        hNS ht hEnd hTail q φ hφ
    _ =
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q) := by
      exact
        (inner_h3WeakTestVectorPhysicalL2Hilbert_zeroProjectedRHSPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail φ q).symm

/-- Ambient-real extension of the endpoint-independent old projected RHS
Hilbert vector.  Only its restriction to the physical elapsed interval is used. -/
noncomputable def h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (r : ℝ) :
    H3PhysicalRealFinVectorL2Hilbert :=
  if hr : r ∈ Set.Icc (0 : ℝ) tau then
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail ⟨r, hr⟩
  else
    0

@[simp]
theorem h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal_apply_of_mem
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hr : r ∈ Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
        hNS ht hEnd hTail r
      =
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertOnElapsed
      hNS ht hEnd hTail ⟨r, hr⟩ := by
  simp only [
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal,
    dite_eq_left hr
  ]

/-- The older scalar ambient-real weak-pairing extension is exactly pairing
against the new Hilbert-valued ambient-real RHS extension. -/
theorem h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_eq_inner_hilbertReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (r : ℝ) :
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal
        hNS ht hEnd hTail φ r
      =
    inner ℝ
      (h3WeakTestVectorPhysicalL2Hilbert φ)
      (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
        hNS ht hEnd hTail r) := by
  by_cases hr : r ∈ Set.Icc (0 : ℝ) tau

  · rw [
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_apply_of_mem
        hNS ht hEnd hTail φ hr,
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal_apply_of_mem
        hNS ht hEnd hTail hr
    ]

    exact
      (inner_h3WeakTestVectorPhysicalL2Hilbert_zeroProjectedRHSPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail φ ⟨r, hr⟩).symm

  · simp [
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal,
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal,
      hr
    ]

/-- Endpoint-independent old weak FTC written directly as a Hilbert pairing
against the bounded physical projected-RHS vector.

This is the noncircular old evolution interface needed by the weak--strong
uniqueness route. -/
theorem h3PreterminalLoggedVelocity_weakPairingDifference_eq_projectedRHSHilbert_intervalIntegral_of_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (hProd :
      H3PreterminalLoggedVelocityTemporalProductIntegrableTo
        hNS t q φ) :
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (loggedVelocityComponent
              u (t + q) (h3AxisOfFin3 i) x
            -
          loggedVelocityComponent
              u t (h3AxisOfFin3 i) x)
        ∂volume)
      =
    ∫ r in (0 : ℝ)..q,
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
          hNS ht hEnd hTail r) := by
  have hFTC :=
    h3PreterminalLoggedVelocity_weakPairingDifference_eq_projectedRHS_intervalIntegral_of_productIntegrable
      hNS ht hEnd hTail φ hφ hq hProd

  simpa only [
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_eq_inner_hilbertReal
  ] using hFTC

end

end Euclidean
end Bridge
end PrimeTensor
