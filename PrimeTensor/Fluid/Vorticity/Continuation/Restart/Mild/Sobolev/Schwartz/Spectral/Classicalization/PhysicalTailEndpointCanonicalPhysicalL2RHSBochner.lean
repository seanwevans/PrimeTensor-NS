import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalPhysicalL2RHSContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEndpointCanonicalWeakL2Evolution

/-!
# Classicalization: Bochner integral of the physical endpoint RHS

`PhysicalTailEndpointCanonicalPhysicalL2RHSContinuity` proves that every
coordinate of the actual quotient-safe physical projected RHS is strongly
continuous as an `L²(Point3)`-valued path on the complete closed elapsed
interval `[0,τ]`.

This file spends exactly that continuity.

First we extend each coordinate by zero outside `[0,τ]`.  The extension need
not be globally continuous, and we do not claim that it is.  Its restriction
to `[0,τ]` is exactly the strongly continuous subtype path, so it is
interval-integrable as an `H3ScalarL2`-valued function.  Hence its Bochner
interval integral is a genuine physical `L²(Point3)` state.

Next, for every compactly supported smooth scalar test `φ`, the real Hilbert
functional

    F ↦ ⟪φ, F⟫_{L²}

commutes with that Bochner interval integral by
`ContinuousLinearMap.intervalIntegral_comp_comm`.

Finally we compare the coordinatewise Hilbert pairings with the weak scalar
RHS pairing from `PhysicalTailEndpointCanonicalWeakL2Evolution`.  Therefore,
under the already-isolated temporal local-domination hypothesis, the weak FTC
identity can be rewritten as

    Σᵢ ⟪φᵢ, Uᵢ(τ) - Uᵢ(0)⟫
      =
    Σᵢ ⟪φᵢ, ∫₀^τ Rᵢ(s) ds⟫.

The important separation is now explicit:

* existence and Hilbert duality of the RHS Bochner integral are unconditional
  consequences of strong physical `L²` continuity;
* the old temporal local-domination hypothesis is used only when importing the
  scalar velocity FTC identity.

No pointwise Fourier evaluation, pressure transform, or Banach-valued temporal
derivative is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalPhysicalL2RHSBochner
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalPhysicalL2RHSBochner :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Ambient-real physical `L²` RHS path -/

/-- Zero extension to ambient elapsed time of one physical projected-RHS
coordinate.

Only its restriction to `[0,τ]` will be used analytically. -/
noncomputable def h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
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
    (i : Fin 3)
    (s : ℝ) :
    H3ScalarL2 :=
  if hs : s ∈ Set.Icc (0 : ℝ) tau then
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2OnElapsed
      hNS ht htau hEnd hE hTail hEndpoint i ⟨s, hs⟩
  else
    0

/-- On `[0,τ]`, the ambient-real RHS extension is the actual closed-interval
physical `L²` RHS path. -/
theorem h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real_apply_of_mem
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
    (i : Fin 3)
    {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
        hNS ht htau hEnd hE hTail hEndpoint i s
      =
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2OnElapsed
      hNS ht htau hEnd hE hTail hEndpoint i ⟨s, hs⟩ := by
  simp only [
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real,
    dif_pos hs
  ]

/-- The ambient-real RHS extension is strongly continuous on the only interval
relevant to its Bochner integral. -/
theorem continuousOn_h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
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
    (i : Fin 3) :
    ContinuousOn
      (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
        hNS ht htau hEnd hE hTail hEndpoint i)
      (Set.Icc (0 : ℝ) tau) := by
  rw [continuousOn_iff_continuous_domRestrict]

  have hClosed :=
    continuous_h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2OnElapsed
      hNS ht htau hEnd hE hTail hEndpoint i

  have hEq :
      (Set.Icc (0 : ℝ) tau).domRestrict
        (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
          hNS ht htau hEnd hE hTail hEndpoint i)
        =
      h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2OnElapsed
        hNS ht htau hEnd hE hTail hEndpoint i := by
    funext q
    exact
      h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real_apply_of_mem
        hNS ht htau hEnd hE hTail hEndpoint i q.property

  rw [hEq]
  exact hClosed

/-- Every physical projected-RHS coordinate is genuinely Bochner
interval-integrable in `L²(Point3)`. -/
theorem h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real_intervalIntegrable
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
    (i : Fin 3) :
    IntervalIntegrable
      (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
        hNS ht htau hEnd hE hTail hEndpoint i)
      volume
      (0 : ℝ)
      tau := by
  exact
    (continuousOn_h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
      hNS ht htau hEnd hE hTail hEndpoint i).intervalIntegrable_of_Icc
        htau.le

/-! ## Bochner integral and Hilbert duality -/

/-- Genuine physical `L²(Point3)` Bochner integral of one projected-RHS
coordinate over the whole elapsed interval. -/
noncomputable def h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegral
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
    (i : Fin 3) :
    H3ScalarL2 :=
  ∫ s in (0 : ℝ)..tau,
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
      hNS ht htau hEnd hE hTail hEndpoint i s

/-- Pairing one compact smooth scalar test with the physical RHS path is
interval-integrable. -/
theorem h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real_inner_intervalIntegrable
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
    (φ : H3WeakTestFunction)
    (i : Fin 3) :
    IntervalIntegrable
      (fun s : ℝ =>
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 φ)
          (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
            hNS ht htau hEnd hE hTail hEndpoint i s))
      volume
      (0 : ℝ)
      tau := by
  have hR :=
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real_intervalIntegrable
      hNS ht htau hEnd hE hTail hEndpoint i

  let L : H3ScalarL2 →L[ℝ] ℝ :=
    innerSL ℝ (h3WeakTestFunctionPhysicalL2 φ)

  have hMapped :
      IntervalIntegrable
        (fun s : ℝ =>
          L
            (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
              hNS ht htau hEnd hE hTail hEndpoint i s))
        volume
        (0 : ℝ)
        tau := by
    constructor
    · exact L.integrable_comp hR.1
    · exact L.integrable_comp hR.2

  simpa only [L, innerSL_apply_apply] using hMapped

/-- Hilbert pairing commutes with the genuine physical `L²` Bochner integral
of the projected RHS. -/
theorem inner_h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegral_eq_intervalIntegral
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
    (φ : H3WeakTestFunction)
    (i : Fin 3) :
    inner ℝ
        (h3WeakTestFunctionPhysicalL2 φ)
        (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegral
          hNS ht htau hEnd hE hTail hEndpoint i)
      =
    ∫ s in (0 : ℝ)..tau,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 φ)
        (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
          hNS ht htau hEnd hE hTail hEndpoint i s) := by
  have hR :=
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real_intervalIntegrable
      hNS ht htau hEnd hE hTail hEndpoint i

  let L : H3ScalarL2 →L[ℝ] ℝ :=
    innerSL ℝ (h3WeakTestFunctionPhysicalL2 φ)

  have hComm :
      (∫ s in (0 : ℝ)..tau,
        L
          (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
            hNS ht htau hEnd hE hTail hEndpoint i s))
        =
      L
        (∫ s in (0 : ℝ)..tau,
          h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
            hNS ht htau hEnd hE hTail hEndpoint i s) :=
    L.intervalIntegral_comp_comm hR

  simpa only [
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegral,
    L,
    innerSL_apply_apply
  ] using hComm.symm

/-! ## Identification with the old weak scalar RHS integral -/

/-- Pointwise, the old scalar weak-RHS wrapper is exactly the finite sum of
Hilbert pairings against the ambient-real physical `L²` RHS coordinates. -/
theorem h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal_eq_sum_inner_physicalL2Real
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
    (φ : H3WeakTestVector)
    (s : ℝ) :
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ s
      =
    ∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
          hNS ht htau hEnd hE hTail hEndpoint i s) := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) tau

  · rw [
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal_apply_of_mem
        hNS ht htau hEnd hE hTail hEndpoint φ hs
    ]

    unfold h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingOnElapsed

    apply Finset.sum_congr rfl
    intro i hi

    rw [
      h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real_apply_of_mem
        hNS ht htau hEnd hE hTail hEndpoint i hs
    ]

    rfl

  · unfold
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal
      h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real

    simp [hs]

/-- The old scalar weak RHS interval integral is exactly the finite sum of
Hilbert pairings against the genuine coordinatewise Bochner RHS integrals. -/
theorem intervalIntegral_h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal_eq_sum_inner_bochner
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
    (φ : H3WeakTestVector) :
    (∫ s in (0 : ℝ)..tau,
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ s)
      =
    ∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegral
          hNS ht htau hEnd hE hTail hEndpoint i) := by
  have hPointwise :
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal
          hNS ht htau hEnd hE hTail hEndpoint φ
        =
      (fun s : ℝ =>
        ∑ i : Fin 3,
          inner ℝ
            (h3WeakTestFunctionPhysicalL2 (φ i))
            (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
              hNS ht htau hEnd hE hTail hEndpoint i s)) := by
    funext s
    exact
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal_eq_sum_inner_physicalL2Real
        hNS ht htau hEnd hE hTail hEndpoint φ s

  rw [hPointwise]

  have hEach
      (i : Fin 3) :
      IntervalIntegrable
        (fun s : ℝ =>
          inner ℝ
            (h3WeakTestFunctionPhysicalL2 (φ i))
            (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
              hNS ht htau hEnd hE hTail hEndpoint i s))
        volume
        (0 : ℝ)
        tau :=
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real_inner_intervalIntegrable
      hNS ht htau hEnd hE hTail hEndpoint (φ i) i

  calc
    (∫ s in (0 : ℝ)..tau,
      ∑ i : Fin 3,
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 (φ i))
          (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
            hNS ht htau hEnd hE hTail hEndpoint i s))
        =
      ∑ i : Fin 3,
        ∫ s in (0 : ℝ)..tau,
          inner ℝ
            (h3WeakTestFunctionPhysicalL2 (φ i))
            (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
              hNS ht htau hEnd hE hTail hEndpoint i s) := by
          exact
            intervalIntegral.integral_finsetSum
              (fun i _hi => hEach i)
    _ =
      ∑ i : Fin 3,
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 (φ i))
          (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegral
            hNS ht htau hEnd hE hTail hEndpoint i) := by
          apply Finset.sum_congr rfl
          intro i hi

          exact
            (inner_h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegral_eq_intervalIntegral
              hNS ht htau hEnd hE hTail hEndpoint
              (φ i) i).symm

/-! ## Velocity increment and Bochner weak evolution -/

/-- Coordinatewise physical `L²` velocity increment across the full elapsed
endpoint interval. -/
noncomputable def h3PreterminalTailCanonicalVelocityIncrementPhysicalL2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (i : Fin 3) :
    H3ScalarL2 :=
  h3PreterminalCanonicalL2JetOnElapsed
      hNS ht hEnd hTail
      (h3JetSlot0 i)
      ⟨tau, ⟨htau.le, le_rfl⟩⟩
    -
  h3PreterminalCanonicalL2JetOnElapsed
      hNS ht hEnd hTail
      (h3JetSlot0 i)
      ⟨0, ⟨le_rfl, htau.le⟩⟩

/-- Pairing against the coordinatewise physical velocity increment is exactly
the terminal weak velocity pairing minus the initial weak velocity pairing. -/
theorem sum_inner_h3PreterminalTailCanonicalVelocityIncrementPhysicalL2_eq_velocity_pairing_difference
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector) :
    (∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2
          hNS ht htau hEnd hTail i))
      =
    (∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 i)
          ⟨tau, ⟨htau.le, le_rfl⟩⟩))
      -
    (∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 i)
          ⟨0, ⟨le_rfl, htau.le⟩⟩)) := by
  unfold h3PreterminalTailCanonicalVelocityIncrementPhysicalL2
  simp only [
    inner_sub_right,
    Finset.sum_sub_distrib
  ]

/-- Weak physical `L²` evolution written directly against the genuine Bochner
integral of the strongly continuous projected RHS.

The temporal local-domination hypothesis appears only because the velocity FTC
theorem still requires it; the RHS integral itself is unconditional. -/
theorem h3PreterminalTailCanonicalWeakPhysicalL2VelocityIncrement_eq_BochnerProjectedRHS_of_localDomination
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
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (hDom :
      H3PreterminalTailCanonicalWeakTemporalLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint φ) :
    (∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2
          hNS ht htau hEnd hTail i))
      =
    ∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegral
          hNS ht htau hEnd hE hTail hEndpoint i) := by
  rw [
    sum_inner_h3PreterminalTailCanonicalVelocityIncrementPhysicalL2_eq_velocity_pairing_difference
      hNS ht htau hEnd hTail φ
  ]

  calc
    (∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 i)
          ⟨tau, ⟨htau.le, le_rfl⟩⟩))
      -
    (∑ i : Fin 3,
      inner ℝ
        (h3WeakTestFunctionPhysicalL2 (φ i))
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 i)
          ⟨0, ⟨le_rfl, htau.le⟩⟩))
        =
      ∫ s in (0 : ℝ)..tau,
        h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal
          hNS ht htau hEnd hE hTail hEndpoint φ s :=
      h3PreterminalTailCanonicalWeakPhysicalL2VelocityDifference_eq_intervalIntegral_projectedRHS_of_localDomination
        hNS ht htau hEnd hE hTail hEndpoint
        φ hφ hDom
    _ =
      ∑ i : Fin 3,
        inner ℝ
          (h3WeakTestFunctionPhysicalL2 (φ i))
          (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegral
            hNS ht htau hEnd hE hTail hEndpoint i) :=
      intervalIntegral_h3PreterminalTailCanonicalProjectedRHSPhysicalL2WeakPairingReal_eq_sum_inner_bochner
        hNS ht htau hEnd hE hTail hEndpoint φ

end

end Euclidean
end Bridge
end PrimeTensor
