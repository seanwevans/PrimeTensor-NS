import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.RHS.Leray.Fixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Defect.Orthogonality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.Encoded.Incompressibility.Duhamel

/-!
# Classicalization: the Bochner-integrated physical endpoint RHS is Leray-fixed

The pointwise result is already closed:

    R(q) is a genuine real physical `L²` vector,
    and its canonical raw Fourier vector is fixed by finite Leray

for every `q ∈ [0,τ]`.

This file transports that fixed-point statement through the genuine Bochner
interval integral already constructed by the weak-evolution branch.

The functional-analytic route is entirely quotient-safe.

1. Package the scalar physical Plancherel bridge as a real continuous linear map.
2. Zero-extend the exact Fourier RHS from `[0,τ]` to ambient elapsed time.
3. Use the existing bounded finite Leray continuous linear map to commute Leray
   through the Fourier-side Bochner interval integral.
4. Commute scalar Plancherel through each physical coordinate integral.
5. Identify the resulting three-coordinate raw Fourier vector with the
   Fourier-side Bochner integral.

Therefore the actual Hilbert-product state

    ∫₀^τ R(s) ds

is Leray-fixed.

No density theorem, pointwise frequency evaluation, pressure transform, or
Banach-valued temporal derivative is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalPhysicalL2RHSBochnerLerayFixed
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalPhysicalL2RHSBochnerLerayFixed :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## The scalar physical Plancherel bridge as a bounded real-linear map -/

/-- Transport from physical `Point3` `L²` to the Euclidean Fourier carrier is
real homogeneous. -/
theorem h3ToFourierRealL2_smul_real
    (c : ℝ)
    (f : H3ScalarL2) :
    h3ToFourierRealL2 (c • f)
      =
    c • h3ToFourierRealL2 f := by
  let e :
      MeasurePreserving
        (WithLp.ofLp : H3FourierPoint3 → Point3)
        (volume : Measure H3FourierPoint3)
        (volume : Measure Point3) :=
    PiLp.volume_preserving_ofLp
      (PrimeTensor.Axis Depth.three)

  let C : H3ScalarL2 →+ H3FourierRealL2 :=
    MeasureTheory.Lp.compMeasurePreserving
      (WithLp.ofLp : H3FourierPoint3 → Point3)
      e

  change C (c • f) = c • C f

  have hInput :
      ((c • f : H3ScalarL2) : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 => c • (f : Point3 → ℝ) x) :=
    MeasureTheory.Lp.coeFn_smul c f

  have hInputComp :
      (fun ξ : H3FourierPoint3 =>
        ((c • f : H3ScalarL2) : Point3 → ℝ)
          (WithLp.ofLp ξ))
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        c • (f : Point3 → ℝ) (WithLp.ofLp ξ)) := by
    exact e.quasiMeasurePreserving.ae_eq_comp hInput

  have hLeft :=
    MeasureTheory.Lp.coeFn_compMeasurePreserving
      (c • f)
      e

  have hBase :=
    MeasureTheory.Lp.coeFn_compMeasurePreserving
      f
      e

  have hSmul :=
    MeasureTheory.Lp.coeFn_smul
      c
      (C f)

  apply MeasureTheory.Lp.ext

  filter_upwards [
    hLeft,
    hInputComp,
    hBase,
    hSmul
  ] with ξ hLeftξ hInputξ hBaseξ hSmulξ

  calc
    ((C (c • f) : H3FourierRealL2) :
        H3FourierPoint3 → ℝ) ξ
        =
      ((c • f : H3ScalarL2) :
        Point3 → ℝ) (WithLp.ofLp ξ) := by
          simpa only [C, Function.comp_apply] using hLeftξ
    _ =
      c • (f : Point3 → ℝ) (WithLp.ofLp ξ) :=
        hInputξ
    _ =
      c •
        ((C f : H3FourierRealL2) :
          H3FourierPoint3 → ℝ) ξ := by
            rw [hBaseξ]
            rfl
    _ =
      ((c • C f : H3FourierRealL2) :
        H3FourierPoint3 → ℝ) ξ := by
          simpa only [Pi.smul_apply] using hSmulξ.symm

/-- Complexification of Fourier-carrier `L²` is real homogeneous. -/
theorem h3ComplexifyFourierL2_smul_real
    (c : ℝ)
    (f : H3FourierRealL2) :
    h3ComplexifyFourierL2 (c • f)
      =
    c • h3ComplexifyFourierL2 f := by
  simpa only [h3ComplexifyFourierL2L_apply] using
    h3ComplexifyFourierL2L.map_smul c f

/-- The full scalar Plancherel bridge is real homogeneous. -/
theorem h3ScalarFourierL2_smul_real
    (c : ℝ)
    (f : H3ScalarL2) :
    h3ScalarFourierL2 (c • f)
      =
    c • h3ScalarFourierL2 f := by
  unfold h3ScalarFourierL2

  rw [
    h3ToFourierRealL2_smul_real,
    h3ComplexifyFourierL2_smul_real
  ]

  change
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
        ((c : ℂ) •
          h3ComplexifyFourierL2 (h3ToFourierRealL2 f))
      =
    (c : ℂ) •
      (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ)
        (h3ComplexifyFourierL2 (h3ToFourierRealL2 f))

  exact
    (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).map_smul
        (c : ℂ)
        (h3ComplexifyFourierL2 (h3ToFourierRealL2 f))

/-- Scalar physical Plancherel as a real linear map. -/
noncomputable def h3ScalarFourierL2RealLinearMap :
    H3ScalarL2 →ₗ[ℝ] H3FourierComplexL2 where
  toFun := h3ScalarFourierL2
  map_add' := h3ScalarFourierL2_add
  map_smul' := h3ScalarFourierL2_smul_real

@[simp]
theorem h3ScalarFourierL2RealLinearMap_apply
    (f : H3ScalarL2) :
    h3ScalarFourierL2RealLinearMap f
      =
    h3ScalarFourierL2 f := rfl

/-- Scalar physical Plancherel is a contractive real continuous linear map
(in fact an isometry). -/
noncomputable def h3ScalarFourierL2RealContinuousLinearMap :
    H3ScalarL2 →L[ℝ] H3FourierComplexL2 :=
  h3ScalarFourierL2RealLinearMap.mkContinuous
    1
    (fun f => by
      rw [
        h3ScalarFourierL2RealLinearMap_apply,
        norm_h3ScalarFourierL2,
        one_mul
      ])

@[simp]
theorem h3ScalarFourierL2RealContinuousLinearMap_apply
    (f : H3ScalarL2) :
    h3ScalarFourierL2RealContinuousLinearMap f
      =
    h3ScalarFourierL2 f := rfl

/-! ## Ambient Fourier RHS path -/

/-- Zero extension to ambient elapsed time of the exact quotient-safe Fourier
`L²` projected RHS vector. -/
noncomputable def h3PreterminalTailCanonicalProjectedRHSFourierL2Real
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
    (s : ℝ) :
    H3SpectralFinVectorState :=
  if hs : s ∈ Set.Icc (0 : ℝ) tau then
    h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed
      hNS ht htau hEnd hE hTail hEndpoint ⟨s, hs⟩
  else
    0

/-- The closed-interval Fourier RHS vector path is strongly continuous. -/
theorem continuous_h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed
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
        hNS ht hEnd hTail) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed
          hNS ht htau hEnd hE hTail hEndpoint q) := by
  apply continuous_pi
  intro i

  unfold h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed

  exact
    (continuous_h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed
      hNS ht htau hEnd hE hTail hEndpoint i).sub
      (continuous_h3PreterminalTailCanonicalLerayForcingFourierL2OnElapsed
        hNS ht htau hEnd hE hTail hEndpoint i)

/-- The ambient Fourier RHS extension is continuous on the interval relevant
to integration. -/
theorem continuousOn_h3PreterminalTailCanonicalProjectedRHSFourierL2Real
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
        hNS ht hEnd hTail) :
    ContinuousOn
      (h3PreterminalTailCanonicalProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint)
      (Set.Icc (0 : ℝ) tau) := by
  rw [continuousOn_iff_continuous_domRestrict]

  have hClosed :=
    continuous_h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed
      hNS ht htau hEnd hE hTail hEndpoint

  have hEq :
      (Set.Icc (0 : ℝ) tau).domRestrict
          (h3PreterminalTailCanonicalProjectedRHSFourierL2Real
            hNS ht htau hEnd hE hTail hEndpoint)
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed
          hNS ht htau hEnd hE hTail hEndpoint q) := by
    funext q
    change
      h3PreterminalTailCanonicalProjectedRHSFourierL2Real
          hNS ht htau hEnd hE hTail hEndpoint (q : ℝ)
        =
      h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed
        hNS ht htau hEnd hE hTail hEndpoint q
    unfold h3PreterminalTailCanonicalProjectedRHSFourierL2Real
    rw [dif_pos q.property]

  rw [hEq]
  exact hClosed

/-- The ambient Fourier RHS path is genuinely Bochner interval-integrable. -/
theorem h3PreterminalTailCanonicalProjectedRHSFourierL2Real_intervalIntegrable
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
        hNS ht hEnd hTail) :
    IntervalIntegrable
      (h3PreterminalTailCanonicalProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint)
      volume
      (0 : ℝ)
      tau := by
  exact
    (continuousOn_h3PreterminalTailCanonicalProjectedRHSFourierL2Real
      hNS ht htau hEnd hE hTail hEndpoint).intervalIntegrable_of_Icc
        htau.le

/-- The zero-extended Fourier RHS is Leray-fixed at every ambient elapsed time.
Outside `[0,τ]` this is simply linearity at zero. -/
theorem h3PreterminalTailCanonicalProjectedRHSFourierL2Real_lerayFixed
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
    (s : ℝ) :
    h3SpectralFinLerayApply
        (h3PreterminalTailCanonicalProjectedRHSFourierL2Real
          hNS ht htau hEnd hE hTail hEndpoint s)
      =
    h3PreterminalTailCanonicalProjectedRHSFourierL2Real
      hNS ht htau hEnd hE hTail hEndpoint s := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) tau

  · unfold h3PreterminalTailCanonicalProjectedRHSFourierL2Real
    rw [dif_pos hs]

    exact
      h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed_lerayFixed
        hNS ht htau hEnd hE hTail hEndpoint ⟨s, hs⟩

  · unfold h3PreterminalTailCanonicalProjectedRHSFourierL2Real
    rw [dif_neg hs]

    have hZero :
        h3SpectralFinLerayLinearMap
            (0 : H3SpectralFinVectorState)
          =
        0 :=
      h3SpectralFinLerayLinearMap.map_zero

    simpa only [h3SpectralFinLerayLinearMap_apply] using hZero

/-! ## Fourier-side Bochner integral -/

/-- Genuine Fourier-vector Bochner integral of the projected RHS. -/
noncomputable def h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegral
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
        hNS ht hEnd hTail) :
    H3SpectralFinVectorState :=
  ∫ s in (0 : ℝ)..tau,
    h3PreterminalTailCanonicalProjectedRHSFourierL2Real
      hNS ht htau hEnd hE hTail hEndpoint s

/-- The Fourier-vector Bochner integral is Leray-fixed. -/
theorem h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegral_lerayFixed
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
        hNS ht hEnd hTail) :
    h3SpectralFinLerayApply
        (h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegral
          hNS ht htau hEnd hE hTail hEndpoint)
      =
    h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegral
      hNS ht htau hEnd hE hTail hEndpoint := by
  have hInt :=
    h3PreterminalTailCanonicalProjectedRHSFourierL2Real_intervalIntegrable
      hNS ht htau hEnd hE hTail hEndpoint

  unfold h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegral

  rw [intervalIntegral.integral_of_le htau.le]

  change
    h3SpectralFinLerayContinuousLinearMap
        (∫ s in Set.Ioc (0 : ℝ) tau,
          h3PreterminalTailCanonicalProjectedRHSFourierL2Real
            hNS ht htau hEnd hE hTail hEndpoint s)
      =
    ∫ s in Set.Ioc (0 : ℝ) tau,
      h3PreterminalTailCanonicalProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint s

  calc
    h3SpectralFinLerayContinuousLinearMap
        (∫ s in Set.Ioc (0 : ℝ) tau,
          h3PreterminalTailCanonicalProjectedRHSFourierL2Real
            hNS ht htau hEnd hE hTail hEndpoint s)
        =
      ∫ s in Set.Ioc (0 : ℝ) tau,
        h3SpectralFinLerayContinuousLinearMap
          (h3PreterminalTailCanonicalProjectedRHSFourierL2Real
            hNS ht htau hEnd hE hTail hEndpoint s) := by
          symm
          exact
            ContinuousLinearMap.integral_comp_comm
              h3SpectralFinLerayContinuousLinearMap
              hInt.1
    _ =
      ∫ s in Set.Ioc (0 : ℝ) tau,
        h3PreterminalTailCanonicalProjectedRHSFourierL2Real
          hNS ht htau hEnd hE hTail hEndpoint s := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with s
            change
              h3SpectralFinLerayApply
                  (h3PreterminalTailCanonicalProjectedRHSFourierL2Real
                    hNS ht htau hEnd hE hTail hEndpoint s)
                =
              h3PreterminalTailCanonicalProjectedRHSFourierL2Real
                hNS ht htau hEnd hE hTail hEndpoint s
            exact
              h3PreterminalTailCanonicalProjectedRHSFourierL2Real_lerayFixed
                hNS ht htau hEnd hE hTail hEndpoint s

/-! ## Coordinate identifications -/

/-- Scalar Plancherel commutes with the genuine physical projected-RHS Bochner
integral. -/
theorem h3ScalarFourierL2_projectedRHSPhysicalL2BochnerIntegral_eq_intervalIntegral
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
    h3ScalarFourierL2
        (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegral
          hNS ht htau hEnd hE hTail hEndpoint i)
      =
    ∫ s in (0 : ℝ)..tau,
      h3ScalarFourierL2
        (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
          hNS ht htau hEnd hE hTail hEndpoint i s) := by
  have hInt :=
    h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real_intervalIntegrable
      hNS ht htau hEnd hE hTail hEndpoint i

  have hComm :
      h3ScalarFourierL2RealContinuousLinearMap
          (∫ s in (0 : ℝ)..tau,
            h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
              hNS ht htau hEnd hE hTail hEndpoint i s)
        =
      ∫ s in (0 : ℝ)..tau,
        h3ScalarFourierL2RealContinuousLinearMap
          (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
            hNS ht htau hEnd hE hTail hEndpoint i s) := by
    symm
    exact
      h3ScalarFourierL2RealContinuousLinearMap.intervalIntegral_comp_comm
        hInt

  simpa only [
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegral,
    h3ScalarFourierL2RealContinuousLinearMap_apply
  ] using hComm

/-- At every ambient elapsed time, scalar Plancherel of one actual physical RHS
coordinate is the matching coordinate of the ambient exact Fourier RHS. -/
theorem h3ScalarFourierL2_projectedRHSPhysicalL2Real_eq_fourierL2Real
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
    h3ScalarFourierL2
        (h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
          hNS ht htau hEnd hE hTail hEndpoint i s)
      =
    h3PreterminalTailCanonicalProjectedRHSFourierL2Real
      hNS ht htau hEnd hE hTail hEndpoint s i := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) tau

  · rw [
      h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real_apply_of_mem
        hNS ht htau hEnd hE hTail hEndpoint i hs
    ]

    unfold h3PreterminalTailCanonicalProjectedRHSFourierL2Real
    rw [dif_pos hs]

    have hVec :=
      congrFun
        (h3PhysicalRealFinVectorL2HilbertRawFourier_projectedRHSPhysicalL2OnElapsed_eq
          hNS ht htau hEnd hE hTail hEndpoint ⟨s, hs⟩)
        i

    unfold
      h3PhysicalRealFinVectorL2HilbertRawFourier
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2HilbertOnElapsed
      at hVec

    simpa only [PiLp.toLp_apply] using hVec

  · unfold
      h3PreterminalTailCanonicalNormalizedRealProjectedRHSPhysicalL2Real
      h3PreterminalTailCanonicalProjectedRHSFourierL2Real

    rw [dif_neg hs, dif_neg hs]
    exact h3ScalarFourierL2_zero

/-- Coordinate projection from the finite Fourier vector state, packaged as a
contractive complex continuous linear map. -/
noncomputable def h3EndpointSpectralFinCoordinateLinearMap
    (i : Fin 3) :
    H3SpectralFinVectorState →ₗ[ℂ] H3SpectralScalarState where
  toFun := fun U => U i
  map_add' := by
    intro U V
    rfl
  map_smul' := by
    intro c U
    rfl

noncomputable def h3EndpointSpectralFinCoordinateCLM
    (i : Fin 3) :
    H3SpectralFinVectorState →L[ℂ] H3SpectralScalarState :=
  (h3EndpointSpectralFinCoordinateLinearMap i).mkContinuous
    1
    (fun U => by
      change ‖U i‖ ≤ 1 * ‖U‖
      simpa using h3SpectralFinVector_coordinate_norm_le U i)

@[simp]
theorem h3EndpointSpectralFinCoordinateCLM_apply
    (i : Fin 3)
    (U : H3SpectralFinVectorState) :
    h3EndpointSpectralFinCoordinateCLM i U = U i := rfl

/-- The Fourier-vector Bochner integral is coordinatewise the Bochner integral
of the Fourier RHS coordinates. -/
theorem h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegral_apply
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
    h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegral
        hNS ht htau hEnd hE hTail hEndpoint i
      =
    ∫ s in (0 : ℝ)..tau,
      h3PreterminalTailCanonicalProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint s i := by
  have hInt :=
    h3PreterminalTailCanonicalProjectedRHSFourierL2Real_intervalIntegrable
      hNS ht htau hEnd hE hTail hEndpoint

  have hComm :
      h3EndpointSpectralFinCoordinateCLM i
          (∫ s in (0 : ℝ)..tau,
            h3PreterminalTailCanonicalProjectedRHSFourierL2Real
              hNS ht htau hEnd hE hTail hEndpoint s)
        =
      ∫ s in (0 : ℝ)..tau,
        h3EndpointSpectralFinCoordinateCLM i
          (h3PreterminalTailCanonicalProjectedRHSFourierL2Real
            hNS ht htau hEnd hE hTail hEndpoint s) := by
    symm
    exact
      (h3EndpointSpectralFinCoordinateCLM i).intervalIntegral_comp_comm
        hInt

  simpa only [
    h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegral,
    h3EndpointSpectralFinCoordinateCLM_apply
  ] using hComm

/-! ## Physical Hilbert Bochner state is Leray-fixed -/

/-- The raw Fourier vector of the actual physical Hilbert-product Bochner RHS
is exactly the Fourier-vector Bochner integral. -/
theorem h3PhysicalRealFinVectorL2HilbertRawFourier_bochnerProjectedRHS_eq
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
        hNS ht hEnd hTail) :
    h3PhysicalRealFinVectorL2HilbertRawFourier
        (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
          hNS ht htau hEnd hE hTail hEndpoint)
      =
    h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegral
      hNS ht htau hEnd hE hTail hEndpoint := by
  funext i

  unfold
    h3PhysicalRealFinVectorL2HilbertRawFourier
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert

  simp only [PiLp.toLp_apply]

  rw [
    h3ScalarFourierL2_projectedRHSPhysicalL2BochnerIntegral_eq_intervalIntegral
      hNS ht htau hEnd hE hTail hEndpoint i,
    h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegral_apply
      hNS ht htau hEnd hE hTail hEndpoint i
  ]

  apply intervalIntegral.integral_congr
  intro s hs

  exact
    h3ScalarFourierL2_projectedRHSPhysicalL2Real_eq_fourierL2Real
      hNS ht htau hEnd hE hTail hEndpoint i s

/-- The genuine Bochner-integrated real physical `L²` projected RHS is
Leray-fixed.  This closes the RHS side of the quotient-safe solenoidal
membership checkpoint. -/
theorem h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert_lerayFixed
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
        hNS ht hEnd hTail) :
    H3PhysicalRealFinVectorL2HilbertLerayFixed
      (h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
        hNS ht htau hEnd hE hTail hEndpoint) := by
  unfold H3PhysicalRealFinVectorL2HilbertLerayFixed

  rw [
    h3PhysicalRealFinVectorL2HilbertRawFourier_bochnerProjectedRHS_eq
      hNS ht htau hEnd hE hTail hEndpoint
  ]

  exact
    h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegral_lerayFixed
      hNS ht htau hEnd hE hTail hEndpoint

end

end Euclidean
end Bridge
end PrimeTensor
