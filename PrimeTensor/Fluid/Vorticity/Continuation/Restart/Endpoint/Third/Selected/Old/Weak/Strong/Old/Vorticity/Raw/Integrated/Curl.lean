import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Old.Vorticity.Raw.Temporal.Pairing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Old.Vorticity.FTC
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Pairing

/-!
# Endpoint-independent integrated old curl identities

The endpoint-era integrated curl frontier carried
`H3PreterminalCanonicalL2EndpointContinuousOnElapsed` in its statement because
its projected-RHS pairing was built from the endpoint-normalized path.

The old projected RHS is now already available endpoint-independently as the
ambient-real Hilbert-valued function

    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal.

The raw old temporal curl identities identify the strict-time compact temporal
pairings with the three vorticity temporal derivatives, while the old weak
momentum identity identifies the same temporal pairings with Hilbert pairing
against the old projected RHS.  The endpoint-independent vorticity FTC then
integrates these identities exactly.

This file packages the resulting three curl01/curl02/curl12 identities in a
frontier whose type itself contains no endpoint-continuity hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldVorticityRawIntegratedCurl
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongOldVorticityRawIntegratedCurl :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Endpoint-independent integrated curl-test frontier, written directly
against the actual old projected-RHS Hilbert vector. -/
def H3PreterminalTailCanonicalCurlWeakVelocityPairingsSatisfyIntegratedZeroProjectedRHSOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ ψ : H3WeakTestFunction,
    ∀ q : Set.Icc (0 : ℝ) tau,
      let q0 : Set.Icc (0 : ℝ) tau :=
        ⟨0, ⟨le_rfl, htau.le⟩⟩
      (
        h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
            hNS ht hEnd hTail (h3WeakTestCurl01 ψ) q
          -
        h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
            hNS ht hEnd hTail (h3WeakTestCurl01 ψ) q0
          =
        ∫ r in (0 : ℝ)..(q : ℝ),
          inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl01 ψ))
            (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
              hNS ht hEnd hTail r)
      )
      ∧
      (
        h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
            hNS ht hEnd hTail (h3WeakTestCurl02 ψ) q
          -
        h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
            hNS ht hEnd hTail (h3WeakTestCurl02 ψ) q0
          =
        ∫ r in (0 : ℝ)..(q : ℝ),
          inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl02 ψ))
            (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
              hNS ht hEnd hTail r)
      )
      ∧
      (
        h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
            hNS ht hEnd hTail (h3WeakTestCurl12 ψ) q
          -
        h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
            hNS ht hEnd hTail (h3WeakTestCurl12 ψ) q0
          =
        ∫ r in (0 : ℝ)..(q : ℝ),
          inner ℝ
            (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl12 ψ))
            (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
              hNS ht hEnd hTail r)
      )

/-- The canonical H³ tail directly closes all three endpoint-independent
integrated old curl-test identities. -/
theorem h3PreterminalTailCanonicalCurlWeakVelocityPairingsSatisfyIntegratedZeroProjectedRHSOnElapsed_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PreterminalTailCanonicalCurlWeakVelocityPairingsSatisfyIntegratedZeroProjectedRHSOnElapsed
      hNS ht htau hEnd hTail := by
  unfold
    H3PreterminalTailCanonicalCurlWeakVelocityPairingsSatisfyIntegratedZeroProjectedRHSOnElapsed

  intro ψ q
  dsimp only

  let q0 : Set.Icc (0 : ℝ) tau :=
    ⟨0, ⟨le_rfl, htau.le⟩⟩

  have hZero :
      h3EndpointElapsedZero q = q0 := by
    apply Subtype.ext
    rfl

  /- curl01: raw old projected RHS = z-vorticity temporal pairing. -/

  have hProjectedVorticity01 :
      (∫ r in (0 : ℝ)..(q : ℝ),
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl01 ψ))
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r))
        =
      ∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume := by
    apply
      intervalIntegral.integral_congr_Ioo_of_le
        q.2.1

    intro r hr

    have hrTau :
        r ∈ Set.Ioo (0 : ℝ) tau :=
      ⟨hr.1, hr.2.trans_le q.2.2⟩

    have hrClosed :
        r ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hrTau.1.le, hrTau.2.le⟩

    have hWeak :=
      h3PreterminalLoggedVelocity_weakTemporalPairing_eq_zeroProjectedRHSPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail
        ⟨r, hrClosed⟩
        (h3WeakTestCurl01 ψ)
        (h3WeakTestCurl01_divergenceFree ψ)

    have hWeakRaw :
        (∑ i : Fin 3,
          h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal
            hNS t ((h3WeakTestCurl01 ψ) i) i r)
          =
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl01 ψ))
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r) := by
      rw [
        h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal_apply_of_mem
          hNS ht hEnd hTail hrClosed
      ]
      simpa only [
        h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal
      ] using hWeak

    have hCurl :=
      h3PreterminalLoggedVelocityWeakTemporalCurl01_eq_vorticityZTemporal
        hNS ht hEnd hrTau ψ

    exact hWeakRaw.symm.trans hCurl

  have hFTCz :=
    intervalIntegral_h3PreterminalWeakVorticityZTemporalDerivative_eq_pairing_sub_tailH3_weakStrong
      hNS ht hEnd hE hTail ψ q

  rw [hZero] at hFTCz

  have h01 :
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail (h3WeakTestCurl01 ψ) q
        -
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail (h3WeakTestCurl01 ψ) q0
        =
      ∫ r in (0 : ℝ)..(q : ℝ),
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl01 ψ))
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r) := by
    rw [
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed_curl01_eq_weakVorticityZ
        hNS ht hEnd hTail ψ q,
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed_curl01_eq_weakVorticityZ
        hNS ht hEnd hTail ψ q0
    ]

    exact
      (hProjectedVorticity01.trans hFTCz).symm

  /- curl02: raw old projected RHS = minus y-vorticity temporal pairing. -/

  have hProjectedVorticity02 :
      (∫ r in (0 : ℝ)..(q : ℝ),
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl02 ψ))
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r))
        =
      -
      (∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume) := by
    calc
      (∫ r in (0 : ℝ)..(q : ℝ),
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl02 ψ))
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r))
          =
        ∫ r in (0 : ℝ)..(q : ℝ),
          -
          ∫ x : Point3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
                hNS (t + r) x)
            ∂volume := by
              apply
                intervalIntegral.integral_congr_Ioo_of_le
                  q.2.1

              intro r hr

              have hrTau :
                  r ∈ Set.Ioo (0 : ℝ) tau :=
                ⟨hr.1, hr.2.trans_le q.2.2⟩

              have hrClosed :
                  r ∈ Set.Icc (0 : ℝ) tau :=
                ⟨hrTau.1.le, hrTau.2.le⟩

              have hWeak :=
                h3PreterminalLoggedVelocity_weakTemporalPairing_eq_zeroProjectedRHSPhysicalL2HilbertOnElapsed
                  hNS ht hEnd hTail
                  ⟨r, hrClosed⟩
                  (h3WeakTestCurl02 ψ)
                  (h3WeakTestCurl02_divergenceFree ψ)

              have hWeakRaw :
                  (∑ i : Fin 3,
                    h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal
                      hNS t ((h3WeakTestCurl02 ψ) i) i r)
                    =
                  inner ℝ
                    (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl02 ψ))
                    (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
                      hNS ht hEnd hTail r) := by
                rw [
                  h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal_apply_of_mem
                    hNS ht hEnd hTail hrClosed
                ]
                simpa only [
                  h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal
                ] using hWeak

              have hCurl :=
                h3PreterminalLoggedVelocityWeakTemporalCurl02_eq_neg_vorticityYTemporal
                  hNS ht hEnd hrTau ψ

              exact hWeakRaw.symm.trans hCurl

      _ =
        -
        (∫ r in (0 : ℝ)..(q : ℝ),
          ∫ x : Point3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
                hNS (t + r) x)
            ∂volume) := by
        rw [intervalIntegral.integral_neg]

  have hFTCy :=
    intervalIntegral_h3PreterminalWeakVorticityYTemporalDerivative_eq_pairing_sub_tailH3_weakStrong
      hNS ht hEnd hE hTail ψ q

  rw [hZero] at hFTCy

  have h02 :
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail (h3WeakTestCurl02 ψ) q
        -
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail (h3WeakTestCurl02 ψ) q0
        =
      ∫ r in (0 : ℝ)..(q : ℝ),
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl02 ψ))
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r) := by
    rw [
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed_curl02_eq_neg_weakVorticityY
        hNS ht hEnd hTail ψ q,
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed_curl02_eq_neg_weakVorticityY
        hNS ht hEnd hTail ψ q0
    ]

    calc
      -h3PreterminalTailCanonicalWeakVorticityYPairingOnElapsed
          (u := u) (t := t) ψ q
        -
      (-h3PreterminalTailCanonicalWeakVorticityYPairingOnElapsed
          (u := u) (t := t) ψ q0)
          =
      -
      (h3PreterminalTailCanonicalWeakVorticityYPairingOnElapsed
          (u := u) (t := t) ψ q
        -
       h3PreterminalTailCanonicalWeakVorticityYPairingOnElapsed
          (u := u) (t := t) ψ q0) := by
        ring

      _ =
      -
      (∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume) := by
        rw [← hFTCy]

      _ =
      ∫ r in (0 : ℝ)..(q : ℝ),
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl02 ψ))
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r) :=
        hProjectedVorticity02.symm

  /- curl12: raw old projected RHS = x-vorticity temporal pairing. -/

  have hProjectedVorticity12 :
      (∫ r in (0 : ℝ)..(q : ℝ),
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl12 ψ))
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r))
        =
      ∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume := by
    apply
      intervalIntegral.integral_congr_Ioo_of_le
        q.2.1

    intro r hr

    have hrTau :
        r ∈ Set.Ioo (0 : ℝ) tau :=
      ⟨hr.1, hr.2.trans_le q.2.2⟩

    have hrClosed :
        r ∈ Set.Icc (0 : ℝ) tau :=
      ⟨hrTau.1.le, hrTau.2.le⟩

    have hWeak :=
      h3PreterminalLoggedVelocity_weakTemporalPairing_eq_zeroProjectedRHSPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail
        ⟨r, hrClosed⟩
        (h3WeakTestCurl12 ψ)
        (h3WeakTestCurl12_divergenceFree ψ)

    have hWeakRaw :
        (∑ i : Fin 3,
          h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal
            hNS t ((h3WeakTestCurl12 ψ) i) i r)
          =
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl12 ψ))
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r) := by
      rw [
        h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal_apply_of_mem
          hNS ht hEnd hTail hrClosed
      ]
      simpa only [
        h3PreterminalLoggedVelocityWeakTemporalCoordinatePairingReal
      ] using hWeak

    have hCurl :=
      h3PreterminalLoggedVelocityWeakTemporalCurl12_eq_vorticityXTemporal
        hNS ht hEnd hrTau ψ

    exact hWeakRaw.symm.trans hCurl

  have hFTCx :=
    intervalIntegral_h3PreterminalWeakVorticityXTemporalDerivative_eq_pairing_sub_tailH3_weakStrong
      hNS ht hEnd hE hTail ψ q

  rw [hZero] at hFTCx

  have h12 :
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail (h3WeakTestCurl12 ψ) q
        -
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail (h3WeakTestCurl12 ψ) q0
        =
      ∫ r in (0 : ℝ)..(q : ℝ),
        inner ℝ
          (h3WeakTestVectorPhysicalL2Hilbert (h3WeakTestCurl12 ψ))
          (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
            hNS ht hEnd hTail r) := by
    rw [
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed_curl12_eq_weakVorticityX
        hNS ht hEnd hTail ψ q,
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed_curl12_eq_weakVorticityX
        hNS ht hEnd hTail ψ q0
    ]

    exact
      (hProjectedVorticity12.trans hFTCx).symm

  exact ⟨h01, h02, h12⟩

end

end Euclidean
end Bridge
end PrimeTensor
