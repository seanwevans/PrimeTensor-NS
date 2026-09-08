import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.TemporalPairing

/-!
# Close the three integrated endpoint curl identities

The strict-time curl-test temporal pairings have now been identified with the
three compactly tested vorticity temporal derivatives:

    curl01(ψ)  ->   <ψ, ∂ₜω_z>,
    curl02(ψ)  -> - <ψ, ∂ₜω_y>,
    curl12(ψ)  ->   <ψ, ∂ₜω_x>.

Independently, the existing weak-temporal layer identifies the time integral of
the complete compact-test temporal pairing with the time integral of the
continuous projected RHS.

The preceding vorticity FTC file identifies the same three scalar time
integrals with the old vorticity pairing increments.  Combining those facts
with the fixed-time curl/vorticity pairing identities closes exactly the
`Curl.Integrated` frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EndpointCurlVorticityIntegrated
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3EndpointCurlVorticityIntegrated :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The endpoint H³ hypotheses imply the three integrated curl-test
projected-RHS identities needed by `Curl.Integrated`. -/
theorem h3PreterminalTailCanonicalCurlWeakVelocityPairingsSatisfyIntegratedProjectedRHSOnElapsed_endpointH3
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
    H3PreterminalTailCanonicalCurlWeakVelocityPairingsSatisfyIntegratedProjectedRHSOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint := by
  unfold
    H3PreterminalTailCanonicalCurlWeakVelocityPairingsSatisfyIntegratedProjectedRHSOnElapsed

  intro ψ q
  dsimp only

  have hZero :
      h3EndpointElapsedZero q
        =
      (⟨0, ⟨le_rfl, htau.le⟩⟩ :
        Set.Icc (0 : ℝ) tau) := by
    apply Subtype.ext
    rfl

  /- curl01: projected RHS = z-vorticity temporal pairing. -/

  have hProjected01 :=
    intervalIntegral_h3PreterminalTailCanonicalWeakTemporalPairing_eq_projectedRHS_to
      hNS ht htau hEnd hE hTail hEndpoint
      (h3WeakTestCurl01 ψ)
      (h3WeakTestCurl01_divergenceFree ψ)
      q.property

  have hProjected01' :
      (∫ r in (0 : ℝ)..(q : ℝ),
        ∑ i : Fin 3,
          h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
            hNS ht htau hEnd hE hTail hEndpoint
            ((h3WeakTestCurl01 ψ) i) i r)
        =
      ∫ r in (0 : ℝ)..(q : ℝ),
        h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
          hNS ht htau hEnd hE hTail hEndpoint
          (h3WeakTestCurl01 ψ) r := by
    simpa only [
      h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
    ] using hProjected01

  have hTemporal01 :
      (∫ r in (0 : ℝ)..(q : ℝ),
        ∑ i : Fin 3,
          h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
            hNS ht htau hEnd hE hTail hEndpoint
            ((h3WeakTestCurl01 ψ) i) i r)
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

    exact
      h3PreterminalTailCanonicalWeakTemporalCurl01_eq_vorticityZTemporal
        hNS ht htau hEnd hE hTail hEndpoint
        hrTau ψ

  have hProjectedVorticity01 :
      (∫ r in (0 : ℝ)..(q : ℝ),
        h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
          hNS ht htau hEnd hE hTail hEndpoint
          (h3WeakTestCurl01 ψ) r)
        =
      ∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume :=
    hProjected01'.symm.trans hTemporal01

  have hFTCz :=
    intervalIntegral_h3PreterminalWeakVorticityZTemporalDerivative_eq_pairing_sub_endpointH3
      hNS ht hEnd hE hTail hEndpoint ψ q

  rw [hZero] at hFTCz

  have h01 :
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail (h3WeakTestCurl01 ψ) q
        -
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail (h3WeakTestCurl01 ψ)
          ⟨0, ⟨le_rfl, htau.le⟩⟩
        =
      ∫ r in (0 : ℝ)..(q : ℝ),
        h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
          hNS ht htau hEnd hE hTail hEndpoint
          (h3WeakTestCurl01 ψ) r := by
    rw [
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed_curl01_eq_weakVorticityZ
        hNS ht hEnd hTail ψ q,
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed_curl01_eq_weakVorticityZ
        hNS ht hEnd hTail ψ
        (⟨0, ⟨le_rfl, htau.le⟩⟩ :
          Set.Icc (0 : ℝ) tau)
    ]

    exact
      (hProjectedVorticity01.trans hFTCz).symm

  /- curl02: projected RHS = minus y-vorticity temporal pairing. -/

  have hProjected02 :=
    intervalIntegral_h3PreterminalTailCanonicalWeakTemporalPairing_eq_projectedRHS_to
      hNS ht htau hEnd hE hTail hEndpoint
      (h3WeakTestCurl02 ψ)
      (h3WeakTestCurl02_divergenceFree ψ)
      q.property

  have hProjected02' :
      (∫ r in (0 : ℝ)..(q : ℝ),
        ∑ i : Fin 3,
          h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
            hNS ht htau hEnd hE hTail hEndpoint
            ((h3WeakTestCurl02 ψ) i) i r)
        =
      ∫ r in (0 : ℝ)..(q : ℝ),
        h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
          hNS ht htau hEnd hE hTail hEndpoint
          (h3WeakTestCurl02 ψ) r := by
    simpa only [
      h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
    ] using hProjected02

  have hTemporal02 :
      (∫ r in (0 : ℝ)..(q : ℝ),
        ∑ i : Fin 3,
          h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
            hNS ht htau hEnd hE hTail hEndpoint
            ((h3WeakTestCurl02 ψ) i) i r)
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

    exact
      h3PreterminalTailCanonicalWeakTemporalCurl02_eq_neg_vorticityYTemporal
        hNS ht htau hEnd hE hTail hEndpoint
        hrTau ψ

  have hProjectedVorticity02 :
      (∫ r in (0 : ℝ)..(q : ℝ),
        h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
          hNS ht htau hEnd hE hTail hEndpoint
          (h3WeakTestCurl02 ψ) r)
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
        h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
          hNS ht htau hEnd hE hTail hEndpoint
          (h3WeakTestCurl02 ψ) r)
          =
        ∫ r in (0 : ℝ)..(q : ℝ),
          ∑ i : Fin 3,
            h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
              hNS ht htau hEnd hE hTail hEndpoint
              ((h3WeakTestCurl02 ψ) i) i r :=
        hProjected02'.symm

      _ =
        ∫ r in (0 : ℝ)..(q : ℝ),
          -
          ∫ x : Point3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
                hNS (t + r) x)
            ∂volume :=
        hTemporal02

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
    intervalIntegral_h3PreterminalWeakVorticityYTemporalDerivative_eq_pairing_sub_endpointH3
      hNS ht hEnd hE hTail hEndpoint ψ q

  rw [hZero] at hFTCy

  have h02 :
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail (h3WeakTestCurl02 ψ) q
        -
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail (h3WeakTestCurl02 ψ)
          ⟨0, ⟨le_rfl, htau.le⟩⟩
        =
      ∫ r in (0 : ℝ)..(q : ℝ),
        h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
          hNS ht htau hEnd hE hTail hEndpoint
          (h3WeakTestCurl02 ψ) r := by
    rw [
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed_curl02_eq_neg_weakVorticityY
        hNS ht hEnd hTail ψ q,
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed_curl02_eq_neg_weakVorticityY
        hNS ht hEnd hTail ψ
        (⟨0, ⟨le_rfl, htau.le⟩⟩ :
          Set.Icc (0 : ℝ) tau)
    ]

    calc
      -h3PreterminalTailCanonicalWeakVorticityYPairingOnElapsed
          (u := u) (t := t) ψ q
        -
      (-h3PreterminalTailCanonicalWeakVorticityYPairingOnElapsed
          (u := u) (t := t) ψ
          (⟨0, ⟨le_rfl, htau.le⟩⟩ :
            Set.Icc (0 : ℝ) tau))
          =
      -
      (h3PreterminalTailCanonicalWeakVorticityYPairingOnElapsed
          (u := u) (t := t) ψ q
        -
       h3PreterminalTailCanonicalWeakVorticityYPairingOnElapsed
          (u := u) (t := t) ψ
          (⟨0, ⟨le_rfl, htau.le⟩⟩ :
            Set.Icc (0 : ℝ) tau)) := by
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
        h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
          hNS ht htau hEnd hE hTail hEndpoint
          (h3WeakTestCurl02 ψ) r :=
        hProjectedVorticity02.symm

  /- curl12: projected RHS = x-vorticity temporal pairing. -/

  have hProjected12 :=
    intervalIntegral_h3PreterminalTailCanonicalWeakTemporalPairing_eq_projectedRHS_to
      hNS ht htau hEnd hE hTail hEndpoint
      (h3WeakTestCurl12 ψ)
      (h3WeakTestCurl12_divergenceFree ψ)
      q.property

  have hProjected12' :
      (∫ r in (0 : ℝ)..(q : ℝ),
        ∑ i : Fin 3,
          h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
            hNS ht htau hEnd hE hTail hEndpoint
            ((h3WeakTestCurl12 ψ) i) i r)
        =
      ∫ r in (0 : ℝ)..(q : ℝ),
        h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
          hNS ht htau hEnd hE hTail hEndpoint
          (h3WeakTestCurl12 ψ) r := by
    simpa only [
      h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
    ] using hProjected12

  have hTemporal12 :
      (∫ r in (0 : ℝ)..(q : ℝ),
        ∑ i : Fin 3,
          h3PreterminalTailCanonicalWeakTemporalCoordinatePairingReal
            hNS ht htau hEnd hE hTail hEndpoint
            ((h3WeakTestCurl12 ψ) i) i r)
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

    exact
      h3PreterminalTailCanonicalWeakTemporalCurl12_eq_vorticityXTemporal
        hNS ht htau hEnd hE hTail hEndpoint
        hrTau ψ

  have hProjectedVorticity12 :
      (∫ r in (0 : ℝ)..(q : ℝ),
        h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
          hNS ht htau hEnd hE hTail hEndpoint
          (h3WeakTestCurl12 ψ) r)
        =
      ∫ r in (0 : ℝ)..(q : ℝ),
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
              hNS (t + r) x)
          ∂volume :=
    hProjected12'.symm.trans hTemporal12

  have hFTCx :=
    intervalIntegral_h3PreterminalWeakVorticityXTemporalDerivative_eq_pairing_sub_endpointH3
      hNS ht hEnd hE hTail hEndpoint ψ q

  rw [hZero] at hFTCx

  have h12 :
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail (h3WeakTestCurl12 ψ) q
        -
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail (h3WeakTestCurl12 ψ)
          ⟨0, ⟨le_rfl, htau.le⟩⟩
        =
      ∫ r in (0 : ℝ)..(q : ℝ),
        h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
          hNS ht htau hEnd hE hTail hEndpoint
          (h3WeakTestCurl12 ψ) r := by
    rw [
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed_curl12_eq_weakVorticityX
        hNS ht hEnd hTail ψ q,
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed_curl12_eq_weakVorticityX
        hNS ht hEnd hTail ψ
        (⟨0, ⟨le_rfl, htau.le⟩⟩ :
          Set.Icc (0 : ℝ) tau)
    ]

    exact
      (hProjectedVorticity12.trans hFTCx).symm

  exact ⟨h01, h02, h12⟩

end

end Euclidean
end Bridge
end PrimeTensor
