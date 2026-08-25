import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralHeatRealC3Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLerayDuhamelRestart

/-!
# Real C³ reconstruction of the regularized Duhamel head

At a positive target time `t`, split the retarded Duhamel integral at `t/2`.
The restart identity writes the first half exactly as

    H_{t/2} D(t/2).

This term has a fixed positive amount of heat in front of an arbitrary H³
spectral state, so the positive-time heat reconstruction theorem applies
without any new nonlinear Fourier estimate.

This file packages that regularized head, proves a real spatial `C³`
representative on `Point3` coordinatewise, identifies it almost everywhere
with the existing real decoder, and records the exact head/tail decomposition
of the complete Duhamel term.

The only remaining classicalization issue after this checkpoint is the
near-endpoint tail `∫_{t/2}^t K_{t-s} ds`, where the heat lag can vanish and a
bootstrap from already-positive-time regularity is genuinely required.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzDuhamelHeadRealC3Bridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SchwartzDuhamelHeadRealC3Bridge :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The regularized first half of the retarded Duhamel contribution.

It is exactly the shorter-time Duhamel state evolved by an additional `t/2`
of heat. -/
noncomputable def h3SpectralFinHeatLerayDuhamelHead
    (ν t : ℝ)
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : ℝ → H3SpectralFinVectorState) :
    H3SpectralFinVectorState :=
  h3SpectralVelocityHeatApplyNN
    ν hν.le
    (NNReal.mk (t / 2) (by linarith))
    (h3SpectralFinHeatLerayDuhamel
      ν (t / 2) hν U V)

/-- Coordinatewise real `C³` representative of the regularized Duhamel head
on the project's spatial carrier. -/
noncomputable def h3SpectralFinHeatLerayDuhamelHeadRealC3RepresentativeOnPoint3
    (ν t : ℝ)
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (j : Fin 3) :
    Point3 → ℝ :=
  h3SpectralVelocityHeatRealC3RepresentativeOnPoint3
    ν (t / 2)
    (h3SpectralFinHeatLerayDuhamel
      ν (t / 2) hν U V)
    j

/-- Every coordinate of the regularized Duhamel head is spatially `C³`. -/
theorem h3SpectralFinHeatLerayDuhamelHeadRealC3RepresentativeOnPoint3_contDiff_three
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (j : Fin 3) :
    ContDiff ℝ 3
      (h3SpectralFinHeatLerayDuhamelHeadRealC3RepresentativeOnPoint3
        ν t hν ht U V j) := by
  unfold h3SpectralFinHeatLerayDuhamelHeadRealC3RepresentativeOnPoint3
  exact
    h3SpectralVelocityHeatRealC3RepresentativeOnPoint3_contDiff_three
      hν (by linarith) (h3SpectralFinHeatLerayDuhamel ν (t / 2) hν U V) j

/-- The real `C³` head representative is exactly the a.e. representative of
its existing real spectral decoder. -/
theorem h3SpectralFinHeatLerayDuhamelHeadRealC3RepresentativeOnPoint3_ae_eq_decodeRealL2
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (j : Fin 3) :
    h3SpectralFinHeatLerayDuhamelHeadRealC3RepresentativeOnPoint3
        ν t hν ht U V j
      =ᵐ[(volume : Measure Point3)]
    ((h3FromFourierRealL2
        (h3SpectralVelocityDecodeRealL2
          (h3SpectralFinHeatLerayDuhamelHead
            ν t hν ht U V) j) : H3ScalarL2) :
      Point3 → ℝ) := by
  unfold h3SpectralFinHeatLerayDuhamelHeadRealC3RepresentativeOnPoint3
  unfold h3SpectralFinHeatLerayDuhamelHead
  change
    h3SpectralVelocityHeatRealC3RepresentativeOnPoint3
        ν (t / 2)
        (h3SpectralFinHeatLerayDuhamel ν (t / 2) hν U V) j
      =ᵐ[(volume : Measure Point3)]
    ((h3FromFourierRealL2
        (h3SpectralVelocityDecodeRealL2
          (h3SpectralVelocityHeatApplyNN
            ν hν.le
            (NNReal.mk (t / 2) (by linarith))
            (h3SpectralFinHeatLerayDuhamel ν (t / 2) hν U V)) j) : H3ScalarL2) :
      Point3 → ℝ)
  exact
    h3SpectralVelocityHeatRealC3RepresentativeOnPoint3_ae_eq_decodeRealL2
      hν (by linarith)
      (h3SpectralFinHeatLerayDuhamel ν (t / 2) hν U V) j

/-- Exact positive-time head/tail decomposition of the Duhamel term at the
midpoint `t/2`.

The hypotheses are precisely the two Bochner-integrability assumptions needed
by the generic Duhamel restart theorem. -/
theorem h3SpectralFinHeatLerayDuhamel_eq_head_add_tail
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (hIntLong :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν U V)
        volume
        0
        t)
    (hIntHalf :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν (t / 2) hν U V)
        volume
        0
        (t / 2)) :
    h3SpectralFinHeatLerayDuhamel ν t hν U V
      =
    h3SpectralFinHeatLerayDuhamelHead ν t hν ht U V
      +
    ∫ s in (t / 2)..t,
      h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν U V s := by
  have htHalf : 0 ≤ t / 2 := by linarith
  have hsplit : t / 2 + t / 2 = t := by ring

  have hIntLong' :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν (t / 2 + t / 2) hν U V)
        volume
        0
        (t / 2 + t / 2) := by
    simpa only [hsplit] using hIntLong

  have hRestart :=
    h3SpectralFinHeatLerayDuhamel_add_time
      (a := t / 2) (b := t / 2)
      hν htHalf htHalf U V hIntLong' hIntHalf

  rw [hsplit] at hRestart
  unfold h3SpectralFinHeatLerayDuhamelHead
  exact hRestart

end

end Euclidean
end Bridge
end PrimeTensor
