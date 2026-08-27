import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NamedSecond
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Reconstruction.L2.Bridge

/-!
# Second Fourier moment of the selected positive-lag Duhamel head

The midpoint Duhamel head is exactly the shorter-time Duhamel state evolved by
an additional positive heat time `t/2`.

The positive-time heat reconstruction layer already packages the deweighted
raw Fourier representative in `L²` and proves polynomial Fourier moments
through order three.

This file specializes that bridge to the canonical selected Duhamel head and
records the order-two moment directly on the named head state.

Together with `NamedSecond`, this supplies the head and tail inputs needed to
give the full selected Duhamel state a second raw Fourier moment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedDuhamelHeadSecond
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Quotient-safe raw Fourier `L²` state of one coordinate of the selected
positive-lag Duhamel head. -/
noncomputable def h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  h3SpectralScalarRawFourierL2
    (h3SpectralFinHeatLerayDuhamelHead
      ν t hν ht W W i)

/-- The deweighted selected head is exactly the canonical `L²` package of the
explicit positive-time heat representative. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_eq_heatRepresentativeL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
        hν U₀ hA hU₀ ht i
      =
    h3SpectralScalarHeatRawRepresentativeL2
      ν (t / 2) hν (by linarith)
      (h3SpectralFinHeatLerayDuhamel
        ν (t / 2) hν W W i) := by
  dsimp only
  unfold h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
  unfold h3SpectralFinHeatLerayDuhamelHead

  change
    h3SpectralScalarRawFourierL2
        (h3SpectralScalarHeatApplyNN
          ν hν.le
          (NNReal.mk (t / 2) (by linarith))
          (h3SpectralFinHeatLerayDuhamel
            ν (t / 2) hν
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀)
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀)
            i))
      =
    h3SpectralScalarHeatRawRepresentativeL2
      ν (t / 2) hν (by linarith)
      (h3SpectralFinHeatLerayDuhamel
        ν (t / 2) hν
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀)
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀)
        i)

  symm
  exact
    h3SpectralScalarHeatRawRepresentativeL2_eq_rawFourierL2_heatApplyNN
      hν (by linarith)
      (h3SpectralFinHeatLerayDuhamel
        ν (t / 2) hν
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀)
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀)
        i)

/-- The explicit positive-time heat amplitude is an a.e. representative of
the actual named selected Duhamel head raw Fourier `L²` state. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heatRepresentative
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
        hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SpectralScalarHeatRawRepresentative
      ν (t / 2)
      (h3SpectralFinHeatLerayDuhamel
        ν (t / 2) hν W W i) := by
  dsimp only

  have hEq :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_eq_heatRepresentativeL2
      hν U₀ hA hU₀ ht i

  have hRep :=
    h3SpectralScalarHeatRawRepresentativeL2_ae
      (t := t / 2)
      hν (by linarith)
      (h3SpectralFinHeatLerayDuhamel
        ν (t / 2) hν
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀)
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀)
        i)

  rw [hEq]
  exact hRep

/-- The actual named selected positive-lag Duhamel head has an integrable
second raw Fourier moment. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_secondMoment_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let G : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel
      ν (t / 2) hν W W i

  have hHeat :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarHeatRawRepresentative
              ν (t / 2) G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      h3SpectralScalarHeatRawRepresentative_moment_integrable
        hν (by linarith) G 2 (by norm_num)

  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heatRepresentative
      hν U₀ hA hU₀ ht i

  have hWeighted :
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarHeatRawRepresentative
            ν (t / 2) G ξ‖) := by
    dsimp only [G, W] at hRep ⊢
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  exact hHeat.congr hWeighted.symm

end
end Euclidean
end Bridge
end PrimeTensor
