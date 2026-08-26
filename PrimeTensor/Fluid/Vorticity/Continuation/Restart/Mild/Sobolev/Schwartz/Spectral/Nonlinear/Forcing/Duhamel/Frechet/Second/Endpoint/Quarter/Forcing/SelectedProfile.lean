import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedUnsplitBudget

/-!
# Selected quarter-Hölder forcing: named second-moment profile

The selected endpoint branch repeatedly uses the scalar profile

    s ↦ ∫ |ξ|² |H_{t-s}(ξ) N(W(s),W(s))(ξ)| dξ.

This file gives that quantity a stable name.  The canonical two-piece budget
from `Forcing.SelectedUnsplitBudget` is then restated entirely in terms of the
profile.

This abstraction is the handoff to the remaining measure-theoretic task:
prove that the selected profile is genuinely interval-integrable on `0..t`.
Once that is closed, `integral_add_adjacent_intervals` can collapse the
two-piece bound into the actual full `0..t` second-Duhamel integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedProfile
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Frequency-integrated second Fourier moment of the retarded raw nonlinear
forcing along a spectral path. -/
noncomputable def h3NonlinearForcingHeatSecondMomentProfile
    (ν t : ℝ)
    (W : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (s : ℝ) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ ^ 2 *
      ‖h3HeatFourierSymbol ν (t - s) ξ *
        h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖

/-- The second-moment profile is nonnegative. -/
theorem h3NonlinearForcingHeatSecondMomentProfile_nonneg
    (ν t : ℝ)
    (W : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (s : ℝ) :
    0 ≤ h3NonlinearForcingHeatSecondMomentProfile ν t W i s := by
  unfold h3NonlinearForcingHeatSecondMomentProfile
  exact integral_nonneg (fun ξ => by positivity)

/-- In profile notation, the selected old head and actual unsplit terminal
tail are bounded together by the canonical selected second-moment budget. -/
theorem norm_h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_head_add_halfTail_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖∫ s in (0 : ℝ)..(t / 2),
        h3NonlinearForcingHeatSecondMomentProfile ν t W i s‖ +
      ‖∫ s in (t / 2)..t,
        h3NonlinearForcingHeatSecondMomentProfile ν t W i s‖
      ≤
    h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t := by
  dsimp only
  simpa only [h3NonlinearForcingHeatSecondMomentProfile] using
    (norm_h3RawFinLerayOuterProductDivergenceHeat_secondMoment_head_add_unsplit_halfTail_intervalIntegrals_le_quarter_selectedRestart
      hν U₀ hA hU₀ ht htR i)

end

end Euclidean
end Bridge
end PrimeTensor
