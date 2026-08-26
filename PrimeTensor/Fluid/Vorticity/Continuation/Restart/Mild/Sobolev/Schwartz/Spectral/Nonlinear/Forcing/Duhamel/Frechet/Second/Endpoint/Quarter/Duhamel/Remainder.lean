import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Heat.Orbit
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Physical.Restart.Interface
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Duhamel.Path
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Restart.Bound

/-!
# Quantitative Duhamel restart remainder bound for the quarter-Hölder bootstrap

The heat side of the endpoint bootstrap is now quarter-Hölder after a positive
base time.  The nonlinear side enters through the canonical restart remainder

    R(a,T) = D_T(U(a+·), V(a+·)).

Before converting its square-root gain to the quarter-power modulus used by
the endpoint theorem, we isolate the exact quantitative bound for this
canonical remainder.  For continuous globally bounded paths,

    ‖R(a,T)‖ ≤ C_D(ν) sqrt(T) M_U M_V.

The final theorem specializes this to the Banach-selected canonical restart
path, where both bounds are `2A`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-- The canonical restart remainder has the same square-root estimate as an
ordinary origin-based Duhamel term. -/
theorem norm_h3SpectralFinHeatLerayDuhamelRestartRemainder_le_pathCoefficient
    {ν a MU MV : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (T : NNReal) :
    ‖h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν a hν U V T‖
      ≤
    h3HeatLerayDuhamelPathCoefficient ν *
      Real.sqrt (T : ℝ) * MU * MV := by
  let Ua : ℝ → H3SpectralFinVectorState :=
    fun q => U (q + a)
  let Va : ℝ → H3SpectralFinVectorState :=
    fun q => V (q + a)

  have hUaCont : Continuous Ua := by
    dsimp only [Ua]
    exact hUcont.comp (continuous_id.add continuous_const)

  have hVaCont : Continuous Va := by
    dsimp only [Va]
    exact hVcont.comp (continuous_id.add continuous_const)

  have hUa : ∀ q : ℝ, ‖Ua q‖ ≤ MU := by
    intro q
    exact hU (q + a)

  have hVa : ∀ q : ℝ, ‖Va q‖ ≤ MV := by
    intro q
    exact hV (q + a)

  have hBound :=
    norm_h3SpectralFinHeatLerayDuhamel_le_pathCoefficient
      hν T.property hMU hMV Ua Va
      hUaCont hVaCont hUa hVa

  change
    ‖h3SpectralFinHeatLerayDuhamel ν (T : ℝ) hν Ua Va‖ ≤
      h3HeatLerayDuhamelPathCoefficient ν *
        Real.sqrt (T : ℝ) * MU * MV
  exact hBound

/-- Selected-restart specialization of the canonical remainder estimate. -/
theorem norm_h3SpectralFinHeatLerayDuhamelRestartRemainder_selectedRestart_le
    {ν A a : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (T : NNReal) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3SpectralFinHeatLerayDuhamelRestartRemainder
        ν a hν W W T‖
      ≤
    h3HeatLerayDuhamelPathCoefficient ν *
      Real.sqrt (T : ℝ) * (2 * A) * (2 * A) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hW : ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have h2A : 0 ≤ 2 * A := by
    positivity

  exact
    norm_h3SpectralFinHeatLerayDuhamelRestartRemainder_le_pathCoefficient
      hν h2A h2A W W hWcont hWcont hW hW T

end

end Euclidean
end Bridge
end PrimeTensor
