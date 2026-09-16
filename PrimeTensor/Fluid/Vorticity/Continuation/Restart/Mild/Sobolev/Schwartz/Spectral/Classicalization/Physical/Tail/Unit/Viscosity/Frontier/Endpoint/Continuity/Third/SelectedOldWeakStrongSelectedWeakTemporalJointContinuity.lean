import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedWeakProjectedRHSPairingContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedTemporalPDE
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Selected.Pressure.Force

/-!
# Joint spacetime continuity of the selected temporal derivative

The selected weak-FTC stack now has

* closed-interval continuity of the selected weak velocity pairing;
* closed-interval continuity and interval integrability of the selected weak
  projected-RHS pairing;
* the strict-positive pointwise temporal PDE

      ∂ₜ S_i
        =
      Σ_j ∂_j² S_i - N_i(S,S).

To differentiate a compact-test spatial pairing honestly, we still need local
spacetime control of `∂ₜ S_i`.

That control is already present in the selected classicalization stack:

* every pure second selected spatial derivative is jointly continuous on
  `(0,tau) × Point3` whenever `tau` lies inside the restart radius;
* the diagonal Leray-forcing reconstruction is jointly continuous along every
  continuous H³ path.

This file combines those two facts with the selected temporal PDE.  Therefore
the actual pointwise temporal derivative is jointly continuous on the complete
strict elapsed slab.

No old-branch regularity, endpoint agreement, or new estimate is introduced.
The next checkpoint can use compact support to obtain the local domination
needed by `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakTemporalJointContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Match the norm topology used by the compact weak-test layer. -/
local instance point3NormTopologicalSpaceH3SelectedOldWeakStrongSelectedWeakTemporalJointContinuity :
    TopologicalSpace Point3 :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- One selected temporal-derivative coordinate is genuinely jointly continuous
in elapsed time and physical space on every strict slab contained in the
restart radius. -/
theorem h3PreterminalSelectedUnitRealVelocity_temporalDerivative_jointContinuousOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
    ContinuousOn
      (fun z : ℝ × Point3 =>
        temporal.d
          (fun r : ℝ =>
            h3SpectralScalarRealC1RepresentativeOnPoint3
              (W r i) z.2)
          z.1)
      (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ) := by
  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalTailCanonicalAnchorSpectralState_le
      hNS ht hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  have hW :
      Continuous W := by
    dsimp only [
      W,
      h3PreterminalTailCanonicalSelectedRestart,
      U₀,
      hA,
      hU₀
    ]

    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)

  have hSecond
      (j : Fin 3) :
      ContinuousOn
        (fun z : ℝ × Point3 =>
          spatial3.d
            (h3AxisOfFin3 j)
            (spatial3.d
              (h3AxisOfFin3 j)
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (W z.1 i)))
            z.2)
        (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ) := by
    dsimp only [
      W,
      h3PreterminalTailCanonicalSelectedRestart,
      U₀,
      hA,
      hU₀
    ]

    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_pureSecond_jointContinuousOn
        (one_pos : (0 : ℝ) < 1)
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        htauR
        i
        (h3AxisOfFin3 j)

  have hLaplacian :
      ContinuousOn
        (fun z : ℝ × Point3 =>
          ∑ j : Fin 3,
            spatial3.d
              (h3AxisOfFin3 j)
              (spatial3.d
                (h3AxisOfFin3 j)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W z.1 i)))
              z.2)
        (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ) := by
    apply continuousOn_finsetSum
    intro j hj
    exact hSecond j

  have hForcingComplex :
      Continuous
        (fun z : ℝ × Point3 =>
          h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W z.1) (W z.1) i z.2) := by
    exact
      h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3_diagonal_jointContinuous_of_continuousPath
        W hW i

  have hForcing :
      ContinuousOn
        (fun z : ℝ × Point3 =>
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W z.1) (W z.1) i z.2).re)
        (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ) := by
    exact
      (Complex.continuous_re.comp hForcingComplex).continuousOn

  have hRHS :
      ContinuousOn
        (fun z : ℝ × Point3 =>
          (∑ j : Fin 3,
            spatial3.d
              (h3AxisOfFin3 j)
              (spatial3.d
                (h3AxisOfFin3 j)
                (h3SpectralScalarRealC1RepresentativeOnPoint3
                  (W z.1 i)))
              z.2)
            -
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            (W z.1) (W z.1) i z.2).re)
        (Set.Ioo (0 : ℝ) tau ×ˢ Set.univ) :=
    hLaplacian.sub hForcing

  apply hRHS.congr

  intro z hz

  have hz0 : 0 < z.1 :=
    hz.1.1

  have hzTau : z.1 < tau :=
    hz.1.2

  have hzR :
      z.1 <
        h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    lt_of_lt_of_le hzTau htauR

  have hPDE :=
    h3PreterminalSelectedUnitRealVelocity_temporal_d_eq_spatialLaplacian_sub_forcing
      hNS ht hE hTail
      hz0 hzR
      i z.2

  dsimp only at hPDE

  simpa only [W] using hPDE

end

end Euclidean
end Bridge
end PrimeTensor
