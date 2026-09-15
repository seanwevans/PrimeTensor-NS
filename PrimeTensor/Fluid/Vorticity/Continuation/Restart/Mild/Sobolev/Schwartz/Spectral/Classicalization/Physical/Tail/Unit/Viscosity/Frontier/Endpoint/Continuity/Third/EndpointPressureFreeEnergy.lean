import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.WeakPressureFree
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.EnergyC1
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.Diffusion
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Raw.L2.Shift
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.RHS.Continuity

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EndpointPressureFreeEnergy
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3EndpointPressureFreeEnergy :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

theorem h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_physicalEnergy_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPhysical :
      H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalSpectralStateContinuousOnElapsed
      hNS ht hEnd hTail := by
  have hWeak :
      H3PreterminalCanonicalSpectralWeakContinuousOnElapsed
        hNS ht hEnd hTail :=
    h3PreterminalCanonicalSpectralWeakContinuousOnElapsed_pressureFree
      hNS ht hEnd hE hTail

  have hSquare :
      H3PreterminalCanonicalSpectralSquareEnergyContinuousOnElapsed
        hNS ht hEnd hTail :=
    h3PreterminalCanonicalSpectralSquareEnergyContinuousOnElapsed_of_physicalEnergy
      hNS ht hEnd hTail hPhysical

  exact
    h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_weak_of_squareEnergy
      hNS ht hEnd hTail hWeak hSquare

theorem h3PreterminalCanonicalL2ZeroContinuousOnElapsed_of_spectralState_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hSpectral :
      H3PreterminalCanonicalSpectralStateContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalL2ZeroContinuousOnElapsed
      hNS ht hEnd hTail := by
  intro j

  let U :
      Set.Icc (0 : ℝ) tau →
        H3SpectralVelocityState :=
    fun q =>
      h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q

  let L :
      Set.Icc (0 : ℝ) tau →
        H3ScalarL2 :=
    fun q =>
      h3PreterminalCanonicalL2JetOnElapsed
        hNS ht hEnd hTail (h3JetSlot0 j) q

  let LF :
      Set.Icc (0 : ℝ) tau →
        H3FourierComplexL2 :=
    fun q =>
      h3PreterminalCanonicalFourierJetOnElapsed
        hNS ht hEnd hTail (h3JetSlot0 j) q

  have hUj :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          U q j) := by
    exact
      (continuous_apply j).comp hSpectral

  have hRaw :
      Continuous
        (fun q : Set.Icc (0 : ℝ) tau =>
          h3SpectralScalarRawFourierL2
            (U q j)) := by
    exact
      h3SpectralScalarRawFourierL2CLM.continuous.comp
        hUj

  have hRawEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3SpectralScalarRawFourierL2
          (U q j))
        =
      LF := by
    funext q
    dsimp only [U, LF]
    rw [
      h3PreterminalTailCanonicalSpectralStateOnElapsed_rawFourierL2_eq_baseFourierAt
        hNS ht hEnd hTail q j
    ]
    rfl

  have hFourier :
      Continuous LF := by
    rw [← hRawEq]
    exact hRaw

  have hTransform :
      (fun q : Set.Icc (0 : ℝ) tau =>
        h3ScalarFourierL2 (L q))
        =
      LF := by
    funext q
    dsimp only [L, LF]
    exact
      (h3PreterminalCanonicalFourierJetOnElapsed_eq_scalarFourierL2
        hNS ht hEnd hTail (h3JetSlot0 j) q).symm

  rw [continuous_iff_continuousAt]
  intro q₀
  apply tendsto_iff_norm_sub_tendsto_zero.2

  have hFourierAt :
      Tendsto
        (fun q : Set.Icc (0 : ℝ) tau =>
          ‖LF q - LF q₀‖)
        (𝓝 q₀)
        (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1
      hFourier.continuousAt

  have hNormEq :
      (fun q : Set.Icc (0 : ℝ) tau =>
        ‖L q - L q₀‖)
        =
      (fun q : Set.Icc (0 : ℝ) tau =>
        ‖LF q - LF q₀‖) := by
    funext q

    have hq :
        h3ScalarFourierL2 (L q) = LF q :=
      congrFun hTransform q

    have hq₀ :
        h3ScalarFourierL2 (L q₀) = LF q₀ :=
      congrFun hTransform q₀

    calc
      ‖L q - L q₀‖
          =
        ‖h3ScalarFourierL2 (L q - L q₀)‖ := by
          symm
          exact norm_h3ScalarFourierL2 (L q - L q₀)
      _ =
        ‖h3ScalarFourierL2 (L q) -
            h3ScalarFourierL2 (L q₀)‖ := by
          rw [h3ScalarFourierL2_sub]
      _ =
        ‖LF q - LF q₀‖ := by
          rw [hq, hq₀]

  rw [hNormEq]
  exact hFourierAt

theorem h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_spectralState_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hSpectral :
      H3PreterminalCanonicalSpectralStateContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalL2EndpointContinuousOnElapsed
      hNS ht hEnd hTail := by
  have hZero :
      H3PreterminalCanonicalL2ZeroContinuousOnElapsed
        hNS ht hEnd hTail :=
    h3PreterminalCanonicalL2ZeroContinuousOnElapsed_of_spectralState_pressureFree
      hNS ht hEnd hTail hSpectral

  have hThird :
      H3PreterminalCanonicalL2ThirdContinuousOnElapsed
        hNS ht hEnd hTail :=
    h3PreterminalCanonicalL2ThirdContinuousOnElapsed_of_spectralState
      hNS ht hEnd hTail hSpectral

  exact
    h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_zero_third
      hNS ht hEnd hTail hZero hThird

theorem h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_physicalEnergy_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPhysical :
      H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalCanonicalL2EndpointContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_spectralState_pressureFree
      hNS ht hEnd hTail
      (h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_physicalEnergy_pressureFree
        hNS ht hEnd hE hTail hPhysical)

theorem h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_canonicalH3EnergyData_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hData :
      CanonicalH3EnergyDataOnTail u t T) :
    H3PreterminalCanonicalL2EndpointContinuousOnElapsed
      hNS ht hEnd hTail := by
  have hPhysical :
      H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed
        hNS ht hEnd hTail :=
    h3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed_of_canonicalH3EnergyData
      hNS ht htau hEnd hTail hData

  exact
    h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_physicalEnergy_pressureFree
      hNS ht hEnd hE hTail hPhysical

theorem h3PreterminalTailUnitViscosityEndpointContinuityOnRestartRadius_of_canonicalEnergyData_pressureFree
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hData :
      CanonicalH3EnergyDataOnTail u t T) :
    H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
      E u T t hNS ht hE hTail := by
  intro q hqPos hEnd

  exact
    h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_canonicalH3EnergyData_pressureFree
      hNS ht hqPos hEnd hE hTail hData

end

end Euclidean
end Bridge
end PrimeTensor
