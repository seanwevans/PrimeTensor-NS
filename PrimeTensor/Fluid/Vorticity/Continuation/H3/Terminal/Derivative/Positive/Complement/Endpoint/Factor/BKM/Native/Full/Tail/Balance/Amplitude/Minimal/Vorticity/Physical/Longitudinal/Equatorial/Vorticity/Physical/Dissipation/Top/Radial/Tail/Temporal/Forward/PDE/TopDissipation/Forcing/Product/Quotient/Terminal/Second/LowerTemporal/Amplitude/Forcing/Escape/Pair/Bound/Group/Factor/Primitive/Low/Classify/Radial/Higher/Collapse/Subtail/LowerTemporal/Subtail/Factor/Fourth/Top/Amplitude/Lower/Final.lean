import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.LowerTemporal.Subtail.Factor.Fourth.Top.Amplitude.Lower
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Full.Energy.Dissipation.Cascade

/-!
# Close the final scalar resolved-PDE frontier

The resolved scalar-amplitude reduction now leaves only one channel-specific
alternative: top dissipation.

At this point no new top-dissipation estimate is required.  Under the same
hypothetical nonextension hypothesis, the already-proved full H³ terminal
cascade gives

    E₃(t) → +∞

along the entire left-terminal filter `𝓝[<] T`.

The explicit sequence produced by the resolved-PDE frontier converges to `T`
and lies strictly below `T` at every index.  Hence it inherits this full-tail
`E₃` divergence.  Since the top H³ energy is bounded by the total H³ energy,
the same sequence carries total H³-energy escape.

Thus the final top-dissipation scalar channel is absorbed into the physical
H³-energy branch.  No resolved PDE scalar channel remains independently
unclassified.

This remains a conditional statement on the hypothetical nonextension branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000

/--
The terminal sequence selected by the fully resolved physical-PDE frontier
necessarily carries total H³-energy escape under hypothetical nonextension.

This closes the final scalar channel (`topDissipation`) without introducing a
new estimate: the result is inherited from the existing full left-terminal
`E₃` divergence theorem.
-/
theorem exists_fixed_terminalSequence_h3Energy_escape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension u v T) :
    ∃ j₀ : Fin 3,
      ∃ τ : ℕ → ℝ,
        ∃ hτ :
          ∀ n : ℕ,
            τ n ∈ Set.Ioo a T
              ∧
            τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T,
          Tendsto τ atTop (𝓝 T)
            ∧
          Tendsto
            (
              fun n : ℕ =>
                velocityH3EnergyAt u (τ n)
            )
            atTop
            atTop := by

  obtain
    ⟨j₀, τ, hτ, hTauTendsto, _hFrontier⟩ :=
    exists_fixed_topDissipationAmplitude_or_energy_or_fixedExtendedHigherRadial_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
      hH3
      hClass
      hPhysical
      hCauchy
      hNoExtension

  have hTauLT :
      Tendsto τ atTop (𝓝[<] T) := by
    exact
      tendsto_nhdsWithin_iff.mpr
        ⟨
          hTauTendsto,
          Eventually.of_forall
            (fun n : ℕ => (hτ n).1.2)
        ⟩

  have hEnergy3Top :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3Energy3At u (τ n)
        )
        atTop
        atTop :=
    (
      velocityH3Energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
    ).comp hTauLT

  have hEnergyTop :
      Tendsto
        (
          fun n : ℕ =>
            velocityH3EnergyAt u (τ n)
        )
        atTop
        atTop := by

    refine tendsto_atTop.2 ?_

    intro M

    have hEventually :
        ∀ᶠ n : ℕ in atTop,
          M ≤ velocityH3Energy3At u (τ n) :=
      hEnergy3Top.eventually
        (eventually_ge_atTop M)

    filter_upwards [hEventually] with n hn

    exact
      hn.trans
        (
          velocityH3Energy3At_le_velocityH3EnergyAt
            u
            (τ n)
        )

  exact
    ⟨
      j₀,
      τ,
      hτ,
      hTauTendsto,
      hEnergyTop
    ⟩

/--
Neutral final formulation of the resolved-PDE scalar closure.

Either the H³ path extends smoothly through `T`, or there is an explicit
terminal sequence, localized at scale `1/(n+1)`, on which total H³ energy
diverges.  The sequence is the one inherited from the fully resolved
physical-PDE channel construction.
-/
theorem smoothContinuationExtension_or_fixed_terminalSequence_h3Energy_escape_after_resolvedPDEClosure
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath hH3 i)
    (hCauchy :
      H3TerminalVelocityRawFourierL2CauchyAtEndpoint hH3) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∃ j₀ : Fin 3,
        ∃ τ : ℕ → ℝ,
          ∃ hτ :
            ∀ n : ℕ,
              τ n ∈ Set.Ioo a T
                ∧
              τ n ∈
                Set.Ioo
                  (T - (1 : ℝ) / ((n : ℝ) + 1))
                  T,
            Tendsto τ atTop (𝓝 T)
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  velocityH3EnergyAt u (τ n)
              )
              atTop
              atTop
    ) := by

  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl hExtension

  · exact
      Or.inr
        (
          exists_fixed_terminalSequence_h3Energy_escape_after_resolvedPDEClosure_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noExtension
            hH3
            hClass
            hPhysical
            hCauchy
            hExtension
        )

end

end Euclidean
end Bridge
end PrimeTensor
