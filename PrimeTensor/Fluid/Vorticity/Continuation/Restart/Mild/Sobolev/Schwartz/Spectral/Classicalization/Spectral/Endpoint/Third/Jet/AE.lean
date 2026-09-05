import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Endpoint.Third.Symbol.Estimate

/-!
# Classicalization: endpoint estimate in actual third-jet coordinates

The pure frequency estimate now involves only the base Fourier difference and
the ordered third-derivative symbol differences.

For two genuine H³ snapshots, order-three Fourier compatibility identifies,
almost everywhere,

    symbol₃(i,k,l,ξ) * F₀(ξ) = F₃(i,k,l,ξ).

Applying this at both snapshots converts the third-symbol difference terms into
the actual ordered third-jet Fourier differences.  First- and second-order
compatibility are not used.

This is the final pointwise representation bridge before integration.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationSpectralEndpointThirdJetAE
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- For two Fourier-compatible H³ snapshots, the complete weighted base
difference is almost everywhere controlled by only the zeroth and ordered
third-jet Fourier differences. -/
theorem velocityH3WeightedBaseFourierRaw_sub_norm_sq_le_three_base_third_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t s : ℝ}
    {hIntT : VelocityH3IntegrableAt u t}
    {hMeasT : VelocityH3MeasurableAt u t}
    {hIntS : VelocityH3IntegrableAt u s}
    {hMeasS : VelocityH3MeasurableAt u s}
    (hFourierT :
      VelocityH3FourierCompatibleAt u t hIntT hMeasT)
    (hFourierS :
      VelocityH3FourierCompatibleAt u s hIntS hMeasS)
    (j : Fin 3) :
    (fun ξ : H3FourierPoint3 =>
      ‖velocityH3WeightedBaseFourierRaw
          u t hIntT hMeasT j ξ
          -
        velocityH3WeightedBaseFourierRaw
          u s hIntS hMeasS j ξ‖ ^ 2)
      ≤ᵐ[volume]
    (fun ξ : H3FourierPoint3 =>
      3 *
        (‖velocityH3FourierJetAt
              u t hIntT hMeasT (h3JetSlot0 j) ξ
              -
            velocityH3FourierJetAt
              u s hIntS hMeasS (h3JetSlot0 j) ξ‖ ^ 2
          +
         ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
           ‖velocityH3FourierJetAt
                u t hIntT hMeasT (h3JetSlot3 j i k l) ξ
                -
             velocityH3FourierJetAt
                u s hIntS hMeasS (h3JetSlot3 j i k l) ξ‖ ^ 2)) := by
  have h3T :=
    velocityH3FourierCompatibleAt_orderThree_all_ae
      hFourierT j

  have h3S :=
    velocityH3FourierCompatibleAt_orderThree_all_ae
      hFourierS j

  filter_upwards
    [h3T, h3S]
    with ξ h3Tξ h3Sξ

  unfold velocityH3WeightedBaseFourierRaw

  have h :=
    h3SobolevFrequencyWeight_mul_sub_norm_sq_le_three_base_third_symbol
      ξ
      (velocityH3BaseFourierAt
        u t hIntT hMeasT j ξ)
      (velocityH3BaseFourierAt
        u s hIntS hMeasS j ξ)

  simp_rw [h3Tξ, h3Sξ]

  simpa only [
    mul_sub,
    velocityH3BaseFourierAt
  ] using h

end

end Euclidean
end Bridge
end PrimeTensor
