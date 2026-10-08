import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Interpolation.Fourier.Moment.Cauchy
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Closure

/-!
# Absorb third-order energy into top-order dissipation

The established spatial interpolation E₃⁴ ≤ E₀ D₃³ implies, for K ≥ 0
and ε > 0,

  K E₃ ≤ ε D₃ + K⁴ E₀ / ε³.

Consequently any third-order transport estimate |T₃| ≤ K E₃ admits this
explicit dissipative bound. The coefficient K and the quartic remainder stay
visible. No terminal integrability or full-transport absorption is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- A polynomial Young estimate; no fractional powers are needed. -/
theorem h3_absorb_of_fourth_power_le
    {x b d ε : ℝ}
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hε : 0 < ε)
    (hPower : x ^ 4 ≤ b * d ^ 3) :
    x ≤ ε * d + b / ε ^ 3 := by
  apply le_of_not_gt
  intro hLarge
  have hQuot : 0 ≤ b / ε ^ 3 := div_nonneg hb (pow_nonneg hε.le _)
  have hProduct : 0 ≤ ε * d := mul_nonneg hε.le hd
  have hxd : ε * d < x := by linarith
  have hx : 0 < x := lt_of_le_of_lt hProduct hxd
  have hxb : b / ε ^ 3 < x := by linarith
  have hbUpper : b < x * ε ^ 3 :=
    (div_lt_iff₀ (pow_pos hε 3)).1 hxb
  have hdUpper : d ≤ x / ε := by
    apply (le_div_iff₀ hε).2
    nlinarith [hxd]
  have hCube : d ^ 3 ≤ (x / ε) ^ 3 :=
    pow_le_pow_left₀ hd hdUpper 3
  have hImpossible : x ^ 4 < x ^ 4 := calc
    x ^ 4 ≤ b * d ^ 3 := hPower
    _ ≤ b * (x / ε) ^ 3 := mul_le_mul_of_nonneg_left hCube hb
    _ < (x * ε ^ 3) * (x / ε) ^ 3 :=
      mul_lt_mul_of_pos_right hbUpper (pow_pos (div_pos hx hε) 3)
    _ = x ^ 4 := by
      field_simp [ne_of_gt hε] <;> ring
  exact (lt_irrefl (x ^ 4)) hImpossible

/-- Spatial Fourier interpolation spends an arbitrary positive fraction of D₃. -/
theorem mul_velocityH3Energy3At_le_dissipation3_add_quartic_remainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hK : 0 ≤ K) (hε : 0 < ε) :
    K * velocityH3Energy3At u t ≤
      ε * velocityH3Dissipation3At u t +
        K ^ 4 * velocityH3Energy0At u t / ε ^ 3 := by
  have hMoment :=
    velocityH3Energy3At_pow_four_le_energy0_mul_dissipation3_pow_three
      hH3 hClass ht
  have hScaled : (K * velocityH3Energy3At u t) ^ 4 ≤
      (K ^ 4 * velocityH3Energy0At u t) * velocityH3Dissipation3At u t ^ 3 := by
    simpa only [mul_pow, mul_assoc] using
      mul_le_mul_of_nonneg_left hMoment (pow_nonneg hK 4)
  exact h3_absorb_of_fourth_power_le
    (mul_nonneg (pow_nonneg hK 4) (velocityH3Energy0At_nonneg u t))
    (velocityH3Dissipation3At_nonneg u t) hε hScaled

/-- Apply the dissipative interpolation to an existing third-order transport bound. -/
theorem abs_velocityH3TransportDerivative3At_le_dissipation3_add_quartic_remainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t K ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hK : 0 ≤ K) (hε : 0 < ε)
    (hTransport : |velocityH3TransportDerivative3At u t| ≤
      K * velocityH3Energy3At u t) :
    |velocityH3TransportDerivative3At u t| ≤
      ε * velocityH3Dissipation3At u t +
        K ^ 4 * velocityH3Energy0At u t / ε ^ 3 := by
  exact le_trans hTransport
    (mul_velocityH3Energy3At_le_dissipation3_add_quartic_remainder
      hH3 hClass ht hK hε)

end Euclidean
end Bridge
end PrimeTensor
