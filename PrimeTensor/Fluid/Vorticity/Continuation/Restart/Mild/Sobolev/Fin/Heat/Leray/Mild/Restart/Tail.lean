import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Overlap.Path
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Duhamel.Restart

/-!
# Restarting an origin-based finite H³ heat--Leray mild solution

The physical overlap theorem asks for a mild identity restarted at the left
endpoint of the overlap interval.  A classical solution, once converted to a
spectral mild solution, is more naturally first obtained in origin-based form

    W(t) = H_t U₀ - D_t(W,W).

Combining the heat semigroup law with the positive Duhamel split at an
intermediate time `a` gives the correctly signed restart identity

    W(a+b)
      = H_b (W(a))
          - ∫ s in a..a+b, K_{a+b-s}(W(s),W(s)) ds.

The positive heat--Leray Duhamel object itself is unchanged; only its sign in
the Navier--Stokes mild equation is negative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-- Fixed-time spectral heat evolution respects subtraction. -/
theorem h3SpectralVelocityHeatApplyNN_sub_restart
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (t : ℝ≥0)
    (U V : H3SpectralVelocityState) :
    h3SpectralVelocityHeatApplyNN ν hν t (U - V)
      =
    h3SpectralVelocityHeatApplyNN ν hν t U
      -
    h3SpectralVelocityHeatApplyNN ν hν t V := by
  change
    h3SpectralVelocityHeatCLM ν hν t (U - V)
      =
    h3SpectralVelocityHeatCLM ν hν t U
      -
    h3SpectralVelocityHeatCLM ν hν t V
  rw [map_sub]

/--
Two origin-based signed mild identities, at `a` and `a+b`, imply the tail-form
restart identity at `a`.
-/
theorem h3SpectralFinHeatLerayMild_restart_tail
    {ν a b : ℝ}
    (hν : 0 < ν)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (Uinit : H3SpectralVelocityState)
    (W : ℝ → H3SpectralFinVectorState)
    (hMildA :
      h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk a ha) Uinit
        -
      h3SpectralFinHeatLerayDuhamel
          ν a hν W W
        =
      W a)
    (hMildAB :
      h3SpectralVelocityHeatApplyNN
          ν hν.le
          (NNReal.mk a ha + NNReal.mk b hb)
          Uinit
        -
      h3SpectralFinHeatLerayDuhamel
          ν (a + b) hν W W
        =
      W (a + b))
    (hIntLong :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν (a + b) hν W W)
        volume
        0
        (a + b))
    (hIntShort :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν a hν W W)
        volume
        0
        a) :
    h3SpectralVelocityHeatApplyNN
        ν hν.le (NNReal.mk b hb) (W a)
      -
    ∫ s in a..(a + b),
      h3SpectralFinHeatLerayDuhamelIntegrand
        ν (a + b) hν W W s
      =
    W (a + b) := by

  have hDuhamelRestart :=
    h3SpectralFinHeatLerayDuhamel_add_time
      hν ha hb W W hIntLong hIntShort

  have hHeatSemigroup :=
    h3SpectralVelocityHeatApplyNN_add_time
      ν hν.le
      (NNReal.mk a ha)
      (NNReal.mk b hb)
      Uinit

  calc
    h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk b hb) (W a)
        -
      ∫ s in a..(a + b),
        h3SpectralFinHeatLerayDuhamelIntegrand
          ν (a + b) hν W W s
        =
      h3SpectralVelocityHeatApplyNN
          ν hν.le (NNReal.mk b hb)
          (
            h3SpectralVelocityHeatApplyNN
                ν hν.le (NNReal.mk a ha) Uinit
              -
            h3SpectralFinHeatLerayDuhamel
                ν a hν W W
          )
        -
      ∫ s in a..(a + b),
        h3SpectralFinHeatLerayDuhamelIntegrand
          ν (a + b) hν W W s := by
            rw [hMildA]
    _ =
      (
        h3SpectralVelocityHeatApplyNN
            ν hν.le (NNReal.mk b hb)
            (h3SpectralVelocityHeatApplyNN
              ν hν.le (NNReal.mk a ha) Uinit)
          -
        h3SpectralVelocityHeatApplyNN
            ν hν.le (NNReal.mk b hb)
            (h3SpectralFinHeatLerayDuhamel
              ν a hν W W)
      )
        -
      ∫ s in a..(a + b),
        h3SpectralFinHeatLerayDuhamelIntegrand
          ν (a + b) hν W W s := by
            rw [h3SpectralVelocityHeatApplyNN_sub_restart]
    _ =
      h3SpectralVelocityHeatApplyNN
          ν hν.le
          (NNReal.mk a ha + NNReal.mk b hb)
          Uinit
        -
      (
        h3SpectralVelocityHeatApplyNN
            ν hν.le (NNReal.mk b hb)
            (h3SpectralFinHeatLerayDuhamel
              ν a hν W W)
          +
        ∫ s in a..(a + b),
          h3SpectralFinHeatLerayDuhamelIntegrand
            ν (a + b) hν W W s
      ) := by
            rw [hHeatSemigroup]
            abel
    _ =
      h3SpectralVelocityHeatApplyNN
          ν hν.le
          (NNReal.mk a ha + NNReal.mk b hb)
          Uinit
        -
      h3SpectralFinHeatLerayDuhamel
          ν (a + b) hν W W := by
            rw [hDuhamelRestart]
    _ = W (a + b) := hMildAB

/--
Uniform origin-based form: if the same spectral path satisfies the signed mild
formula at every nonnegative time under consideration, then every interior
restart automatically satisfies the signed tail-form restart identity.
-/
theorem h3SpectralFinHeatLerayMild_restart_tail_of_forall
    {ν a b : ℝ}
    (hν : 0 < ν)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (Uinit : H3SpectralVelocityState)
    (W : ℝ → H3SpectralFinVectorState)
    (hMild :
      ∀ (t : ℝ) (ht : 0 ≤ t),
        h3SpectralVelocityHeatApplyNN
            ν hν.le (NNReal.mk t ht) Uinit
          -
        h3SpectralFinHeatLerayDuhamel
            ν t hν W W
          =
        W t)
    (hIntLong :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν (a + b) hν W W)
        volume
        0
        (a + b))
    (hIntShort :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν a hν W W)
        volume
        0
        a) :
    h3SpectralVelocityHeatApplyNN
        ν hν.le (NNReal.mk b hb) (W a)
      -
    ∫ s in a..(a + b),
      h3SpectralFinHeatLerayDuhamelIntegrand
        ν (a + b) hν W W s
      =
    W (a + b) := by

  have hab : 0 ≤ a + b := add_nonneg ha hb

  have hMildA := hMild a ha
  have hMildAB := hMild (a + b) hab

  have hNN :
      NNReal.mk (a + b) hab
        =
      NNReal.mk a ha + NNReal.mk b hb := by
    apply Subtype.ext
    simp

  rw [hNN] at hMildAB

  exact
    h3SpectralFinHeatLerayMild_restart_tail
      hν ha hb Uinit W
      hMildA hMildAB
      hIntLong hIntShort

end

end Euclidean
end Bridge
end PrimeTensor
