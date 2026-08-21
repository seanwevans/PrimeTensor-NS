import PrimeTensor.Analysis.Growth

/-!
# End-to-end response growth for positive-depth powers

A positive-depth power consumes a finite number of intrinsic refinement levels.
We encode that loss without subtraction and without a zeroth depth.

`powerInput d level` is the input scale sufficient to control the `d`-power
at `level`.

`powerOutput d level` is the scale left after paying the finite refinement
cost of the `d`-power, floored at the first positive scale.

These two transforms let us prove that every positive-depth power satisfies
`ResponseScaleControlledAt`.
-/

namespace PrimeTensor

namespace Depth

/--
Input refinement required for a positive-depth power.

Power depth `one` costs no refinement.  Every additional multiplicative factor
requires one additional input refinement.
-/
def powerInput : Depth → Depth → Depth
  | .one, level => level
  | .succ d, level => powerInput d (.succ level)

/--
Output scale remaining after the finite refinement cost of a positive-depth
power has been paid.

There is no scale below `one`; insufficient input depth saturates at `one`.
-/
def powerOutput : Depth → Depth → Depth
  | .one, level => level
  | .succ d, .one => .one
  | .succ d, .succ level => powerOutput d level

/-- `powerInput` commutes with successor. -/
theorem powerInput_succ :
    ∀ d level : Depth,
      powerInput d (.succ level) = .succ (powerInput d level)
  | .one, level => rfl
  | .succ d, level => by
      change
        powerInput d (.succ (.succ level)) =
          .succ (powerInput d (.succ level))
      exact powerInput_succ d (.succ level)

/-- A required power-input scale is always at or after its requested output scale. -/
theorem powerInput_atOrAfter :
    ∀ d level : Depth,
      AtOrAfter level (powerInput d level)
  | .one, level => .here level
  | .succ d, level => by
      exact atOrAfter_trans
        (.later (.here level))
        (powerInput_atOrAfter d (.succ level))

/--
`powerInput` after `powerOutput` is exactly the join of the supplied scale and
the minimum scale needed by that power.
-/
theorem powerInput_output_join :
    ∀ d level : Depth,
      powerInput d (powerOutput d level) =
        join level (powerInput d .one)
  | .one, .one => rfl
  | .one, .succ level => rfl
  | .succ d, .one => rfl
  | .succ d, .succ level => by
      calc
        powerInput (.succ d) (powerOutput (.succ d) (.succ level))
            = powerInput d (.succ (powerOutput d level)) := rfl
        _ = .succ (powerInput d (powerOutput d level)) :=
            powerInput_succ d (powerOutput d level)
        _ = .succ (join level (powerInput d .one)) :=
            congrArg Depth.succ (powerInput_output_join d level)
        _ = join (.succ level) (.succ (powerInput d .one)) := rfl
        _ = join (.succ level) (powerInput (.succ d) .one) := by
            rw [show powerInput (.succ d) .one =
              .succ (powerInput d .one) from powerInput_succ d .one]

/-- Advancing the base scale preserves tail order. -/
theorem advance_base_atOrAfter {a b : Depth}
    (hab : AtOrAfter a b) :
    ∀ gain : Depth,
      AtOrAfter (advance a gain) (advance b gain)
  | .one => succ_atOrAfter hab
  | .succ gain =>
      succ_atOrAfter (advance_base_atOrAfter hab gain)

/-- Advancing a successor base is the successor of advancing the base. -/
theorem advance_succ_base :
    ∀ level gain : Depth,
      advance (.succ level) gain =
        .succ (advance level gain)
  | level, .one => rfl
  | level, .succ gain =>
      congrArg Depth.succ (advance_succ_base level gain)

/--
Paying a power refinement cost before or after a common advance gives the same
final scale.
-/
theorem advance_powerInput_comm :
    ∀ d level gain : Depth,
      advance (powerInput d level) gain =
        advance level (powerInput d gain)
  | .one, level, gain => rfl
  | .succ d, level, gain => by
      calc
        advance (powerInput (.succ d) level) gain
            = advance (.succ (powerInput d level)) gain := by
                rw [show powerInput (.succ d) level =
                  .succ (powerInput d level) from powerInput_succ d level]
        _ = .succ (advance (powerInput d level) gain) :=
            advance_succ_base (powerInput d level) gain
        _ = .succ (advance level (powerInput d gain)) :=
            congrArg Depth.succ (advance_powerInput_comm d level gain)
        _ = advance level (.succ (powerInput d gain)) := rfl
        _ = advance level (powerInput (.succ d) gain) := by
            rw [show powerInput (.succ d) gain =
              .succ (powerInput d gain) from powerInput_succ d gain]

/-- A join is definitionally one of its two positive-depth inputs. -/
theorem join_eq_left_or_right :
    ∀ a b : Depth,
      join a b = a ∨ join a b = b
  | .one, b => Or.inr rfl
  | .succ a, .one => Or.inl rfl
  | .succ a, .succ b => by
      rcases join_eq_left_or_right a b with h | h
      · exact Or.inl (congrArg Depth.succ h)
      · exact Or.inr (congrArg Depth.succ h)

end Depth

namespace MulReal

/-- If the same pair is near at two scales, it is near at their joined scale. -/
theorem scaleNear_join {a b : Depth} {x y : MulReal}
    (ha : ScaleNear a x y)
    (hb : ScaleNear b x y) :
    ScaleNear (Depth.join a b) x y := by
  rcases Depth.join_eq_left_or_right a b with h | h
  · rw [h]
    exact ha
  · rw [h]
    exact hb

/-- Positive-depth powers distribute over multiplication. -/
theorem depthPow_mul (a b : MulReal) :
    ∀ d : Depth,
      depthPow (a * b) d =
        depthPow a d * depthPow b d
  | .one => rfl
  | .succ d => by
      change
        (a * b) * depthPow (a * b) d =
          (a * depthPow a d) * (b * depthPow b d)
      rw [depthPow_mul a b d]
      exact mul_four_shuffle
        a b
        (depthPow a d)
        (depthPow b d)

/--
A positive-depth power consumes exactly the finite refinement budget encoded by
`Depth.powerInput`.
-/
theorem scaleNear_depthPow (h : MulReal) :
    ∀ d level : Depth,
      ScaleNear (Depth.powerInput d level) h 1 →
      ScaleNear level (depthPow h d) 1
  | .one, level, hh => by
      exact hh
  | .succ d, level, hh => by
      have hbase :
          ScaleNear (.succ level) h 1 :=
        scaleNear_weaken
          (Depth.powerInput_atOrAfter d (.succ level))
          hh

      have hpow :
          ScaleNear (.succ level) (depthPow h d) 1 :=
        scaleNear_depthPow h d (.succ level) hh

      have hprod := scaleNear_mul hbase hpow
      rw [one_mul] at hprod
      exact hprod

end MulReal

namespace MulDifferential

/-- The response of a positive-depth power is exactly the same power of the perturbation. -/
theorem response_depthPow
    (x : MulReal) (h : MulReal.Seq) (d : Depth) :
    ∀ n : Depth,
      response (fun y => MulReal.depthPow y d) x h n =
        MulReal.depthPow (h n) d := by
  intro n
  unfold response
  change
    MulReal.ratio
      (MulReal.depthPow (x * h n) d)
      (MulReal.depthPow x d) =
        MulReal.depthPow (h n) d
  rw [MulReal.depthPow_mul]
  exact MulReal.ratio_mul_base
    (MulReal.depthPow x d)
    (MulReal.depthPow (h n) d)

/--
Every positive-depth power has primitive response-scale control.
-/
theorem responseScaleControlledAt_depthPow
    (x : MulReal) :
    ∀ d : Depth,
      ResponseScaleControlledAt
        (fun y => MulReal.depthPow y d)
        x := by
  intro d h hh targetGain

  obtain ⟨anchor, hbudget⟩ :=
    hh (Depth.powerInput d .one)

  refine ⟨Depth.powerInput d targetGain, anchor, ?_⟩
  intro n hn level hbase

  have hminimum :
      MulReal.ScaleNear
        (Depth.powerInput d .one)
        (h n) 1 :=
    hbudget n hn

  have hjoined :
      MulReal.ScaleNear
        (Depth.join level (Depth.powerInput d .one))
        (h n) 1 :=
    MulReal.scaleNear_join hbase hminimum

  let responseLevel := Depth.powerOutput d level
  refine ⟨responseLevel, ?_, ?_⟩

  · have hinput :
        MulReal.ScaleNear
          (Depth.powerInput d responseLevel)
          (h n) 1 := by
      dsimp [responseLevel]
      rw [Depth.powerInput_output_join]
      exact hjoined

    have hpower :
        MulReal.ScaleNear responseLevel
          (MulReal.depthPow (h n) d) 1 :=
      MulReal.scaleNear_depthPow
        (h n) d responseLevel hinput

    rw [response_depthPow x h d n]
    exact hpower

  · have hlevel :
        Depth.AtOrAfter
          level
          (Depth.powerInput d responseLevel) := by
      dsimp [responseLevel]
      rw [Depth.powerInput_output_join]
      exact Depth.left_atOrAfter
        level
        (Depth.powerInput d .one)

    have hadv :=
      Depth.advance_base_atOrAfter hlevel targetGain

    rw [Depth.advance_powerInput_comm
      d responseLevel targetGain] at hadv

    exact hadv

/--
Positive-depth powers now satisfy the full user-facing chain-rule hypotheses:
derivative, tangent control, and response-scale control.
-/
theorem hasMulDerivativeAt_comp_depthPow
    {g : MulReal → MulReal}
    {x : MulReal}
    {Dg : MulTangentMap}
    (d : Depth)
    (hg :
      HasMulDerivativeAt g
        (MulReal.depthPow x d)
        Dg)
    (hDg : Dg.ScaleControlled) :
    HasMulDerivativeAt
      (fun y => g (MulReal.depthPow y d))
      x
      (MulTangentMap.comp
        Dg
        (MulTangentMap.depthPow d)) := by
  exact hasMulDerivativeAt_comp_of_responseScaleControlled
    (hasMulDerivativeAt_depthPow x d)
    (MulTangentMap.scaleControlled_depthPow d)
    (responseScaleControlledAt_depthPow x d)
    hg
    hDg

end MulDifferential

end PrimeTensor
