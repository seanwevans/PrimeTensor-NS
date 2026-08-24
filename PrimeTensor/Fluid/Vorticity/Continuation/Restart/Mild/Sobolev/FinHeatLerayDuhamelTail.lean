import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLerayDuhamelRestart

/-!
# Restart-tail estimate for the Fin-indexed H³ Duhamel term

The restart identity isolates the genuinely new part of the Volterra history:

    ∫_a^{a+b} K_{a+b-s}(U(s),V(s)) ds.

This file identifies that tail with an ordinary length-`b` Duhamel term for
the translated paths

    q ↦ U(q+a),   q ↦ V(q+a).

Translation preserves Lebesgue interval integrals, so no Jacobian factor
appears.  The already-proved Duhamel estimate can therefore be reused
verbatim, giving the crucial `O(sqrt b)` restart-tail bound.

This is the quantitative input needed for continuity of the variable-target
Volterra map.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-! ## Translation of the retarded integrand -/

/--
Translating both the source time and the input paths converts the tail kernel
at target `a+b` into the ordinary retarded kernel at target `b`.
-/
theorem h3SpectralFinHeatLerayDuhamelIntegrand_shift
    {ν a b q : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState) :
    h3SpectralFinHeatLerayDuhamelIntegrand
        ν (a + b) hν U V (q + a)
      =
    h3SpectralFinHeatLerayDuhamelIntegrand
        ν b hν
        (fun r => U (r + a))
        (fun r => V (r + a))
        q := by
  unfold h3SpectralFinHeatLerayDuhamelIntegrand
  have hlag :
      (a + b) - (q + a) = b - q := by
    ring
  by_cases hq : 0 < b - q
  · have hlong : 0 < (a + b) - (q + a) := by
      linarith
    rw [dif_pos hlong, dif_pos hq]
    calc
      h3SpectralFinHeatLerayVelocityApply
          ν ((a + b) - (q + a)) hν hlong
          (U (q + a)) (V (q + a))
          =
        h3SpectralFinHeatLerayVelocityApplyZero
          ν ((a + b) - (q + a)) hν
          (U (q + a)) (V (q + a)) := by
            symm
            exact
              h3SpectralFinHeatLerayVelocityApplyZero_of_pos
                hν hlong (U (q + a)) (V (q + a))
      _ =
        h3SpectralFinHeatLerayVelocityApplyZero
          ν (b - q) hν
          (U (q + a)) (V (q + a)) := by
            rw [hlag]
      _ =
        h3SpectralFinHeatLerayVelocityApply
          ν (b - q) hν hq
          (U (q + a)) (V (q + a)) := by
            exact
              h3SpectralFinHeatLerayVelocityApplyZero_of_pos
                hν hq (U (q + a)) (V (q + a))
  · have hlong : ¬ 0 < (a + b) - (q + a) := by
      linarith
    rw [dif_neg hlong, dif_neg hq]

/-! ## Tail as a translated ordinary Duhamel term -/

/--
The restart tail on `a..a+b` is exactly the ordinary length-`b` Duhamel term
for the translated paths.
-/
theorem h3SpectralFinHeatLerayDuhamel_tail_eq_shifted
    {ν a b : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState) :
    (∫ s in a..(a + b),
      h3SpectralFinHeatLerayDuhamelIntegrand
        ν (a + b) hν U V s)
      =
    h3SpectralFinHeatLerayDuhamel
      ν b hν
      (fun q => U (q + a))
      (fun q => V (q + a)) := by
  unfold h3SpectralFinHeatLerayDuhamel
  calc
    (∫ s in a..(a + b),
      h3SpectralFinHeatLerayDuhamelIntegrand
        ν (a + b) hν U V s)
        =
      ∫ q in (0 : ℝ)..b,
        h3SpectralFinHeatLerayDuhamelIntegrand
          ν (a + b) hν U V (q + a) := by
            symm
            simpa [add_comm, add_left_comm, add_assoc] using
              (intervalIntegral.integral_comp_add_right
                (f :=
                  h3SpectralFinHeatLerayDuhamelIntegrand
                    ν (a + b) hν U V)
                (a := (0 : ℝ))
                (b := b)
                a)
    _ =
      ∫ q in (0 : ℝ)..b,
        h3SpectralFinHeatLerayDuhamelIntegrand
          ν b hν
          (fun r => U (r + a))
          (fun r => V (r + a))
          q := by
            apply intervalIntegral.integral_congr
            intro q _hq
            exact
              h3SpectralFinHeatLerayDuhamelIntegrand_shift
                hν U V

/-! ## Quantitative restart-tail bound -/

/--
For continuous globally bounded real-time paths, the restart tail over a new
time interval of length `b ≥ 0` has the same `sqrt b` bound as an ordinary
Duhamel term.
-/
theorem norm_h3SpectralFinHeatLerayDuhamel_tail_le
    {ν a b MU MV : ℝ}
    (hν : 0 < ν)
    (hb : 0 ≤ b)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV) :
    ‖∫ s in a..(a + b),
        h3SpectralFinHeatLerayDuhamelIntegrand
          ν (a + b) hν U V s‖
      ≤
    h3HeatLerayDuhamelCoefficient ν *
      Real.sqrt b * MU * MV := by
  let Ua : ℝ → H3SpectralFinVectorState :=
    fun q => U (q + a)
  let Va : ℝ → H3SpectralFinVectorState :=
    fun q => V (q + a)

  have hUaCont : Continuous Ua := by
    dsimp [Ua]
    exact
      hUcont.comp
        (continuous_id.add continuous_const)

  have hVaCont : Continuous Va := by
    dsimp [Va]
    exact
      hVcont.comp
        (continuous_id.add continuous_const)

  have hUa :
      ∀ q ∈ Set.Ioc (0 : ℝ) b,
        ‖Ua q‖ ≤ MU := by
    intro q _hq
    exact hU (q + a)

  have hVa :
      ∀ q ∈ Set.Ioc (0 : ℝ) b,
        ‖Va q‖ ≤ MV := by
    intro q _hq
    exact hV (q + a)

  have hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν b hν Ua Va)
        volume
        0
        b :=
    h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
      hν hb hMU hMV Ua Va
      hUaCont hVaCont hUa hVa

  have hDuhamel :
      ‖h3SpectralFinHeatLerayDuhamel
          ν b hν Ua Va‖
        ≤
      h3HeatLerayDuhamelCoefficient ν *
        Real.sqrt b * MU * MV :=
    norm_h3SpectralFinHeatLerayDuhamel_le
      hν hb hMU hMV Ua Va
      hInt hUa hVa

  rw [
    h3SpectralFinHeatLerayDuhamel_tail_eq_shifted
      hν U V
  ]
  exact hDuhamel

end

end Euclidean
end Bridge
end PrimeTensor
