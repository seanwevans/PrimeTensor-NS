import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySemigroup
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLerayRetardedIntegrability

/-!
# Restart identity for the Fin-indexed H³ heat--Leray Duhamel term

The pointwise nonlinear kernel now satisfies

    K_{a+b}(U,V) = H_b (K_a(U,V))

for positive `a` and nonnegative `b`, and the real-time retarded kernels are
genuinely Bochner interval integrable on the continuous path class.

This file performs the next algebraic step: split a Duhamel integral at an
intermediate time `a`.

For a target time `a+b`,

    D(a+b)
      = H_b D(a)
        + ∫_a^{a+b} K_{a+b-s}(U(s),V(s)) ds.

There is one endpoint subtlety.  On the first interval the shorter retarded
integrand is defined to be zero at `s = a`, while the longer integrand still
has lag `b`.  Thus the semigroup identity is used only on the open interval
`(0,a)`.  Since Lebesgue measure has no atoms,
`intervalIntegral.integral_congr_Ioo_of_le` is exactly the correct bridge.

The theorem keeps only the two genuine integrability assumptions needed:

* the long retarded integrand on `0..a+b`;
* the short retarded integrand on `0..a`.

The long assumption automatically splits at `a`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-! ## Pointwise restart before the intermediate endpoint -/

/--
For `s < a`, the long retarded integrand at target `a+b` is ordinary heat
evolution by time `b` of the short retarded integrand at target `a`.
-/
theorem h3SpectralFinHeatLerayDuhamelIntegrand_add_time
    {ν a b s : ℝ}
    (hν : 0 < ν)
    (hb : 0 ≤ b)
    (hs : s < a)
    (U V : ℝ → H3SpectralFinVectorState) :
    h3SpectralFinHeatLerayDuhamelIntegrand
        ν (a + b) hν U V s
      =
    h3SpectralVelocityHeatApplyNN
        ν (le_of_lt hν)
        (NNReal.mk b hb)
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν a hν U V s) := by
  have hlagA : 0 < a - s :=
    sub_pos.mpr hs
  have hlagAB : 0 < (a + b) - s := by
    linarith
  rw [
    h3SpectralFinHeatLerayDuhamelIntegrand,
    dif_pos hlagAB,
    h3SpectralFinHeatLerayDuhamelIntegrand,
    dif_pos hlagA
  ]
  have htime :
      (a + b) - s = (a - s) + b := by
    ring
  have hlagSum : 0 < (a - s) + b :=
    add_pos_of_pos_of_nonneg hlagA hb
  let Kpos : {r : ℝ // 0 < r} → H3SpectralFinVectorState :=
    fun r =>
      h3SpectralFinHeatLerayVelocityApply
        ν r.1 hν r.2 (U s) (V s)
  have hq :
      (⟨(a + b) - s, hlagAB⟩ : {r : ℝ // 0 < r})
        =
      ⟨(a - s) + b, hlagSum⟩ := by
    apply Subtype.ext
    exact htime
  have htransport :
      Kpos ⟨(a + b) - s, hlagAB⟩
        =
      Kpos ⟨(a - s) + b, hlagSum⟩ := by
    rw [hq]
  calc
    h3SpectralFinHeatLerayVelocityApply
        ν ((a + b) - s) hν hlagAB (U s) (V s)
        =
      h3SpectralFinHeatLerayVelocityApply
        ν ((a - s) + b) hν hlagSum (U s) (V s) := by
          exact htransport
    _ =
      h3SpectralVelocityHeatApplyNN
        ν (le_of_lt hν)
        (NNReal.mk b hb)
        (h3SpectralFinHeatLerayVelocityApply
          ν (a - s) hν hlagA (U s) (V s)) := by
      exact
        h3SpectralFinHeatLerayVelocityApply_add_time
          hν hlagA hb (U s) (V s)

/-! ## Integral restart identity -/

/--
Duhamel restart identity at an intermediate nonnegative time `a` with
additional elapsed time `b`.

The long integrability hypothesis is split automatically at `a`; the short
integrability hypothesis is exactly what permits the heat CLM to commute with
the first Bochner interval integral.
-/
theorem h3SpectralFinHeatLerayDuhamel_add_time
    {ν a b : ℝ}
    (hν : 0 < ν)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (U V : ℝ → H3SpectralFinVectorState)
    (hIntLong :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν (a + b) hν U V)
        volume
        0
        (a + b))
    (hIntShort :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν a hν U V)
        volume
        0
        a) :
    h3SpectralFinHeatLerayDuhamel
        ν (a + b) hν U V
      =
    h3SpectralVelocityHeatApplyNN
        ν (le_of_lt hν)
        (NNReal.mk b hb)
        (h3SpectralFinHeatLerayDuhamel
          ν a hν U V)
      +
    ∫ s in a..(a + b),
      h3SpectralFinHeatLerayDuhamelIntegrand
        ν (a + b) hν U V s := by
  let fLong : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelIntegrand
      ν (a + b) hν U V
  let fShort : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelIntegrand
      ν a hν U V
  let H :
      H3SpectralFinVectorState →L[ℝ]
        H3SpectralFinVectorState :=
    h3SpectralVelocityHeatCLM
      ν (le_of_lt hν) (NNReal.mk b hb)

  have hab : 0 ≤ a + b := by
    linarith

  have haMem :
      a ∈ Set.uIcc (0 : ℝ) (a + b) := by
    rw [Set.uIcc_of_le hab]
    exact ⟨ha, by linarith⟩

  have hLongSplit :
      IntervalIntegrable fLong volume 0 a ∧
        IntervalIntegrable fLong volume a (a + b) := by
    exact
      (IntervalIntegrable.trans_iff haMem).1
        hIntLong

  have hFirstPointwise :
      Set.EqOn
        fLong
        (fun s => H (fShort s))
        (Set.Ioo (0 : ℝ) a) := by
    intro s hs
    dsimp [fLong, fShort, H]
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_add_time
        hν hb hs.2 U V

  have hFirstIntegral :
      (∫ s in (0 : ℝ)..a, fLong s)
        =
      H (∫ s in (0 : ℝ)..a, fShort s) := by
    calc
      (∫ s in (0 : ℝ)..a, fLong s)
          =
        ∫ s in (0 : ℝ)..a, H (fShort s) := by
          exact
            intervalIntegral.integral_congr_Ioo_of_le
              ha hFirstPointwise
      _ =
        H (∫ s in (0 : ℝ)..a, fShort s) := by
          exact
            H.intervalIntegral_comp_comm hIntShort

  unfold h3SpectralFinHeatLerayDuhamel
  change
    (∫ s in (0 : ℝ)..(a + b), fLong s)
      =
    H (∫ s in (0 : ℝ)..a, fShort s)
      +
    ∫ s in a..(a + b), fLong s

  calc
    (∫ s in (0 : ℝ)..(a + b), fLong s)
        =
      (∫ s in (0 : ℝ)..a, fLong s)
        +
      ∫ s in a..(a + b), fLong s := by
          exact
            (intervalIntegral.integral_add_adjacent_intervals
              hLongSplit.1 hLongSplit.2).symm
    _ =
      H (∫ s in (0 : ℝ)..a, fShort s)
        +
      ∫ s in a..(a + b), fLong s := by
          rw [hFirstIntegral]

end

end Euclidean
end Bridge
end PrimeTensor
