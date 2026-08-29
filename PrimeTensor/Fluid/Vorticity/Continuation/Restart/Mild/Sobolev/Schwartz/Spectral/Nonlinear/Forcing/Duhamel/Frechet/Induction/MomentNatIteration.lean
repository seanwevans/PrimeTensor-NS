import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.MomentComposedSuccessor

/-!
# Fréchet endpoint induction: finite natural iteration

`MomentComposedSuccessor` closes the reusable analytic step

    M_n on [a/4,t]  ->  M_{n+1} on [a,t].

This file iterates that theorem an arbitrary finite number of times.  To keep
the interval bookkeeping definitionally simple, define the required starting
time recursively:

    backstep 0 a       = a,
    backstep (k+1) a   = backstep k (a/4).

Thus `k` successor steps consume a natural `n` slab beginning at
`backstep k a` and produce a natural `n+k` slab beginning at `a`.

The numerical state and Duhamel budgets are existentially packaged here.
Every individual successor still has the explicit budgets proved in
`MomentComposedSuccessor`; the finite iteration only needs the fact that such
finite bounds exist.  This keeps the induction statement independent of a
large recursively nested budget expression.

No new Fourier, heat, convolution, or Fubini estimate occurs in this file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-!
## Recursive positive-time backstep
-/

/-- Lower endpoint required before `k` complete natural-moment successor
steps whose final lower endpoint is `a`. -/
noncomputable def h3SelectedMomentBackstep : ℕ → ℝ → ℝ
  | 0, a => a
  | k + 1, a => h3SelectedMomentBackstep k (a / 4)

/-- The recursively shifted lower endpoint remains strictly positive. -/
theorem h3SelectedMomentBackstep_pos
    (k : ℕ)
    {a : ℝ}
    (ha : 0 < a) :
    0 < h3SelectedMomentBackstep k a := by
  induction k generalizing a with
  | zero =>
      simpa [h3SelectedMomentBackstep] using ha
  | succ k ih =>
      rw [h3SelectedMomentBackstep]
      exact ih (by positivity)

/-!
## Arbitrary finite natural iteration
-/

/-- Iterate the complete natural successor an arbitrary finite number of
times.

Starting from a natural `n` slab at the recursively earlier positive time
`h3SelectedMomentBackstep k a`, one obtains a natural `n+k` slab on `[a,t]`.
The output state and Duhamel bounds are finite witnesses assembled from the
explicit one-step budgets. -/
theorem h3SelectedMomentSlab_nat_iterate
    {ν A a t BState BDuhamel B0 : ℝ}
    (n k : ℕ)
    (hn : 1 ≤ n)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hSlab :
      H3SelectedMomentSlab
        (n : ℝ) ν A
        (h3SelectedMomentBackstep k a) t
        BState BDuhamel B0
        hν U₀ hA hU₀) :
    ∃ BState' BDuhamel' : ℝ,
      H3SelectedMomentSlab
        ((n + k : ℕ) : ℝ)
        ν A a t
        BState' BDuhamel' B0
        hν U₀ hA hU₀ := by
  induction k generalizing a BState BDuhamel with
  | zero =>
      refine ⟨BState, BDuhamel, ?_⟩
      simpa [h3SelectedMomentBackstep] using hSlab

  | succ k ih =>
      have ha4 : 0 < a / 4 := by
        positivity

      have hat4 : a / 4 ≤ t := by
        linarith

      have hInput :
          H3SelectedMomentSlab
            (n : ℝ) ν A
            (h3SelectedMomentBackstep k (a / 4)) t
            BState BDuhamel B0
            hν U₀ hA hU₀ := by
        simpa only [h3SelectedMomentBackstep] using hSlab

      obtain ⟨BStateK, BDuhamelK, hK⟩ :=
        ih
          (a := a / 4)
          (BState := BState)
          (BDuhamel := BDuhamel)
          ha4 hat4 hInput

      have hnk : 1 ≤ n + k := by
        omega

      have hSucc :=
        h3SelectedMomentSlab_nat_to_natSucc
          (n + k) hnk
          hν U₀ hA hU₀
          ha hat htR hK

      refine
        ⟨h3SelectedNatSuccessorStateBudget
            (n + k) ν A a t BStateK BDuhamelK B0,
          h3SelectedNatSuccessorDuhamelBudget
            (n + k) ν A a t BStateK BDuhamelK B0,
          ?_⟩

      simpa only [
        Nat.add_succ,
        Nat.cast_succ,
        Nat.cast_add,
        Nat.cast_one
      ] using hSucc

/-!
## Order-one seed formulation
-/

/-- Convenient specialization of finite iteration to an order-one seed.

For every natural target `m ≥ 1`, an order-one slab beginning at
`backstep (m-1) a` yields an order-`m` slab on `[a,t]`.  A later base-slab
file only has to supply the order-one hypothesis at arbitrary positive lower
endpoint; all higher natural moments then follow from this theorem. -/
theorem h3SelectedMomentSlab_one_to_nat
    {ν A a t BState BDuhamel B0 : ℝ}
    (m : ℕ)
    (hm : 1 ≤ m)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hSlab :
      H3SelectedMomentSlab
        (1 : ℝ) ν A
        (h3SelectedMomentBackstep (m - 1) a) t
        BState BDuhamel B0
        hν U₀ hA hU₀) :
    ∃ BState' BDuhamel' : ℝ,
      H3SelectedMomentSlab
        (m : ℝ)
        ν A a t
        BState' BDuhamel' B0
        hν U₀ hA hU₀ := by
  have hSlabNat :
      H3SelectedMomentSlab
        (((1 : ℕ) : ℝ)) ν A
        (h3SelectedMomentBackstep (m - 1) a) t
        BState BDuhamel B0
        hν U₀ hA hU₀ := by
    simpa using hSlab

  have hIter :=
    h3SelectedMomentSlab_nat_iterate
      (BState := BState)
      (BDuhamel := BDuhamel)
      (B0 := B0)
      (1 : ℕ) (m - 1) (by norm_num)
      hν U₀ hA hU₀
      ha hat htR hSlabNat

  obtain ⟨BState', BDuhamel', hOut⟩ := hIter

  refine ⟨BState', BDuhamel', ?_⟩

  have hmNat :
      1 + (m - 1) = m := by
    omega

  simpa only [hmNat] using hOut

end
end Euclidean
end Bridge
end PrimeTensor
