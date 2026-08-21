import PrimeTensor.Fluid.Vorticity.H3.Energy.Pressure

/-!
# Three-axis finite-sum bridge

The fluid bridge uses the project's positive-dimensional recursive axis fold,
while the H³ energy uses Mathlib finite sums.  In dimension three these are
the same three coordinates.

This tiny module isolates that representation bridge so subsequent
differentiated-incompressibility proofs do not depend on how the `Fintype`
instance for `Axis` is chosen.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open scoped BigOperators

noncomputable local instance axisFintypeH3AxisSum
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

noncomputable local instance axisDecidableEqH3AxisSum
    (d : Depth) :
    DecidableEq (PrimeTensor.Axis d) :=
  Classical.decEq
    (PrimeTensor.Axis d)

/--
`Finset.univ` on the three-dimensional positive axis consists exactly of the
three named Euclidean coordinates.
-/
theorem axis_univ_three :
    (Finset.univ :
      Finset (PrimeTensor.Axis Depth.three))
      =
    {xAxis, yAxis, zAxis} := by

  classical

  ext i

  cases i with
  | first =>
      simp [xAxis, yAxis, zAxis]

  | next i =>
      cases i with
      | first =>
          constructor

          · intro h

            change
              yAxis ∈
                {xAxis, yAxis, zAxis}

            exact
              Finset.mem_insert_of_mem
                (
                  Finset.mem_insert_self
                    yAxis
                    {zAxis}
                )

          · intro h
            exact
              Finset.mem_univ _

      | next i =>
          cases i with
          | first =>
              constructor

              · intro h

                change
                  zAxis ∈
                    {xAxis, yAxis, zAxis}

                exact
                  Finset.mem_insert_of_mem
                    (
                      Finset.mem_insert_of_mem
                        (
                          Finset.mem_singleton_self
                            zAxis
                        )
                    )

              · intro h

                exact
                  Finset.mem_univ _

/--
Recursive ordinal of a positive axis: the outermost `first` is rank zero,
and each `next` increases the rank by one.
-/
def axisRank :
    {d : Depth} →
      PrimeTensor.Axis d →
      Nat
  | _, .first =>
      0
  | _, .next i =>
      axisRank i + 1

/--
A conventional finite sum over the three axes has the same association as
`axis_fold_three`.
-/
theorem axis_sum_three
    {A : Type}
    [AddCommMonoid A]
    (f : PrimeTensor.Axis Depth.three → A) :
    (∑ i : PrimeTensor.Axis Depth.three, f i)
      =
    f xAxis + (f yAxis + f zAxis) := by

  classical

  rw [axis_univ_three]

  have hxy :
      xAxis ≠ yAxis := by

    intro h

    change
      (PrimeTensor.Axis.first :
        PrimeTensor.Axis Depth.three)
        =
      PrimeTensor.Axis.next
        (PrimeTensor.Axis.first :
          PrimeTensor.Axis Depth.two)
      at h

    cases h

  have hxz :
      xAxis ≠ zAxis := by

    intro h

    change
      (PrimeTensor.Axis.first :
        PrimeTensor.Axis Depth.three)
        =
      PrimeTensor.Axis.next
        (
          PrimeTensor.Axis.next
            (PrimeTensor.Axis.first :
              PrimeTensor.Axis Depth.one)
        )
      at h

    cases h

  have hyz :
      yAxis ≠ zAxis := by

    intro h

    have hRank :=
      congrArg
        (fun i : PrimeTensor.Axis Depth.three =>
          axisRank i)
        h

    norm_num [axisRank, yAxis, zAxis] at hRank

  have hxNotMem :
      xAxis ∉
        ({yAxis, zAxis} :
          Finset (PrimeTensor.Axis Depth.three)) := by

    intro h

    rcases
      Finset.mem_insert.mp h
      with hxy' | hxz'

    · exact
        hxy hxy'

    · exact
        hxz
          (
            Finset.mem_singleton.mp
              hxz'
          )

  have hyNotMem :
      yAxis ∉
        ({zAxis} :
          Finset (PrimeTensor.Axis Depth.three)) := by

    intro h

    exact
      hyz
        (
          Finset.mem_singleton.mp
            h
        )

  rw [
    Finset.sum_insert hxNotMem,
    Finset.sum_insert hyNotMem,
    Finset.sum_singleton
  ]

/--
The ordinary additive project axis fold agrees with the Mathlib finite sum in
dimension three.
-/
theorem axis_fold_add_eq_sum_three
    {A : Type}
    [AddCommMonoid A]
    (f : PrimeTensor.Axis Depth.three → A) :
    PrimeTensor.Axis.fold
        (· + ·)
        Depth.three
        f
      =
    ∑ i : PrimeTensor.Axis Depth.three, f i := by

  rw [
    axis_fold_three,
    axis_sum_three
  ]

end Euclidean
end Bridge
end PrimeTensor
