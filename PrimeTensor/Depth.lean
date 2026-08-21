import Mathlib

/-!
# Positive depth and nonempty finite axes

Every dimension/rank begins at `one`.  There is no zeroth constructor.
`Axis d` therefore always contains at least one coordinate, and `foldAxis`
folds without an empty case or an identity element.
-/

namespace PrimeTensor

inductive Depth where
  | one : Depth
  | succ : Depth → Depth
  deriving DecidableEq, Repr

namespace Depth

/-- Two, represented without a zeroth stage. -/
def two : Depth := .succ .one

/-- Three, represented without a zeroth stage. -/
def three : Depth := .succ two

end Depth

/-- A finite coordinate axis with exactly `d` positive positions. -/
inductive Axis : Depth → Type where
  | first {d : Depth} : Axis d
  | next {d : Depth} : Axis d → Axis (.succ d)

namespace Axis

/--
Fold over every coordinate of a positive-dimensional axis.

There is deliberately no identity argument: an axis can never be empty.
-/
def fold {A : Type} (op : A → A → A) :
    (d : Depth) → (Axis d → A) → A
  | .one, f => f .first
  | .succ d, f => op (f .first) (fold op d (fun i => f (.next i)))

@[simp] theorem fold_one {A : Type} (op : A → A → A) (f : Axis .one → A) :
    fold op .one f = f .first := rfl

@[simp] theorem fold_succ {A : Type} (op : A → A → A)
    (d : Depth) (f : Axis (.succ d) → A) :
    fold op (.succ d) f =
      op (f .first) (fold op d (fun i => f (.next i))) := rfl

end Axis

/--
A positive-rank tensor index tuple.  Rank one is one axis index; each successor
prepends another index.  There is no empty tuple.
-/
def IndexTuple (dim : Depth) : Depth → Type
  | .one => Axis dim
  | .succ r => Axis dim × IndexTuple dim r

end PrimeTensor
