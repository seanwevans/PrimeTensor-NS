import PrimeTensor.Tensor.Basic

/-!
# Multiplicative contraction

Contraction is a nonempty product over diagonal components. Because dimensions
start at one, no empty-product identity is required.
-/

namespace PrimeTensor
namespace Tensor

/-- Multiplicative contraction / trace of a matrix. -/
def contract₂ {A : Type} [Mul A] {dim : Depth} (m : Matrix A dim) : A :=
  Axis.fold (· * ·) dim (fun i => m.component (i, i))

@[simp] theorem contract₂_dim_one {A : Type} [Mul A]
    (m : Matrix A .one) :
    contract₂ m = m.component (.first, .first) := rfl

@[simp] theorem contract₂_dim_succ {A : Type} [Mul A]
    {d : Depth} (m : Matrix A (.succ d)) :
    contract₂ m =
      m.component (.first, .first) *
        Axis.fold (· * ·) d (fun i => m.component (.next i, .next i)) := rfl

end Tensor
end PrimeTensor
