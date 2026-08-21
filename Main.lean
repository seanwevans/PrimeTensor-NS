import PrimeTensor

/-- A finite probe: 12 has the prime multiset 2·2·3. -/
example : PrimeTensor.PrimeMultiset.eval PrimeTensor.twelve = 12 := by
  norm_num [PrimeTensor.twelve, PrimeTensor.twelveBag,
    PrimeTensor.PrimeMultiset.eval, PrimeTensor.PrimeMultiset.ofBag,
    PrimeTensor.PrimeBag.eval, PrimeTensor.primeTwo, PrimeTensor.primeThree]

/-- Factor ordering is gone at the public prime-multiset layer. -/
example (a b : PrimeTensor.PrimeMultiset) :
    a * b = b * a :=
  PrimeTensor.PrimeMultiset.mul_comm a b

/-- Rank-two contraction in dimension one has exactly one factor. -/
example (m : PrimeTensor.Tensor.Matrix PrimeTensor.PrimeRatio PrimeTensor.Depth.one) :
    PrimeTensor.Tensor.contract₂ m = m.component (.first, .first) := rfl

#check PrimeTensor.Tensor.contract₂
#check PrimeTensor.Differential.divergence
#check PrimeTensor.Differential.laplacian
#check PrimeTensor.Bridge.contract₂_toRat

def main : IO Unit := do
  IO.println "PrimeTensor core compiled."