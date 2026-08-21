import PrimeTensor.Bridge.Cauchy

/-!
# Descent of the concrete dyadic kernel

`Bridge.Cauchy` constructs the explicit prime-pair stream kernel

    PrimePairApprox.kernel : PrimePairStreamSeed

and proves that each atomic stream is intrinsically Cauchy and converges, in
the conventional bridge, to

    exp (log p * log q).

`Fluid.CouplingUFD` proves that every prime-pair stream seed canonically
descends through unique factorization to:

* positive prime multisets,
* finite positive barcode coupling,
* finite oriented-rational coupling.

This file simply instantiates that general descent theorem with the concrete
dyadic kernel.  No additional algebraic or number-theoretic hypothesis is
introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace PrimePairApprox

/--
Concrete stream coupling on positive prime multisets obtained by canonical UFD
descent of the dyadic prime-pair kernel.
-/
noncomputable def multisetKernel :
    PrimeTensor.MultisetStreamCouplingSeed :=
  kernel.toMultisetCanonical

/-- The concrete positive-multiset stream coupling is termwise bilinear. -/
theorem multisetKernel_lawful :
    PrimeTensor.IsMultisetStreamCouplingSeed
      multisetKernel := by
  exact kernel.toMultisetCanonical_lawful

/--
Concrete positive-barcode coupling obtained from the explicit dyadic
prime-pair kernel.
-/
noncomputable def barcodeKernel :
    PrimeTensor.BarcodeCouplingSeed :=
  kernel.toBarcodeSeedCanonical

/--
Concrete finite multiplicative-rational coupling obtained from the explicit
dyadic prime-pair kernel.
-/
noncomputable def finiteKernel :
    PrimeTensor.FiniteMulCoupling :=
  kernel.toFiniteCanonical

/--
The concrete finite coupling satisfies the multiplicative bilinearity laws.
-/
theorem finiteKernel_lawful :
    PrimeTensor.IsFiniteMulCoupling
      finiteKernel := by
  exact kernel.toFiniteCanonical_lawful

/--
The atomic kernel is symmetric before descent.

This is stronger than symmetry merely at the semantic limit: the dyadic term
at every native depth is identical after swapping the prime inputs.
-/
theorem term_symm
    (p q : Prime)
    (d : Depth) :
    term p q d =
      term q p d := by

  have hnum :
      numerator p q d =
        numerator q p d := by

    unfold numerator
    unfold scaled
    unfold target

    rw [
      PrimeTensor.Bridge.PrimePairStreamSeed.logProductTarget_symm
        p q
    ]

  unfold term
  unfold PrimeTensor.Bridge.Encode.ratio

  rw [hnum]

/-- The concrete prime-pair stream seed is pointwise symmetric. -/
theorem kernel_symmetric :
    PrimeTensor.PrimePairStreamSeed.Symmetric
      kernel := by

  intro p q n

  change
    term p q n =
      term q p n

  exact term_symm p q n

end PrimePairApprox
end Bridge
end PrimeTensor
