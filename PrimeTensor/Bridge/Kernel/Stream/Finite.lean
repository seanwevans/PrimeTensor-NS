import PrimeTensor.Bridge.Kernel.Descent
import PrimeTensor.Fluid.Coupling.Stream.Finite
import PrimeTensor.Fluid.Coupling.Tail.Control

/-!
# Concrete stream-preserving finite kernel

The dyadic prime-pair kernel has already been:

* proved intrinsically Cauchy,
* descended canonically through unique factorization to
  `MultisetStreamCouplingSeed`,
* descended after quotienting outputs to a lawful `FiniteMulCoupling`.

`CouplingStreamFinite` supplies the missing stream-preserving oriented-rational
extension.  This file simply instantiates it with the concrete dyadic kernel.

The resulting object is the exact input required by the completion machinery:

    PrimePairApprox.streamFiniteKernel : StreamFiniteMulCoupling

and it satisfies exact termwise bilinearity.

The only remaining analytic obligation for completion is therefore
`CouplingTailScaleControl streamFiniteKernel`.
-/

namespace PrimeTensor
namespace Bridge
namespace PrimePairApprox

/--
Concrete canonical stream-valued coupling on all finite multiplicative
rationals.
-/
noncomputable def streamFiniteKernel :
    PrimeTensor.StreamFiniteMulCoupling :=
  multisetKernel.toStreamFinite
    multisetKernel_lawful

/--
The concrete stream-valued finite kernel satisfies all four exact termwise
multiplicative coupling laws.
-/
theorem streamFiniteKernel_lawful :
    PrimeTensor.IsStreamFiniteMulCoupling
      streamFiniteKernel := by

  exact
    multisetKernel.toStreamFinite_lawful
      multisetKernel_lawful

/--
The precise remaining analytic proposition needed to lift the concrete kernel
to the completed carrier.
-/
def StreamFiniteKernelTailControlled : Prop :=
  PrimeTensor.CouplingTailScaleControl
    streamFiniteKernel

/--
Once tail-local scale control is proved, the concrete stream kernel gives a
lawful intrinsic coupling on all of `MulReal`.
-/
noncomputable def completedKernel
    (hScale : StreamFiniteKernelTailControlled) :
    PrimeTensor.MulCoupling :=
  streamFiniteKernel.complete
    hScale.toCompletionStable

/--
Conditional closure theorem: tail-local control is the only missing hypothesis
for the concrete completed kernel to satisfy `IsMulCoupling`.
-/
theorem completedKernel_lawful
    (hScale : StreamFiniteKernelTailControlled) :
    PrimeTensor.IsMulCoupling
      (completedKernel hScale) := by

  unfold completedKernel

  exact
    streamFiniteKernel.complete_lawful_of_tailScaleControl
      streamFiniteKernel_lawful
      hScale

end PrimePairApprox
end Bridge
end PrimeTensor
