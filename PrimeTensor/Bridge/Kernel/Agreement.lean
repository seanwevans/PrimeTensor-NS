import PrimeTensor.Bridge.Kernel.Stream.Finite
import PrimeTensor.Fluid.Coupling.Stream.Agreement

/-!
# Agreement of the concrete stream and finite kernels

The concrete dyadic kernel has two finite incarnations:

* `finiteKernel`, where canonical streams are quotiented before orientation;
* `streamFiniteKernel`, where orientation is performed on the streams first.

The generic agreement theorem proves that the second realizes the first
exactly in `MulReal`.
-/

namespace PrimeTensor
namespace Bridge
namespace PrimePairApprox

/--
The concrete stream-preserving finite kernel represents exactly the previously
constructed canonical finite coupling.
-/
theorem streamFiniteKernel_realizes_finiteKernel :
    PrimeTensor.RealizesFiniteCoupling
      streamFiniteKernel
      finiteKernel := by

  exact
    multisetKernel.toStreamFinite_realizes_toFinite
      multisetKernel_lawful

end PrimePairApprox
end Bridge
end PrimeTensor
