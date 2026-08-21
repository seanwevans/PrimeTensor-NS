import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderThreeInterpolationLandauDirectClosure

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators ENNReal NNReal

#check SpatialL2SquareIntegrable
#print SpatialL2SquareIntegrable

#check VelocityH3IntegrableAt
#print VelocityH3IntegrableAt

#check MeasureTheory.memLp_two_iff_integrable_sq
#check MeasureTheory.MemLp
#check MeasureTheory.Integrable
#check MeasureTheory.Integrable.aestronglyMeasurable
#check MeasureTheory.Integrable.aemeasurable

#check MeasureTheory.memLp_two_iff_integrable_sq
#check MeasureTheory.MemLp.integrable_norm_pow

end Euclidean
end Bridge
end PrimeTensor
