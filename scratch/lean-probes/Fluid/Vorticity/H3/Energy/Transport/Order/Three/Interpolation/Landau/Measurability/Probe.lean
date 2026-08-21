import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.L2.Bridge

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators ENNReal NNReal

#check VelocitySpatialC5OnTail
#print VelocitySpatialC5OnTail

#check PreterminalH3EnergyClass
#print PreterminalH3EnergyClass

#check Continuous.aestronglyMeasurable
#check Continuous.aemeasurable
#check Continuous.continuousAt
#check Continuous.comp

#check ContDiff
#check ContDiff.continuous
#check ContDiff.contDiff
#check ContDiff.iterateFDeriv

#check spatial3.d
#print spatial3.d

#check loggedVelocityComponent
#print loggedVelocityComponent

end Euclidean
end Bridge
end PrimeTensor
