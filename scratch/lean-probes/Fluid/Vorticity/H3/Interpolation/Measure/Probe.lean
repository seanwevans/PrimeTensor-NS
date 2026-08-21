import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Holder.Real

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory

set_option pp.all true in
#print spatialEnergyPairing

set_option pp.all true in
#print spatialSquareEnergy

set_option pp.all true in
#check (inferInstance : MeasurableSpace Point3)

end Euclidean
end Bridge
end PrimeTensor
