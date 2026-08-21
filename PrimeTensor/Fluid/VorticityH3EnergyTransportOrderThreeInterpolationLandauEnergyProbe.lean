import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderThreeInterpolationLandauMonomials

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators ENNReal NNReal

#check VelocityH3IntegrableAt
#print VelocityH3IntegrableAt

#check velocityH3Energy3At
#print velocityH3Energy3At

#check velocityH3Energy3At_nonneg

#check spatialSquareEnergy
#print spatialSquareEnergy

#check spatialSquareEnergy_nonneg
#check spatialSquareEnergy_eq_zero
#check spatialSquareEnergy_add
#check spatialSquareEnergy_smul

#print axisFintypeH3EnergyDerivative
#print axisFintypeH3EnergyFunctional

#check landauL2
#print landauL2
#check landauL2_nonneg
#check landauL4Squared_mul_self

#check Finset.single_le_sum
#check Finset.sum_le_sum
#check Finset.sum_nonneg
#check Finset.le_sum_of_subadditive_on_pred

#check MeasureTheory.MemLp
#check MeasureTheory.MemLp.integrable_norm_pow
#check MeasureTheory.MemLp.integrable_norm_rpow
#check MeasureTheory.memLp_two_iff_integrable_sq
#check MeasureTheory.memLp_two_iff_integrable_mul_self

end Euclidean
end Bridge
end PrimeTensor
