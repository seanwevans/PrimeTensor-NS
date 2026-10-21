# Physical H³ gradient triple: old Point3 integral bridge

Base: `8af41a97` (`prove physical H3 gradient strong L2-L2-Linfty trace and triple limits`).

The spectral-matched Schwartz sequence supplies two strong third-derivative L² limits and one strong first-derivative L∞ limit, with all three landing in the actual old physical velocity jets.

This module compares the corresponding trilinear `h3PhysicalGradientLpTriple244` to the original `Point3` Lebesgue integral for any two third-order physical derivatives and any first-order derivative. The comparison uses the earlier physical L² jet a.e. identity, the actual first-jet L∞ class (also a.e. equal to the physical derivative), and the volume-preserving coordinate change. It proves Schwartz triple integrals converge to the old physical triple integral.

The factor two belonging to `spatialEnergyPairing` is restored explicitly in `h3MatchedSchwartz_fullGradientTriple_tendsto_oldPhysical244`; the four orientations of one commutator gradient axis must still be reassembled. The 243 ordered axis slots are a separate, finite summation step. This checkpoint does NOT yet assert full third-order equality or any unconditional global Navier–Stokes regularity.
