# Adjustable low-quarter Schwartz packet width: support geometry

Base commit: `51a848e1` (uniform positive tube at twelve coherent centers).

This module separates the strict nonresonance support geometry from the still-open **kernel sign under width changes**.

For each independently chosen `ρ > 0`, `lowNormalQuarterNarrowCutoff` constructs real smooth bumps of radius `ρ` at the original signed lattice center locations. The resulting Fourier field `lowNormalQuarterNarrowFourier` remains divergence-free, Hermitian, smooth, and compactly supported. Its Schwartz packaging is `lowNormalQuarterNarrowSchwartz`.

A nonzero vector Fourier value forces proximity to one of the six centers: `dist ξ (center i) < ρ`. If `ρ` does not exceed the earlier quantitative separation radius, any momentum-conserving triple of nonzero values must have three *coherent* labels, and its two independent frequencies lie within product distance `ρ` of the labeled ordered pair `(center i,center k)`. This is `lowNormalQuarterNarrowFourier_coherent_pair_support`. Equivalently, the pair lies in the radius-`ρ` open thickening of `lowNormalQuarterLabeledCoherentPairSet`, by `lowNormalQuarterNarrowFourier_support_in_coherent_thickening`.

**Important remaining steps:** (1) identify the 12 coherent labeled pairs with the previously defined orbit `lowNormalQuarterCoherentCenterSet`, (2) prove that the **new ρ-dependent signed kernel** is positive on every coherent interaction for sufficiently small `ρ` (the uniform positive tube for the original width-1/16 field alone is insufficient), (3) establish integrability and a positive-measure interaction, then conclude the full signed integral is positive. No assertion about Navier–Stokes continuation or singularities is made.
