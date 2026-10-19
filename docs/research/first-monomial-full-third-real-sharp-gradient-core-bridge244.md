# Actual full-third H³: sharp-gradient-core bridge (53daaf20)

The physical Fourier core from `...RealSectorWindowFactor244` has a
five-index 3+3+1 gradient term and a separate 3+2+2 interpolation term.
The preceding `...RealSharpInterpolationCenters244` established the
interpolation-center bridge. This step establishes the previously missing
physical *gradient* bridge, respecting the original four differentiated
slots and the factor two.

## Exact physical objects

`thirdFullSharpPhysicalGradientAxis244` is the four-pattern axis block in
the original seven-derivative Hermitian-Fourier weights, now contracted
against three fixed real polarizations. `thirdFullSharpPhysicalGradientFive244`
sums all 243 five-axis labels. `thirdFullSharpPhysicalOrderedCore244`
adds six times the true real interpolation contraction.

The bridge takes as explicit hypotheses the matching outer centers,
middle-frequency resonance, transversality, and fixed-center norm
nonvanishing. Its conclusions identify, successively, the actual
cutoff-free Fourier triple, a gradient-axis block, all five gradient sums,
and the complete physical polynomial with the matching sharp expression.

The crucial algebraic identity at the core is:

```
actual_cutoff_free_physical_core_at_center
    = full_sharp_four_pattern_five_axis_gradient +
      6 * sharp_interpolation_ordered
```

This deliberately neither assumes nor proves an identification with the
older six-permutation surrogate or the `-192` Hermitian total. The next
mathematical step is to contract the physical seven-frequency weights
across five finite axes, then compare the resulting per-order formula
against `thirdFullPhysicalOrderedSymbol244` and the already verified
six-center coefficients.

No change is made to any Navier--Stokes PDE assumption.
