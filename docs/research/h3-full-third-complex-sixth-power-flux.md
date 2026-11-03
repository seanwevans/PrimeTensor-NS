# Actual unrestricted complex polarization: full H3 sixth-power triad flux

**Baseline:** `66bf5efe` — exact real sixth-power flux of the complete corrected physical H3 six-order symbol.

## Mathematical increment

The accepted real-valued `thirdFullPhysicalSix_sixthPowerFlux244` cannot be substituted directly into the Fourier coefficient of an arbitrary solenoidal *real* Schwartz velocity: its Fourier transforms are complex. At a generic triad they are not single real polarizations multiplied by a shared phase. Taking a Hermitian inner product in place of a trilinear Fourier product would introduce an incorrect conjugate and change the symbol.

This patch builds `thirdFullComplexOrderedSymbol244` using the *corrected* two-contraction gradient plus interpolation polynomial with complex polarization slots and physical real frequencies. `thirdFullComplexSixSymbol244` sums all six paired momentum/polarization permutations. `thirdFullComplexPolarizationDot244` is bilinear (`Σ A_i B_i`), not Hermitian.

For real p+q+r=0 and arbitrary complex A,B,C satisfying `p·A=q·B=r·C=0`, the theorem

`thirdFullComplexSix_sixthPowerFlux244`

proves **exactly**

```
S6_complex = (A·C)(r·B) (|r|^6 - |p|^6)
           + (A·B)(q·C) (|q|^6 - |p|^6)
           + (B·C)(r·A) (|r|^6 - |q|^6).
```

No absolute values, imaginary-part projections, conjugations, new frequency cutoffs, or terminal hypotheses enter this formula. Momentum conservation supplies the three real radial relations; complex linearity transfers polarization conservation. The scalar polynomial identity is proved in Lean over complex numbers using `ring`, and checked independently with exact symbolic polynomial algebra.

The corollaries identify the residual transfer when `|p|=|q|` and prove cancellation for three equal radii for **arbitrary complex Fourier phases**.

## Actual Fourier transforms, no frozen germ

The theorem `thirdFullSchwartzComplexSix_eq_sixthPowerFlux244` applies the identity pointwise to the three actual amplitudes `h3SchwartzTriadPolarization f` evaluated at `(p,-p-r,r)` on `H3FourierPoint3 × H3FourierPoint3`.

The stronger physical corollary `thirdFullRealSchwartz_sixthPowerFlux_of_point3Solenoidal244` begins with any **real**, 3-component `SchwartzMap` satisfying the repository's literal `lowNormalRealSchwartz_Point3Solenoidal` predicate. Its proof uses the already existing spatial derivative/complexification identity and Fourier divergence theorem to obtain spectral solenoidality, then applies the complex six-flux equation pointwise. Thus the corollary does NOT ask for a new spectral-divergence or packet-realization assumption.

## Remaining acceptance test

The exact real physical static commutator is already identified with the real part of `fullThirdSchwartzFourierCoefficient244 f`. What is **not yet** established for every Schwartz field is its conversion, with all correct numerical factors and the common seventh-derivative Fourier phase, to the integral of the newly defined complex six-order kernel. The existing `h3TriadSixOrbit_integral` handles the measure-preserving permutations for a generic integrable complex kernel. The next work must:

1. Identify one corrected ordered full-gradient-plus-interpolation Fourier kernel for arbitrary Schwartz data.
2. Prove this kernel integrable using Schwartz decay, then apply the existing six-permutation measure-preserving theorem.
3. Identify the pointwise six-orbit with the complex symbol in this patch and thus obtain the **unrestricted physical integral** of the sixth-power flux.
4. Quantify intershell transfer against viscous dissipation **without** claiming a static fixed-coefficient inequality already ruled out by the accepted Schwartz counterexample.

No Navier–Stokes blowup exclusion, terminal control, or new critical coefficient is claimed here. The Lean compiler is not installed in the assistant runtime; local compilation and all existing audit checks are required.
