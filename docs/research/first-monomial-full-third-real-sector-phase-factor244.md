# Actual full-third six-sector cubic Fourier phase — checkpoint `c5bb06f7`

The previous checkpoint proves exact isolation of the Fourier transforms of a **real solenoidal Schwartz velocity** inside the six positively oriented momentum-pair sectors, conditional on nonzero actual triple spectral mass. The exact global identity is already

\[
\mathcal C_3(u) = 2 (2\pi)^7 \sum_{n=0}^5 \int_{\Omega_n} \operatorname{Im}K(p,r)\,dp\,dr.
\]

## What this patch adds

- Exact algebraic extraction of the product phase of three complex Fourier packets whose windows and transverse polarization germs are real.
- An explicit physical three-frequency real factor: at each ordered momentum triplet, evaluate **three different smooth scalar windows** and **three moving fixed-center solenoidal projection germs**, never their sharp-center stand-ins.
- On any positive sector where the actual Schwartz triple mass is nonzero, the product of the actual recovered Fourier components is precisely `Complex.I` times this real factor; its imaginary part equals that factor and its real part vanishes.
- Every one of the true seven-derivative `3+3+1` gradient slots has imaginary part equal to the **original real seven-derivative multiplier**, unchanged, times the actual real triple factor.
- The true `3+2+2` interpolation kernel is rewritten at the same physical sector point as the previously defined `complexCoefficient` times `amplitudeDot` of the three isolated Fourier vectors. This closes the triple-spectrum substitution for both types of PDE terms, but does not yet extract the real interpolation coefficient.

## Scope and outstanding proof

All sector-specific equalities are conditional on nonzero actual triple mass. The zero-mass case and integration can be handled separately using the previously established vanishing lemmas. No unsupported pointwise strict sign, uniform sign for all six permutations, or negative global integral is asserted.

Next: factor the `complexCoefficient` and `amplitudeDot` into a common nonnegative scalar window product times a **real moving-germ polynomial**, combine the actual gradient and interpolation contributions, and compare the resulting *full physical six-sector polynomial* with the earlier sharp `-192` center. Only after a uniform local sign estimate and positivity of the window mass on an open subset can the global sign be proved.
