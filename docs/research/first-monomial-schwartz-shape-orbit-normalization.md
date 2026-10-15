# Intrinsic critical-half Schwartz shape quotient and orbit normalization

Based on commit `0d5f6007` (canonical positive Schwartz balance scale).

For real Schwartz velocity fields set `M` to the signed 243-slot physical
first monomial, `D` to the complete 243-slot fourth derivative dissipation,
`E0` to the componentwise L² square mass, and `E3` to all 81 third-order
squared derivative integrals. Define the dimensionless shape ratio

    R(f) = M(f)^12 / (D(f)^12 E0(f)^5 E3(f)).

The coefficient-one interpolation and the existing physical dilation
homogeneities imply `R(a f) = R(f)` for `a != 0` and `R(f(scale * .)) = R(f)`
for positive scale, even though the four underlying physical quantities
have distinct homogeneity exponents. The denominator scales with amplitude
degree 36 and spatial degree 48, exactly like the numerator.

For `E0 > 0` and `E3 > 0`, choose a positive balance scale satisfying
`scale^6 E3 = E0`. At this scale, the two endpoint energies of the spatially
dilated field coincide and are positive. A further positive amplitude
rescaling makes both endpoint energies equal to one. The resulting real
Schwartz profile has exactly the same shape ratio. The divergence-free
condition is preserved by both transformations.

When also `D > 0`, `R(f) > (2 C)^12` is a sign-free conditional obstruction
to the proposed uniform solenoidal critical-half coefficient `C >= 0`.
The module does not prove `E3 > 0` from nontriviality, compactness of the
unit-endpoint class, or existence of a strict-excess witness.
