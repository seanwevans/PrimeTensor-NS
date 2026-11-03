# Hard H³ transport: exact sixth-power radial energy-flux identity

**Pinned base:** `feb20784` — integrate full H³ radial cancellation over physical projected Fourier kernels.

## The new algebraic point

For an exact momentum-conserving triad `p+q+r=0`, set

`P = |p|²`, `Q = |q|²`, `R = |r|²`, `a = p·q`, `b = p·r`, `c = q·r`.

The momentum law yields **without division**

`a+b=-P`, `a+c=-Q`, and `b+c=-R`.

The previous generic quadratic factor has the previously unrecognized identity

`G(x,y;z)=(x+z)²+(x+z)(y+z)+(y+z)²`

and is everywhere nonnegative, since

`4G(x,y;z)=(x-y)²+3(x+y+2z)²`.

Hence its three physical specializations are

- `G(a,c;b)=P²+PR+R²`,
- `G(b,c;a)=P²+PQ+Q²`,
- `G(a,b;c)=Q²+QR+R²`.

Multiply by the corresponding linear radius defect. Each becomes an **exact difference of cubes of squared radii**—i.e., differences of SIXTH POWERS of Fourier lengths. For the corrected FULL third-gradient-plus-interpolation symbol,

```
S₆(p,q,r;A,B,C)
  = (A·C)(B·r) (R³-P³)
  + (A·B)(C·q) (Q³-P³)
  + (B·C)(A·r) (R³-Q³).
```

All six permutations, distinct gradient contractions, momentum conservation and three solenoidal polarizations are retained. No angular multiplier, Fourier phase or extra assumed bound has been silently deleted. The `-96` adverse witness is compatible because `(P,Q,R)=(1,2,5)`.

An additional exact **two-shell** identity shows, when `P=Q`,

```
S₆ = (R³-P³) ((A·C)(B·r) + (B·C)(A·r)).
```

It is incorrect to infer that matching only two radii produces cancellation; the remaining flux can persist.

## Actual projected Hermitian kernel and integrated identity

For the already constructed globally smooth moving solenoidal germs `U(p),V(q),W(r)` with `q=-(p+r)`, the exact Hermitian Fourier kernel is twice this symbol. Define `thirdFullProjectedSixthPowerFluxDensity244` by inserting the three actual germs and retaining the three sixth-power differences. Then, pointwise, for **all** momentum pairs,

```
thirdFullProjectedHermitianKernel244 ... z
  = thirdFullProjectedSixthPowerFluxDensity244 ... z.
```

Continuity of the prior projected kernel implies integrability of this flux density on compact momentum-pair balls. The resulting theorem integrates the identity over the real physical six-dimensional momentum measure, with no radial near-balance assumption:

```
∫_ball physicalHermitianKernel = ∫_ball threeSixthPowerFluxes.
```

Unlike the earlier near-equal-radius estimate, this is **exact at arbitrarily disparate radii**. It provides a clean analytical entry point for intershell flux/commutator estimates, where individual sixth-power weights can be compared with physical H³ dissipation and the time-evolved spectrum.

## Boundary and next acceptance test

This is not an equality with `fullThirdSchwartzFourierCoefficient244 f` for every real solenoidal Schwartz `f`; that coefficient is already proved to represent the true static third commutator, but its complete arbitrary-amplitude six-permutation/Hermitian integration has not yet been identified with this simpler sixth-power density. The existing moving germs are a legitimate exactly transverse *specialization*. We should establish the unrestricted bridge using the actual Fourier amplitudes and the existing measure-preserving triad permutations, not by postulating an additional compatibility predicate.

Even that unrestricted identity alone cannot yield global regularity: the static fixed-kinetic adverse Schwartz family survives. A genuine PDE-time estimate controlling intershell flux at unrestricted amplitudes remains necessary. Do not claim a total bound from a local cancellation alone.

## Lean validation

The new module imports the accepted `FullThirdProjectedRadialIntegral`, the existing triad cyclic integral, and Mathlib. Its seven theorems establish the nonnegative shifted-square multiplier, exact physical sixth-power flux, two-shell reduction, its frequency-dependent projected counterpart, and compact integral identity. The idempotent registrar adds the source to the root and standalone triad audit and prints its axiom dependencies. The pinned Lean compiler is unavailable in the assistant environment; local elaboration and the repository baseline are required.
