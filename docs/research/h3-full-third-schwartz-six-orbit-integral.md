# Unrestricted H³ Fourier six-orbit: complex Schwartz radial flux

**Pinned baseline:** `a65f05c1` — extend the exact full H³ sixth-power flux to complex solenoidal Fourier polarizations.

## New mathematical statement

Let `u` be *any* three-component complex Schwartz field on the genuine `H3FourierPoint3` carrier, with no selected Fourier packets, no real-polarization substitution, and no frequency cutoff. Let `K_u(p,r)` be the corrected **ordered** complex symbol evaluated on the three actual Fourier transforms `U(p), U(q), U(r)` with `q=-p-r`.

On the full six-dimensional Hilbert Fourier pair, the previously verified volume-preserving permutations of `(p,r)` give the exact pointwise equality:

```
thirdFullSchwartzComplexSixSymbol244 u z
  = h3TriadSixOrbit (thirdFullSchwartzComplexOrderedKernel244 u) z
```

This identity does not assume solenoidality. Under the exact Fourier-divergence equation `ξ·Û(ξ)=0`, the already proved complex sixth-power factorization gives:

```
F_u(z) := thirdFullSchwartzComplexSixthPowerFlux244 u z
        = thirdFullSchwartzComplexSixSymbol244 u z
```

If the ordered complex multiplier `K_u` is integrable over the full product Fourier volume, the six measure-preserving changes of variables yield:

```
∫ F_u(p,r) dp dr = 6 ∫ K_u(p,r) dp dr.
```

The integrability of the flux then follows automatically from the six-orbit integrability theorem: it is not assumed separately. The physical `lowNormalRealSchwartz_Point3Solenoidal` hypothesis also supplies the Fourier-divergence equation through the repo's existing derivative/Fourier bridge; no ad hoc solenoidal assumption is needed for real physical data.

## Crucial normalization boundary

The unrestricted physical full third-order commutator is already identified as `Re(fullThirdSchwartzFourierCoefficient244 f)` in the prior repository. Its unphased Fourier density is **twice** the corrected ordered polynomial. Hence, after the remaining pointwise Fourier-gradient identification and absolute-integrability proof, the mathematically expected normalization is

```
fullSchwartzThirdCommutator244 f
  = (2*pi)^7 / 3 * Im(∫ F_f(p,r) dp dr).
```

The `1/3` is crucial: the six terms integrate to six times the corrected ordered term, while the physical energy pairing contributes two. We DO NOT assert this final formula here, because the generic pointwise gradient-coefficient comparison has not yet been Lean-proved, and its global absolute-integrability lemma is not yet supplied. In particular, no unproved Fourier identification is inserted as an axiom or a typeclass.

## What to prove next

1. Identify the generic (arbitrary-amplitude) complete seven-derivative raw unphased Fourier density with `2 * thirdFullSchwartzComplexOrderedKernel244`, retaining the four distinct gradient contractions, all five axis sums, and the actual interpolation coefficient.
2. Derive the ordered-kernel integrability from the already proved Schwartz seven-derivative gradient kernels and first-monomial Fourier kernel, discharging the explicit `Integrable K_u` contract in this module.
3. Combine the results with `fullSchwartzThirdCommutator_eq_fullFourierRe244` to prove the physical equality above. Check the `-96` adverse triad and the real Schwartz non-absorption witness for sign and normalization.
4. Only then attempt a genuine Navier–Stokes *dynamical* estimate for the intershell sixth-power transfer. The algebraic identity cannot refute the existing static Schwartz counterexample.

## Validation

Registrar adds the source import to both root and standalone audit, with `#check` and `#print axioms` for all declarations. The repository's pinned `lake`/`lean` is required for compiler acceptance. No global regularity or terminal H³ bound is claimed.
