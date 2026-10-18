# Full third-order transport: corrected gradient symbol and Hermitian phase

Base: `d3e05c67` (2026-10-17). This checkpoint audits a **substantive problem**
in the old ordered third-order gradient symbol. The six-permutation result was
correct, but individual ordered gradient coefficients were not identified with
the true spatial-derivative placements of `fullSchwartzGradientAxis244`.

Let `(p,A)` be the tested Fourier mode, `(q,B)` the middle mode, `(r,C)` the
last mode; put `a=p·q`, `b=p·r`. The actual physical gradient block has one
term with polarization factor `(A·C)(B·r)`, and three terms with the different
factor `(A·B)(C·q)`. The threefold symmetrized first interpolation monomial
contributes the first factor `(A·C)(B·r)`. The corrected ordered expression is

```
K(p,q,r;A,B,C) = (A·C)(B·r) (a^3 + 3 a^2 b)
                 + 3(A·B)(C·q) a^2 b.
```

The earlier **incorrect as an ordered physical expression** form was

```
K_old = (A·C)(B·r) a(a^2 + 3ab + 3b^2).
```

`K(p,q,r)+K(p,r,q) = K_old(p,q,r)+K_old(p,r,q)` is an exact
identity for **all** frequencies and polarizations: the mismatched term is
restored after exchanging the two non-tested modes. Summing the six terms
gives the same coefficient, without requiring the divergence or momentum
constraints for this particular equality.

For the explicit solenoidal frequencies and polarizations

```
p = (1,0,0), q = (1,1,0), r = (-2,-1,0)
A = (0,1,0), B = (1,-1,0), C = (1,-2,0)
```

we have momentum conservation and A·p = B·q = C·r = 0. The corrected ordered
values are `-16, 28, 33, -81, -60, 0`; the total remains **-96**.

The frequency-reflected orbit picks up a minus sign from the seven total
spatial derivative orders. On the real physical Fourier side, a Hermitian
reflection conjugates its polarization product `z`. Since `i^7=-i`, the
complex-real algebra of the reflected pair is

```
Re[i^7 S z + i^7(-S) conj(z)] = 2 S Im(z).
```

For `S=-96`, `z=i`, the paired result is **-192**. Multiplication by the
physical `2(2π)^7` factor preserves the strict negative sign. The complex
phase is attainable by assigning a relative imaginary polarization to one of
the three positive modes and assigning conjugate values at negative modes,
but the present Lean source formalizes the **finite orbit algebra**, not a
Schwartz wave-packet existence theorem.

## Frontier still open

1. An exact Fourier-transform theorem identifying the full real-Schwartz
   gradient functional (not just the interpolation monomial) with this newly
   corrected ordered kernel and its `(2πi)^7` factor.
2. A divergence-free Hermitian Schwartz-frequency localization whose six
   dominant positive-frequency interactions and reflected partners have a
   controlled nonzero integral; all unwanted frequency combinations require
   quantitative support separation and error estimates.
3. Only then discharge the condition `fullSchwartzThirdCommutator244 f ≠ 0`
   in the existing static full-transport absorption theorem. This would NOT
   settle smooth Navier–Stokes continuation.

The new code is a proof candidate: independent mathematical/numerical checks
were made, but the assistant environment has no Lean toolchain. Run the local
Lean build before committing.
