# A width-averaged Fourier kinetic shell at the physical first crossing

Base commit: `6bfdc2c0`.

## Beyond the final-shell overshoot

The previous theorem shows that the last integer shell of the actual first
crossing has strictly positive dissipation, but the last-shell overshoot can be
arbitrarily small. No fixed fraction of the inner cubic height can be assigned
to that last shell without another hypothesis.

A different fact requires only finite telescoping. Let

- `R = n+1`, `Q = N+1`, where `N` is the *minimal* first-crossing outer index;
- `D(j)` be the actual low-radial H3 dissipation below `j+1`;
- `L = N-n > 0`, the number of integer Fourier shells in `[R,Q)`.

Because `D(N)-D(n) > 3 R^3/4`, some `m` in `[n,N)` satisfies

    3 R^3/4 < L * (D(m+1)-D(m)).

This is proved by a Nat-indexed telescoping contradiction, with no radial
monotonicity premise for the abstract lemma. The chosen `m` need not be `N-1`.

## Physical raw Fourier kinetic mass on that exact shell

The existing *actual physical* annular Fourier comparison gives

    D(m+1)-D(m) <= 4 (m+3)^8 * K_[m+1,m+2),

where `K_[m+1,m+2)` is the integral of raw Fourier squared velocity amplitude
on the exact unit-gradient-frequency band `[m+1,m+2)`.

Combining,

    3 R^3/4 < L * 4 (m+3)^8 * K_[m+1,m+2).

In particular this unit shell has strictly positive raw kinetic Fourier mass.
The theorem is stronger than merely saying the final shell has positive mass:
it quantifies how much dissipation *somewhere* in the first-crossing annulus
must be borne by an individual shell. The lower bound decays with the number
of shells; no bound on `L` is silently assumed.

## Physical cofinal selection and logical limits

The cofinal no-strong-terminal-L2-trace selector uses the same physical time
and minimal first-crossing index on every natural step. Its strict physical
time membership is inherited from the prior selector. Terminal full-H3
dissipation integrability is NOT needed for this cofinal result.

This theorem does not prove that any one shell carries a fixed cubic fraction,
that raw kinetic mass has a uniform positive lower bound, or that an
unconditional Navier–Stokes continuation contradiction has been obtained.
The conditional ninth/eighth cutoff separation remains a distinct result;
combining these exact shell witnesses with its disjoint PDE window selection
is a further proof step.

## Validation

Registration is checked for repeatability, ZIP integrity and source structure
are checked statically. Lean and lake are not installed in the packaging
environment. The module must be compiled in PrimeTensor-NS before commit.
