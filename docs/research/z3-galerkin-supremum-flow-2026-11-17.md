# Finite Z³ Galerkin: canonical supremum flow and cutoff-independent closed analytic window

## Exact claim

At repository HEAD `69c669deb`, the complete finite Z³ Fourier Leray-Galerkin
polynomial field is `thirdFullThreeBandZ3GalerkinFiniteField244 mu s`.
For each finite cutoff `s`, every `0 ≤ mu ≤ 1/10`, initial time `a`, and
finite coefficient state `x0` satisfying **strict**
`W_(log 2)(zeroExtend(x0)) < 100`, the terminal theorem
`thirdFullThreeBand_z3GalerkinFiniteODE_exists_commonHorizon244` constructs
an actual real-time C¹ solution `gamma` on the closed interval

    [a, a + τ],  τ = (log 2 - log(9/5)) / 100 = log(10/9)/100,

with `gamma a = x0`, exact strong derivative `gamma' = F_s(gamma)` at **every**
time including `a+τ`, and the existing moving-radius Wiener-mass ceiling
`W_(log 2 - 100(t-a))(gamma(t)) ≤ 100` throughout.

## Construction (nothing postulated)

1. `StrongSegment`: actual strong ODE solution with positive endpoint, supplied by real-C¹
   Picard local existence.
2. `Reachable` and `CanonicalUnion`: at each covered time choose any actual
   segment. Earlier unrestricted overlap uniqueness proves independence of that choice.
   Before initial time the union uses one fixed Picard path to retain a two-sided derivative.
3. `CappedEndpoints`: real terminal times of initial strong segments, clipped to
   `T=a+τ`. The set is nonempty and bounded above; define `B=sSup CappedEndpoints`.
4. Every `a≤t<B` is reachable via `exists_lt_of_lt_csSup`. The canonical union
   therefore satisfies the exact ODE on `[a,B)` and retains the original data.
5. If `B<T`, the already verified automatic analytic barrier and **strong**
   Picard restart extend the canonical solution across `B`. Restrict that
   extension to `min(B+δ/2,T)`, giving a capped endpoint strictly greater than `B`,
   contradicting `le_csSup`.
6. Hence `B=T`. Restart once at `T` to obtain the exact derivative at the
   endpoint; apply the existing moving-ball persistence theorem on the CLOSED
   interval `[a,T]`.

## Scope and certification

The endpoint duration and Wiener ceilings do not depend on the finite cutoff
or the number of Fourier modes. The local Picard restart radius, and the
regularity constants for each finite-dimensional field, may depend on the
cutoff. No infinite-frequency limit, uniform spatial `H³` continuation of the
full physical velocity, or solution of the Clay Navier–Stokes problem is
claimed.

The package is statically audited for explicit unproved assertions and registry
consistency. Its Lean elaboration and full repository build must pass on the
pinned project toolchain before these proof claims are considered certified.
