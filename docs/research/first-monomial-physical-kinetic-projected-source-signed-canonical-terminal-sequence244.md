# One fixed physical signed channel with an actual canonical cubic terminal sequence

**Base**: `fe9345b0` — isolate fixed cofinal signed physical H³ channel.

## New mathematical content

Under admissible preterminal physical H³ data, a strictly positive canonical
terminal kinetic mass and *failure of the strong physical kinetic L² terminal
trace*, the existing fixed signed-channel alternative is diagonalized.
There is one sequence `τ(n)` inside the strict physical energy-class tail,
with `dist(τ(n),T)<1/(n+1)` and `τ(n)→T`, such that **one and the same channel**
exceeds the growing normalized threshold `n+1` for all n:

1. `-E'(τ(n)) > (n+1) E(τ(n))`; **or**
2. `-W(τ(n)) > (n+1) E(τ(n))`, where `W` is the exact signed **full** physical H³ transport derivative.

The second case is transferred to the existing exactly identified spectral
third-order cubic `C₃(G)=G₃(G)+3 M₃(G)` at **the same physical times** and for the
actual weighted H³ spectral state `G(t)`:

    (n+1 - 24*C₁*sqrt(E(τ(n)))) * E(τ(n)) < -C₃(G(τ(n))).

The argument is a sharp chain of already-proved identities/estimates:

    E' + 2D = -W
    E' + 2D ≤ 24*C₁*sqrt(E)*E - C₃(G).

Subtract the two statements to obtain the signed bound on `-W`, then apply
the diagonal witness. No new choice of Fourier representatives is made.

A separate theorem shows that if `E'≥-B E` throughout one strict terminal
subtail, the fast-decay branch is impossible, so the actual canonical adverse
third-cubic witness can be selected without the disjunction.

## Interpretation

This is a fixed-branch *sequence* refinement. It does **not** show that `C₃`
is negative, because the term `24*C₁*sqrt(E)` may be larger than `n+1`.
It does not show kinetic-trace failure follows from H³ nonextension.
Further progress needs an actual PDE mechanism controlling this lower-order
allowance relative to the selected transport and dissipation clocks, or a
separate constraint on arbitrarily rapid negative energy slopes.

## Registered Lean declarations

- `h3Path_cofinalSignedRate_diagonalSequence244`
- `h3Path_adverseFullTransport_forces_weightedThirdDeficit244`
- `h3Path_physicalNoL2Trace_forces_fixedSignedCanonicalSequence244`
- `h3Path_physicalSlopeFloor_forces_canonicalAdverseTerminalSequence244`
