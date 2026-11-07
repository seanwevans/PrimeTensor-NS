# Kinetic eighth-power outer cutoff barrier for the actual disjoint H3 annular clocks

Base: `f221e640e76c2c9070d7d6f38c1f55266db2eed5`.

## Hard new frequency estimate

The accepted previous local annular witness gives, at its ORIGINAL sample time x,

    M/4 < D_low,N+1(x) - D_low,n+1(x)

where the natural radii n+1 and N+1, physical source and velocity, and PDE-selected
width δ are unchanged. Since actual low-radial H3 dissipation is nonnegative,

    M/4 < D_low,N+1(x).

The accepted physical kinetic Bernstein bound gives

    D_low,Q(x) <= Q^2 W3(Q) E,  E=velocityH3Energy0At(u,b).

The existing proved polynomial radial estimate `h3Critical_scalar_lowRadialKineticCeiling_le_eighthPower`
then yields the NEW local certificate

    M <= 16 E (N+1)^8.

No terminal full-H3 dissipation integrability, physical source maximum, or
full-H3 state maximum is used. This is a genuine non-temporal necessary
bandwidth condition. It is a counterpart to the previous *kinetic annular
PDE-rate* obstruction, not a substitute for the latter.

## Arbitrary prescribed gauge escape

Fix ANY natural-valued outer-frequency gauge G : ℕ -> ℕ. Choose the positive
height profile

    M(n) = 16 E (G(n)+1)^8 + 1.

The accepted no-terminal-H3-trace arbitrary-height diagonal provides genuine
H3 high-radial spikes exceeding M(n). The accepted kinetic local-window
lemma realizes each spike in a finite annulus and explicitly selects δ(n).
The accepted geometric selection lemma extracts a cofinal strictly increasing
index subsequence v with *exact*, pairwise separated physical intervals.

The new eighth-power inequality contradicts N(v(k)) <= G(v(k)). Hence

    G(v(k)) < N(v(k))   for EVERY retained k.

The exact same selected intervals satisfy the already-accepted single-global
extended-real full physical dissipation bound

    sum_{k<m} ofReal(M(v(k))/4) * ofReal(δ(v(k)))
       <= lintegral_{(a,T)} ofReal(D_H3(r)) dr.

This is a strong necessary spectral-concentration statement for *any*
prescribed gauge. It is not a continuation result: the outer radius is
allowed to grow faster than G and the kinetic clock can simultaneously shrink.
The result assumes failure of the **H3** terminal trace, not failure of the
physical L2 terminal trace, and does not assume finite full-H3 dissipation.

## Finite extended physical budget: clock compression or frequency escape

Suppose a local window lies in (a,T), a global extended full-dissipation
budget C >= 0 is available, and for proposed cutoff G0 one has

    lintegral_(a,T) ofReal(D_H3) <= ofReal(C),
    8*(sum_{j=0}^{G0} L_j(E) + L_n(E) + 1)*C < (M/2)^2.

The previously accepted local extended-budget clock/rate lemma and the global
set-inclusion comparison imply the new unconditional-on-L1 dichotomy

    (T-x)*(M/2) <= 16*C  OR  G0 < N.

Here `L_j(E)` is the verified true physical kinetic-only PDE variation rate.
This makes the obstruction to completing the NS continuation theorem explicit:
large spectral heights alone can be absorbed by terminal-time compression;
no lower clock scale independent of the selected outer radius has been proved.

## Audit

5 theorem declarations, 1 positive gauge-height definition, and their
`#check` / `#print axioms` registrations. Source contains no `sorry`, `admit`,
or added axiom. The module must still be compiled on the repository's pinned
Lean/mathlib toolchain; static validation is not elaboration.
