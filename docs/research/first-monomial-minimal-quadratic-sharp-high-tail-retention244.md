# Retaining physical high-radial dissipation beneath the first crossing

Base commit: `79d7b704`.

## The mathematical issue

The preceding minimal-cutoff proof forces an enormous outer first-crossing
radius on the conditional ninth/eighth branch. But minimality itself is a
statement about accumulated annular dissipation, and a lower bound on the
first-crossing radius must be tied back to the actual exterior H3 spectrum.

Let `R=n+1` and `B(R,Q,t)=lowDiss(Q,t)-lowDiss(R,t)`.
The original physical high-radial cubic snapshot has `R^3<highDiss(R,t)`.
The least first crossing `N` satisfies `B(R,N+1,t)>3*R^3/4`, and for
`n<=m<N`, `B(R,m+1,t)<=3*R^3/4`.

The exact physical spectral partition gives

    highDiss(m+1,t) = highDiss(R,t) - B(R,m+1,t) > R^3/4.

The first Lean lemma proves this with the *actual physical* full H3
dissipation partition, without assuming the full H3 dissipation is
continuous in time. A second lemma shows the weaker estimate available
if only the annular first-crossing surplus is retained:

    highDiss(m+1,t) >= gap(R,N,t) - R^3/4 > 0.

The difference matters: the right-hand side can vanish in a cofinal
limit. Thus the stronger quarter-cubic lower floor requires preserving
the ORIGINAL high-radial cubic snapshot.

## Physical selector

The third theorem reconstructs the actual cofinal no-terminal-L2-trace
sequence from the pre-existing cubic high-radial snapshot theorem. It
chooses the minimal outer Fourier cutoff and the exact quadratic-sharp
PDE width at the *same* time, retains the annular lower bound along that
window, and adds the quarter-cubic high-tail lower bound at all preceding
integer Fourier radii. It does NOT assert finite terminal H3 dissipation.

The immediate next theorem should repeat the disjoint-window extraction
with this enriched selector and transfer the conditional ninth/eighth
separation to its high-tail floor. No terminal regularity contradiction is
claimed: high-frequency H3 dissipation can coexist with small kinetic L2
mass unless an additional physical localization estimate is established.

## Validation

Static checks and audit registration idempotence are performed at packaging
time. Lean compilation and the full project build remain to be verified
in the user's repository. No unproven axioms are introduced.
