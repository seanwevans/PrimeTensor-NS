# Fixed physical source component: non-L¹ residual under integrable corrections

Base commit: `4957959c340ab29503e2a9780c5aa579e82732be`.

## Established starting point

`TerminalFixedSpatialComponentNonintegrability.lean` provides one coordinate
`j : Fin 3` of the **actual projected physical momentum source** `R(t)` such that,
assuming the admissible physical path and failure of the strong physical
`L²` terminal velocity trace, `t ↦ R_j(t)` is not Bochner-L¹ on any `(b,T)`.
The same coordinate has arbitrarily large `L²` norm arbitrarily near `T`.
This theorem does not establish that a missing terminal trace ever occurs.

## New analytic step

For *any* scalar-`L²` source `F` and time-integrable correction `B`,

    F ∉ L¹((b,T);L²_x),  B ∈ L¹((b,T);L²_x)
       ⇒ F − B ∉ L¹((b,T);L²_x).

The argument is the contrapositive of additivity of Bochner integrability:
`(F−B) + B = F`. It works simultaneously on all terminal tails. When both
paths are continuous at positive times, the residual norm must exceed every
threshold arbitrarily near the terminal time, since a bounded measurable
function on a finite time interval is integrable.

The fixed coordinate can be selected BEFORE any family index for corrections
whose time-integrability holds for every coordinate. No new energy or terminal
kinetic-mass assumptions are added.

## Conditional Fourier-cutoff interface

For each real cutoff parameter `ρ`, let

    P ρ : H3ScalarL2 →L[ℝ] H3ScalarL2

be any bounded linear operator. If all `(P ρ)(R_j(t))` are time-integrable on
every terminal tail for every coordinate `j`, the same fixed `j` satisfies,
for **every** `ρ`, both persistent nonintegrability and arbitrarily large
terminal spikes of

    R_j(t) − (P ρ)(R_j(t)).

This is the abstract high-pass obstruction. The new module **does not**
construct the physical Fourier low-pass cutoff or prove that the cutoff of
the genuine projected source is L¹. Proving that bound for the Navier–Stokes
projected Laplacian-minus-Leray source is the next genuine analytic obligation.
A mere continuous map from the weighted spectral H³ state need not have
uniformly bounded source amplitude near the endpoint.

## Formal status

Four declarations, no `sorry`, `admit`, new `axiom`, or weakened old theorem
statement. The registrar adds one root import, one audit import, four `#check`
and four `#print axioms`. The full Lean build must be run locally using the
repository's pinned Mathlib; ZIP packaging is not a Lean kernel check.
