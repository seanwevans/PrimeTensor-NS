# Physical projected FTC: differentiated compact solenoidal momentum

Checkpoint: `6fc4c741` — physical FTC defect cocycle and local weak gluing.

## Exact analytic task

Let `U(s)` be the actual physical three-component velocity in its L² Hilbert
space, and `R(s)` the actual projected Laplacian-minus-Leray source. In the
repository, the hypotheses of `LoggedPreterminalH3PathAdmissible` establish
continuous physical L²-valued `U` and `R` on every compact interval
`[a,b] ⊂ (0,T)`. The previous module formalizes the additive defect

    D(a,b) = U(b) - U(a) - ∫_a^b R(s) ds.

For every compact divergence-free spatial test `φ`, the present module shows
that the following are equivalent on `[a,b]`:

1. **Differentiated scalar weak momentum:** At every `s ∈ (a,b)`,
   `HasDerivAt (fun t => ⟨φ,U(t)⟩) ⟨φ,R(s)⟩ s`.
2. **Solenoidal scalar weak FTC:** For all `r ∈ [a,b]`,
   `⟨φ,U(r)-U(a)⟩ = ∫_a^r ⟨φ,R(s)⟩ ds`.

The first direction uses the *actual* scalar FTC in Mathlib, continuous U,
continuous R, and source-pairing integrability. The reverse direction uses
the preexisting Leray-fixed weak-to-strong Hilbert derivative theorem.
Consequently, the differentiated identity forces the actual Hilbert defect
to vanish on every prefix. Its contrapositive says that if the actual defect
is nonzero, there must be a compact divergence-free test and an interior time
at which the required pointwise scalar derivative identity fails.

## Why this is not an unconditional Navier--Stokes theorem

The preterminal PDE proves the momentum identity **at each spatial point**;
pointwise differentiability and separate spacetime continuity do **not**
automatically permit temporal differentiation through the spatial integral.
That is precisely the unresolved bridge. The new scalar differentiated identity
is a named hypothesis in these theorems, not a theorem following from bare
H³ admissibility. The source itself already has unconditional uniform L²
bounds, but these do not independently prove the weak velocity derivative.

## What to prove next

Use a compactly supported divergence-free `φ` and the classical PDE to
establish that the distributional time derivative of `t ↦ ⟨φ,U(t)⟩` equals
the continuous scalar `t ↦ ⟨φ,R(t)⟩`. Such a distributional identification,
together with the existing time-continuity of both scalar functions, would
supply the interior `HasDerivAt` condition without a compact pointwise
majorant for the old temporal derivative. Do not confuse an a.e. derivative
identity for an arbitrary continuous function with absolute continuity;
singular functions demonstrate why an additional distributional/AC premise
is essential.
