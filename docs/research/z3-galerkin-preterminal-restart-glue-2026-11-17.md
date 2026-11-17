# Finite Z³ Galerkin — automatic endpoint restart and two-sided ODE paste

Commit anchor: `be56e00056fcb2ac0975f3d4e531da2535d7137b`.

## Mathematically new in this stage

The audited predecessor established that an actual finite Galerkin solution
on `[a,b)` with strict initial `W_{log 2} < 100` and `b-a ≤ τ` has a
preterminal endpoint trace with `W_{log(9/5)} ≤ 100`, finite-state norm at
most `100`, derivative/field norm at most `51000`, and distance-to-endpoint
bound `51000 (b-t)`. It supplied an approaching Cauchy time sequence as a
hypothesis.

This stage **constructs the approaching sequence** from `a < b` using
`b ∈ closure (Ico a b)` and sequential characterization of closure, thereby
eliminating that explicit sequence assumption. Next, it applies the **actual
finite-dimensional Picard theorem** to the endpoint state: no strict Wiener
bound at the restart time is needed, nor is one assumed. The existence time
of the restarted local solution may depend on the finite cutoff `S`.

Define the pasted path

```
γ(t) = α(t)  for t < b
γ(t) = β(t)  for t ≥ b.
```

Because the old and new vector fields are the same complete complex
Leray-Galerkin field, `γ` solves `γ'=F_S(γ)` at every `t∈[a,b)` and
every `t∈(b,b+δ)`. At `b` the two definitions match and

```
‖γ(t)-γ(b)‖ ≤ 51000 (b-t)     (a ≤ t < b),
W_{log(9/5)}(γ(b)) ≤ 100,
‖F_S(γ(b))‖ ≤ 51000.
```

The **derivative at the joining time b is not yet proven** in this module.
In particular the formalized pasted object is NOT yet claimed to be a
strong solution on the entire `[a,b+δ)`. For full maximal continuation,
prove the seam derivative from the one-sided ODE and continuity of `F_S`,
then construct a maximal solution and rule out finite termination before
`a + τ = a + log(10/9)/100`. A glued path alone is not an unconditional
global Navier–Stokes solution; this is still finite periodic Z³ Galerkin
mathematics and does not settle the arbitrary-data R³ Clay problem.

## Verification

The accompanying source-level checker enforces exact upstream theorem
usage, the explicit topological sequence construction, both local ODE
halves, and absence of admitted assertions or new strict endpoint-ball
hypotheses. The Lean module itself MUST pass on the pinned project
Lean/mathlib environment. Do not commit a source-check-only pass.
