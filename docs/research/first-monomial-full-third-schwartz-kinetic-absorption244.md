# Real-Schwartz kinetic absorption and signed top-order frontier (244)

Base: `38e8b614` — bound Schwartz lower transport by kinetic and top H3 energies.

## Mathematical advance

Earlier real-Schwartz path results controlled first and second transport by
`C1 sqrt(E) (10 E0 + 14 E3)`, and imposed an additional endpoint ceiling to
force the adverse top-order branch. That ceiling is unnecessary **for the
nonextension obstruction**: PrimeTensor already proves kinetic-anchored Young
absorption of both lower commutators for actual H3 solution paths.

For b < t < T, the existing physical estimate is

    E'(t) + D(t) <= 3 C1 sqrt(E(t)) E0(b)
                      + 441 C1^2 E0(b) E(t) - T3(t).

The present Lean bridge identifies the **actual** quantities at a realized
Schwartz time slice: full energy `E(t)=E(f)`, complete dissipation
`D(t)=E1(f)+E2(f)+E3(f)+D4(f)`, signed cubic `T3(t)=G3(f)+3M(f)`,
and the top 243-slot dissipation `D3(t)=D4(f)`.

Under hypothetical nonextension, each strict tail and each `M>=0` contains a
physical time with

    M * E(f) + D_full(f) < -(G3(f)+3M(f)).

The `M` on the left is an arbitrary growth threshold; the `M(f)` in the
commutator is the original first monomial. **No fixed endpoint ceiling** is
required for these witnesses. Exact Fourier/Landau bounds give the same
witness the strict corridor

    D4(f) + M E(f) < 4398 C1 sqrt(E(f)) E3(f),

and `E3(f)>0`.

## Conditional continuation tests

A finite bound on the *actual tail slices*,

    -(G3(f)+3M(f)) <= B E(f) + D_full(f),

for a fixed `B>=0`, implies continuation. Likewise, continuation follows if
at every realized tail slice

    4398 C1 sqrt(E(f)) E3(f) <= D4(f).

Both are explicit solution-slice hypotheses, not universal static Schwartz
inequalities. The established static noncoercivity witnesses do not refute
these time-dependent criteria. Nothing here deduces that every admissible
Navier--Stokes time slice is Schwartz, nor does it resolve global regularity.

## Validation

The accompanying register script adds the module import to `PrimeTensor.lean`
and `tools/audit/FirstMonomialTriad.lean`, checks theorem declarations, and
registers `#check` / `#print axioms` for all eight public theorems.
Run `lake env lean` and the repository's full audit on Rocky Linux; no Lean
compiler is available in the package-authoring environment.
