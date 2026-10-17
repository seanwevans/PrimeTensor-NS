# Signed first monomial: strong Schwartz jet continuity (244)

Base commit: `e0128e2a` (`refresh Lean source index for CI`).

The preceding `SchwartzIntegratedStability244` theorem bounded the difference
of signed 243-slot first monomials by twice a finite sum of three exact
`L² × L⁴ × L⁴` root products. The present file makes that estimate into a
continuity theorem.

Given a sequence `fₙ` of three-component *real* Schwartz fields and a fixed
real Schwartz `g`, assume for every physical slot `p`:

- `‖D³(fₙ−g)‖₂ → 0` for the corresponding third-jet;
- `‖D²(fₙ−g)‖₄ → 0` for each of its two second-jets;
- both variable `L⁴` second-jet roots converge to their finite target roots.

Then each integrated telescoping envelope tends to zero, hence so does its
finite sum over 243 slots. The established factor-two estimate yields

    |M(fₙ) − M(g)| → 0,

so `M(fₙ) → M(g)` with the physical sign and slot multiplicities intact.
Convergence of `M` was **not** assumed.

The last theorem connects this analytic continuity to the earlier
`H3SchwartzCriticalHalfApproximable244` predicate, provided that `M(g)` is
identified with the path's actual signed physical monomial and the scalar
energy and top dissipation limits also hold.

## Remaining analytical obligations

The extra convergence of the undifferenced `L⁴` roots should eventually be
proved from convergence in the actual `L⁴` norm, for example by a reverse
triangle inequality. More importantly, this theorem is at a **Schwartz target**
`g`. An arbitrary non-Schwartz H³ path still needs a graph/Sobolev density
construction, passage of the 243 integral pairings to that completion, and
explicit physical energy identifications. This theorem is not a proof of
unconditional Navier–Stokes continuation.

## Validation

Run the registration script, regenerate `proof/order.txt` using
`python3 proof/generate_index.py`, then `lake env lean` on the module,
`lake build` on its module, theorem audit, and full `lake build` plus
`bash tools/audit/baseline.sh --reuse-build` before committing. The source
is prepared externally; it has not been typechecked in the project's Lean
4/mathlib environment.
