# Three strong difference jets suffice for 243-slot nonlinear continuity

Baseline commit: `c8f07398` (`prove signed Schwartz monomial continuity under strong jets`).

## Result

For real Schwartz `f,g`, the actual L4 norm is

`N4(f) = sqrt(sqrt( integral (f x)^4 dx ))`.

Mathlib's `eLpNorm_add_le` at exponent 4, the already established `realLpEnorm`
identification, and `ENNReal.ofReal_add` yield

`N4(f) <= N4(f-g) + N4(g)`.

Swapping the arguments (and using evenness of fourth powers) proves

`|N4(f)-N4(g)| <= N4(f-g)`.

This produces convergence of the unperturbed L4 roots when their difference
roots tend to zero, closing the two redundant assumptions in the predecessor's
five-condition Schwartz strong-jet convergence predicate.

The new predicate `SchwartzThreeDifferenceJetConvergence244` asks only for:

1. convergence of the third derivative factor in L2, per physical slot;
2. convergence of the middle second derivative factor in L4;
3. convergence of the cross second derivative factor in L4.

`lowNormalRealSchwartz_firstMonomial_tendsto_of_threeDifferenceJets244` applies
the previous all-243-slot Hölder stability theorem and concludes convergence
of the signed first monomial, including the physical factor two.

`h3PathCanonical_approximable_of_threeDifferenceJets244` carries this into
the prior physical approximation property, but still explicitly assumes a
fixed real Schwartz target with the physical monomial identification and
convergence of physical E0, E1 and top fourth-order dissipation masses.

## Scope and remaining frontier

No general H3/H4 graph-density theorem is proved here; an arbitrary physical
H3 slice is not claimed to be Schwartz. A useful next task is replacing the
fixed Schwartz target by an arbitrary Sobolev limit while preserving the
signed triple-product integrals and all four physical jet energy blocks.

## Validation

After unpacking: run the registration script, regenerate `proof/order.txt`,
run `lake env lean` on the new module, build the module, run the audit check,
full `lake build` and `bash tools/audit/baseline.sh --reuse-build` before push.
