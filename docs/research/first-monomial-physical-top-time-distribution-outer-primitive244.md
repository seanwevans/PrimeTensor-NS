# Outer primitive distribution implies true closed-window physical weak FTC

Base: `a826c2a8` (reduce physical time distributions to homogeneous FTC defect).

The exact defect reduction from the previous checkpoint is

    ∂_t (T_M - T_J) = 0  iff  ∂_t T_M = T_R

where `M(t) = <φ,U(t)>`, `R(t) = <φ, projectedRHS(t)>`, and
`J_c(t) = ∫_c^t R(s) ds`. This is a proved equivalence, not a proof of the
right-hand momentum identity from the old PDE.

The new module packages a different, useful implication. If on an *outer*
interval `(c,d)` there is a real scalar `K_φ` such that

    T_M = T_(J_c + K_φ),

then continuous-distribution injectivity identifies actual physical momentum
pointwise on `(c,d)`. For each pair of strict interior times `a<b`,

    M(b) - M(a) = [J_c(b)+K_φ] - [J_c(a)+K_φ]
                = ∫_a^b R(s)ds.

The *same* K_φ cancels and source interval integrability follows from physical
L² continuity. The current Leray-fixed weak-test determination theorem upgrades
the scalar identity, for all compact divergence-free spatial tests, to the
zero of the actual vector-valued L² FTC defect. Repeating over every prefix
recovers the physical solenoidal weak FTC on the entire *closed* smaller window.

This deliberately avoids an endpoint-continuity argument for identifying
`K_φ` at `c`: both `a` and `b` lie strictly inside the larger window.

## The precise still-open distribution lemma

For a continuous scalar `f` on a connected open real interval I, prove

    ∂_t T_f = 0  =>  ∃ K, T_f = T_(constant K).

A concrete analytic proof proceeds through compact smooth test functions:
choose a test bump `β` supported in I with `∫β = 1`. Every compact smooth test
`η` with `∫η=0` is the derivative of a compact smooth test supported in I.
Indeed its cumulative integral is zero to the left of its support and zero
to the right because the total mass vanishes. Thus `∂T_f=0` annihilates all
zero-integral tests. Subtract `(∫θ)β` from an arbitrary test `θ` to conclude

    T_f(θ) = (∫θ) T_f(β),

which is exactly the constant distribution with value `K = T_f(β)`.
Continuous-distribution injectivity then proves `f(t) = K` pointwise on I.

In Lean this needs a *genuine* zero-mass compact-test antiderivative lemma,
including smoothness and support containment, and a normalized nonzero bump.
Those two constructions are not supplied by this patch and must not be silently
replaced by a new axiom. Nor does this patch derive the physical
momentum distributional equation from the spatially pointwise old PDE.

## Build / audit

- Run `python3 tools/audit/register_first_monomial_physical_top_time_distribution_outer_primitive244.py`
- Run `python3 proof/generate_index.py`
- Use targeted `lake build` **before** `lake env lean tools/audit/FirstMonomialTriad.lean`
- Run `lake build` for the full repository

The source has not been checked with the user's pinned Lean toolchain here.
