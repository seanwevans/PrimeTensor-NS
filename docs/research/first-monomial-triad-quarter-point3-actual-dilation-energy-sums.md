# Exact H3 derivative-energy scaling under actual Schwartz spatial dilation

**Base checkpoint:** `36149015` (`prove actual H3 Schwartz dilation Jacobian`).

This module applies the existing *proved* change-of-variables theorem and the
Schwartz derivative identities to all the finite sums used by the canonical
componentwise H3 energy. It does not assume the desired scaling relations.

For `f : Axis three → SchwartzMap V3 ℝ` and positive `scale`, let
`f_scale j x = f j (scale • x)`. For the ordered square-integral sums at
spatial derivative order `k = 0,1,2,3`, the module establishes

    E_k(f_scale) = scale^(2k) * (scale^3)^(-1) * E_k(f).

The cases are respectively 3, 9, 27 and 81 scalar integrals. In the exact
fourth-order dissipation form already defined in the amplitude-scaling module,

    D(f_scale) = scale^8 * (scale^3)^(-1) * D(f),

including all 243 integral slots. Equivalently the spatial degrees are
`-3, -1, +1, +3, +5`, matching the scalar dilation model.

The normalized H3 energy also has an exact expansion. Its constant term
stays `1`, rather than being multiplied by the Jacobian.

**What this does not prove:** identification with the `Point3` coordinate
energy of a physical solution, preservation of the physical divergence-free
constraint under the coordinate bridge, or scaling of the *signed* 243-slot
first monomial. The last requires a separate analysis of the physical
spatial derivatives in the cubic integral; the current theorem on 243 slots
concerns *quadratic fourth-derivative dissipation*, not the cubic monomial.

Validation: run this source in the user's Lean 4/mathlib environment, then
`lake build`, source indexing, proof fragments and the registered theorem
checks. The archive has no `sorry`, `admit`, or additional axioms. The
container building the archive cannot compile this Lean/mathlib project.
