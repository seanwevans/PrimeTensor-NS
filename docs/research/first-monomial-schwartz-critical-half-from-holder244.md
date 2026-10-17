# Homogeneous critical-half bound from the actual 243-slot Holder estimate

Base: `bbb90302` — fix Schwartz Holder 244 norm normalization.

The raw extended-real 2-4-4 Hölder bound on the signed first monomial has now
been connected to the real square/fourth-root moment identities of all 243
physical Schwartz slots. The unconditional estimate is

    |M(f)|^4 <= C * E2(f) * E3(f)^5,
    C = 16 * card(Axis Depth.three)^9 * S^6,

where `S = lowNormalSecondJetSobolevRealConstant`. The exact adjacent physical
Schwartz energy inequalities already yield

    E2(f) * E3(f)^5 <= E0(f) * E1(f) * D(f)^4.

Taking nonnegative fourth roots (with no exceptions for zero energies) yields

    |M(f)| <= C^(1/4) * (E0(f)*E1(f))^(1/4) * D(f).

This has the correct homogeneous scaling under spatial dilations:
`(E0*E1)^(1/4)` scales like the homogeneous half derivative seminorm,
while `D` is the fourth-order energy. The same coefficient also yields
`|M| <= C^(1/4) * sqrt(E0+E1) * D` from the preexisting integer closure.

The proof does **not** assert `E0*E1` is literally the homogeneous `H^(1/2)`
norm; it is an interpolation majorant. It applies to this particular
third-order signed first monomial, not to every term in the H3 energy
identity. Therefore it does not settle global three-dimensional
Navier–Stokes regularity, nor prove a critical-half absorption threshold
for arbitrary initial data. The bound is a classical analytic inequality
with an explicit, finite, potentially nonsharp constant.

For validation, first run `lake env lean` on the new file, then
`lake build` on its module before `lake env lean tools/audit/FirstMonomialTriad.lean`.
Finally run the full `lake build` and check its `#print axioms` audit output.
