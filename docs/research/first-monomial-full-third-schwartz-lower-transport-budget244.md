# Complete static viscosity obstruction and actual lower-transport budget

Base checkpoint: `3becf6ca` (full Schwartz viscous dissipation / unforced H3 balance).

Two logically independent results are formalized.

## Static, fixed kinetic mass

`lowNormalRealSchwartzH3FullDissipation244 f` is the entire canonical viscous
mass `E1(f)+E2(f)+E3(f)+D4(f)`. Nonnegativity of the kinetic energy implies
`E1+E2+E3 <= E`, where `E=1+E0+E1+E2+E3` is the normalized H3 energy.

The already-proved fixed-kinetic adverse Schwartz witness defeats `C*D4 + K*E`
for *every* real pair `(C,K)`. For `C >= 0` replace `K` by `K+C`. Because
`Dfull <= D4 + E`, the same witness then defeats `C*Dfull + K*E`.
In particular with the physical viscosity coefficient `2`, a single kinetic
mass E0 supports solenoidal Schwartz packets against any energy compensation.

This is a **static** noncoercivity theorem, not an NS realization theorem.

## Actual admissible path

With the existing explicit whole-space kinetic flux cancellation, `T0=0`.
The existing first- and second-order gradient-envelope estimates give
`|T1| <= 6 h E` and `|T2| <= 18 h E` under their separate flux,
pairing-integrability and H3-energy hypotheses. Thus `|T1+T2| <= 24 h E`.
On a real Schwartz-realized time slice `E(u(t)) = E(f)`.

Combining these with the new complete viscous identity yields

    E'(t)+2 Dfull(f) = -[T1(t)+T2(t)+G3(f)+3 M(f)]

and consequently the **conditional** sufficient criterion

    -[G3(f)+3M(f)] > 2 Dfull(f) + 24 h(t) E(f)
       ==> E'(t) > 0.

No dynamic realization of arbitrary Schwartz packets is assumed. The specific
missing mathematical bridge is control of the actual gradient envelope `h(t)`
relative to the static witness and its realization along a solution.

No `sorry`, `admit`, extra axioms, or claimed global regularity proof is added.
Lean compilation must be checked against the target Rocky Linux mathlib build.
