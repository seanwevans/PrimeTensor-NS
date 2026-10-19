# Reserved kinetic/top-energy transport budget and high-growth threshold

Parent checkpoint: `0e7d5b72` — transfer canonical orderwise transport to actual Schwartz H³ slices.

The existing signed orderwise estimate charges `6 E1 + 18 E2` to the lower
commutators at an admissible Schwartz-realized Navier–Stokes slice. The
normalization of the canonical energy is `E = 1 + E0 + E1 + E2 + E3`.
Consequently:

    6 E1 + 18 E2 + 18(1 + E0 + E3) <= 18 E.

The stronger 18 coefficient (rather than the previous 24 coefficient) is
valid because E1 and E2 are disjoint nonnegative summands of total energy.
It is not claimed to be a sharp constant for actual solutions.

Let `H = C1 sqrt(E)` be the existing, canonical physical gradient envelope.
The new signed balance is

    E' + 2 D_full + 18 H (1 + E0 + E3) <= 18 H E - T3.

The exact signed balance, *not the upper bound above*, supplies the positive
slope theorem when the adverse cubic exceeds the full viscous and reserved
lower-order budget. The proof needs the upper bound on `T1 + T2`; it does NOT
attempt to infer a lower bound for `E'` from an upper bound for `E'`.

At a high unabsorbed Riccati rate `M`, the previous no-extension alternative
specializes to either

    4422 + M < 18 C1 sqrt(E)

or

    2 D_full < -T3.

The more refined alternative preserves `18 H (1 + E0 + E3)` on the left.
Thus, at any realized slice where `18 C1 sqrt(E) <= 4422 + M`, large
unabsorbed growth requires signed top transport to defeat complete viscosity.

**Logical boundaries:** All path conclusions retain the already-defined
`LoggedPreterminalH3PathAdmissible`, `PreterminalH3EnergyClass`,
Schwartz-realization, and (where used) high-rate premises. The theorem does
not establish that fixed-kinetic static Schwarz packets appear along a real
NS trajectory; it neither proves finite-time singularity nor continuation.

**Validation:** Register with the included script; run the pinned project's
`proof/generate_index.py` and source-index checks; typecheck the new Lean
file, Lake target, full root build, and the baseline audit on Rocky Linux.
No compiler execution is claimed for the artifact-preparation environment.
