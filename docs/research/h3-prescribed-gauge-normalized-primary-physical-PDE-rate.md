# Normalized primary H³ clock / attained physical PDE rate

**Base:** `10a237c374279d3c2a41eab0f74acadaa52b6384`.

The existing deep-excess theorem retains an actual second physical PDE
clock with the same selected cutoff `J2`, actual attained spectral-state
norm `K2` and projected momentum-source norm `C2`. For

- `A = V/(2P)` (primary physical H³ height),
- `B = integral_m^T D_H3` (actual remaining viscous action),
- `R = 96*(3+initialLerayEnergyCoefficient)*(J+2)^5`,
- `H = A/(24 sqrt(R B))` (constructive second floor),

under the existing activated physical two-slice rate, kinetic gap and
`48 sqrt(R B) <= 1`, the deep-excess conclusion is

    (T-s)*H <= 8*B
    OR H² <= (96*K2*C2*(J2+2)^5+4)*B.

The first rate and second height are now transferred to the **primary**
height, using `H * (24 sqrt(R B)) = A` and
`(sqrt(R B))² = R B` (requires `R*B>0`):

    (T-s)*A <= 192*B*sqrt(R B)
    OR A² <= 576*R*B²*(96*K2*C2*(J2+2)^5+4).

A further scalar theorem shows that if a fixed cap `M` bounds the actually
selected `K2*C2*(J2+2)^5`, and
`576*R*B²*(96*M+4)<A²`, then the compressed-clock arm is mandatory.
If that arm fails, the lower bound

    A²/(576*R*B²) <= 96*K2*C2*(J2+2)^5+4

quantifies the necessary physical amplification. Neither `R` nor `J2`,
`K2`, `C2` are claimed uniformly bounded along the cofinal witnesses.

The normalized cofinal ledger is an *extension* of the deep-excess ledger,
not a replacement of the exact two-clock overlap envelope. The resulting
no-terminal-H³-trace theorem preserves frequency escape, disjoint viscous
charges, and all original physical alternatives.

No `sorry`, `admit`, or new axioms are added. Compilation and transitive
axiom audit must be performed with the pinned Lean toolchain in the user's
repository; the ZIP build does not itself establish a successful Lean proof.
