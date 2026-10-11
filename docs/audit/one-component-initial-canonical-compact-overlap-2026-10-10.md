# Initial canonical overlap and compact-test initial data

Base checkpoint: `572a6052` (`identify initial physical L2 from compact smooth weak tests`).

## Claim and dependencies

The canonical selected spectral mild solution is continuous in the three-component H3 topology and has specified initial value U0. The existing `H3AuditInitialCanonicalMildOverlapAt` hypothesis identifies the actual old velocity with that selected state coordinatewise, using the six curl-gradient pairs. All three Fin 3 coordinates occur among the complementary components.

`h3Audit_initialCanonicalOverlap_fullStrongH3Trace` therefore extracts the strong right H3 trace of the entire old spectral velocity from the overlap *without separately postulating the old-solution physical mild equation or a physical H3 energy ceiling*.

The compact-test weak initial condition identifies the decoded trace with actual u(0), using the existing dense-test theorem and spectral injectivity. The energy limit then follows from exact H3 spectral energy identities. The final bridge recovers `H3AuditInitialPhysicalZeroJetL2AndEnergyUpper` and the conditional transverse full-time Sobolev theorem.

## Outstanding obligations

- Actual old/selected canonical mild overlap on a nonempty interval starting at zero remains a hypothesis. It is not automatically implied by open-time Navier--Stokes classical admissibility.
- Compact smooth weak-test convergence to actual u(0) remains a hypothesis, as does the initial H3 snapshot with Fourier compatibility.
- The actual terminal vorticity strong H3 endpoint remains an independent hypothesis.
- No global Navier--Stokes continuation, no unconditional regularity result, and no external Liu--Zhang theorem is claimed here.

## Local verification

No `sorry`, `admit`, or new axiom declarations are included. Lean compilation must be performed with `lake env lean` and `lake build` against the target local repository (Lean is not available in this artifact workspace).
