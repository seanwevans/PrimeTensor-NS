# Physical time distributions are exactly strong Hilbert derivatives on strict intervals

Base: `7f23ee91` — derive physical weak FTC from distributional momentum kernel.

## Result

For `0 < a < b < T`, with `LoggedPreterminalH3PathAdmissible`, the following are equivalent:

* The genuine regular-time-distribution momentum equation holds on `(a,b)` against every compact divergence-free physical spatial test.
* The **actual old physical L² Hilbert velocity** `U` has `HasDerivAt U (R s) s` for **every** `s ∈ (a,b)`, with `R` the previously constructed continuous Leray-projected physical source.

The nontrivial distribution-to-strong direction selects a smaller closed time interval around each `s`, uses the unconditional connected-interval kernel and distribution-to-weak-FTC bridge from `7f23ee91`, and invokes the already proved Leray-fixed weak-FTC-to-Hilbert-derivative theorem. No differentiation under spatial integrals is postulated.

The converse tests the strong derivative against compact solenoidal vectors, obtains weak FTC by scalar FTC, and then uses the prior weak-FTC-to-time-distribution theorem.

This does **not** supply the missing implication from `LoggedPreterminalNavierStokesAdmissible` and its pointwise spatial PDE to either of the equivalent conditions. The outstanding analytic issue is justified time/spatial interchange (or another rigorous PDE-to-distribution route).

## Build

`lake env lean PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionStrongDerivative244.lean`

Run registration script before `proof/generate_index.py` and full `lake build`.
