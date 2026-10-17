# Physical H3 energy identification on Schwartz-realized slices

Base: `8c919e0f` — transfer Schwartz critical half bound to physical H3 transport.

For an actual canonical path slice `u(t)` represented by the real Schwartz field `f` via
`loggedVelocityComponent u t j = h3SchwartzPoint3Scalar (f j)`:

- The complete physical zeroth through third spatial energy blocks are equal to the corresponding real Schwartz energies `E0(f)` through `E3(f)`, preserving their 3, 9, 27 and 81 slots.
- The 243-slot Schwartz fourth-derivative square mass is **exactly** `velocityH3Dissipation3At u t`, not the entire four-block dissipation.
- Reindexing the position of the outermost fourth derivative occurs via finite summation commutativity. No commutation of derivatives is assumed.
- The full physical H3 energy is `1 + E0(f) + E1(f) + E2(f) + E3(f)`, with the normalization unchanged.

Thus, with the previously established universal Schwartz constant `K`, the canonical third-order transport satisfies

`|T3(u,t)| <= 24 C1 sqrt(E(u,t)) E3(u,t) + 3 K (E0(u,t) E1(u,t))^(1/4) D(u,t)`.

Here `D(u,t)` is the **full** canonical dissipation, which bounds its top block. The only field-class restriction still visible is the exact real Schwartz realization of this path slice. This does not establish a Schwartz realization for arbitrary `H3` slices, uniform approximation in a time interval, a sign for the transport terms, or unconditional continuation.

The patch is meant to be checked first with `lake env lean` on the module, then `lake build` of the module to produce its `.olean`, then the audit, and finally the full `lake build`.
