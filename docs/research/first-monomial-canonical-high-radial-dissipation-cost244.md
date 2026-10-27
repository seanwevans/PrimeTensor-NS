# Canonical source-maximizer high-radial viscous heights and persistence costs

**Base:** `a126e220` (`force canonical source peaks into genuine high-radial spectral mass`).

**Module:** `PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalHighRadialDissipationCost244`.

## Exact physical bridge

For each actual strict-time weighted H³ state `U(t)` and radial cutoff `ρ >= 0`, the repository already proves

`ρ² HighMass_ρ(U(t)) <= HighDissipation_ρ(U(t))` and

`LowDissipation_ρ(U(t)) + HighDissipation_ρ(U(t)) = velocityH3DissipationAt u t`.

Both integrals are genuine Fourier integrals. Since the low-radial dissipation density is nonnegative,

`ρ² HighMass_ρ(U(t)) <= velocityH3DissipationAt u t`.

For `ρ > 0`, high mass escaping to infinity along a sequence of physical times therefore forces both high-radial and full physical viscous dissipation heights to infinity on **that same sequence**. Under the *conditional* canonical critical ninth/eighth-width, sixth-order linear-rate and noncompression hypotheses, this applies to the previously selected attained physical projected-source maxima `s_k`. It does not require the additional vanishing-source-exposure premise.

## Integrated residence cost, not automatically inherited from snapshots

For any **additional** intervals `[τ_k, τ_k+δ_k]` that are genuinely disjoint, strictly inside the H³ path tail and on which `HighMass_ρ(U(r)) >= H_k`, the actual finite full-dissipation integral obeys

`sum_{k<m} δ_k ρ² H_k <= integral_a^T velocityH3DissipationAt u r dr`.

If `ρ > 0`, the widths are nonnegative, and `H_k -> +infinity`, then necessarily `δ_k -> 0`. The proof uses the already established physical disjoint-window integral summation, NOT any claim that half-terminal source-maximizing windows are disjoint.

A pointwise peak **does not supply** a quantitative positive persistence radius, a uniform high-frequency H³ time modulus, or an integrated contradiction. The open analytic problem is to derive a useful persistence lower bound around these maxima or transfer their high viscous heights to the *previously constructed disjoint quadratic-sharp windows* with explicit constants. Merely proving `δ_k -> 0` does not contradict finite total dissipation.

## Verification

No `sorry`, `admit`, or added axioms. The environment compiling the full project must check this Lean module. The package includes an idempotent audit registrar. No claim of global Navier–Stokes smooth continuation is made.
