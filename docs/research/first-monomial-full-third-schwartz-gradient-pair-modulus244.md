# Two-profile H³-compatible 3–3–1 Schwartz gradient modulus

**Base checkpoint:** `3d46b5a7` — identify matched Schwartz first jets with physical H3 gradient.

## The missing nonlinear passage

The completed signed 243-slot `3–2–2` monomial already exists as a choice-independent scalar on the weighted spectral H³ Hilbert space. The physical first-derivative bridge now compares a synchronized real Schwartz approximation directly to the actual logged velocity at every spatial point. However, a Schwartz-target sequential continuity theorem does not establish that the `3–3–1` gradient block converges against a **non-Schwartz** physical H³ target.

We therefore first prove a genuine **two-profile** nonlinear estimate on real Schwartz triples. It requires third-derivative factors only in the natural `L²` topology, and the first derivative only in a common uniform `L∞` pointwise bound:

```
|I(a,b,c) - I(a',b',c')|
 ≤ K (‖a-a'‖₂ ‖b‖₂ + ‖a'‖₂ ‖b-b'‖₂)
   + δ ‖a'‖₂ ‖b'‖₂,
```

where `|c(x)| ≤ K` and `|(c-c')(x)| ≤ δ` for all `x`. This uses the exact real Schwartz integral, the established telescoping identity, and the existing verified `L²×L²×L∞` integral estimate. The project’s factor `2` in the gradient energy pairing is retained explicitly.

## Spectral and physical realization

For independent decoder-matched real Schwartz components `f,g` representing weighted H³ states `F,G`, the same estimate admits the concrete majorants

- `K = C₁ ‖F‖`;
- `δ = C₁ ‖F-G‖`.

The main theorem `fullGradientTriple_spectralMatchedPair_modulus244` gives the resulting weighted-H³ perturbation estimate for one entire physical `3–3–1` gradient triple, with no extra matching hypotheses beyond exact zeroth-order realization.

When both Schwartz components approximate the **same physical Navier–Stokes snapshot**, `thirdFullSchwartz_physicalPairFirstJet_abs_le_sumErrors244` additionally bounds their first-jet discrepancy by the sum of their individual H³ spectral errors relative to the actual snapshot. This provides a directly physical common-target error gauge, independent of any claim that the target itself is Schwartz.

## Scope and next frontier

This is a strict quantitative two-profile modulus, not yet a complete 243-slot gradient Cauchy/physical integral identification. The next step is to sum the 4 gradient triples per slot and all 243 finite slots, use the synchronized 81 third-jet `L²` Cauchy bounds and spectral first-jet gauge, and identify the resulting scalar with the independently defined physical trilinear pairing by `L²×L²×L∞` product convergence. The signed 3–2–2 monomial additionally requires identifying its completed `L⁴` second-derivative limits with the physical derivatives. No H⁴ dissipation approximation or unconditional Navier–Stokes continuation is claimed.
