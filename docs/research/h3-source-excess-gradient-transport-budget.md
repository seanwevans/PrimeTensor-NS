# Cofinal source-excess H³ costs versus the physical gradient-energy transport budget

**Base:** `2d9ef134`, the accepted automatic integrated positive signed-gap transport theorem.

## Exact local physical comparison

At each strict H³ energy-class time `s`, write

- `E(s) = velocityH3EnergyAt u s ≥ 1`;
- `D(s) = velocityH3DissipationAt u s ≥ 0`;
- `Tr(s) = velocityH3TransportDerivativeAt u s`;
- `h(s) = h3PathCanonicalSqrtEnergyGradientEnvelope u s`;
- `M(s) = 4422*(1+|h(s)|)*E(s) ≥ 0`.

The already accepted full H³ transport commutator implies

    |Tr(s)| ≤ M(s).

Consequently

    max(0,-Tr(s)-2*D(s)) ≤ M(s).

This bound retains both copies of the viscous term *inside* the left-hand positive part. It does not claim that the canonical envelope `h` is a sharp lower bound on the actual C¹ gradient.

Both the coefficient `4422*(1+|h(s)|)` and `E(s)` are continuous on every strict-time energy-class tail by the committed compact interval Landau/energy regularity theorems. Therefore `M` is interval-integrable on any closed `[x,y] ⊂ (a,T)`. The earlier automatic signed-gap theorem provides independent interval integrability of the positive transport surplus. Actual interval monotonicity proves

    ∫_x^y max(0,-Tr(s)-2*D(s)) ds ≤ ∫_x^y M(s) ds.

No terminal integrability of either profile is assumed.

## Cumulative source-excess alternative

Reuse precisely the source windows selected by the accepted `h3Critical_noL2Trace_cofinalQuintic_endpointDrain_or_gapTransport` witness, with times `a_k = t(v(k))`, right endpoints `e_k = a_k+δ_k`, and enhanced dissipation floor

    H_k = M(v(k)) + q(v(k)) / [3(3+C_L)].

For every finite `m`, either a genuine large-Riccati-energy observation occurs on one of the first `m+1` selected windows, or

    Σ_(k=0)^m H_k δ_k + 1
      ≤ E(a_0) + Σ_(k=0)^(m-1) ∫_(e_k)^(a_(k+1))
              4422*(1+|h(s)|)*E(s) ds.

This is the first cofinal source-excess compensation bound here with a *fully explicit continuous physical gradient-energy integrand* on the actual intervening gaps, rather than sampled transport or positive transport derivative itself. It remains a necessary cost alternative, not an a priori upper bound on the coefficient, and proves no terminal continuation. If the cumulative charges diverge, the right-hand gradient-energy budget must diverge unless the Riccati-energy alternative occurs; a terminal-uniform physical budget would be a separate theorem.

## Lean and audit

The module `TerminalActualSourceExcessGradientTransportBudget.lean` contains four theorems:

1. `h3Critical_positiveSignedTransport_le_canonicalGradientEnergy`
2. `h3Critical_canonicalGradientEnergy_intervalIntegrable_onGap`
3. `h3Critical_physicalGap_positiveTransportIntegral_le_gradientEnergy`
4. `h3Critical_noL2Trace_cofinalQuintic_gradientTransportBudget`

Registrar adds the module to the root and the axiom audit with eight checks. The source has no new axioms or `sorry`. Static checks do not replace Lean elaboration in the pinned toolchain.
