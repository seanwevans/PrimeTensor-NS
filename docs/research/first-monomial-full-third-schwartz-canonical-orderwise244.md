# Canonical orderwise H³ transport at an actual Schwartz-realized NS slice

Base: `c252128d` — complete Schwartz static obstruction and lower transport budget.

## Why the preceding bound was not the sharp path result

The preceding bridge applied the `6 h E` and `18 h E` *total-energy* versions
of the order-one and order-two commutator estimates, and carried explicit
flux/pairing assumptions. Independent, already-proved results in
`KineticQuarticCanonicalLowerOrderSignedTransport.lean` eliminate those
contracts on an admissible path and retain the true energy orders:

```
|T₁(t)+T₂(t)| ≤ C₁ sqrt(E(t)) (6 E₁(t)+18 E₂(t)).
```

The canonical gradient envelope is
`h3PathCanonicalSqrtEnergyGradientEnvelope`; its proof uses the existing
spectral derivative-evaluation estimate. The H³ path hypotheses yield the
H³ integrability at time `t`, energy-class integration by parts, cancellation
of zeroth-order flux, and the first/second transport pairing integrability.
No new PDE hypothesis is inserted by this module.

## Exact spatial bridge

For a real Schwartz velocity `f` that **actually realizes the NS slice**
`u(t)`, the previously proved spatial identities identify E, E₁, E₂,
the entire four-order dissipation and the signed third-order commutator.
The new quantitative statement is

```
E'(t) + 2 D_full(f)
    ≤ C₁ sqrt(E(f)) (6 E₁(f)+18 E₂(f)) - [G₃(f)+3M(f)].
```

The exact equality without `T₀` is also reconstructed without a separate
kinetic-flux premise. An adverse cubic dominating `2 D_full` **plus** the
orderwise lower transport budget therefore suffices for positive H³ slope.
Conversely positive slope forces the necessary signed inequality, which
is weaker than that sufficient condition.

## Actual nonextension alternative

The repository's prior conditional nonextension result says arbitrarily
high unabsorbed Riccati rate entails at least one of two physical branches:

```
(4422 + M) E < C₁ sqrt(E) (6 E₁ + 18 E₂),
      OR
2 D_full < -[G₃+3M].
```

The present transfer states this in Schwartz variables for each **realized**
actual NS slice. A corollary takes the preexisting no-extension witness
and assumes a separate Schwartz-realization contract on the chosen subtail.
Neither branch is ruled out; the contract does not construct a solution,
prove blowup, or establish global regularity. The fixed-kinetic *static*
noncoercivity theorem is logically separate and cannot be substituted for
that realization contract.

## Lean proof registration and validation

Seven statements are registered in `PrimeTensor.lean` and
`tools/audit/FirstMonomialTriad.lean` using the included idempotent script.
Run `python3 proof/generate_index.py` and its `--check`, the new Lean module,
the audit module, full `lake build` and baseline audit on Rocky Linux before
committing. The ZIP was prepared without a local Lean executable; its source
has not been typechecked by Lean in the packaging runtime.
