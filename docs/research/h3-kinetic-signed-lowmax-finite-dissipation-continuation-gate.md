# Finite full-H3 dissipation: terminal continuation criterion

Base: `651e2aae9396dc71120bf792e48d8adb377a8d14`.

## Mathematical derivation

The accepted `exists_terminalTail_one_div_terminalDistance_le_dissipation3_of_noH3PathExtension` shows, under `LoggedPreterminalH3PathAdmissible`, `PreterminalH3EnergyClass`, and hypothetical nonextension, that for every strict tail start `b` some `c` in `(b,T)` satisfies

`1 / (T-t) <= velocityH3Dissipation3At u t` for all `t in (c,T)`.

The separately established physical component inequality `velocityH3Dissipation3At_le_dissipationAt u t` therefore gives

`1 / (T-t) <= velocityH3DissipationAt u t` on the *same* strict tail.

But the library theorem `not_integrableOn_one_div_terminalDistance` proves the left side is not Lebesgue integrable over `(c,T)`. Consequently the entire physical full-H3 dissipation is not integrable there under nonextension.

By contrapositive, if the **additional** hypothesis

`IntervalIntegrable (velocityH3DissipationAt u) volume b T`

holds for even one positive strict terminal subtail, then `∃ v, SmoothContinuationExtension u v T`.

## Research implications

This is a conditional regularity theorem, NOT unconditional Navier–Stokes global regularity: it does **not** derive finite full-H3 dissipation from basic solution hypotheses. In particular the kinetic signed-sixth-flux branch frequently assumes exactly this finiteness while also studying failure of terminal extension or trace. Its analytic relevance should be reassessed: if the intended research goal is unconditional continuation, it must establish finiteness, or abandon that premise in the blowup branch.

The earlier tenth-power residual vacuity remains independently valid and is not repaired by this result. A conditional high-radial packing theorem under finite full-H3 dissipation may still be mathematically true, but it no longer describes a path failing smooth continuation.

## Formal declarations

- `thirdFullPhysical_noExtension_harmonicFullDissipation244`
- `thirdFullPhysical_noExtension_fullDissipation_nonintegrableStrictTail244`
- `thirdFullPhysical_finiteFullDissipation_strictTail_forcesContinuation244`
- `thirdFullPhysical_finiteFullDissipation_energyTail_forcesContinuation244`

No `sorry`, `admit`, or additional axiom. Source-level audits are not Lean compilation; run the supplied targeted and full Lake checks.
