# Inverse-square terminal H³ dissipation and a weighted continuation criterion

Base: `ca95047fd4e43e88fda53b0cfc3a74d79cc8e4be`.

## PDE-derived inverse-square rate

The pre-existing formalized terminal rate under hypothetical nonextension gives, for a fixed kinetic anchor `b` and sufficiently late `t`,

    1 <= B * (T - t)^8 * D3(t)^3,
    B = 81 * K^8 * E0(b).

The previously formalized `exists_terminalTail_const_mul_terminalDistance_sq_le_one` supplies a still shorter terminal interval where `max(B,1) * (T-t)^2 <= 1`. Let `d=T-t` and `X=d^2*D3(t) >= 0`. Then

    1 <= (B*d^2) * X^3 <= X^3,

so `X >= 1`. Thus

    1 <= (T-t)^2 * D3(t) <= (T-t)^2 * D_full(t).

This is the **inverse-square** consequence already latent in the original proof, stronger than the subsequently recorded harmonic bound `D3 >= 1/(T-t)`. The final step uses the established physical `velocityH3Dissipation3At_le_dissipationAt`.

## Conditional continuation with a vanishing weight

On the same terminal interval `d>0`, division by `d` shows

    1/(T-t) <= (T-t)*D_full(t).

The left side is nonintegrable on any strict terminal interval ending at `T`, by the existing `not_integrableOn_one_div_terminalDistance`. Hence hypothetical nonextension forces

    NOT IntegrableOn (fun t => (T-t)*D_full(t)) (Ioo b T)

for every `b` on the energy-class tail. The contrapositive gives smooth extension from the **additional** analytic premise

    IntervalIntegrable (fun t => (T-t)*D_full(t)) volume b T.

The time weight vanishes at `T`. Thus this is a weaker finiteness requirement than unweighted terminal full-H3 dissipation, though it is not derived from basic Navier–Stokes data in this patch. In particular it is not a resolution of the Clay problem.

## Interpretation for the signed-sixth-flux programme

The old tenth-power residual remains automatic because its existential viscous width is unanchored. The later residual-free actual high-tail packing theorem is meaningful as a *conditional* spectral statement. But finite ordinary full-H3 dissipation already implies smooth continuation, and the present weighted criterion rules out nonextension under a wider, explicitly quantified class of tail budgets.

The hard unresolved PDE task is to derive the weighted finiteness premise (or another truly independent regularity mechanism) without presupposing continuation. No adverse-activity recurrence or bounded Fourier-cutoff hypothesis is introduced here.

## Declarations

- `thirdFullKinetic_scalar_cubicRate_forces_inverseSquare244`
- `thirdFullPhysical_noExtension_inverseSquareFullDissipation244`
- `thirdFullPhysical_noExtension_harmonicWeightedFullDissipation244`
- `thirdFullPhysical_noExtension_weightedFullDissipation_nonintegrableStrictTail244`
- `thirdFullPhysical_weightedFullDissipation_strictTail_forcesContinuation244`
- `thirdFullPhysical_weightedFullDissipation_energyTail_forcesContinuation244`

No proof placeholders or new axioms are introduced. Source/registration checks do not constitute Lean kernel compilation.
