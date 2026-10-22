# Exact temporal action of the two-band HEAT concentration rate

Base commit: `b7398322`, *prove two-band heat temporal exhaustion of near-Young concentration*.

For the scalar two-band heat orbit with radial weights `1` and `n²`, squared masses `n⁹` and `exp(-2(n²-1)t)`, define the normalized Young gap `R_n(t)` and the instantaneous signed heat concentration source `B_n(t)` (the previously formalized six-moment heat rate evaluated on those masses).

A direct differentiation of the original rational two-band gap proves

    R_n'(t) = -B_n(t).

The derivative of the high-band mass is `-2(n²-1) exp(-2(n²-1)t)`; the general high-mass gap derivative factors as

    ∂_y R = x (r²-1)² (x²-r⁴ y²)/((x+y)(x+r⁴y))².

The exact identity is obtained by the product / quotient / exponential derivative rules and the heat moment factorization. This is **not** an inferred PDE equation for Navier–Stokes: the model is an algebraic heat spectral orbit.

Continuous differentiability of the rational/exponential orbit supplies interval integrability and the fundamental theorem of calculus:

    ∫_s^t B_n(τ) dτ = R_n(s) - R_n(t).

Since the preceding checkpoint proved `R_n` nonnegative and nonincreasing for nonnegative time and `R_n(0) ≤ 1/n`, we obtain for every `0 ≤ s ≤ t`,

    0 ≤ ∫_s^t B_n(τ)dτ ≤ 1/n.

At the same time `B_n(0) ≥ n/128`. Hence growing instantaneous heat production is compatible with a vanishing integrated action. The result distinguishes time coherence from pointwise Fourier concentration and directs subsequent work to the **actual PDE signed transport forcing of the evolving spectral distribution**.

Compilation note: the Lean code is supplied as a patch for the user's local `lake env lean`; no local Lean compiler was available during authoring.
