# Compact-time-test spanning and the homogeneous physical distribution kernel

Base commit: `7ccb61f1` — derive physical time distributions from solenoidal weak FTC.

## Formal statement

On the actual open physical interval `Ioo a b`, define an explicit compact test
span property: there exists one smooth compact time test `ρ` such that every
compact smooth test `θ` has a decomposition

    θ = ∂η + (∫ θ) ρ,

where `η` is itself a smooth compactly supported time test on the same interval.

**Proved conditionally on this span:** for an arbitrary scalar distribution `D`
with `∂D=0`, take `K=D(ρ)`. The derivative-zero identity gives `D(∂η)=0`,
and therefore `D(θ) = K * ∫θ` for every test. Thus `D` equals the genuine
regular distribution of the constant function `K`. No representation theorem
for locally integrable functions is required for this abstract step.

Apply the result to the established physical FTC defect distribution and the
previous equivalence between its vanishing derivative and the physical
solenoidal time-distribution momentum equation. The defect is then exactly a
constant regular distribution for each solenoidal spatial test.

## Strictly outstanding hard mathematics

1. **Prove the compact-test span unconditionally on connected open intervals.**
   Normalize a nonnegative compact bump `ρ` to integral 1. For a test `θ`,
   `θ₀ := θ - (∫θ) ρ` has integral zero. Show the primitive
   `η(t) = ∫_{-∞}^t θ₀(s) ds` is smooth, compactly supported, and supported
   inside `(a,b)`; its derivative is `θ₀`. This is the true one-dimensional
   test-function construction. It is NOT proved by the present Lean module.
2. Transfer the resulting constant defect to the earlier outer primitive
   representation, cancel the constant, and conclude the physical Hilbert FTC.
3. Establish the actual momentum time-distribution PDE from the spatially
   tested classical preterminal PDE, with justified interchange of time
   differentiation and spatial pairing. This remains independent.

The new proof makes no changes to the path admissibility assumptions and does
not claim an unconditional Navier–Stokes continuation theorem.
