# Quantitative two-band radial Fourier variance

Base: `0e35a937` — strict physical H³ Fourier radial variance from null spheres.

## Exact spectral mass input

Write `q(ξ)=(2π)^2 |ξ|²`, `S(ξ)=Σ_j |û_j(ξ)|²` and

- `E0=∫S`, `E2=∫q²S`, `D3=∫q⁴S`;
- `F1=E0 D3-E2²` (the first physical Fourier Cauchy defect).

For a frequency split `lo<hi`, suppose the actual Fourier mass in each band

    {ξ | q(ξ)² ≤ lo} and {ξ | hi ≤ q(ξ)²}

is at least `bandMass`, a nonnegative quantity if the hypothesis is useful.
The new exact integral comparison gives

    F1 ≥ E0 · bandMass · ((hi-lo)/2)²,

provided `E0>0`. This is a quantitative variance inequality **conditional on
observed band masses**, not an assumed universal spectral-spread property.

## Reason for the factor 1/4

The centered quantity `E0 q²-E2` differs from zero by at least
`E0 (hi-lo)/2` on one of the two separated frequency bands, depending on
whether the energy-weighted mean `E2/E0` falls below or above their midpoint.
The centered variance integral is therefore at least this deviation squared
times the mass of that band. Its exact physical identification is

    E0 F1 = ∫ (E0 q²-E2)² S.

No spectral regularity or finite ambient volume is assumed in the measure
comparison. The generic theorem works on arbitrary measured spaces.

## Consequence for sharp Young absorption

For nonnegative `K` and positive top dissipation, the previous first-Cauchy
variance correction is now a **band-mass-dependent quantitative improvement**:

    K E3 + (27/256) K⁴ E0 bandMass ((hi-lo)/2)²/D3
      ≤ D3 + (27/256) K⁴ E0.

This genuinely strengthens the strict pointwise variance result under a
concrete measurable condition. It is not an unconditional regularity proof:
one would need to show that both band masses remain adequately large relative
to the terminal growth scale, rather than collapsing into a thin shell.

## Audit

The registrar appends the root import, `#check` and `#print axioms` checks for
four new theorems. Regenerate the proof index, verify fragments, compile the
new module, run the full Lean build and baseline audit before committing.
