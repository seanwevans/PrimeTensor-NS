# Full H³ sixth-power Fourier flux: exact off-solenoidal defect

**Baseline:** `1bbee05f` — identify full physical H³ Schwartz commutator with exact sixth-power spectral flux.

## Why this is the next genuine obstruction

The physical H³ theorem established the exact sixth-power flux for arbitrary **solenoidal** real Schwartz velocities. The existing matched Schwartz families completing the canonical weighted H³ state are not themselves proved divergence-free. Substituting them directly into the solenoidal theorem would introduce an unproved premise.

The natural remedy is an exact longitudinal remainder rather than a new hypothesis.

## Full momentum-conserving complex formula

Use `p+q+r=0`, let `a=p·q`, `b=p·r`, `c=q·r`, and let `A,B,C` be arbitrary complex Fourier polarizations. Define the three longitudinal contractions

```
α := p·A, β := q·B, γ := r·C.
X := A·C, Y := A·B, Z := B·C.
```

All polarization dots are **complex bilinear**, without conjugation. The existing fully symmetrized corrected physical six-symbol `S₆` satisfies

```
S₆ = F₆ + D_long,

D_long = -Z α b (b² + 3bc + 3c²)
         -X β c (3b² + 3bc + c²)
         -Y γ c (3a² + 3ac + c²).
```

Here `F₆` is the established three-term sixth-power radial flux. This polynomial identity is exact and independent of any regularity or solenoidality hypothesis. `D_long=0` when α=β=γ=0, recovering the previous theorem.

## Unrestricted Schwartz integral and actual physical transport

For an arbitrary complex Schwartz field, the corrected integrand `F₆ + D_long` is integrable (the prior six-orbit and ordered-kernel estimates supply this without estimating the two summands separately), and

```
∫(F₆ + D_long) = 6 ∫ K_ordered.
```

For every **real** Schwartz field (not necessarily divergence-free), this yields

```
fullSchwartzThirdCommutator244(f)
  = ((2π)^7/3) · Im ∫(F₆(complexify f) + D_long(complexify f)).
```

The `1/3` normalization comes from `2/6`, and `i^7 = -i` fixes the imaginary-part sign.

For every already-existing H³ matched Schwartz completion `F`, this corrected scalar converges to the canonical full-third transport. Under the existing physical-gradient/canonical identification and admissible genuine Navier–Stokes slice assumptions, it converges to the **actual physical** `velocityH3TransportDerivative3At`. No solenoidality of the approximating Schwartz profiles is postulated.

## Remaining hard analysis

Prove that the explicit divergence correction vanishes under a *solenoidality-preserving* weighted H³ approximation, or obtain a quantitative divergence-weighted bound that tends to zero on the existing matched completion. Until then the physical H³ limit is a corrected flux limit, not an unqualified limit of its separate uncorrected flux term. No new universal signed absorption estimate is asserted.

## Local checks

The universal scalar polynomial was checked independently with symbolic algebra. The repair parenthesizes the defect definition and uses an explicit final algebraic reassociation after applying the universal scalar identity. Registrar repeated `--apply`/`--check`, ZIP member validity, and Python source syntax were checked. **Lean compilation must be performed in the project's Lake environment.**
